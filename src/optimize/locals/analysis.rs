//! Web decomposition, liveness, interference, and copy detection.

use crate::wasm::{FuncInstr, LocalValType, OtherInstr, WasmFunction};
use std::collections::{HashMap, HashSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct WebId(pub usize);

#[derive(Clone, Debug)]
pub struct Web {
    pub id: WebId,
    pub ty: LocalValType,
    pub param_index: Option<u32>,
    pub def_sites: Vec<usize>,
    pub use_sites: Vec<usize>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CopyKind {
    GetSet,
    GetTee,
}

#[derive(Clone, Debug)]
pub struct CopyPair {
    pub src: WebId,
    pub dst: WebId,
    pub at: usize,
    pub kind: CopyKind,
    pub instr_saved: u32,
}

#[derive(Clone, Debug)]
pub struct Analysis {
    pub webs: Vec<Web>,
    pub web_of_instr: Vec<Option<WebId>>,
    pub interferes: Vec<(WebId, WebId)>,
    pub copies: Vec<CopyPair>,
    pub cfg: Cfg,
}

#[derive(Clone, Debug)]
pub struct Cfg {
    pub blocks: Vec<BasicBlock>,
}

#[derive(Clone, Debug)]
pub struct BasicBlock {
    pub start: usize,
    pub end: usize,
    pub succs: Vec<usize>,
    pub preds: Vec<usize>,
}

struct UnionFind {
    parent: Vec<usize>,
}

impl UnionFind {
    fn new(n: usize) -> Self {
        Self {
            parent: (0..n).collect(),
        }
    }

    fn find(&mut self, x: usize) -> usize {
        if self.parent[x] != x {
            let root = self.find(self.parent[x]);
            self.parent[x] = root;
        }
        self.parent[x]
    }

    fn union(&mut self, a: usize, b: usize) {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra != rb {
            self.parent[rb] = ra;
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum DefNode {
    Param(u32),
    Instr(usize),
}

/// Number of basic blocks in `instrs` (empty body → 0).
pub fn basic_block_count(instrs: &[FuncInstr]) -> usize {
    if instrs.is_empty() {
        return 0;
    }
    build_cfg(instrs).blocks.len()
}

impl Analysis {
    pub fn build(func: &WasmFunction) -> Result<Self, String> {
        if func.local_types.is_empty() {
            return Err("no locals".into());
        }
        if func.instrs.is_empty() {
            return Err("empty body".into());
        }

        let cfg = build_cfg(&func.instrs);
        let (webs, web_of_instr) = build_webs(func, &cfg);
        if webs.is_empty() {
            return Err("no webs".into());
        }
        let interferes = build_interference(&webs);
        let copies = find_copies(func, &web_of_instr);

        Ok(Self {
            webs,
            web_of_instr,
            interferes,
            copies,
            cfg,
        })
    }
}

fn build_cfg(instrs: &[FuncInstr]) -> Cfg {
    let mut block_starts: Vec<usize> = vec![0];
    for (i, instr) in instrs.iter().enumerate() {
        match instr {
            FuncInstr::Other(OtherInstr::Block | OtherInstr::Loop | OtherInstr::If) => {
                if i + 1 <= instrs.len() {
                    block_starts.push(i + 1);
                }
            }
            FuncInstr::Other(OtherInstr::Else) => block_starts.push(i + 1),
            _ => {}
        }
    }
    block_starts.sort_unstable();
    block_starts.dedup();

    let mut blocks: Vec<BasicBlock> = Vec::new();
    for (bi, &start) in block_starts.iter().enumerate() {
        let end = block_starts
            .get(bi + 1)
            .copied()
            .unwrap_or(instrs.len())
            .min(instrs.len());
        if start < end {
            blocks.push(BasicBlock {
                start,
                end,
                succs: Vec::new(),
                preds: Vec::new(),
            });
        }
    }
    if blocks.is_empty() {
        blocks.push(BasicBlock {
            start: 0,
            end: instrs.len(),
            succs: Vec::new(),
            preds: Vec::new(),
        });
    }

    let block_of: Vec<usize> = (0..instrs.len())
        .map(|i| {
            blocks
                .partition_point(|b| b.start <= i)
                .saturating_sub(1)
        })
        .collect();

    #[derive(Clone)]
    struct CtrlFrame {
        header_block: usize,
        kind: CtrlKind,
    }

    #[derive(Clone, Copy)]
    enum CtrlKind {
        Block,
        Loop,
        If,
    }

    fn br_target(stack: &[CtrlFrame], depth: u32) -> Option<usize> {
        let idx = stack.len().checked_sub(depth as usize + 1)?;
        Some(stack[idx].header_block)
    }

    let mut stack: Vec<CtrlFrame> = Vec::new();

    for (i, instr) in instrs.iter().enumerate() {
        let bi = block_of[i];
        match instr {
            FuncInstr::Other(OtherInstr::Block) => {
                stack.push(CtrlFrame {
                    header_block: bi,
                    kind: CtrlKind::Block,
                });
            }
            FuncInstr::Other(OtherInstr::Loop) => {
                stack.push(CtrlFrame {
                    header_block: bi,
                    kind: CtrlKind::Loop,
                });
            }
            FuncInstr::Other(OtherInstr::If) => {
                stack.push(CtrlFrame {
                    header_block: bi,
                    kind: CtrlKind::If,
                });
            }
            FuncInstr::Other(OtherInstr::End) => {
                if let Some(frame) = stack.pop() {
                    let after = bi + 1;
                    if after < blocks.len() {
                        add_edge(&mut blocks, bi, after);
                    }
                    match frame.kind {
                        CtrlKind::Block | CtrlKind::If => {
                            if after < blocks.len() {
                                add_edge(&mut blocks, frame.header_block, after);
                            }
                        }
                        CtrlKind::Loop => {
                            add_edge(&mut blocks, bi, frame.header_block);
                        }
                    }
                }
            }
            FuncInstr::Other(OtherInstr::Br(depth)) => {
                if let Some(target) = br_target(&stack, *depth) {
                    add_edge(&mut blocks, bi, target);
                }
            }
            FuncInstr::Other(OtherInstr::BrIf(depth)) => {
                if let Some(target) = br_target(&stack, *depth) {
                    add_edge(&mut blocks, bi, target);
                }
                if bi + 1 < blocks.len() {
                    add_edge(&mut blocks, bi, bi + 1);
                }
            }
            FuncInstr::Other(OtherInstr::BrTable { targets }) => {
                for &depth in targets {
                    if let Some(target) = br_target(&stack, depth) {
                        add_edge(&mut blocks, bi, target);
                    }
                }
                if bi + 1 < blocks.len() {
                    add_edge(&mut blocks, bi, bi + 1);
                }
            }
            FuncInstr::Other(OtherInstr::Return | OtherInstr::Unreachable) => {}
            _ => {
                if bi + 1 < blocks.len() && !is_terminator(instr) {
                    add_edge(&mut blocks, bi, bi + 1);
                }
            }
        }
    }

    for bi in 0..blocks.len().saturating_sub(1) {
        let last = blocks[bi].end.saturating_sub(1);
        if last < instrs.len() && !is_terminator(&instrs[last]) {
            add_edge(&mut blocks, bi, bi + 1);
        }
    }

    Cfg { blocks }
}

fn is_terminator(instr: &FuncInstr) -> bool {
    matches!(
        instr,
        FuncInstr::Other(
            OtherInstr::Br(_)
                | OtherInstr::BrIf(_)
                | OtherInstr::BrTable { .. }
                | OtherInstr::Return
                | OtherInstr::Unreachable
        )
    )
}

fn add_edge(blocks: &mut [BasicBlock], from: usize, to: usize) {
    if from >= blocks.len() || to >= blocks.len() || from == to {
        return;
    }
    if !blocks[from].succs.contains(&to) {
        blocks[from].succs.push(to);
    }
    if !blocks[to].preds.contains(&from) {
        blocks[to].preds.push(from);
    }
}

fn build_webs(func: &WasmFunction, cfg: &Cfg) -> (Vec<Web>, Vec<Option<WebId>>) {
    let mut nodes: Vec<DefNode> = Vec::new();
    let mut node_index: HashMap<DefNode, usize> = HashMap::new();

    for p in 0..func.num_params {
        let n = DefNode::Param(p);
        node_index.insert(n, nodes.len());
        nodes.push(n);
    }

    for (i, instr) in func.instrs.iter().enumerate() {
        if matches!(instr, FuncInstr::LocalSet(_) | FuncInstr::LocalTee(_)) {
            let n = DefNode::Instr(i);
            node_index.insert(n, nodes.len());
            nodes.push(n);
        }
    }

    let n_nodes = nodes.len();
    let mut uf = UnionFind::new(n_nodes + func.instrs.len());

    let reaching = reaching_defs_per_local(func, cfg);

    for (i, instr) in func.instrs.iter().enumerate() {
        let FuncInstr::LocalGet(local) = instr else { continue };
        let get_node = n_nodes + i;
        let reaching_defs = &reaching[i];
        let mut defs_for_get: Vec<usize> = Vec::new();

        if let Some(&pid) = node_index.get(&DefNode::Param(*local)) {
            if reaching_defs.contains(&pid) {
                defs_for_get.push(pid);
            }
        }
        for (j, other) in func.instrs.iter().enumerate() {
            match other {
                FuncInstr::LocalSet(l) | FuncInstr::LocalTee(l) if *l == *local => {
                    if let Some(&did) = node_index.get(&DefNode::Instr(j)) {
                        if reaching_defs.contains(&did) {
                            defs_for_get.push(did);
                        }
                    }
                }
                _ => {}
            }
        }

        for &d in &defs_for_get {
            uf.union(get_node, d);
        }
        for w in defs_for_get.windows(2) {
            uf.union(w[0], w[1]);
        }
    }

    let mut groups: HashMap<usize, Vec<usize>> = HashMap::new();
    for i in 0..n_nodes + func.instrs.len() {
        let root = uf.find(i);
        groups.entry(root).or_default().push(i);
    }

    let mut webs = Vec::new();
    let mut instr_web: Vec<Option<WebId>> = vec![None; func.instrs.len()];

    for members in groups.values() {
        let mut def_sites = Vec::new();
        let mut use_sites = Vec::new();
        let mut ty = None;
        let mut param_index = None;

        for &m in members {
            if m < n_nodes {
                match nodes[m] {
                    DefNode::Param(p) => {
                        param_index = Some(p);
                        ty = func.local_types.get(p as usize).copied();
                    }
                    DefNode::Instr(i) => {
                        def_sites.push(i);
                        match &func.instrs[i] {
                            FuncInstr::LocalSet(l) | FuncInstr::LocalTee(l) => {
                                ty = func.local_types.get(*l as usize).copied();
                            }
                            _ => {}
                        }
                    }
                }
            } else {
                let i = m - n_nodes;
                use_sites.push(i);
                if ty.is_none() {
                    if let FuncInstr::LocalGet(l) = &func.instrs[i] {
                        ty = func.local_types.get(*l as usize).copied();
                    }
                }
            }
        }

        let Some(ty) = ty else { continue };

        let id = WebId(webs.len());
        for &i in &def_sites {
            instr_web[i] = Some(id);
        }
        for &i in &use_sites {
            instr_web[i] = Some(id);
        }
        webs.push(Web {
            id,
            ty,
            param_index,
            def_sites,
            use_sites,
        });
    }

    (webs, instr_web)
}

fn reaching_defs_per_local(func: &WasmFunction, cfg: &Cfg) -> Vec<HashSet<usize>> {
    let n = func.instrs.len();
    let mut nodes: Vec<DefNode> = Vec::new();
    let mut node_index: HashMap<DefNode, usize> = HashMap::new();

    for p in 0..func.num_params {
        let dn = DefNode::Param(p);
        node_index.insert(dn, nodes.len());
        nodes.push(dn);
    }
    for (i, instr) in func.instrs.iter().enumerate() {
        if matches!(instr, FuncInstr::LocalSet(_) | FuncInstr::LocalTee(_)) {
            let dn = DefNode::Instr(i);
            node_index.insert(dn, nodes.len());
            nodes.push(dn);
        }
    }

    let mut gen_set = vec![HashSet::new(); n];
    let mut kill = vec![HashSet::new(); n];
    for (i, instr) in func.instrs.iter().enumerate() {
        match instr {
            FuncInstr::LocalSet(local) | FuncInstr::LocalTee(local) => {
                if let Some(&did) = node_index.get(&DefNode::Instr(i)) {
                    gen_set[i].insert(did);
                    for (j, other) in func.instrs.iter().enumerate() {
                        match other {
                            FuncInstr::LocalSet(l) | FuncInstr::LocalTee(l) if *l == *local && j != i => {
                                if let Some(&oid) = node_index.get(&DefNode::Instr(j)) {
                                    kill[i].insert(oid);
                                }
                            }
                            _ => {}
                        }
                    }
                    if let Some(&pid) = node_index.get(&DefNode::Param(*local)) {
                        kill[i].insert(pid);
                    }
                }
            }
            _ => {}
        }
    }

    let mut block_gen = vec![HashSet::new(); cfg.blocks.len()];
    let mut block_kill = vec![HashSet::new(); cfg.blocks.len()];
    for (bi, block) in cfg.blocks.iter().enumerate() {
        for i in block.start..block.end {
            block_gen[bi].extend(gen_set[i].iter().copied());
            block_kill[bi].extend(kill[i].iter().copied());
        }
    }

    let mut in_set = vec![HashSet::new(); cfg.blocks.len()];
    let mut out_set = vec![HashSet::new(); cfg.blocks.len()];
    for p in 0..func.num_params {
        if let Some(&pid) = node_index.get(&DefNode::Param(p)) {
            in_set[0].insert(pid);
            out_set[0].insert(pid);
        }
    }

    let mut changed = true;
    while changed {
        changed = false;
        for bi in 0..cfg.blocks.len() {
            let mut new_in = HashSet::new();
            if cfg.blocks[bi].preds.is_empty() {
                for p in 0..func.num_params {
                    if let Some(&pid) = node_index.get(&DefNode::Param(p)) {
                        new_in.insert(pid);
                    }
                }
            } else {
                for &p in &cfg.blocks[bi].preds {
                    new_in.extend(out_set[p].iter().copied());
                }
            }
            if new_in != in_set[bi] {
                in_set[bi] = new_in;
                changed = true;
            }

            let mut new_out = in_set[bi].clone();
            for k in &block_kill[bi] {
                new_out.remove(k);
            }
            new_out.extend(block_gen[bi].iter().copied());
            if new_out != out_set[bi] {
                out_set[bi] = new_out;
                changed = true;
            }
        }
    }

    let block_of: Vec<usize> = (0..n)
        .map(|i| {
            cfg.blocks
                .partition_point(|b| b.start <= i)
                .saturating_sub(1)
        })
        .collect();

    let mut reaching_at = vec![HashSet::new(); n];
    for i in 0..n {
        let bi = block_of[i];
        reaching_at[i] = in_set[bi].clone();
        for b in cfg.blocks[bi].start..i {
            for k in &kill[b] {
                reaching_at[i].remove(k);
            }
            reaching_at[i].extend(gen_set[b].iter().copied());
        }
    }
    reaching_at
}

fn build_interference(webs: &[Web]) -> Vec<(WebId, WebId)> {
    let mut intervals: Vec<(usize, usize, WebId)> = Vec::new();
    for web in webs {
        let mut points: Vec<usize> = web.def_sites.clone();
        points.extend(web.use_sites.iter().copied());
        if points.is_empty() {
            continue;
        }
        let first = *points.iter().min().unwrap();
        let last = *points.iter().max().unwrap();
        intervals.push((first, last, web.id));
    }

    let mut pairs = HashSet::new();
    for i in 0..intervals.len() {
        for j in (i + 1)..intervals.len() {
            let (a0, a1, wa) = intervals[i];
            let (b0, b1, wb) = intervals[j];
            if wa != wb && a0 <= b1 && b0 <= a1 {
                pairs.insert((wa.min(wb), wa.max(wb)));
            }
        }
    }
    pairs.into_iter().collect()
}

fn find_copies(func: &WasmFunction, web_of: &[Option<WebId>]) -> Vec<CopyPair> {
    let mut copies = Vec::new();
    let instrs = &func.instrs;
    let mut i = 0;
    while i + 1 < instrs.len() {
        if let FuncInstr::LocalGet(_) = &instrs[i] {
            let src = web_of[i];
            match &instrs[i + 1] {
                FuncInstr::LocalSet(_) => {
                    if let (Some(src), Some(dst)) = (src, web_of[i + 1]) {
                        copies.push(CopyPair {
                            src,
                            dst,
                            at: i,
                            kind: CopyKind::GetSet,
                            instr_saved: 2,
                        });
                    }
                    i += 2;
                    continue;
                }
                FuncInstr::LocalTee(_) => {
                    if let (Some(src), Some(dst)) = (src, web_of[i + 1]) {
                        copies.push(CopyPair {
                            src,
                            dst,
                            at: i,
                            kind: CopyKind::GetTee,
                            instr_saved: 1,
                        });
                    }
                    i += 2;
                    continue;
                }
                _ => {}
            }
        }
        i += 1;
    }
    copies
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wasm::parse_wasm_functions_bytes;

    #[test]
    fn finds_get_set_copy() {
        let wasm = wat::parse_str(
            r#"(module (func (param i32) (local i32)
              local.get 0
              local.set 1
              local.get 1))"#,
        )
        .unwrap();
        let m = parse_wasm_functions_bytes(&wasm).unwrap();
        let a = Analysis::build(&m.functions[0]).unwrap();
        assert_eq!(a.copies.len(), 1);
        assert_eq!(a.copies[0].instr_saved, 2);
    }
}
