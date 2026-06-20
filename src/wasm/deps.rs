//! Dependency edges between opaque instructions (SuperStack-compatible).

use crate::semantics::SemOp;
use crate::wasm::segment::OpaqueMeta;
use std::collections::{BTreeSet, HashMap};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum MemWidth {
    B1,
    B2,
    B4,
}

#[derive(Clone, Debug)]
struct MemAccess {
    id: u32,
    is_load: bool,
    is_call: bool,
    mem: u32,
    offset: u32,
    width: MemWidth,
    addr_symbol: String,
}

#[derive(Clone, Debug)]
struct VarAccess {
    id: u32,
    is_call: bool,
    is_get: bool,
    index: u32,
}

fn mem_width_for_op(op: &SemOp) -> MemWidth {
    MemWidth::B4
}

fn overlap_address(a: i64, w1: i64, b: i64, w2: i64) -> bool {
    a <= b && b < a + w1 || b <= a && a < b + w2
}

fn width_bytes(w: MemWidth) -> i64 {
    match w {
        MemWidth::B1 => 1,
        MemWidth::B2 => 2,
        MemWidth::B4 => 4,
    }
}

fn effective_addr(addr_symbol: &str, offset: u32) -> Option<i64> {
    addr_symbol
        .trim()
        .parse::<i64>()
        .ok()
        .map(|a| a.saturating_add(offset as i64))
}

fn are_dependent_mem(a: &MemAccess, b: &MemAccess) -> bool {
    if a.is_load && b.is_load {
        return false;
    }
    if a.is_call || b.is_call {
        return true;
    }
    let w1 = width_bytes(a.width);
    let w2 = width_bytes(b.width);
    match (
        effective_addr(&a.addr_symbol, a.offset),
        effective_addr(&b.addr_symbol, b.offset),
    ) {
        (Some(e1), Some(e2)) => overlap_address(e1, w1, e2, w2),
        _ => a.mem == b.mem,
    }
}

fn are_dependent_var(a: &VarAccess, b: &VarAccess) -> bool {
    if a.is_call || b.is_call {
        return true;
    }
    if a.is_get && b.is_get {
        return false;
    }
    a.index == b.index
}

fn simplify_dependencies(deps: &[(u32, u32)]) -> Vec<(u32, u32)> {
    let mut edges: BTreeSet<(u32, u32)> = deps.iter().copied().collect();
    loop {
        let mut changed = false;
        let current: Vec<_> = edges.iter().copied().collect();
        for &(a, b) in &current {
            for &(c, d) in &current {
                if b == c && edges.contains(&(a, d)) {
                    if edges.remove(&(a, b)) {
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
    edges.into_iter().collect()
}

fn collect_mem_accesses(ops: &[SemOp], meta: &[OpaqueMeta]) -> Vec<MemAccess> {
    let meta_by_id: HashMap<u32, &OpaqueMeta> = meta.iter().map(|m| (m.id, m)).collect();
    let mut out = Vec::new();
    for op in ops {
        match op {
            SemOp::I32Load { id, mem, offset } => {
                let m = meta_by_id.get(id).expect("opaque meta for load");
                let addr = m
                    .input_symbols
                    .first()
                    .cloned()
                    .unwrap_or_else(|| "?".into());
                out.push(MemAccess {
                    id: *id,
                    is_load: true,
                    is_call: false,
                    mem: *mem,
                    offset: *offset,
                    width: mem_width_for_op(op),
                    addr_symbol: addr,
                });
            }
            SemOp::I32Store { id, mem, offset } => {
                let m = meta_by_id.get(id).expect("opaque meta for store");
                let addr = m
                    .input_symbols
                    .get(1)
                    .or_else(|| m.input_symbols.first())
                    .cloned()
                    .unwrap_or_else(|| "?".into());
                out.push(MemAccess {
                    id: *id,
                    is_load: false,
                    is_call: false,
                    mem: *mem,
                    offset: *offset,
                    width: mem_width_for_op(op),
                    addr_symbol: addr,
                });
            }
            SemOp::Call { id, .. } => {
                out.push(MemAccess {
                    id: *id,
                    is_load: false,
                    is_call: true,
                    mem: 0,
                    offset: 0,
                    width: MemWidth::B4,
                    addr_symbol: String::new(),
                });
            }
            _ => {}
        }
    }
    out
}

fn collect_var_accesses(ops: &[SemOp]) -> Vec<VarAccess> {
    let mut out = Vec::new();
    for op in ops {
        match op {
            SemOp::GlobalGet { id, global_index } => out.push(VarAccess {
                id: *id,
                is_call: false,
                is_get: true,
                index: *global_index,
            }),
            SemOp::GlobalSet { id, global_index } => out.push(VarAccess {
                id: *id,
                is_call: false,
                is_get: false,
                index: *global_index,
            }),
            SemOp::Call { id, .. } => out.push(VarAccess {
                id: *id,
                is_call: true,
                is_get: false,
                index: 0,
            }),
            _ => {}
        }
    }
    out
}

pub fn compute_dependencies(ops: &[SemOp], opaque_meta: &[OpaqueMeta]) -> Vec<(u32, u32)> {
    let mem = collect_mem_accesses(ops, opaque_meta);
    let mut deps = Vec::new();
    for i in 0..mem.len() {
        for j in i + 1..mem.len() {
            if are_dependent_mem(&mem[i], &mem[j]) {
                deps.push((mem[i].id, mem[j].id));
            }
        }
    }

    let vars = collect_var_accesses(ops);
    for i in 0..vars.len() {
        for j in i + 1..vars.len() {
            if are_dependent_var(&vars[i], &vars[j]) {
                if vars[i].is_call && vars[j].is_call {
                    continue;
                }
                deps.push((vars[i].id, vars[j].id));
            }
        }
    }

    // Subterm dependencies: if opaque B uses result symbol of opaque A, A before B.
    let producer: HashMap<&str, u32> = opaque_meta
        .iter()
        .flat_map(|m| m.result_symbols.iter().map(move |s| (s.as_str(), m.id)))
        .collect();
    for m in opaque_meta {
        for input in &m.input_symbols {
            if let Some(&before) = producer.get(input.as_str()) {
                if before != m.id {
                    deps.push((before, m.id));
                }
            }
        }
    }

    simplify_dependencies(&deps)
}

pub fn ops_respect_dependencies(ops: &[SemOp], dependencies: &[(u32, u32)]) -> bool {
    let mut index_of: HashMap<u32, usize> = HashMap::new();
    for (i, op) in ops.iter().enumerate() {
        if let Some(id) = op.opaque_id() {
            index_of.insert(id, i);
        }
    }
    dependencies.iter().all(|&(before, after)| {
        match (index_of.get(&before), index_of.get(&after)) {
            (Some(&i), Some(&j)) => i < j,
            _ => true,
        }
    })
}

pub fn storage_ops_preserved(original: &[SemOp], optimized: &[SemOp]) -> bool {
    for id in original
        .iter()
        .filter(|op| op.is_storage_boundary())
        .filter_map(|op| op.opaque_id())
    {
        let count = optimized
            .iter()
            .filter(|op| op.opaque_id() == Some(id))
            .count();
        if count != 1 {
            return false;
        }
    }
    true
}
