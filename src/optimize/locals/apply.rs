//! Apply allocation: reindex locals and remove self-copies.

use super::analysis::{Analysis, CopyKind, WebId};
use super::encode::Allocation;
use crate::wasm::{FuncInstr, LocalValType, WasmFunction};
use std::collections::HashMap;

#[derive(Clone, Debug)]
pub struct AppliedFunction {
    pub instrs: Vec<FuncInstr>,
    pub local_types: Vec<LocalValType>,
    pub copies_removed: usize,
}

impl AppliedFunction {
    pub fn instr_count(&self) -> usize {
        self.instrs.len()
    }

    pub fn local_slots(&self) -> usize {
        self.local_types.len()
    }
}

pub fn apply_allocation(
    func: &WasmFunction,
    analysis: &Analysis,
    alloc: &Allocation,
) -> AppliedFunction {
    let web_index = |wid: WebId| alloc.web_to_index[wid.0];

    let mut skip = vec![false; func.instrs.len()];
    let mut copies_removed = 0usize;

    for copy in &analysis.copies {
        if web_index(copy.src) == web_index(copy.dst) {
            match copy.kind {
                CopyKind::GetSet => {
                    skip[copy.at] = true;
                    skip[copy.at + 1] = true;
                    copies_removed += 1;
                }
                CopyKind::GetTee => {
                    skip[copy.at] = true;
                    // get+tee -> single get at tee position
                    copies_removed += 1;
                }
            }
        }
    }

    let mut new_instrs = Vec::new();
    for (i, instr) in func.instrs.iter().enumerate() {
        if skip[i] {
            if let FuncInstr::LocalGet(_) = instr {
                // get+tee coalesced: emit get at tee site if next was tee
                if i + 1 < func.instrs.len()
                    && matches!(func.instrs[i + 1], FuncInstr::LocalTee(_))
                    && skip[i + 1]
                {
                    if let Some(wid) = analysis.web_of_instr[i] {
                        let idx = web_index(wid);
                        new_instrs.push(FuncInstr::LocalGet(idx));
                    }
                }
            }
            continue;
        }

        let mapped = match instr {
            FuncInstr::LocalGet(local) => {
                let wid = analysis.web_of_instr[i].unwrap_or(WebId(0));
                FuncInstr::LocalGet(web_index(wid))
            }
            FuncInstr::LocalSet(local) => {
                let wid = analysis.web_of_instr[i].unwrap_or(WebId(*local as usize));
                FuncInstr::LocalSet(web_index(wid))
            }
            FuncInstr::LocalTee(local) => {
                let wid = analysis.web_of_instr[i].unwrap_or(WebId(*local as usize));
                FuncInstr::LocalTee(web_index(wid))
            }
            other => other.clone(),
        };
        new_instrs.push(mapped);
    }

    // Rebuild local types: params first in order, then declared locals by used indices.
    let mut index_to_type: HashMap<u32, LocalValType> = HashMap::new();
    for web in &analysis.webs {
        let idx = web_index(web.id);
        index_to_type.entry(idx).or_insert(web.ty);
    }

    let mut used_indices: Vec<u32> = index_to_type.keys().copied().collect();
    used_indices.sort_unstable();

    let mut remap: HashMap<u32, u32> = HashMap::new();
    let mut new_local_types = Vec::new();
    for (new_idx, &old_idx) in used_indices.iter().enumerate() {
        remap.insert(old_idx, new_idx as u32);
        new_local_types.push(index_to_type[&old_idx]);
    }

    let final_instrs: Vec<FuncInstr> = new_instrs
        .into_iter()
        .map(|instr| match instr {
            FuncInstr::LocalGet(i) => FuncInstr::LocalGet(*remap.get(&i).unwrap_or(&i)),
            FuncInstr::LocalSet(i) => FuncInstr::LocalSet(*remap.get(&i).unwrap_or(&i)),
            FuncInstr::LocalTee(i) => FuncInstr::LocalTee(*remap.get(&i).unwrap_or(&i)),
            other => other,
        })
        .collect();

    AppliedFunction {
        instrs: final_instrs,
        local_types: new_local_types,
        copies_removed,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::optimize::locals::analysis::Analysis;
    use crate::optimize::locals::encode::solve_allocation;
    use crate::wasm::parse_wasm_functions_bytes;

    #[test]
    fn apply_removes_copy() {
        let wasm = wat::parse_str(
            r#"(module (func (param i32) (local i32)
              local.get 0
              local.set 1
              local.get 1
              i32.const 0
              i32.add))"#,
        )
        .unwrap();
        let m = parse_wasm_functions_bytes(&wasm).unwrap();
        let func = &m.functions[0];
        let analysis = Analysis::build(func).unwrap();
        let alloc = solve_allocation(func, &analysis, 10_000).unwrap();
        let applied = apply_allocation(func, &analysis, &alloc);
        assert_eq!(applied.instr_count(), 4);
        assert_eq!(applied.copies_removed, 1);
    }
}
