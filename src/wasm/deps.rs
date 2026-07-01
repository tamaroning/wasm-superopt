//! Dependency edges between opaque instructions (SuperStack-compatible).

use crate::semantics::SemOp;
use crate::wasm::segment::OpaqueMeta;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum MemWidth {
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

fn overlap_address(a: i64, w1: i64, b: i64, w2: i64) -> bool {
    a <= b && b < a + w1 || b <= a && a < b + w2
}

fn width_bytes(_w: MemWidth) -> i64 {
    4
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
        (None, None) => {
            // Same symbolic base may alias; distinct symbols are independent.
            !a.addr_symbol.is_empty() && a.addr_symbol == b.addr_symbol
        }
        // One concrete and one symbolic address — conservative (SuperStack).
        _ => true,
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
    if deps.len() <= 1 {
        return deps.to_vec();
    }

    let mut adj: HashMap<u32, HashSet<u32>> = HashMap::new();
    for &(a, b) in deps {
        adj.entry(a).or_default().insert(b);
    }

    // Reachability from each node (SuperStack: nx.transitive_reduction).
    let mut reach: HashMap<u32, HashSet<u32>> = HashMap::new();
    for start in adj.keys().copied().collect::<Vec<_>>() {
        let mut seen = HashSet::new();
        let mut stack = vec![start];
        while let Some(n) = stack.pop() {
            if !seen.insert(n) {
                continue;
            }
            if let Some(nexts) = adj.get(&n) {
                stack.extend(nexts);
            }
        }
        reach.insert(start, seen);
    }

    deps.iter()
        .copied()
        .filter(|&(a, b)| {
            let Some(succ) = adj.get(&a) else {
                return true;
            };
            !succ.iter().any(|&c| {
                c != b && reach.get(&c).is_some_and(|r| r.contains(&b))
            })
        })
        .collect()
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
                    width: MemWidth::B4,
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
                    width: MemWidth::B4,
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Instant;

    #[test]
    fn simplify_dependencies_dense_call_edges_is_fast() {
        let n = 500u32;
        let mut deps = Vec::new();
        for i in 0..n {
            for j in i + 1..n {
                deps.push((i, j));
            }
        }
        let t0 = Instant::now();
        let out = simplify_dependencies(&deps);
        eprintln!(
            "simplify dense n=500: {:.3}ms -> {} edges",
            t0.elapsed().as_secs_f64() * 1000.0,
            out.len()
        );
        assert!(t0.elapsed().as_secs_f32() < 1.0, "took {:?}", t0.elapsed());
        assert_eq!(out.len(), (n - 1) as usize);
    }
}
