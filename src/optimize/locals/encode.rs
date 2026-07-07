//! Z3 MaxSAT encoding for local allocation (instruction-count objective).

use super::analysis::Analysis;
use crate::wasm::WasmFunction;
use std::collections::HashMap;
use z3::ast::Bool;
use z3::{Config, Context, Optimize, SatResult};

const LOCAL_SLOT_WEIGHT: u32 = 1;
const COPY_WEIGHT_SCALE: u32 = 1;

#[derive(Clone, Debug)]
pub struct Allocation {
    /// web id -> local index
    pub web_to_index: Vec<u32>,
    /// local index is used
    pub used_indices: Vec<bool>,
}

pub fn solve_allocation(
    func: &WasmFunction,
    analysis: &Analysis,
    timeout_ms: u32,
) -> Result<Allocation, String> {
    let n_webs = analysis.webs.len();
    if n_webs == 0 {
        return Err("no webs".into());
    }

    let r = n_webs;
    let mut cfg = Config::new();
    cfg.set_timeout_msec(timeout_ms as u64);
    let ctx = Context::new(&cfg);
    let opt = Optimize::new(&ctx);

    let mut a: Vec<Vec<Bool<'_>>> = Vec::new();
    for w in 0..n_webs {
        let mut row = Vec::new();
        for slot in 0..r {
            row.push(Bool::new_const(&ctx, format!("a_{w}_{slot}")));
        }
        a.push(row);
    }

    let mut used: Vec<Bool<'_>> = Vec::new();
    for slot in 0..r {
        used.push(Bool::new_const(&ctx, format!("used_{slot}")));
    }

    // (H1) exactly one slot per web
    for w in 0..n_webs {
        let lits: Vec<(&Bool<'_>, i32)> = a[w].iter().map(|b| (b, 1)).collect();
        opt.assert(&Bool::pb_eq(&ctx, &lits, 1));
    }

    // (H2) parameter webs fixed to their param index
    for web in &analysis.webs {
        if let Some(p) = web.param_index {
            let w = web.id.0;
            let p = p as usize;
            if p < r {
                opt.assert(&a[w][p]);
            }
        }
    }

    // (H3) type consistency
    for w1 in 0..n_webs {
        for w2 in (w1 + 1)..n_webs {
            if analysis.webs[w1].ty != analysis.webs[w2].ty {
                for slot in 0..r {
                    opt.assert(&a[w1][slot].implies(&a[w2][slot].not()));
                }
            }
        }
    }

    // (H4) interference
    for &(u, v) in &analysis.interferes {
        for slot in 0..r {
            opt.assert(&a[u.0][slot].implies(&a[v.0][slot].not()));
        }
    }

    // (H5) used slot definition
    for w in 0..n_webs {
        for slot in 0..r {
            opt.assert(&a[w][slot].implies(&used[slot]));
        }
    }

    // (B1) symmetry breaking: pack non-parameter slots
    let p = func.num_params as usize;
    for slot in (p + 1)..r {
        opt.assert(&used[slot].implies(&used[slot - 1]));
    }

    // Merge variables m_{u,v} for copy pairs
    let mut merge_vars: HashMap<(usize, usize), Bool<'_>> = HashMap::new();
    for copy in &analysis.copies {
        let key = (copy.src.0.min(copy.dst.0), copy.src.0.max(copy.dst.0));
        merge_vars
            .entry(key)
            .or_insert_with(|| Bool::new_const(&ctx, format!("m_{}_{}", key.0, key.1)));
    }

    for ((u, v), m) in &merge_vars {
        let mut same_slot: Vec<Bool<'_>> = Vec::new();
        for slot in 0..r {
            let both = Bool::and(&ctx, &[&a[*u][slot], &a[*v][slot]]);
            same_slot.push(both);
        }
        let refs: Vec<&Bool<'_>> = same_slot.iter().collect();
        let any_same = Bool::or(&ctx, &refs);
        opt.assert(&m.implies(&any_same));
    }

    // (S1) copy removal — soft: prefer m = true
    for copy in &analysis.copies {
        let key = (
            copy.src.0.min(copy.dst.0),
            copy.src.0.max(copy.dst.0),
        );
        let m = merge_vars.get(&key).unwrap();
        let weight = copy.instr_saved * COPY_WEIGHT_SCALE;
        opt.assert_soft(m, weight, None);
    }

    // (S2) minimize used locals
    for slot in 0..r {
        opt.assert_soft(&used[slot].not(), LOCAL_SLOT_WEIGHT, None);
    }

    match opt.check(&[]) {
        SatResult::Sat => {}
        SatResult::Unknown => return Err("solver timeout or unknown".into()),
        SatResult::Unsat => return Err("unexpected UNSAT".into()),
    }

    let model = opt
        .get_model()
        .ok_or_else(|| "no model".to_string())?;

    let mut web_to_index = vec![0u32; n_webs];
    for w in 0..n_webs {
        let mut chosen = 0usize;
        for slot in 0..r {
            if model.eval(&a[w][slot], true).map(|v| v.as_bool()).flatten() == Some(true) {
                chosen = slot;
                break;
            }
        }
        web_to_index[w] = chosen as u32;
    }

    let mut used_indices = vec![false; r];
    for slot in 0..r {
        used_indices[slot] = model
            .eval(&used[slot], true)
            .map(|v| v.as_bool())
            .flatten()
            .unwrap_or(false);
    }

    Ok(Allocation {
        web_to_index,
        used_indices,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::optimize::locals::analysis::Analysis;
    use crate::wasm::parse_wasm_functions_bytes;

    #[test]
    fn solves_simple_copy() {
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
        assert_eq!(alloc.web_to_index.len(), analysis.webs.len());
    }
}
