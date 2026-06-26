//! Admissible heuristics for backward A*.

use super::canon::{CanonId, Canonizer, ValueExpr};
use crate::sym::{LocalReq, SymState, all_subtree_exprs, subtree_expr};
use crate::lang::ValueLang;
use crate::wasm::SegmentBounds;
use std::collections::HashSet;

pub fn h_stack(g: &SymState, init: &SymState, canon: &mut Canonizer) -> usize {
    let mut k = 0usize;
    while k < g.stack.len().min(init.stack.len())
        && canon.canon(&g.stack[k]) == canon.canon(&init.stack[k])
    {
        k += 1;
    }
    g.stack.len().saturating_sub(k)
}

pub fn h_local(g: &SymState, init: &SymState, bounds: &SegmentBounds, canon: &mut Canonizer) -> usize {
    let mut n = 0usize;
    for slot in 0..=bounds.max_local {
        let cur = g.locals.get(&slot);
        let init_v = init.locals.get(&slot);
        let need = match cur {
            None | Some(LocalReq::DontCare) => false,
            Some(LocalReq::Need(v)) => match init_v {
                Some(LocalReq::Need(iv)) => canon.canon(v) != canon.canon(iv),
                _ => true,
            },
        };
        if need {
            n += 1;
        }
    }
    n
}

pub fn available_canon(init: &SymState, canon: &mut Canonizer) -> HashSet<CanonId> {
    let mut set = HashSet::new();
    for e in &init.stack {
        for sub in all_subtree_exprs(e) {
            set.insert(canon.canon(&sub));
        }
    }
    for req in init.locals.values() {
        if let LocalReq::Need(e) = req {
            for sub in all_subtree_exprs(e) {
                set.insert(canon.canon(&sub));
            }
        }
    }
    set
}

pub fn h_node(g: &SymState, init: &SymState, canon: &mut Canonizer) -> usize {
    let avail = available_canon(init, canon);
    let mut need = HashSet::new();
    for e in &g.stack {
        for sub in all_subtree_exprs(e) {
            let c = canon.canon(&sub);
            if !avail.contains(&c) {
                need.insert(c);
            }
        }
    }
    for req in g.locals.values() {
        if let LocalReq::Need(e) = req {
            for sub in all_subtree_exprs(e) {
                let c = canon.canon(&sub);
                if !avail.contains(&c) {
                    need.insert(c);
                }
            }
        }
    }
    need.len()
}

/// Longest binop dependency chain among required value roots not already in `init`.
///
/// Each binop on a root-to-leaf path needs at least one inverse peel, so this never
/// overestimates the remaining instruction count.
pub fn h_dep(g: &SymState, init: &SymState, canon: &mut Canonizer) -> usize {
    let avail = available_canon(init, canon);
    let mut best = 0usize;
    for e in required_roots(g) {
        best = best.max(residual_depth(e, &avail, canon));
    }
    best
}

fn required_roots(g: &SymState) -> Vec<&ValueExpr> {
    let mut roots: Vec<&ValueExpr> = g.stack.iter().collect();
    for req in g.locals.values() {
        if let LocalReq::Need(e) = req {
            roots.push(e);
        }
    }
    roots
}

fn residual_depth(expr: &ValueExpr, avail: &HashSet<CanonId>, canon: &mut Canonizer) -> usize {
    if avail.contains(&canon.canon(expr)) {
        return 0;
    }
    match &expr[expr.root()] {
        ValueLang::I32Const(_) | ValueLang::I64Const(_) | ValueLang::Symbol(_) => 1,
        ValueLang::I32Add([a, b])
        | ValueLang::I32Sub([a, b])
        | ValueLang::I32Mul([a, b])
        | ValueLang::I32Shl([a, b])
        | ValueLang::I32DivU([a, b])
        | ValueLang::I32DivS([a, b])
        | ValueLang::I32RemU([a, b])
        | ValueLang::I32RemS([a, b])
        | ValueLang::I32And([a, b])
        | ValueLang::I32Or([a, b])
        | ValueLang::I32Xor([a, b])
        | ValueLang::I32ShrU([a, b])
        | ValueLang::I32ShrS([a, b])
        | ValueLang::I32Rotl([a, b])
        | ValueLang::I32Rotr([a, b])
        | ValueLang::I32Eq([a, b])
        | ValueLang::I32Ne([a, b])
        | ValueLang::I32LtS([a, b])
        | ValueLang::I32LeS([a, b])
        | ValueLang::I32GtS([a, b])
        | ValueLang::I64Add([a, b])
        | ValueLang::I64Sub([a, b])
        | ValueLang::I64Mul([a, b])
        | ValueLang::I64Shl([a, b])
        | ValueLang::I64DivU([a, b])
        | ValueLang::I64DivS([a, b])
        | ValueLang::I64RemU([a, b])
        | ValueLang::I64RemS([a, b])
        | ValueLang::I64And([a, b])
        | ValueLang::I64Or([a, b])
        | ValueLang::I64Xor([a, b])
        | ValueLang::I64ShrU([a, b])
        | ValueLang::I64ShrS([a, b])
        | ValueLang::I64Rotl([a, b])
        | ValueLang::I64Rotr([a, b])
        | ValueLang::I64Eq([a, b])
        | ValueLang::I64Ne([a, b])
        | ValueLang::I64LtS([a, b])
        | ValueLang::I64LeS([a, b])
        | ValueLang::I64GtS([a, b]) => {
            let da = residual_depth(&subtree_expr(expr, *a), avail, canon);
            let db = residual_depth(&subtree_expr(expr, *b), avail, canon);
            1 + da.max(db)
        }
        ValueLang::I32Eqz([a])
        | ValueLang::I32Clz([a])
        | ValueLang::I32Ctz([a])
        | ValueLang::I32Popcnt([a])
        | ValueLang::I64Eqz([a])
        | ValueLang::I64Clz([a])
        | ValueLang::I64Ctz([a])
        | ValueLang::I64Popcnt([a])
        | ValueLang::I64ExtendI32S([a])
        | ValueLang::I64ExtendI32U([a])
        | ValueLang::I32WrapI64([a]) => {
            1 + residual_depth(&subtree_expr(expr, *a), avail, canon)
        }
    }
}

pub fn h_goal(g: &SymState, init: &SymState, bounds: &SegmentBounds, canon: &mut Canonizer) -> usize {
    h_stack(g, init, canon)
        .max(h_local(g, init, bounds, canon))
        .max(h_node(g, init, canon))
        .max(h_dep(g, init, canon))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::optimize::fixtures::{fin, init};
    use crate::synthesis::test_synthesis_rewrites;
    use crate::value::parse_value_expr;

    fn canonizer() -> Canonizer {
        Canonizer::new(test_synthesis_rewrites())
    }

    #[test]
    fn h_dep_zero_at_init() {
        let init = init();
        let mut canon = canonizer();
        assert_eq!(h_dep(&init, &init, &mut canon), 0);
    }

    #[test]
    fn h_dep_deep_chain_on_example_fin() {
        let init = init();
        let fin = fin();
        let mut canon = canonizer();
        let dep = h_dep(&fin, &init, &mut canon);
        assert!(dep >= 1, "shl/mul chain should depth ≥ 1, got {dep}");
        assert!(dep <= 7, "must stay admissible vs optimal 7-instr solution");
    }

    #[test]
    fn h_dep_can_exceed_h_node_on_single_deep_expr() {
        let init = init();
        let mut canon = canonizer();
        let deep = parse_value_expr("(i32.mul (i32.add (i32.add ?L0 1) 1) 2)");
        let g = SymState {
            stack: vec![deep],
            locals: Default::default(),
        };
        let dep = h_dep(&g, &init, &mut canon);
        let nodes = h_node(&g, &init, &mut canon);
        assert!(dep >= 3, "nested binops depth ≥ 3, got {dep}");
        assert!(nodes >= 1, "needs at least one residual subtree, got {nodes}");
    }

    use crate::wasm::SegmentBounds;

    #[test]
    fn h_goal_includes_h_dep() {
        let init = init();
        let fin = fin();
        let mut canon = canonizer();
        let goal = h_goal(&fin, &init, &SegmentBounds::new(1, 4), &mut canon);
        let dep = h_dep(&fin, &init, &mut canon);
        assert!(goal >= dep);
    }
}
