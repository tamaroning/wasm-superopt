//! Inverse peel rules (backward search steps).

use super::canon::Canonizer;
use crate::lang::ValueLang;
use crate::semantics::{InstKind, SemOp};
use crate::sym::{LocalReq, SymState, subtree_expr};
use crate::wasm::SegmentBounds;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PeelAction {
    Forward(SemOp),
}

pub fn applicable_peels(
    g: &SymState,
    bounds: &SegmentBounds,
    canon: &mut Canonizer,
) -> Vec<(PeelAction, SymState)> {
    if !g.validate_bounds(bounds) {
        return vec![];
    }
    let mut out = Vec::new();

    for (&slot, req) in &g.locals {
        if slot > bounds.max_local {
            continue;
        }
        if let LocalReq::Need(v) = req {
            let mut next = g.clone();
            next.locals.insert(slot, LocalReq::DontCare);
            next.stack.push(v.clone());
            if next.stack.len() <= bounds.max_stack {
                out.push((PeelAction::Forward(SemOp::LocalSet(slot)), next));
            }
        }
    }

    if let Some(top) = g.top() {
        for (&slot, req) in &g.locals {
            if slot > bounds.max_local {
                continue;
            }
            if let LocalReq::Need(v) = req {
                if canon.values_equivalent(top, v) {
                    let mut next = g.clone();
                    next.locals.insert(slot, LocalReq::DontCare);
                    out.push((PeelAction::Forward(SemOp::LocalTee(slot)), next));
                }
            }
        }
    }

    if let Some(top) = g.top().cloned() {
        if let ValueLang::I32Const(c) = &top[top.root()] {
            let mut next = g.clone();
            next.stack.pop();
            out.push((PeelAction::Forward(SemOp::I32Const(*c)), next));
        }

        for (kind, e1, e2) in canon.binop_decompositions(&top) {
            let sem = inst_kind_to_sem(kind);
            let mut next = g.clone();
            next.stack.pop();
            next.stack.push(e1);
            next.stack.push(e2);
            if next.stack.len() <= bounds.max_stack {
                out.push((PeelAction::Forward(sem), next));
            }
        }

        if let Some((sem, a, b)) = structural_binop_peel(&top) {
            let mut next = g.clone();
            next.stack.pop();
            next.stack.push(a);
            next.stack.push(b);
            if next.stack.len() <= bounds.max_stack {
                out.push((PeelAction::Forward(sem), next));
            }
        }

        if !g.stack.is_empty() {
            let v = top;
            for slot in 0..=bounds.max_local {
                let mut next = g.clone();
                next.stack.pop();
                match next.locals.get(&slot) {
                    Some(LocalReq::Need(existing)) if canon.values_equivalent(existing, &v) => {}
                    Some(LocalReq::DontCare) | None => {
                        next.locals.insert(slot, LocalReq::Need(v.clone()));
                    }
                    Some(LocalReq::Need(_)) => continue,
                }
                out.push((PeelAction::Forward(SemOp::LocalGet(slot)), next));
            }
        }
    }

    out
}

fn structural_binop_peel(top: &crate::sym::ValueExpr) -> Option<(SemOp, crate::sym::ValueExpr, crate::sym::ValueExpr)> {
    let root = top.root();
    match &top[root] {
        ValueLang::I32Sub([a, b]) => Some((
            SemOp::I32Sub,
            subtree_expr(top, *a),
            subtree_expr(top, *b),
        )),
        ValueLang::I32Eq([a, b]) => Some((
            SemOp::I32Eq,
            subtree_expr(top, *a),
            subtree_expr(top, *b),
        )),
        ValueLang::I32Ne([a, b]) => Some((
            SemOp::I32Ne,
            subtree_expr(top, *a),
            subtree_expr(top, *b),
        )),
        ValueLang::I32LtS([a, b]) => Some((
            SemOp::I32LtS,
            subtree_expr(top, *a),
            subtree_expr(top, *b),
        )),
        ValueLang::I32LeS([a, b]) => Some((
            SemOp::I32LeS,
            subtree_expr(top, *a),
            subtree_expr(top, *b),
        )),
        ValueLang::I32GtS([a, b]) => Some((
            SemOp::I32GtS,
            subtree_expr(top, *a),
            subtree_expr(top, *b),
        )),
        _ => None,
    }
}

fn inst_kind_to_sem(kind: InstKind) -> SemOp {
    match kind {
        InstKind::I32Add => SemOp::I32Add,
        InstKind::I32Sub => SemOp::I32Sub,
        InstKind::I32Mul => SemOp::I32Mul,
        InstKind::I32Shl => SemOp::I32Shl,
        InstKind::I32DivU => SemOp::I32DivU,
        InstKind::I32DivS => SemOp::I32DivS,
        InstKind::I32Eq => SemOp::I32Eq,
        InstKind::I32Ne => SemOp::I32Ne,
        InstKind::I32LtS => SemOp::I32LtS,
        InstKind::I32LeS => SemOp::I32LeS,
        InstKind::I32GtS => SemOp::I32GtS,
        other => panic!("not a peelable binop: {other:?}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::optimize::fixtures::{fin, init};
    use crate::synthesis::{
        TEST_SYNTHESIS_AST_SIZE, load_or_synthesize_rules, synthesized_to_rewrites,
    };
    use crate::value::parse_value_expr;
    use crate::wasm::SegmentBounds;

    fn canonizer() -> Canonizer {
        Canonizer::new(synthesized_to_rewrites(&load_or_synthesize_rules(
            TEST_SYNTHESIS_AST_SIZE,
            10,
        )))
    }

    #[test]
    fn memo_convergence_mul_vs_shl() {
        let mut canon = canonizer();
        let top = parse_value_expr("(i32.mul (i32.add ?L0 1) 2)");
        let l_plus_1 = parse_value_expr("(i32.add ?L0 1)");
        let mut locals = std::collections::BTreeMap::new();
        locals.insert(0, crate::sym::LocalReq::Need(l_plus_1));
        let g = SymState {
            stack: vec![top],
            locals,
        };
        let bounds = SegmentBounds::new(1, 4);
        let top_expr = g.stack.last().expect("top");
        let decomps = canon.binop_decompositions(top_expr);
        assert!(decomps.iter().any(|(k, _, _)| *k == InstKind::I32Mul));
        let (_, e1, e2) = decomps
            .iter()
            .find(|(k, _, _)| *k == InstKind::I32Mul)
            .unwrap();
        let mut after_mul = g.clone();
        after_mul.stack.pop();
        after_mul.stack.push(e1.clone());
        after_mul.stack.push(e2.clone());
        after_mul.stack.pop();
        let key_mul_stack: Vec<_> = after_mul.stack.iter().map(|e| canon.canon(e)).collect();
        let (_, e1s, e2s) = decomps
            .iter()
            .find(|(k, _, _)| *k == InstKind::I32Shl)
            .expect("shl decomposition");
        let mut after_shl = g.clone();
        after_shl.stack.pop();
        after_shl.stack.push(e1s.clone());
        after_shl.stack.push(e2s.clone());
        after_shl.stack.pop();
        let key_shl_stack: Vec<_> = after_shl.stack.iter().map(|e| canon.canon(e)).collect();
        assert_eq!(key_mul_stack, key_shl_stack);
        assert_eq!(key_mul_stack.len(), 1, "both paths require only L+1");
        let _ = bounds;
    }

    #[test]
    fn peel_sequence_reaches_init() {
        let mut canon = canonizer();
        let init = init();
        let mut g = fin();
        let bounds = SegmentBounds::new(1, 4);
        let manual: Vec<SemOp> = vec![
            SemOp::LocalTee(0),
            SemOp::I32Shl,
            SemOp::I32Const(1),
            SemOp::LocalGet(0),
            SemOp::I32Shl,
            SemOp::I32Const(3),
            SemOp::LocalGet(0),
        ];
        for op in manual {
            let peels = applicable_peels(&g, &bounds, &mut canon);
            let next = peels
                .into_iter()
                .find(|(a, _)| match (&a, &op) {
                    (PeelAction::Forward(SemOp::I32Const(a)), SemOp::I32Const(b)) => a == b,
                    (PeelAction::Forward(SemOp::LocalGet(a)), SemOp::LocalGet(b)) => a == b,
                    (PeelAction::Forward(SemOp::LocalSet(a)), SemOp::LocalSet(b)) => a == b,
                    (PeelAction::Forward(SemOp::LocalTee(a)), SemOp::LocalTee(b)) => a == b,
                    (PeelAction::Forward(SemOp::I32Mul), SemOp::I32Mul) => true,
                    (PeelAction::Forward(SemOp::I32Add), SemOp::I32Add) => true,
                    (PeelAction::Forward(SemOp::I32Shl), SemOp::I32Shl) => true,
                    _ => false,
                })
                .map(|(_, n)| n)
                .expect("peel step");
            g = next;
        }
        assert!(crate::optimize::search::is_grounded(
            &g,
            &init,
            &bounds,
            &mut canon
        ));
    }
}
