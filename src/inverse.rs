//! Inverse peel rules (backward search steps).

use crate::canon::Canonizer;
use crate::goal::{LocalReq, MachineState, MAX_LOCAL_SLOT, MAX_STACK_HEIGHT};
use crate::lang::ValueLang;
use crate::semantics::{InstKind, SemOp};
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PeelAction {
    Forward(SemOp),
}

pub fn applicable_peels(
    g: &MachineState,
    canon: &mut Canonizer,
) -> Vec<(PeelAction, MachineState)> {
    if !g.validate_bounds() {
        return vec![];
    }
    let mut out = Vec::new();

    for (&slot, req) in &g.locals {
        if slot > MAX_LOCAL_SLOT {
            continue;
        }
        if let LocalReq::Need(v) = req {
            let mut next = g.clone();
            next.locals.insert(slot, LocalReq::DontCare);
            next.stack.push(v.clone());
            if next.stack.len() <= MAX_STACK_HEIGHT {
                out.push((PeelAction::Forward(SemOp::LocalSet(slot)), next));
            }
        }
    }

    if let Some(top) = g.top() {
        for (&slot, req) in &g.locals {
            if slot > MAX_LOCAL_SLOT {
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
            if next.stack.len() <= MAX_STACK_HEIGHT {
                out.push((PeelAction::Forward(sem), next));
            }
        }

        if !g.stack.is_empty() {
            let v = top;
            for slot in 0..=MAX_LOCAL_SLOT {
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

fn inst_kind_to_sem(kind: InstKind) -> SemOp {
    match kind {
        InstKind::I32Add => SemOp::I32Add,
        InstKind::I32Mul => SemOp::I32Mul,
        InstKind::I32Shl => SemOp::I32Shl,
        InstKind::I32DivU => SemOp::I32DivU,
        InstKind::I32DivS => SemOp::I32DivS,
        other => panic!("not a peelable binop: {other:?}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::goal::{example_fin, example_init};
    use crate::synthesis::{
        load_or_synthesize_rules, synthesized_to_rewrites, TEST_SYNTHESIS_AST_SIZE,
    };
    use crate::value::parse_value_expr;

    fn canonizer() -> Canonizer {
        Canonizer::new(synthesized_to_rewrites(&load_or_synthesize_rules(
            TEST_SYNTHESIS_AST_SIZE,
            10,
        )))
    }

    #[test]
    fn memo_convergence_mul_vs_shl() {
        let mut canon = canonizer();
        let fin = example_fin();
        let mut g = fin.clone();
        // peel top get_0
        let peels = applicable_peels(&g, &mut canon);
        let (_, g1) = peels
            .iter()
            .find(|(a, _)| matches!(a, PeelAction::Forward(SemOp::LocalGet(0))))
            .expect("get peel");
        g = g1.clone();
        let key1 = canon.normal_goal(&g);
        // peel mul path
        let mut g_mul = g.clone();
        let top = g_mul.stack.pop().expect("top");
        let decomps = canon.binop_decompositions(&top);
        assert!(decomps.iter().any(|(k, _, _)| *k == InstKind::I32Mul));
        let (_, e1, e2) = decomps
            .iter()
            .find(|(k, _, _)| *k == InstKind::I32Mul)
            .unwrap();
        let mut after_mul = g.clone();
        after_mul.stack.pop();
        after_mul.stack.push(e1.clone());
        after_mul.stack.push(e2.clone());
        after_mul.stack.push(parse_value_expr("2"));
        after_mul.stack.pop();
        let key_mul = canon.normal_goal(&after_mul);
        // peel shl path
        let (_, e1s, e2s) = decomps
            .iter()
            .find(|(k, _, _)| *k == InstKind::I32Shl)
            .unwrap();
        let mut after_shl = g.clone();
        after_shl.stack.pop();
        after_shl.stack.push(e1s.clone());
        after_shl.stack.push(e2s.clone());
        after_shl.stack.push(parse_value_expr("1"));
        after_shl.stack.pop();
        let key_shl = canon.normal_goal(&after_shl);
        assert_eq!(key_mul.stack, key_shl.stack);
        assert_eq!(key_mul.locals, key_shl.locals);
        assert_ne!(key1.stack.len(), key_mul.stack.len());
    }

    #[test]
    fn peel_sequence_reaches_init() {
        let mut canon = canonizer();
        let init = example_init();
        let mut g = example_fin();
        let manual: Vec<SemOp> = vec![
            SemOp::LocalGet(0),
            SemOp::I32Mul,
            SemOp::I32Const(2),
            SemOp::LocalTee(0),
            SemOp::I32Add,
            SemOp::I32Const(1),
            SemOp::LocalGet(0),
        ];
        for op in manual {
            let peels = applicable_peels(&g, &mut canon);
            let next = peels
                .into_iter()
                .find(|(a, _)| match (&a, &op) {
                    (PeelAction::Forward(SemOp::I32Const(a)), SemOp::I32Const(b)) => a == b,
                    (PeelAction::Forward(SemOp::LocalGet(a)), SemOp::LocalGet(b)) => a == b,
                    (PeelAction::Forward(SemOp::LocalTee(a)), SemOp::LocalTee(b)) => a == b,
                    (PeelAction::Forward(SemOp::I32Mul), SemOp::I32Mul) => true,
                    (PeelAction::Forward(SemOp::I32Add), SemOp::I32Add) => true,
                    _ => false,
                })
                .map(|(_, n)| n)
                .expect("peel step");
            g = next;
        }
        assert!(g.is_grounded(&init, &mut canon));
    }
}
