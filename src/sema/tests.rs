use super::derive::{POPS_0_TEST, POPS_1_TEST, POPS_2_TEST, PUSHES_0_TEST, PUSHES_1_TEST};
use super::defs::{NumType, Sign, WasmBinOp};
use super::ast::format_rule_binop_pretty;
use super::policy::STRAIGHT_LINE_EMBED;
use super::{al_spec_for, derive_inst_spec, derive_rule_binop_spec};
use crate::semantics::{spec_for, InstSpec, SemOp, concrete_ops};

fn is_binop(op: &SemOp) -> bool {
    matches!(
        op,
        SemOp::I32Add | SemOp::I32Mul | SemOp::I32Shl | SemOp::I32DivU | SemOp::I32DivS
    )
}

#[test]
fn derive_inst_spec_matches_expected() {
    let policy = STRAIGHT_LINE_EMBED;
    for op in concrete_ops() {
        let derived = spec_for(&op);
        let expected = expected_inst_spec(&op);
        assert_eq!(derived.pops, expected.pops, "{op:?} pops");
        assert_eq!(derived.pushes, expected.pushes, "{op:?} pushes");
        assert_eq!(
            derived.touches_state, expected.touches_state,
            "{op:?} state"
        );
        assert_eq!(derived.can_trap, expected.can_trap, "{op:?} can_trap");
        if !is_binop(&op) {
            let al = al_spec_for(&op);
            assert_eq!(derive_inst_spec(&al, &policy), derived);
        }
    }
}

fn expected_inst_spec(op: &SemOp) -> InstSpec {
    match op {
        SemOp::I32Const(_) => InstSpec {
            pops: POPS_0_TEST,
            pushes: PUSHES_1_TEST,
            touches_state: false,
            can_trap: false,
        },
        SemOp::I32Add | SemOp::I32Mul | SemOp::I32Shl => InstSpec {
            pops: POPS_2_TEST,
            pushes: PUSHES_1_TEST,
            touches_state: false,
            can_trap: false,
        },
        SemOp::I32DivU | SemOp::I32DivS => InstSpec {
            pops: POPS_2_TEST,
            pushes: PUSHES_1_TEST,
            touches_state: false,
            can_trap: true,
        },
        SemOp::LocalGet(_) => InstSpec {
            pops: POPS_0_TEST,
            pushes: PUSHES_1_TEST,
            touches_state: true,
            can_trap: false,
        },
        SemOp::LocalSet(_) => InstSpec {
            pops: POPS_1_TEST,
            pushes: PUSHES_0_TEST,
            touches_state: true,
            can_trap: false,
        },
        SemOp::I32Load => InstSpec {
            pops: POPS_1_TEST,
            pushes: PUSHES_1_TEST,
            touches_state: true,
            can_trap: false,
        },
        SemOp::I32Store => InstSpec {
            pops: POPS_2_TEST,
            pushes: PUSHES_0_TEST,
            touches_state: true,
            can_trap: false,
        },
        SemOp::Drop => InstSpec {
            pops: POPS_1_TEST,
            pushes: PUSHES_0_TEST,
            touches_state: false,
            can_trap: false,
        },
    }
}

#[test]
fn derive_rule_binop_spec_div_s_can_trap() {
    let spec = derive_rule_binop_spec(WasmBinOp::Div(Sign::S));
    assert!(spec.can_trap);
    assert_eq!(spec.pops.len(), 2);
    assert_eq!(spec.pushes.len(), 1);
}

#[test]
fn format_rule_binop_pretty_div_s_mentions_binop_call() {
    let pretty = format_rule_binop_pretty(NumType::I32, WasmBinOp::Div(Sign::S));
    assert!(pretty.contains("$binop_"));
    assert!(pretty.contains("trap"));
}
