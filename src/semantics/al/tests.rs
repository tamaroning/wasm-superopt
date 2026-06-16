use super::derive::{POPS_0_TEST, POPS_1_TEST, POPS_2_TEST, PUSHES_0_TEST, PUSHES_1_TEST};
use super::ir::{format_al_pretty, AlCond, AlExpr, AlStep, BinOpKind, NumType, Sign, WasmBinOp};
use super::policy::STRAIGHT_LINE_EMBED;
use super::{al_spec_for, derive_inst_spec, step_pure_binop};
use crate::semantics::{InstSpec, SemOp, concrete_ops};

#[test]
fn derive_inst_spec_matches_expected() {
    let policy = STRAIGHT_LINE_EMBED;
    for op in concrete_ops() {
        let al = al_spec_for(&op);
        let derived = derive_inst_spec(&al, &policy);
        let expected = expected_inst_spec(&op);
        assert_eq!(derived.pops, expected.pops, "{op:?} pops");
        assert_eq!(derived.pushes, expected.pushes, "{op:?} pushes");
        assert_eq!(
            derived.touches_state, expected.touches_state,
            "{op:?} state"
        );
        assert_eq!(derived.can_trap, expected.can_trap, "{op:?} can_trap");
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
fn div_u_al_has_wasm_binop_shape() {
    let al = al_spec_for(&SemOp::I32DivU);
    assert!(matches!(
        al.steps.as_slice(),
        [AlStep::Pop("c2"), AlStep::Pop("c1"), AlStep::If { .. }]
    ));
    if let AlStep::If {
        cond,
        then_steps,
        else_steps,
    } = &al.steps[2]
    {
        assert!(matches!(
            cond,
            AlCond::BinOpEmpty(BinOpKind::DivU, "c1", "c2")
        ));
        assert_eq!(then_steps.as_slice(), [AlStep::Trap]);
        assert!(matches!(else_steps.as_slice(), [AlStep::Push(_)]));
    } else {
        panic!("expected If");
    }
}

#[test]
fn instantiate_i32_div_s_has_wasm_binop_shape() {
    let al = step_pure_binop(NumType::I32, WasmBinOp::Div(Sign::S));
    assert!(matches!(
        al.steps.as_slice(),
        [AlStep::Pop("c2"), AlStep::Pop("c1"), AlStep::If { .. }]
    ));
    if let AlStep::If {
        cond,
        then_steps,
        else_steps,
    } = &al.steps[2]
    {
        assert!(matches!(
            cond,
            AlCond::BinOpEmpty(BinOpKind::DivS, "c1", "c2")
        ));
        assert_eq!(then_steps.as_slice(), [AlStep::Trap]);
        assert!(matches!(
            else_steps.as_slice(),
            [AlStep::Push(AlExpr::BinOp(BinOpKind::DivS, "c1", "c2"))]
        ));
    } else {
        panic!("expected If");
    }
}

#[test]
fn instantiate_i32_div_s_partiality_matches_binop_kind() {
    let kind = BinOpKind::DivS;
    assert!(kind.binop_empty_concrete(0, 0));
    assert!(kind.binop_empty_concrete(i32::MIN, -1));
    assert!(!kind.binop_empty_concrete(8, 2));
    assert!(kind.binop_empty_concrete(8, 0));
}

#[test]
fn format_al_pretty_div_s() {
    let al = step_pure_binop(NumType::I32, WasmBinOp::Div(Sign::S));
    let pretty = format_al_pretty(&al);
    assert_eq!(
        pretty,
        "pop c2\npop c1\nif empty(DivS, c1, c2) then\n  trap\nelse\n  push DivS(c1, c2)"
    );
}

#[test]
fn al_spec_for_div_s_matches_instantiate() {
    let via_spec = al_spec_for(&SemOp::I32DivS);
    let via_inst = step_pure_binop(NumType::I32, WasmBinOp::Div(Sign::S));
    assert_eq!(via_spec.steps, via_inst.steps);
}
