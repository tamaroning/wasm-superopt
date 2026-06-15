//! Instantiate parameterized AL step templates into flat [`AlSpec`](super::ir::AlSpec).

use super::al_defs::{instantiate_binop_, step_pure_binop_template};
use super::meta::{AlMetaExpr, AlMetaStep, BinopInstantiation, PopPattern};
use super::ir::{AlCond, AlExpr, AlSpec, AlStep, NumType, WasmBinOp};

/// Instantiate `Step_pure/binop(nt, binop)` from binop.al L5–15.
pub fn step_pure_binop(nt: NumType, binop: WasmBinOp) -> AlSpec {
    let inst = instantiate_binop_(nt, binop);
    let template = step_pure_binop_template(nt, binop);
    AlSpec {
        steps: lower_meta_steps(&template, &inst),
    }
}

fn lower_meta_steps(steps: &[AlMetaStep], inst: &BinopInstantiation) -> Vec<AlStep> {
    let mut out = Vec::new();
    for step in steps {
        lower_meta_step(step, inst, &mut out);
    }
    out
}

fn lower_meta_step(step: &AlMetaStep, inst: &BinopInstantiation, out: &mut Vec<AlStep>) {
    match step {
        AlMetaStep::Assert(AlMetaExpr::TopValue(_)) => {}
        AlMetaStep::Assert(expr) => {
            panic!("unsupported Assert in Step_pure/binop lowering: {expr:?}")
        }
        AlMetaStep::Pop(PopPattern::NumConst(name)) => {
            out.push(AlStep::Pop(normalize_var(name)));
        }
        AlMetaStep::Let { .. } => {
            panic!("Let should be skipped during lowering (inlined into Push)")
        }
        AlMetaStep::Push(_) => {
            panic!("Push should be lowered via BinopInstantiation, not directly")
        }
        AlMetaStep::Trap => out.push(AlStep::Trap),
        AlMetaStep::If {
            cond,
            then_steps,
            else_steps: _,
        } => {
            if !inst.is_partial {
                out.push(AlStep::Push(AlExpr::BinOp(
                    inst.kind,
                    inst.lhs,
                    inst.rhs,
                )));
                return;
            }
            assert!(matches!(
                cond,
                AlMetaExpr::OptionalLen(inner) if matches!(inner.as_ref(), AlMetaExpr::Call("binop_", _))
            ));
            assert_eq!(then_steps.as_slice(), [AlMetaStep::Trap]);
            out.push(AlStep::If {
                cond: AlCond::BinOpEmpty(inst.kind, inst.lhs, inst.rhs),
                then_steps: vec![AlStep::Trap],
                else_steps: vec![AlStep::Push(AlExpr::BinOp(
                    inst.kind,
                    inst.lhs,
                    inst.rhs,
                ))],
            });
        }
    }
}

fn normalize_var(name: &str) -> &'static str {
    match name {
        "c_1" => "c1",
        "c_2" => "c2",
        other => panic!("unknown AL variable: {other}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::semantics::al::ir::{AlCond, BinOpKind, Sign, WasmBinOp};

    #[test]
    fn div_s_shape() {
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
            assert!(matches!(else_steps.as_slice(), [AlStep::Push(_)]));
        } else {
            panic!("expected If");
        }
    }

    #[test]
    fn add_is_straight_line() {
        let al = step_pure_binop(NumType::I32, WasmBinOp::Add);
        assert_eq!(
            al.steps,
            vec![
                AlStep::Pop("c2"),
                AlStep::Pop("c1"),
                AlStep::Push(AlExpr::BinOp(BinOpKind::Add, "c1", "c2")),
            ]
        );
    }
}
