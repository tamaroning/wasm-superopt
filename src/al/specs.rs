//! Per-op AL spec definitions (non-binop flat specs; binops use meta AL).

use super::ast::Instr;
use super::defs::{
    NumType, Sign, WasmBinOp, step_local_set_template, step_pure_binop_template,
    step_pure_local_tee_template, step_read_local_get_template,
};
use super::ir::{AlExpr, AlSpec, AlStep};
use crate::semantics::SemOp;
use std::borrow::Cow;

/// Meta-level `Step_...` template for an op, if any.
pub fn rule_instrs_for(op: &SemOp) -> Option<Vec<Instr>> {
    match op {
        SemOp::I32Add => Some(step_pure_binop_template(NumType::I32, WasmBinOp::Add)),
        SemOp::I32Mul => Some(step_pure_binop_template(NumType::I32, WasmBinOp::Mul)),
        SemOp::I32Shl => Some(step_pure_binop_template(NumType::I32, WasmBinOp::Shl)),
        SemOp::I32DivU => Some(step_pure_binop_template(
            NumType::I32,
            WasmBinOp::Div(Sign::U),
        )),
        SemOp::I32DivS => Some(step_pure_binop_template(
            NumType::I32,
            WasmBinOp::Div(Sign::S),
        )),
        SemOp::LocalGet(x) => Some(step_read_local_get_template(*x)),
        SemOp::LocalSet(x) => Some(step_local_set_template(*x)),
        SemOp::LocalTee(x) => Some(step_pure_local_tee_template(*x)),
        _ => None,
    }
}

pub fn al_spec_for(op: &SemOp) -> Cow<'_, AlSpec> {
    match op {
        SemOp::I32Const(n) => Cow::Owned(AlSpec {
            steps: vec![AlStep::Push(AlExpr::ConstI32(*n))],
        }),
        SemOp::I32Add | SemOp::I32Mul | SemOp::I32Shl | SemOp::I32DivU | SemOp::I32DivS => {
            panic!("binop {op:?} uses meta AL (Step_pure/binop), not flat AlSpec")
        }
        SemOp::LocalGet(_) | SemOp::LocalSet(_) | SemOp::LocalTee(_) => {
            panic!("local {op:?} uses meta AL (Step_read/local.*), not flat AlSpec")
        }
    }
}
