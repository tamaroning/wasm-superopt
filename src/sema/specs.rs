//! Per-op AL spec definitions (non-binop flat specs; binops use meta AL).

use super::defs::{step_pure_binop_template, NumType, Sign, WasmBinOp};
use super::ir::{AlExpr, AlSpec, AlStep};
use super::ast::Instr;
use crate::semantics::SemOp;
use std::borrow::Cow;

/// Meta-level `Step_pure/...` template for an op, if any.
pub fn rule_instrs_for(op: &SemOp) -> Option<Vec<Instr>> {
    let (nt, binop) = match op {
        SemOp::I32Add => (NumType::I32, WasmBinOp::Add),
        SemOp::I32Mul => (NumType::I32, WasmBinOp::Mul),
        SemOp::I32Shl => (NumType::I32, WasmBinOp::Shl),
        SemOp::I32DivU => (NumType::I32, WasmBinOp::Div(Sign::U)),
        SemOp::I32DivS => (NumType::I32, WasmBinOp::Div(Sign::S)),
        _ => return None,
    };
    Some(step_pure_binop_template(nt, binop))
}

pub fn al_spec_for(op: &SemOp) -> Cow<'_, AlSpec> {
    match op {
        SemOp::I32Const(n) => Cow::Owned(AlSpec {
            steps: vec![AlStep::Push(AlExpr::ConstI32(*n))],
        }),
        SemOp::I32Add | SemOp::I32Mul | SemOp::I32Shl | SemOp::I32DivU | SemOp::I32DivS => {
            panic!("binop {op:?} uses meta AL (Step_pure/binop), not flat AlSpec")
        }
        _ => panic!("{op:?} has no flat AlSpec"),
    }
}
