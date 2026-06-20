//! Per-op AL spec definitions (non-binop flat specs; binops use meta AL).

use super::ir::{AlExpr, AlSpec, AlStep};
use crate::semantics::SemOp;
use std::borrow::Cow;

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
