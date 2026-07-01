//! Per-op AL spec definitions (non-binop flat specs; binops use meta AL).

use super::ir::{AlExpr, AlSpec, AlStep};
use crate::semantics::SemOp;
use std::borrow::Cow;

pub fn al_spec_for(op: &SemOp) -> Cow<'_, AlSpec> {
    match op {
        SemOp::I32Const(n) => Cow::Owned(AlSpec {
            steps: vec![AlStep::Push(AlExpr::ConstI32(*n))],
        }),
        SemOp::I64Const(n) => Cow::Owned(AlSpec {
            steps: vec![AlStep::Push(AlExpr::ConstI64(*n))],
        }),
        SemOp::F32Const(bits) => Cow::Owned(AlSpec {
            steps: vec![AlStep::Push(AlExpr::ConstF32(*bits))],
        }),
        SemOp::F64Const(bits) => Cow::Owned(AlSpec {
            steps: vec![AlStep::Push(AlExpr::ConstF64(*bits))],
        }),
        SemOp::Pure(v) => {
            panic!("pure {v:?} uses meta AL (Step_pure), not flat AlSpec")
        }
        SemOp::I32Add
        | SemOp::I32Sub
        | SemOp::I32Mul
        | SemOp::I32Shl
        | SemOp::I32DivU
        | SemOp::I32DivS
        | SemOp::I32RemU
        | SemOp::I32RemS
        | SemOp::I32And
        | SemOp::I32Or
        | SemOp::I32Xor
        | SemOp::I32ShrU
        | SemOp::I32ShrS
        | SemOp::I32Rotl
        | SemOp::I32Rotr => {
            panic!("binop {op:?} uses meta AL (Step_pure/binop), not flat AlSpec")
        }
        SemOp::I32Eq | SemOp::I32Ne | SemOp::I32LtS | SemOp::I32LeS | SemOp::I32GtS => {
            panic!("relop {op:?} uses meta AL (Step_pure/relop), not flat AlSpec")
        }
        SemOp::I32Eqz => {
            panic!("testop {op:?} uses meta AL (Step_pure/testop), not flat AlSpec")
        }
        SemOp::I32Clz | SemOp::I32Ctz | SemOp::I32Popcnt => {
            panic!("unop {op:?} uses meta AL (Step_pure/unop), not flat AlSpec")
        }
        SemOp::LocalGet(_) | SemOp::LocalSet(_) | SemOp::LocalTee(_) => {
            panic!("local {op:?} uses meta AL (Step_read/local.*), not flat AlSpec")
        }
        SemOp::Drop
        | SemOp::I32Load { .. }
        | SemOp::I32Store { .. }
        | SemOp::Call { .. }
        | SemOp::GlobalGet { .. }
        | SemOp::GlobalSet { .. }
        | SemOp::Opaque { .. } => {
            panic!("opaque {op:?} is not supported in AL synthesis")
        }
    }
}
