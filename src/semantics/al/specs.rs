//! Per-op AL spec definitions.

use super::instantiate::step_pure_binop;
use super::ir::{AlExpr, AlSpec, AlStep, NumType, Sign, WasmBinOp};
use super::super::SemOp;
use std::borrow::Cow;

fn steps_load() -> Vec<AlStep> {
    vec![AlStep::Pop("addr"), AlStep::Push(AlExpr::MemLoad("addr"))]
}

fn steps_store() -> Vec<AlStep> {
    vec![
        AlStep::Pop("val"),
        AlStep::Pop("addr"),
        AlStep::StoreMem {
            addr: "addr",
            val: "val",
        },
    ]
}

fn steps_drop() -> Vec<AlStep> {
    vec![AlStep::Pop("_")]
}

pub fn al_spec_for(op: &SemOp) -> Cow<'_, AlSpec> {
    match op {
        SemOp::I32Const(n) => Cow::Owned(AlSpec {
            steps: vec![AlStep::Push(AlExpr::ConstI32(*n))],
        }),
        SemOp::I32Add => Cow::Owned(step_pure_binop(NumType::I32, WasmBinOp::Add)),
        SemOp::I32Mul => Cow::Owned(step_pure_binop(NumType::I32, WasmBinOp::Mul)),
        SemOp::I32Shl => Cow::Owned(step_pure_binop(NumType::I32, WasmBinOp::Shl)),
        SemOp::I32DivU => Cow::Owned(step_pure_binop(
            NumType::I32,
            WasmBinOp::Div(Sign::U),
        )),
        SemOp::I32DivS => Cow::Owned(step_pure_binop(
            NumType::I32,
            WasmBinOp::Div(Sign::S),
        )),
        SemOp::LocalGet(i) => Cow::Owned(AlSpec {
            steps: vec![AlStep::Push(AlExpr::LocalGet(*i))],
        }),
        SemOp::LocalSet(i) => Cow::Owned(AlSpec {
            steps: vec![AlStep::Pop("v"), AlStep::SetLocal { idx: *i, var: "v" }],
        }),
        SemOp::I32Load => Cow::Owned(AlSpec {
            steps: steps_load(),
        }),
        SemOp::I32Store => Cow::Owned(AlSpec {
            steps: steps_store(),
        }),
        SemOp::Drop => Cow::Owned(AlSpec {
            steps: steps_drop(),
        }),
    }
}
