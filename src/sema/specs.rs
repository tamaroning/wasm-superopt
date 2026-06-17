//! Per-op AL spec definitions (non-binop flat specs; binops use meta AL).

use super::defs::{step_pure_binop_template, NumType, Sign, WasmBinOp};
use super::ir::{AlExpr, AlSpec, AlStep};
use super::ast::Instr;
use crate::semantics::SemOp;
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
