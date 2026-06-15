//! Per-op AL spec definitions.

use super::super::SemOp;
use super::ir::{AlCond, AlExpr, AlSpec, AlStep, BinOpKind};
use std::borrow::Cow;

fn steps_add() -> Vec<AlStep> {
    vec![
        AlStep::Pop("b"),
        AlStep::Pop("a"),
        AlStep::Push(AlExpr::BinOp(BinOpKind::Add, "a", "b")),
    ]
}

fn steps_mul() -> Vec<AlStep> {
    vec![
        AlStep::Pop("b"),
        AlStep::Pop("a"),
        AlStep::Push(AlExpr::BinOp(BinOpKind::Mul, "a", "b")),
    ]
}

fn steps_shl() -> Vec<AlStep> {
    vec![
        AlStep::Pop("b"),
        AlStep::Pop("a"),
        AlStep::Push(AlExpr::BinOp(BinOpKind::Shl, "a", "b")),
    ]
}

fn steps_div_u() -> Vec<AlStep> {
    vec![
        AlStep::Pop("c2"),
        AlStep::Pop("c1"),
        AlStep::If {
            cond: AlCond::BinOpEmpty(BinOpKind::DivU, "c1", "c2"),
            then_steps: vec![AlStep::Trap],
            else_steps: vec![AlStep::Push(AlExpr::BinOp(BinOpKind::DivU, "c1", "c2"))],
        },
    ]
}

fn steps_div_s() -> Vec<AlStep> {
    vec![
        AlStep::Pop("c2"),
        AlStep::Pop("c1"),
        AlStep::If {
            cond: AlCond::BinOpEmpty(BinOpKind::DivS, "c1", "c2"),
            then_steps: vec![AlStep::Trap],
            else_steps: vec![AlStep::Push(AlExpr::BinOp(BinOpKind::DivS, "c1", "c2"))],
        },
    ]
}

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
        SemOp::I32Add => Cow::Owned(AlSpec { steps: steps_add() }),
        SemOp::I32Mul => Cow::Owned(AlSpec { steps: steps_mul() }),
        SemOp::I32Shl => Cow::Owned(AlSpec { steps: steps_shl() }),
        SemOp::I32DivU => Cow::Owned(AlSpec {
            steps: steps_div_u(),
        }),
        SemOp::I32DivS => Cow::Owned(AlSpec {
            steps: steps_div_s(),
        }),
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
