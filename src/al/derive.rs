//! Derive static `InstSpec` from AL definitions.

use super::ir::{AlCond, AlSpec, AlStep};
use super::policy::EmbeddingPolicy;
use super::util::is_trap_else_push;
use crate::semantics::{InstKind, InstSpec, StackTy, value_op_from_inst_kind};
use crate::value::ValueOp;

const POPS_0: &[StackTy] = &[];
const PUSHES_0: &[StackTy] = &[];

fn count_pops(steps: &[AlStep]) -> usize {
    let mut n = 0;
    for step in steps {
        match step {
            AlStep::If {
                then_steps,
                else_steps,
                ..
            } => {
                n += count_pops(then_steps) + count_pops(else_steps);
            }
            AlStep::Push(_) | AlStep::Trap => {}
        }
    }
    n
}

fn count_pushes(steps: &[AlStep], policy: &EmbeddingPolicy) -> usize {
    let mut n = 0;
    for step in steps {
        match step {
            AlStep::Push(_) => n += 1,
            AlStep::If {
                then_steps,
                else_steps,
                ..
            } => {
                let then_p = count_pushes(then_steps, policy);
                let else_p = count_pushes(else_steps, policy);
                if is_trap_else_push(then_steps, else_steps) && policy.trap_dummy_push {
                    n += else_p.max(1);
                } else {
                    n += then_p + else_p;
                }
            }
            AlStep::Trap => {}
        }
    }
    n
}

fn derive_can_trap(steps: &[AlStep]) -> bool {
    for step in steps {
        if let AlStep::If {
            cond: AlCond::BinOpEmpty(..),
            then_steps,
            ..
        } = step
        {
            if then_steps.as_slice() == [AlStep::Trap] {
                return true;
            }
        }
    }
    false
}

fn push_slice(ty: StackTy) -> &'static [StackTy] {
    match ty {
        StackTy::I32 => &[StackTy::I32],
        StackTy::I64 => &[StackTy::I64],
        StackTy::F32 => &[StackTy::F32],
        StackTy::F64 => &[StackTy::F64],
    }
}

fn value_op_may_trap(op: ValueOp) -> bool {
    matches!(
        op,
        ValueOp::I32DivU
            | ValueOp::I32DivS
            | ValueOp::I32RemU
            | ValueOp::I32RemS
            | ValueOp::I64DivU
            | ValueOp::I64DivS
            | ValueOp::I64RemU
            | ValueOp::I64RemS
            | ValueOp::F32Div
            | ValueOp::F64Div
    )
}

fn is_relop(op: ValueOp) -> bool {
    matches!(
        op,
        ValueOp::I32Eq
            | ValueOp::I32Ne
            | ValueOp::I32LtS
            | ValueOp::I32LeS
            | ValueOp::I32GtS
            | ValueOp::I64Eq
            | ValueOp::I64Ne
            | ValueOp::I64LtS
            | ValueOp::I64LeS
            | ValueOp::I64GtS
            | ValueOp::F64Eq
            | ValueOp::F64Ne
            | ValueOp::F64Lt
            | ValueOp::F64Le
            | ValueOp::F64Gt
            | ValueOp::F64Ge
            | ValueOp::F32Eq
            | ValueOp::F32Ne
            | ValueOp::F32Lt
            | ValueOp::F32Le
            | ValueOp::F32Gt
            | ValueOp::F32Ge
    )
}

fn is_testop(op: ValueOp) -> bool {
    matches!(op, ValueOp::I32Eqz | ValueOp::I64Eqz)
}

pub fn derive_inst_spec(al: &AlSpec, policy: &EmbeddingPolicy) -> InstSpec {
    let pop_n = count_pops(&al.steps);
    let push_n = count_pushes(&al.steps, policy);
    InstSpec {
        kind: InstKind::I32Const,
        pops: match pop_n {
            0 => POPS_0,
            1 => &[StackTy::I32],
            _ => &[StackTy::I32, StackTy::I32],
        },
        pushes: match push_n {
            0 => PUSHES_0,
            _ => &[StackTy::I32],
        },
        can_trap: derive_can_trap(&al.steps),
    }
}

/// Static `InstSpec` for `Step_pure/binop` from meta template shape.
pub fn derive_rule_binop_spec(kind: InstKind) -> InstSpec {
    let op = value_op_from_inst_kind(kind).expect("derive_rule_binop_spec");
    assert_eq!(op.pops().len(), 2, "derive_rule_binop_spec: {kind:?}");
    assert!(
        !is_relop(op) && !is_testop(op),
        "derive_rule_binop_spec: {kind:?}"
    );
    InstSpec {
        kind,
        pops: op.pops(),
        pushes: push_slice(op.push()),
        can_trap: value_op_may_trap(op),
    }
}

/// `Step_read/local.get` — push only.
pub fn derive_rule_local_get_spec(slot: u32) -> InstSpec {
    InstSpec {
        kind: InstKind::LocalGet(slot),
        pops: POPS_0,
        pushes: &[StackTy::I32],
        can_trap: false,
    }
}

/// `Step/local.set` — pop one value, no push.
pub fn derive_rule_local_set_spec(slot: u32) -> InstSpec {
    InstSpec {
        kind: InstKind::LocalSet(slot),
        pops: &[StackTy::I32],
        pushes: PUSHES_0,
        can_trap: false,
    }
}

/// `Step_pure/local.tee` — pop one, push one (via duplicate + `LOCAL.SET`).
pub fn derive_rule_local_tee_spec(slot: u32) -> InstSpec {
    InstSpec {
        kind: InstKind::LocalTee(slot),
        pops: &[StackTy::I32],
        pushes: &[StackTy::I32],
        can_trap: false,
    }
}

/// Static `InstSpec` for `Step_pure/relop` — pop two `nt`, push one `i32`.
pub fn derive_rule_relop_spec(kind: InstKind) -> InstSpec {
    let op = value_op_from_inst_kind(kind).expect("derive_rule_relop_spec");
    assert!(is_relop(op), "derive_rule_relop_spec: {kind:?}");
    InstSpec {
        kind,
        pops: op.pops(),
        pushes: &[StackTy::I32],
        can_trap: false,
    }
}

/// Static `InstSpec` for `Step_pure/testop` — pop one `nt`, push one `i32`.
pub fn derive_rule_testop_spec(kind: InstKind) -> InstSpec {
    let op = value_op_from_inst_kind(kind).expect("derive_rule_testop_spec");
    assert!(is_testop(op), "derive_rule_testop_spec: {kind:?}");
    InstSpec {
        kind,
        pops: op.pops(),
        pushes: &[StackTy::I32],
        can_trap: false,
    }
}

/// Static `InstSpec` for `Step_pure/unop` — pop one `nt`, push one result `nt`.
pub fn derive_rule_unop_spec(kind: InstKind) -> InstSpec {
    let op = value_op_from_inst_kind(kind).expect("derive_rule_unop_spec");
    assert_eq!(op.pops().len(), 1, "derive_rule_unop_spec: {kind:?}");
    assert!(!is_testop(op), "derive_rule_unop_spec: {kind:?}");
    InstSpec {
        kind,
        pops: op.pops(),
        pushes: push_slice(op.push()),
        can_trap: value_op_may_trap(op),
    }
}
