//! Derive static `InstSpec` from AL definitions.

use crate::semantics::{InstSpec, StackTy};
use super::defs::WasmBinOp;
use super::ir::{AlCond, AlSpec, AlStep};
use super::policy::EmbeddingPolicy;
use super::util::is_trap_else_push;

const I32: StackTy = StackTy::I32;
const POPS_0: &[StackTy] = &[];
const POPS_1: &[StackTy] = &[I32];
const POPS_2: &[StackTy] = &[I32, I32];
const PUSHES_0: &[StackTy] = &[];
const PUSHES_1: &[StackTy] = &[I32];

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

fn pops_slice(n: usize) -> &'static [StackTy] {
    match n {
        0 => POPS_0,
        1 => POPS_1,
        2 => POPS_2,
        _ => POPS_2,
    }
}

fn pushes_slice(n: usize) -> &'static [StackTy] {
    match n {
        0 => PUSHES_0,
        1 => PUSHES_1,
        _ => PUSHES_1,
    }
}

pub fn derive_inst_spec(al: &AlSpec, policy: &EmbeddingPolicy) -> InstSpec {
    let pop_n = count_pops(&al.steps);
    let push_n = count_pushes(&al.steps, policy);
    InstSpec {
        pops: pops_slice(pop_n),
        pushes: pushes_slice(push_n),
        can_trap: derive_can_trap(&al.steps),
    }
}

/// Static `InstSpec` for `Step_pure/binop` from meta template shape.
pub fn derive_rule_binop_spec(binop: WasmBinOp) -> InstSpec {
    InstSpec {
        pops: POPS_2,
        pushes: PUSHES_1,
        can_trap: binop.is_partial(),
    }
}

/// `Step_read/local.get` — push only.
pub fn derive_rule_local_get_spec() -> InstSpec {
    InstSpec {
        pops: POPS_0,
        pushes: PUSHES_1,
        can_trap: false,
    }
}

/// `Step/local.set` — pop one value, no push.
pub fn derive_rule_local_set_spec() -> InstSpec {
    InstSpec {
        pops: POPS_1,
        pushes: PUSHES_0,
        can_trap: false,
    }
}

/// `Step_pure/local.tee` — pop one, push one (via duplicate + `LOCAL.SET`).
pub fn derive_rule_local_tee_spec() -> InstSpec {
    InstSpec {
        pops: POPS_1,
        pushes: PUSHES_1,
        can_trap: false,
    }
}
