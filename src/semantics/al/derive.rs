//! Derive static `InstSpec` from AL definitions.

use super::super::{InstSpec, StackTy};
use super::ir::{AlCond, AlExpr, AlSpec, AlStep};
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
            AlStep::Pop(_) => n += 1,
            AlStep::If {
                then_steps,
                else_steps,
                ..
            } => {
                n += count_pops(then_steps) + count_pops(else_steps);
            }
            AlStep::Push(_) | AlStep::SetLocal { .. } | AlStep::StoreMem { .. } | AlStep::Trap => {}
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
            AlStep::Pop(_) | AlStep::SetLocal { .. } | AlStep::StoreMem { .. } | AlStep::Trap => {}
        }
    }
    n
}

fn touches_state(steps: &[AlStep]) -> bool {
    for step in steps {
        match step {
            AlStep::SetLocal { .. } | AlStep::StoreMem { .. } => return true,
            AlStep::Push(expr) => {
                if matches!(expr, AlExpr::LocalGet(_) | AlExpr::MemLoad(_)) {
                    return true;
                }
            }
            AlStep::If {
                then_steps,
                else_steps,
                ..
            } => {
                if touches_state(then_steps) || touches_state(else_steps) {
                    return true;
                }
            }
            AlStep::Pop(_) | AlStep::Trap => {}
        }
    }
    false
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
        touches_state: touches_state(&al.steps),
        can_trap: derive_can_trap(&al.steps),
    }
}

/// Static `InstSpec` for `Step_pure/binop` from meta template shape.
pub fn derive_meta_binop_spec(binop: super::ir::WasmBinOp) -> InstSpec {
    InstSpec {
        pops: POPS_2,
        pushes: PUSHES_1,
        touches_state: false,
        can_trap: binop.is_partial(),
    }
}

#[cfg(test)]
pub(crate) const POPS_0_TEST: &[StackTy] = POPS_0;
#[cfg(test)]
pub(crate) const POPS_1_TEST: &[StackTy] = POPS_1;
#[cfg(test)]
pub(crate) const POPS_2_TEST: &[StackTy] = POPS_2;
#[cfg(test)]
pub(crate) const PUSHES_0_TEST: &[StackTy] = PUSHES_0;
#[cfg(test)]
pub(crate) const PUSHES_1_TEST: &[StackTy] = PUSHES_1;
