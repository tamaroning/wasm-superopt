//! Concrete (i32) interpreter for flat [`AlSpec`](super::ir::AlSpec) step lists.

use super::super::env::AlEnv;
use super::super::ir::{AlCond, AlExpr, AlSpec, AlStep, BinOpKind};
use super::super::policy::EmbeddingPolicy;
use super::super::util::{else_push_expr, is_trap_else_push};
use crate::semantics::ConcreteState;

fn eval_cond(cond: &AlCond, env: &AlEnv<i32>) -> bool {
    match cond {
        AlCond::BinOpEmpty(kind, lhs, rhs) => {
            let a = *env.get(lhs);
            let b = *env.get(rhs);
            kind.binop_empty_concrete(a, b)
        }
    }
}

fn eval_expr(expr: &AlExpr, env: &AlEnv<i32>) -> i32 {
    match expr {
        AlExpr::ConstI32(n) => *n,
        AlExpr::Var(name) => *env.get(name),
        AlExpr::BinOp(kind, lhs, rhs) => {
            let a = *env.get(lhs);
            let b = *env.get(rhs);
            eval_binop(*kind, a, b)
        }
    }
}

fn eval_binop(kind: BinOpKind, a: i32, b: i32) -> i32 {
    match kind {
        BinOpKind::Add => a.wrapping_add(b),
        BinOpKind::Sub => a.wrapping_sub(b),
        BinOpKind::Mul => a.wrapping_mul(b),
        BinOpKind::DivU => (a as u32).wrapping_div(b as u32) as i32,
        BinOpKind::DivS => a.wrapping_div(b),
        BinOpKind::RemU => (a as u32).wrapping_rem(b as u32) as i32,
        BinOpKind::RemS => a.wrapping_rem(b),
        BinOpKind::Shl => a.wrapping_shl(b as u32 & 31),
        BinOpKind::And => a & b,
        BinOpKind::Or => a | b,
    }
}

fn exec_step(
    step: &AlStep,
    stack: &mut Vec<i32>,
    state: &mut ConcreteState,
    trap: &mut bool,
    env: &mut AlEnv<i32>,
    policy: &EmbeddingPolicy,
) {
    match step {
        AlStep::Push(expr) => stack.push(eval_expr(expr, env)),
        AlStep::If {
            cond,
            then_steps,
            else_steps,
        } => {
            if is_trap_else_push(then_steps, else_steps) && policy.trap_dummy_push {
                let cond_val = eval_cond(cond, env);
                *trap = *trap || cond_val;
                let result = if cond_val {
                    0
                } else {
                    eval_expr(else_push_expr(else_steps), env)
                };
                stack.push(result);
            } else if eval_cond(cond, env) {
                exec_steps(then_steps, stack, state, trap, env, policy);
            } else {
                exec_steps(else_steps, stack, state, trap, env, policy);
            }
        }
        AlStep::Trap => {
            *trap = true;
        }
    }
}

fn exec_steps(
    steps: &[AlStep],
    stack: &mut Vec<i32>,
    state: &mut ConcreteState,
    trap: &mut bool,
    env: &mut AlEnv<i32>,
    policy: &EmbeddingPolicy,
) {
    for step in steps {
        exec_step(step, stack, state, trap, env, policy);
    }
}

pub fn exec_al_concrete(
    al: &AlSpec,
    stack: &mut Vec<i32>,
    state: &mut ConcreteState,
    policy: &EmbeddingPolicy,
) -> bool {
    let mut trap = false;
    let mut env = AlEnv::new();
    exec_steps(&al.steps, stack, state, &mut trap, &mut env, policy);
    trap
}
