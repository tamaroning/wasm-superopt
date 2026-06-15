//! Concrete (i32) interpreter for AL specs.

use super::env::AlEnv;
use super::ir::{AlCond, AlExpr, AlSpec, AlStep, BinOpKind};
use super::policy::EmbeddingPolicy;
use super::util::{else_push_expr, is_trap_else_push};
use super::super::ConcreteState;

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
        AlExpr::LocalGet(_idx) => panic!("LocalGet in eval_expr requires state"),
        AlExpr::MemLoad(_) => panic!("MemLoad in eval_expr requires state"),
    }
}

fn eval_push_expr(expr: &AlExpr, env: &AlEnv<i32>, state: &ConcreteState) -> i32 {
    match expr {
        AlExpr::LocalGet(idx) => state.load_local(*idx),
        AlExpr::MemLoad(addr) => state.load_mem(*env.get(addr)),
        _ => eval_expr(expr, env),
    }
}

fn eval_binop(kind: BinOpKind, a: i32, b: i32) -> i32 {
    match kind {
        BinOpKind::Add => a.wrapping_add(b),
        BinOpKind::Mul => a.wrapping_mul(b),
        BinOpKind::DivU => (a as u32).wrapping_div(b as u32) as i32,
        BinOpKind::DivS => a.wrapping_div(b),
        BinOpKind::Shl => a.wrapping_shl(b as u32 & 31),
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
        AlStep::Pop(name) => {
            let val = stack.pop().expect("stack underflow");
            env.bind(name, val);
        }
        AlStep::Push(expr) => stack.push(eval_push_expr(expr, env, state)),
        AlStep::SetLocal { idx, var } => {
            let val = *env.get(var);
            *state = state.store_local(*idx, val);
        }
        AlStep::StoreMem { addr, val } => {
            let a = *env.get(addr);
            let v = *env.get(val);
            *state = state.store_mem(a, v);
        }
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
                    eval_push_expr(else_push_expr(else_steps), env, state)
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
