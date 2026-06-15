//! Z3 symbolic interpreter for AL specs.

use super::env::AlEnv;
use super::ir::{AlCond, AlExpr, AlSpec, AlStep, BinOpKind};
use super::policy::EmbeddingPolicy;
use super::util::{else_push_expr, is_trap_else_push};
use super::super::{StateTouches, Z3State, I32_BITS};
use z3::ast::{BV, Bool};
use z3::Context;

fn eval_cond<'ctx>(ctx: &'ctx Context, cond: &AlCond, env: &AlEnv<BV<'ctx>>) -> Bool<'ctx> {
    match cond {
        AlCond::BinOpEmpty(kind, lhs, rhs) => {
            let a = env.get(lhs).clone();
            let b = env.get(rhs).clone();
            kind.binop_empty_z3(ctx, &a, &b)
        }
    }
}

fn eval_expr<'ctx>(
    ctx: &'ctx Context,
    expr: &AlExpr,
    env: &AlEnv<BV<'ctx>>,
    state: &Z3State<'ctx>,
) -> BV<'ctx> {
    match expr {
        AlExpr::ConstI32(n) => BV::from_i64(ctx, *n as i64, I32_BITS),
        AlExpr::Var(name) => env.get(name).clone(),
        AlExpr::BinOp(kind, lhs, rhs) => {
            let a = env.get(lhs).clone();
            let b = env.get(rhs).clone();
            eval_binop(ctx, *kind, &a, &b)
        }
        AlExpr::LocalGet(idx) => state.load_local(ctx, *idx),
        AlExpr::MemLoad(addr) => state.load_mem(env.get(addr)),
    }
}

fn eval_binop<'ctx>(ctx: &'ctx Context, kind: BinOpKind, a: &BV<'ctx>, b: &BV<'ctx>) -> BV<'ctx> {
    match kind {
        BinOpKind::Add => a.bvadd(b),
        BinOpKind::Mul => a.bvmul(b),
        BinOpKind::DivU => a.bvudiv(b),
        BinOpKind::DivS => a.bvsdiv(b),
        BinOpKind::Shl => {
            let mask = BV::from_u64(ctx, 31, I32_BITS);
            a.bvshl(&b.bvand(&mask))
        }
    }
}

fn exec_step<'ctx>(
    ctx: &'ctx Context,
    step: &AlStep,
    stack: &mut Vec<BV<'ctx>>,
    state: &mut Z3State<'ctx>,
    trap: &mut Bool<'ctx>,
    env: &mut AlEnv<BV<'ctx>>,
    touches: &mut StateTouches<'ctx>,
    policy: &EmbeddingPolicy,
) {
    match step {
        AlStep::Pop(name) => {
            let val = stack.pop().expect("stack underflow");
            env.bind(name, val);
        }
        AlStep::Push(expr) => stack.push(eval_expr(ctx, expr, env, state)),
        AlStep::SetLocal { idx, var } => {
            let val = env.get(var).clone();
            touches.local_writes.insert(*idx);
            *state = state.store_local(ctx, *idx, &val);
        }
        AlStep::StoreMem { addr, val } => {
            let a = env.get(addr).clone();
            let v = env.get(val).clone();
            touches.mem_writes.push(a.clone());
            *state = state.store_mem(&a, &v);
        }
        AlStep::If {
            cond,
            then_steps,
            else_steps,
        } => {
            if is_trap_else_push(then_steps, else_steps) && policy.trap_dummy_push {
                let c = eval_cond(ctx, cond, env);
                *trap = Bool::or(ctx, &[trap, &c]);
                let zero = BV::from_i64(ctx, 0, I32_BITS);
                let result = eval_expr(ctx, else_push_expr(else_steps), env, state);
                stack.push(c.ite(&zero, &result));
            } else {
                let c = eval_cond(ctx, cond, env);
                let mut trap_t = trap.clone();
                let mut trap_e = trap.clone();
                let mut stack_t = stack.clone();
                let mut stack_e = stack.clone();
                let mut state_t = state.clone();
                let mut state_e = state.clone();
                let mut env_t = env.clone();
                let mut env_e = env.clone();
                let mut touches_t = StateTouches::default();
                let mut touches_e = StateTouches::default();
                exec_steps(
                    ctx,
                    then_steps,
                    &mut stack_t,
                    &mut state_t,
                    &mut trap_t,
                    &mut env_t,
                    &mut touches_t,
                    policy,
                );
                exec_steps(
                    ctx,
                    else_steps,
                    &mut stack_e,
                    &mut state_e,
                    &mut trap_e,
                    &mut env_e,
                    &mut touches_e,
                    policy,
                );
                *trap = Bool::or(
                    ctx,
                    &[
                        &Bool::and(ctx, &[&c, &trap_t]),
                        &Bool::and(ctx, &[&c.not(), &trap_e]),
                    ],
                );
                let base_len = stack.len();
                let new_len = stack_t.len().max(stack_e.len());
                stack.truncate(base_len);
                for i in base_len..new_len {
                    let t = stack_t.get(i).cloned();
                    let e = stack_e.get(i).cloned();
                    match (t, e) {
                        (Some(tv), Some(ev)) => stack.push(c.ite(&tv, &ev)),
                        (Some(tv), None) => stack.push(tv),
                        (None, Some(ev)) => stack.push(ev),
                        (None, None) => {}
                    }
                }
                touches.local_writes.extend(touches_t.local_writes);
                touches.local_writes.extend(touches_e.local_writes);
                touches.mem_writes.extend(touches_t.mem_writes);
                touches.mem_writes.extend(touches_e.mem_writes);
                *state = state_t;
                let _ = state_e;
            }
        }
        AlStep::Trap => {
            *trap = Bool::from_bool(ctx, true);
        }
    }
}

fn exec_steps<'ctx>(
    ctx: &'ctx Context,
    steps: &[AlStep],
    stack: &mut Vec<BV<'ctx>>,
    state: &mut Z3State<'ctx>,
    trap: &mut Bool<'ctx>,
    env: &mut AlEnv<BV<'ctx>>,
    touches: &mut StateTouches<'ctx>,
    policy: &EmbeddingPolicy,
) {
    for step in steps {
        exec_step(ctx, step, stack, state, trap, env, touches, policy);
    }
}

pub fn exec_al_z3<'ctx>(
    ctx: &'ctx Context,
    al: &AlSpec,
    stack: &mut Vec<BV<'ctx>>,
    state: &mut Z3State<'ctx>,
    touches: &mut StateTouches<'ctx>,
    policy: &EmbeddingPolicy,
) -> Bool<'ctx> {
    let mut trap = Bool::from_bool(ctx, false);
    let mut env = AlEnv::new();
    exec_steps(
        ctx,
        &al.steps,
        stack,
        state,
        &mut trap,
        &mut env,
        touches,
        policy,
    );
    trap
}
