//! Z3 executor for [`RuleA`](super::super::ast::Algorithm::RuleA) bodies (`instr` in OCaml).

use super::func::{encode_expr, SymEnv, SymValue};
use super::super::ast::{Expr, Instr, InstrCond, LetLhs, PopTarget};
use super::super::policy::EmbeddingPolicy;
use crate::semantics::{I32_BITS, StateTouches, Z3State};
use z3::Context;
use z3::ast::{Ast, BV, Bool};

fn sym_if_cond<'ctx>(
    ctx: &'ctx Context,
    cond: &Expr,
    env: &SymEnv<'ctx>,
) -> Bool<'ctx> {
    match encode_expr(ctx, cond, env).expect("if cond") {
        SymValue::Nat(bv) => bv._eq(&BV::from_u64(ctx, 0, I32_BITS)),
        other => panic!("if cond expected nat, got {other:?}"),
    }
}

fn stack_push_bv<'ctx>(
    ctx: &'ctx Context,
    val: SymValue<'ctx>,
    trap_guard: Option<&Bool<'ctx>>,
) -> BV<'ctx> {
    let bv = match val {
        SymValue::Nat(bv) => bv,
        SymValue::Int(bv) => bv,
        other => panic!("stack push expected nat/int, got {other:?}"),
    };
    match trap_guard {
        Some(guard) => {
            let zero = BV::from_i64(ctx, 0, I32_BITS);
            guard.ite(&zero, &bv)
        }
        None => bv,
    }
}

fn is_trap_else_push_rule(then_steps: &[Instr], else_steps: &[Instr]) -> bool {
    then_steps == [Instr::TrapI]
        && else_steps
            .last()
            .is_some_and(|s| matches!(s, Instr::PushI(_)))
}

fn exec_instr_z3<'ctx>(
    ctx: &'ctx Context,
    step: &Instr,
    stack: &mut Vec<BV<'ctx>>,
    trap: &mut Bool<'ctx>,
    env: &mut SymEnv<'ctx>,
    policy: &EmbeddingPolicy,
) {
    match step {
        Instr::AssertI(InstrCond::Expr(expr)) => {
            if matches!(expr, Expr::TopValue(_)) {
                return;
            }
            encode_expr(ctx, expr, env).expect("assert expr");
        }
        Instr::AssertI(InstrCond::Pred(_)) => panic!("pred assert in rule body"),
        Instr::PopI(pattern) => {
            let name = match pattern {
                PopTarget::NumConst(n) => *n,
            };
            let val = stack.pop().expect("stack underflow");
            env.bind(name, SymValue::nat_from_stack(val));
        }
        Instr::LetI {
            lhs: LetLhs::Var(name),
            expr,
        } => {
            env.bind(name, encode_expr(ctx, expr, env).expect("let expr"));
        }
        Instr::LetI { .. } => panic!("binop-case let in rule body"),
        Instr::IfI {
            cond: InstrCond::Expr(cond),
            then_steps,
            else_steps,
        } => {
            if policy.trap_dummy_push && is_trap_else_push_rule(then_steps, else_steps) {
                let is_empty = sym_if_cond(ctx, cond, env);
                *trap = Bool::or(ctx, &[trap, &is_empty]);
                let mut else_env = env.clone();
                for step in else_steps {
                    match step {
                        Instr::LetI {
                            lhs: LetLhs::Var(name),
                            expr,
                        } => {
                            else_env.bind(
                                name,
                                encode_expr(ctx, expr, &else_env).expect("else let"),
                            );
                        }
                        Instr::PushI(expr) => {
                            let val =
                                encode_expr(ctx, expr, &else_env).expect("else push expr");
                            stack.push(stack_push_bv(ctx, val, Some(&is_empty)));
                        }
                        other => exec_instr_z3(
                            ctx,
                            other,
                            stack,
                            trap,
                            &mut else_env,
                            policy,
                        ),
                    }
                }
                return;
            }

            let c = sym_if_cond(ctx, cond, env);
            let mut stack_t = stack.clone();
            let mut stack_e = stack.clone();
            let mut trap_t = trap.clone();
            let mut trap_e = trap.clone();
            let mut env_t = env.clone();
            let mut env_e = env.clone();
            exec_instrs_inner(
                ctx,
                then_steps,
                &mut stack_t,
                &mut trap_t,
                &mut env_t,
                policy,
            );
            exec_instrs_inner(
                ctx,
                else_steps,
                &mut stack_e,
                &mut trap_e,
                &mut env_e,
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
                match (stack_t.get(i), stack_e.get(i)) {
                    (Some(tv), Some(ev)) => stack.push(c.ite(tv, ev)),
                    (Some(tv), None) => stack.push(tv.clone()),
                    (None, Some(ev)) => stack.push(ev.clone()),
                    (None, None) => {}
                }
            }
            *env = env_e;
        }
        Instr::IfI {
            cond: InstrCond::Pred(_), ..
        } => panic!("pred if in rule body"),
        Instr::PushI(expr) => {
            let val = encode_expr(ctx, expr, env).expect("push expr");
            stack.push(stack_push_bv(ctx, val, None));
        }
        Instr::TrapI => *trap = Bool::from_bool(ctx, true),
        Instr::ReturnI(_) | Instr::FailI => panic!("func instr in rule body"),
    }
}

fn exec_instrs_inner<'ctx>(
    ctx: &'ctx Context,
    steps: &[Instr],
    stack: &mut Vec<BV<'ctx>>,
    trap: &mut Bool<'ctx>,
    env: &mut SymEnv<'ctx>,
    policy: &EmbeddingPolicy,
) {
    for step in steps {
        if trap.as_bool() == Some(true) {
            return;
        }
        exec_instr_z3(ctx, step, stack, trap, env, policy);
    }
}

/// Z3 execution of a `Step_pure/...` rule body.
pub fn exec_instrs_z3<'ctx>(
    ctx: &'ctx Context,
    steps: &[Instr],
    stack: &mut Vec<BV<'ctx>>,
    _state: &mut Z3State<'ctx>,
    touches: &mut StateTouches<'ctx>,
    policy: &EmbeddingPolicy,
) -> Bool<'ctx> {
    let mut trap = Bool::from_bool(ctx, false);
    let mut env = SymEnv::empty();
    exec_instrs_inner(ctx, steps, stack, &mut trap, &mut env, policy);
    let _ = touches;
    trap
}
