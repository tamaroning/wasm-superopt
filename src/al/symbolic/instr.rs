//! Z3 executor for [`RuleA`](super::super::ast::Algorithm::RuleA) bodies (`instr` in OCaml).

use super::super::ast::{Arg, Expr, Instr, InstrCond, LetLhs, PopTarget};
use super::super::defs::step_local_set_template;
use super::super::policy::EmbeddingPolicy;
use super::func::{SymEnv, SymValue, encode_expr};
use crate::semantics::{I32_BITS, StateTouches, Z3State};
use z3::Context;
use z3::ast::{Ast, BV, Bool};

fn sym_if_cond<'ctx>(ctx: &'ctx Context, cond: &Expr, env: &SymEnv<'ctx>) -> Bool<'ctx> {
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

fn symval_to_bv<'ctx>(val: &SymValue<'ctx>) -> BV<'ctx> {
    match val {
        SymValue::Nat(bv) | SymValue::Int(bv) => bv.clone(),
        other => panic!("expected nat/int, got {other:?}"),
    }
}

fn local_index(args: &[Arg]) -> u32 {
    match args {
        [Arg::Var(_), Arg::Nat(x)] => *x,
        [Arg::Nat(x)] => *x,
        _ => panic!("$local(z, x) expected store + nat index, got {args:?}"),
    }
}

fn with_local_args(args: &[Arg]) -> (u32, &'static str) {
    match args {
        [Arg::Var(_), Arg::Nat(x), Arg::Var(val)] => (*x, val),
        [Arg::Nat(x), Arg::Var(val)] => (*x, val),
        _ => panic!("$with_local(z, x, val) expected 3 args, got {args:?}"),
    }
}

fn push_expr_z3<'ctx>(
    ctx: &'ctx Context,
    expr: &Expr,
    stack: &mut Vec<BV<'ctx>>,
    state: &Z3State<'ctx>,
    env: &SymEnv<'ctx>,
    trap_guard: Option<&Bool<'ctx>>,
) {
    if let Expr::Call("local", args) = expr {
        let x = local_index(args);
        let idx = BV::from_u64(ctx, x as u64, I32_BITS);
        let val = state
            .locals
            .select(&idx)
            .as_bv()
            .expect("local select is i32 bv");
        stack.push(match trap_guard {
            Some(guard) => {
                let zero = BV::from_i64(ctx, 0, I32_BITS);
                guard.ite(&zero, &val)
            }
            None => val,
        });
        return;
    }
    let val = encode_expr(ctx, expr, env).expect("push expr");
    stack.push(stack_push_bv(ctx, val, trap_guard));
}

fn perform_with_local_z3<'ctx>(
    ctx: &'ctx Context,
    args: &[Arg],
    state: &mut Z3State<'ctx>,
    touches: &mut StateTouches<'ctx>,
    env: &SymEnv<'ctx>,
) {
    let (x, val_name) = with_local_args(args);
    let val = symval_to_bv(env.get(val_name));
    let idx = BV::from_u64(ctx, x as u64, I32_BITS);
    state.locals = state.locals.store(&idx, &val);
    touches.local_writes.insert(x);
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
    state: &mut Z3State<'ctx>,
    trap: &mut Bool<'ctx>,
    env: &mut SymEnv<'ctx>,
    touches: &mut StateTouches<'ctx>,
    policy: &EmbeddingPolicy,
) {
    match step {
        Instr::AssertI(InstrCond::Expr(expr)) => {
            if matches!(expr, Expr::TopValue(_) | Expr::TopValueAny) {
                return;
            }
            encode_expr(ctx, expr, env).expect("assert expr");
        }
        Instr::AssertI(InstrCond::Pred(_)) => panic!("pred assert in rule body"),
        Instr::PopI(pattern) => {
            let name = match pattern {
                PopTarget::NumConst(n) | PopTarget::Val(n) => *n,
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
                            else_env
                                .bind(name, encode_expr(ctx, expr, &else_env).expect("else let"));
                        }
                        Instr::PushI(expr) => {
                            push_expr_z3(ctx, expr, stack, state, &else_env, Some(&is_empty));
                        }
                        other => exec_instr_z3(
                            ctx,
                            other,
                            stack,
                            state,
                            trap,
                            &mut else_env,
                            touches,
                            policy,
                        ),
                    }
                }
                return;
            }

            let c = sym_if_cond(ctx, cond, env);
            let mut stack_t = stack.clone();
            let mut stack_e = stack.clone();
            let mut state_t = state.clone();
            let mut state_e = state.clone();
            let mut trap_t = trap.clone();
            let mut trap_e = trap.clone();
            let mut env_t = env.clone();
            let mut env_e = env.clone();
            let mut touches_t = StateTouches::default();
            let mut touches_e = StateTouches::default();
            exec_instrs_inner(
                ctx,
                then_steps,
                &mut stack_t,
                &mut state_t,
                &mut trap_t,
                &mut env_t,
                &mut touches_t,
                policy,
            );
            exec_instrs_inner(
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
                match (stack_t.get(i), stack_e.get(i)) {
                    (Some(tv), Some(ev)) => stack.push(c.ite(tv, ev)),
                    (Some(tv), None) => stack.push(tv.clone()),
                    (None, Some(ev)) => stack.push(ev.clone()),
                    (None, None) => {}
                }
            }
            touches.local_writes.extend(touches_t.local_writes);
            touches.local_writes.extend(touches_e.local_writes);
            touches.mem_writes.extend(touches_t.mem_writes);
            touches.mem_writes.extend(touches_e.mem_writes);
            *state = state_t;
            let _ = state_e;
            *env = env_e;
        }
        Instr::IfI {
            cond: InstrCond::Pred(_),
            ..
        } => panic!("pred if in rule body"),
        Instr::PushI(expr) => push_expr_z3(ctx, expr, stack, state, env, None),
        Instr::ExecuteI(expr) => {
            if let Expr::CaseE("LOCAL.SET", args) = expr {
                let x = match args.first() {
                    Some(Expr::NatLit(x)) => *x,
                    _ => panic!("LOCAL.SET expected nat index"),
                };
                exec_instrs_inner(
                    ctx,
                    &step_local_set_template(x),
                    stack,
                    state,
                    trap,
                    env,
                    touches,
                    policy,
                );
            } else {
                panic!("unsupported ExecuteI: {expr:?}");
            }
        }
        Instr::PerformI(name, args) => {
            if *name == "with_local" {
                perform_with_local_z3(ctx, args, state, touches, env);
            } else {
                panic!("unsupported PerformI: {name}");
            }
        }
        Instr::TrapI => *trap = Bool::from_bool(ctx, true),
        Instr::ReturnI(_) | Instr::FailI | Instr::ReplaceI { .. } => {
            panic!("func instr in rule body")
        }
    }
}

fn exec_instrs_inner<'ctx>(
    ctx: &'ctx Context,
    steps: &[Instr],
    stack: &mut Vec<BV<'ctx>>,
    state: &mut Z3State<'ctx>,
    trap: &mut Bool<'ctx>,
    env: &mut SymEnv<'ctx>,
    touches: &mut StateTouches<'ctx>,
    policy: &EmbeddingPolicy,
) {
    for step in steps {
        if trap.as_bool() == Some(true) {
            return;
        }
        exec_instr_z3(ctx, step, stack, state, trap, env, touches, policy);
    }
}

/// Z3 execution of a `Step_...` rule body.
pub fn exec_instrs_z3<'ctx>(
    ctx: &'ctx Context,
    steps: &[Instr],
    stack: &mut Vec<BV<'ctx>>,
    state: &mut Z3State<'ctx>,
    touches: &mut StateTouches<'ctx>,
    policy: &EmbeddingPolicy,
) -> Bool<'ctx> {
    let mut trap = Bool::from_bool(ctx, false);
    let mut env = SymEnv::empty();
    exec_instrs_inner(
        ctx, steps, stack, state, &mut trap, &mut env, touches, policy,
    );
    trap
}
