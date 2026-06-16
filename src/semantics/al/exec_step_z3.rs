//! Z3 executor for meta-level `AlMetaStep` templates (e.g. `Step_pure/binop`).

use super::al_defs::step_pure_binop_template;
use super::encode_sym::{encode_binop_stack, sym_choose_nat, sym_is_empty, SymEnv, SymValue};
use super::ir::{NumType, WasmBinOp};
use super::meta::AlMetaStep;
use super::policy::EmbeddingPolicy;
use super::super::{I32_BITS, StateTouches, Z3State};
use z3::Context;
use z3::ast::{BV, Bool};

fn exec_meta_step_z3<'ctx>(
    ctx: &'ctx Context,
    step: &AlMetaStep,
    nt: NumType,
    binop: WasmBinOp,
    stack: &mut Vec<BV<'ctx>>,
    trap: &mut Bool<'ctx>,
    env: &mut SymEnv<'ctx>,
    policy: &EmbeddingPolicy,
) {
    match step {
        AlMetaStep::Assert(_) => {}
        AlMetaStep::Pop(pattern) => {
            let name = match pattern {
                super::meta::PopPattern::NumConst(n) => *n,
            };
            let val = stack.pop().expect("stack underflow");
            env.bind(name, SymValue::nat_from_stack(val));
        }
        AlMetaStep::If { then_steps, else_steps, .. } => {
            let c1 = as_stack_bv(env.get("c_1"));
            let c2 = as_stack_bv(env.get("c_2"));
            let binop_result =
                encode_binop_stack(ctx, nt, binop, c1, c2).expect("binop_ encode failed");
            let is_empty = sym_is_empty(ctx, &binop_result);
            if policy.trap_dummy_push {
                *trap = Bool::or(ctx, &[trap, &is_empty]);
                let zero = BV::from_i64(ctx, 0, I32_BITS);
                let result = sym_choose_nat(ctx, binop_result);
                stack.push(is_empty.ite(&zero, &result));
            } else if is_empty.as_bool().unwrap_or(false) {
                exec_meta_steps_z3_inner(ctx, then_steps, nt, binop, stack, trap, env, policy);
            } else {
                exec_meta_steps_z3_inner(ctx, else_steps, nt, binop, stack, trap, env, policy);
            }
        }
        AlMetaStep::Let { .. } | AlMetaStep::Push(_) => {
            panic!("Let/Push in Step_pure/binop are encoded in the If/else branch")
        }
        AlMetaStep::Trap => {
            *trap = Bool::from_bool(ctx, true);
        }
    }
}

fn as_stack_bv<'ctx>(v: &SymValue<'ctx>) -> BV<'ctx> {
    match v {
        SymValue::Nat(bv) => bv.clone(),
        other => panic!("expected stack nat, got {other:?}"),
    }
}

fn exec_meta_steps_z3_inner<'ctx>(
    ctx: &'ctx Context,
    steps: &[AlMetaStep],
    nt: NumType,
    binop: WasmBinOp,
    stack: &mut Vec<BV<'ctx>>,
    trap: &mut Bool<'ctx>,
    env: &mut SymEnv<'ctx>,
    policy: &EmbeddingPolicy,
) {
    for step in steps {
        exec_meta_step_z3(ctx, step, nt, binop, stack, trap, env, policy);
    }
}

pub fn exec_meta_steps_z3<'ctx>(
    ctx: &'ctx Context,
    steps: &[AlMetaStep],
    nt: NumType,
    binop: WasmBinOp,
    stack: &mut Vec<BV<'ctx>>,
    _state: &mut Z3State<'ctx>,
    trap: &mut Bool<'ctx>,
    _touches: &mut StateTouches<'ctx>,
    policy: &EmbeddingPolicy,
) {
    let mut env = SymEnv::new(&[], &[]);
    exec_meta_steps_z3_inner(ctx, steps, nt, binop, stack, trap, &mut env, policy);
}

pub fn exec_meta_binop_z3<'ctx>(
    ctx: &'ctx Context,
    nt: NumType,
    binop: WasmBinOp,
    stack: &mut Vec<BV<'ctx>>,
    state: &mut Z3State<'ctx>,
    touches: &mut StateTouches<'ctx>,
    policy: &EmbeddingPolicy,
) -> Bool<'ctx> {
    let steps = step_pure_binop_template(nt, binop);
    let mut trap = Bool::from_bool(ctx, false);
    exec_meta_steps_z3(ctx, &steps, nt, binop, stack, state, &mut trap, touches, policy);
    trap
}
