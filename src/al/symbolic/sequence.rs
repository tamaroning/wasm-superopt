//! Symbolic execution of [`SemOp`](crate::semantics::SemOp) sequences.

use super::state::{ExecResult, StateTouches, Z3State};
use crate::al::eval::state::LOCAL_SLOTS;
use crate::al::{
    I32_BITS, STRAIGHT_LINE_EMBED, al_spec_for, exec_al_z3, exec_instrs_z3, rule_instrs_for,
};
use crate::semantics::{SemOp, StackTy, same_stack_effect};
use z3::Context;
use z3::ast::{Ast, BV, Bool};

pub fn exec_op<'ctx>(
    ctx: &'ctx Context,
    op: &SemOp,
    stack: &mut Vec<BV<'ctx>>,
    state: &mut Z3State<'ctx>,
    touches: &mut StateTouches<'ctx>,
) -> Bool<'ctx> {
    if let Some(steps) = rule_instrs_for(op) {
        return exec_instrs_z3(ctx, &steps, stack, state, touches, &STRAIGHT_LINE_EMBED);
    }
    let al = al_spec_for(op);
    exec_al_z3(ctx, &al, stack, state, touches, &STRAIGHT_LINE_EMBED)
}

pub fn exec_sequence<'ctx>(
    ctx: &'ctx Context,
    ops: &[SemOp],
    mut stack: Vec<BV<'ctx>>,
    mut state: Z3State<'ctx>,
) -> ExecResult<'ctx> {
    let mut trap = Bool::from_bool(ctx, false);
    let mut touches = StateTouches::default();
    for op in ops {
        let t = exec_op(ctx, op, &mut stack, &mut state, &mut touches);
        trap = Bool::or(ctx, &[&trap, &t]);
    }
    ExecResult {
        stack,
        state,
        trap,
        touches,
    }
}

fn state_diff_z3<'ctx>(
    ctx: &'ctx Context,
    lhs: &ExecResult<'ctx>,
    rhs: &ExecResult<'ctx>,
) -> Bool<'ctx> {
    let mut diff = Bool::from_bool(ctx, false);
    if lhs.stack.len() != rhs.stack.len() {
        return Bool::from_bool(ctx, true);
    }
    for (l, r) in lhs.stack.iter().zip(rhs.stack.iter()) {
        diff = Bool::or(ctx, &[&diff, &l._eq(r).not()]);
    }

    for idx in 0..LOCAL_SLOTS {
        let idx_bv = BV::from_u64(ctx, idx as u64, I32_BITS);
        diff = Bool::or(
            ctx,
            &[
                &diff,
                &lhs.state
                    .locals
                    .select(&idx_bv)
                    .as_bv()
                    .expect("locals array stores i32")
                    ._eq(
                        &rhs.state
                            .locals
                            .select(&idx_bv)
                            .as_bv()
                            .expect("locals array stores i32"),
                    )
                    .not(),
            ],
        );
    }

    for addr in lhs
        .touches
        .mem_writes
        .iter()
        .chain(rhs.touches.mem_writes.iter())
    {
        diff = Bool::or(
            ctx,
            &[
                &diff,
                &lhs.state
                    .memory
                    .select(addr)
                    ._eq(&rhs.state.memory.select(addr))
                    .not(),
            ],
        );
    }

    diff
}

/// Z3 proof only (call after [`crate::al::sequences_valid_rewrite_random`] passes).
pub fn sequences_valid_rewrite_z3(
    ctx: &Context,
    input: &[StackTy],
    source: &[SemOp],
    target: &[SemOp],
) -> bool {
    if !same_stack_effect(input, source, target) {
        return false;
    }
    let stack_in: Vec<BV<'_>> = (0..input.len())
        .map(|i| BV::new_const(ctx, format!("in_{i}"), I32_BITS))
        .collect();

    let init = Z3State::fresh(ctx, "init");
    let source_r = exec_sequence(ctx, source, stack_in.clone(), init.clone());
    let target_r = exec_sequence(ctx, target, stack_in, init);

    let solver = z3::Solver::new(ctx);

    // δ_s ⇒ δ_t and trap preservation (trap kinds are not distinguished).
    let trap_violation = source_r.trap.xor(&target_r.trap);
    let defined_both = Bool::and(ctx, &[&source_r.trap.not(), &target_r.trap.not()]);
    let diff = state_diff_z3(ctx, &source_r, &target_r);
    let value_violation = Bool::and(ctx, &[&defined_both, &diff]);

    solver.assert(&Bool::or(ctx, &[&trap_violation, &value_violation]));
    matches!(solver.check(), z3::SatResult::Unsat)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::al::sequences_valid_rewrite_random;
    use crate::al::z3_context;
    use crate::semantics::SemOp;

    #[test]
    fn add_const0_equivalent_to_identity() {
        let ctx = z3_context();
        let input = vec![StackTy::I32];
        let add = vec![SemOp::I32Const(0), SemOp::I32Add];
        let identity = vec![];
        assert!(sequences_valid_rewrite_random(&input, &add, &identity, 200));
        assert!(sequences_valid_rewrite_z3(&ctx, &input, &add, &identity));
    }

    #[test]
    fn mul_const2_equivalent_to_shl_const1_via_z3() {
        let ctx = z3_context();
        let input = vec![StackTy::I32];
        let mul_seq = vec![SemOp::I32Const(2), SemOp::I32Mul];
        let shl_seq = vec![SemOp::I32Const(1), SemOp::I32Shl];
        assert!(sequences_valid_rewrite_z3(&ctx, &input, &mul_seq, &shl_seq));
    }

    #[test]
    fn div_s_not_equivalent_to_div_u_via_z3() {
        let ctx = z3_context();
        let input = vec![StackTy::I32, StackTy::I32];
        let div_s = vec![SemOp::I32DivS];
        let div_u = vec![SemOp::I32DivU];
        assert!(!sequences_valid_rewrite_z3(&ctx, &input, &div_s, &div_u));
    }

    #[test]
    fn div_s_const1_not_equivalent_to_mul_const2_via_z3() {
        let ctx = z3_context();
        let input = vec![StackTy::I32];
        let div_s = vec![SemOp::I32Const(2), SemOp::I32DivS];
        let mul = vec![SemOp::I32Const(2), SemOp::I32Mul];
        assert!(!sequences_valid_rewrite_z3(&ctx, &input, &div_s, &mul));
    }

    #[test]
    fn defined_source_must_not_trap_on_target() {
        let ctx = z3_context();
        let input = vec![StackTy::I32, StackTy::I32];
        let div_u = vec![SemOp::I32DivU];
        let mul = vec![SemOp::I32Mul];
        assert!(!sequences_valid_rewrite_z3(&ctx, &input, &div_u, &mul));
    }

    #[test]
    fn div_u_const1_equivalent_to_add_const0_via_z3() {
        let ctx = z3_context();
        let input = vec![StackTy::I32];
        let div_u = vec![SemOp::I32Const(1), SemOp::I32DivU];
        let add = vec![SemOp::I32Const(0), SemOp::I32Add];
        assert!(sequences_valid_rewrite_z3(&ctx, &input, &div_u, &add));
    }

    #[test]
    fn local_tee_not_equivalent_to_nop_via_z3() {
        let ctx = z3_context();
        let input = vec![StackTy::I32];
        let tee = vec![SemOp::LocalTee(0)];
        let nop = vec![];
        assert!(same_stack_effect(&input, &tee, &nop));
        assert!(!sequences_valid_rewrite_z3(&ctx, &input, &tee, &nop));
    }

    #[test]
    fn local_get_not_equivalent_to_const0_via_z3() {
        let ctx = z3_context();
        let input = vec![];
        let get = vec![SemOp::LocalGet(0)];
        let c0 = vec![SemOp::I32Const(0)];
        assert!(same_stack_effect(&input, &get, &c0));
        assert!(!sequences_valid_rewrite_z3(&ctx, &input, &get, &c0));
    }
}
