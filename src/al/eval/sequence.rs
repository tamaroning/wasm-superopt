//! Concrete execution of [`SemOp`](crate::semantics::SemOp) sequences.

use super::state::{ConcreteResult, ConcreteState, LOCAL_SLOTS, MEM_SLOTS};
use crate::al::{
    STRAIGHT_LINE_EMBED, al_spec_for, exec_al_concrete, exec_instrs_concrete, rule_instrs_for,
};
use crate::semantics::{SemOp, StackTy, is_type_valid, same_stack_effect};

/// Default number of randomized concrete tests before invoking Z3.
pub const DEFAULT_RANDOM_TESTS: usize = 100;

pub fn exec_op_concrete(op: &SemOp, stack: &mut Vec<i32>, state: &mut ConcreteState) -> bool {
    if let Some(steps) = rule_instrs_for(op) {
        return exec_instrs_concrete(&steps, stack, state);
    }
    let al = al_spec_for(op);
    exec_al_concrete(&al, stack, state, &STRAIGHT_LINE_EMBED)
}

pub fn exec_sequence_concrete(
    ops: &[SemOp],
    stack: Vec<i32>,
    state: ConcreteState,
) -> ConcreteResult {
    let mut stack = stack;
    let mut state = state;
    let mut trap = false;
    for op in ops {
        if trap {
            break;
        }
        trap = exec_op_concrete(op, &mut stack, &mut state);
    }
    ConcreteResult { stack, state, trap }
}

struct Lcg(u64);

impl Lcg {
    fn new(seed: u64) -> Self {
        Self(seed)
    }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1);
        self.0
    }

    fn next_i32(&mut self) -> i32 {
        self.next_u64() as i32
    }
}

fn concrete_inputs_for_test(
    input: &[StackTy],
    rng: &mut Lcg,
    case: usize,
) -> (Vec<i32>, ConcreteState) {
    let stack_in = if input.is_empty() {
        vec![]
    } else {
        match case % 8 {
            0 => vec![0; input.len()],
            1 => vec![1; input.len()],
            2 => vec![-1; input.len()],
            3 => (0..input.len()).map(|i| i as i32).collect(),
            4 => vec![i32::MAX; input.len()],
            5 => vec![i32::MIN; input.len()],
            6 => (0..input.len())
                .map(|i| if i % 2 == 0 { 0 } else { 1 })
                .collect(),
            _ => (0..input.len()).map(|_| rng.next_i32()).collect(),
        }
    };

    let locals = std::array::from_fn(|i| match case % 6 {
        0 => 0,
        1 => 1,
        2 => -1,
        3 => i as i32,
        4 => i32::MAX,
        _ => rng.next_i32(),
    });
    let memory = std::array::from_fn(|i| match case % 5 {
        0 => 0,
        1 => 42,
        2 => i as i32,
        3 => -1,
        _ => rng.next_i32(),
    });

    (stack_in, ConcreteState::new(locals, memory))
}

fn concrete_valid_rewrite(source: &ConcreteResult, target: &ConcreteResult) -> bool {
    if source.trap != target.trap {
        return false;
    }
    if source.trap {
        return true;
    }
    source.stack == target.stack
        && source.state.locals == target.state.locals
        && source.state.memory == target.state.memory
}

/// Fast filter: returns `false` if a concrete counterexample is found.
pub fn sequences_valid_rewrite_random(
    input: &[StackTy],
    lhs: &[SemOp],
    rhs: &[SemOp],
    num_tests: usize,
) -> bool {
    if !is_type_valid(input, lhs) || !is_type_valid(input, rhs) {
        return false;
    }
    if !same_stack_effect(input, lhs, rhs) {
        return false;
    }
    if num_tests == 0 {
        return true;
    }

    let mut rng = Lcg::new(0xE6A3_9A1B_CDE2_4701);
    for case in 0..num_tests {
        let (stack_in, state_in) = concrete_inputs_for_test(input, &mut rng, case);
        let lhs_r = exec_sequence_concrete(lhs, stack_in.clone(), state_in.clone());
        let rhs_r = exec_sequence_concrete(rhs, stack_in, state_in);
        if !concrete_valid_rewrite(&lhs_r, &rhs_r) {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::semantics::SemOp;

    #[test]
    fn local_get_pushes_state_concrete() {
        let state = ConcreteState::new([42; LOCAL_SLOTS], [0; MEM_SLOTS]);
        let mut stack = vec![];
        exec_op_concrete(&SemOp::LocalGet(0), &mut stack, &mut state.clone());
        assert_eq!(stack, vec![42]);
    }

    #[test]
    fn local_set_writes_state_concrete() {
        let mut state = ConcreteState::new([0; LOCAL_SLOTS], [0; MEM_SLOTS]);
        let mut stack = vec![99];
        exec_op_concrete(&SemOp::LocalSet(0), &mut stack, &mut state);
        assert_eq!(stack, Vec::<i32>::new());
        assert_eq!(state.locals[0], 99);
    }

    #[test]
    fn local_tee_preserves_stack_concrete() {
        let mut state = ConcreteState::new([0; LOCAL_SLOTS], [0; MEM_SLOTS]);
        let mut stack = vec![77];
        exec_op_concrete(&SemOp::LocalTee(1), &mut stack, &mut state);
        assert_eq!(stack, vec![77]);
        assert_eq!(state.locals[1], 77);
    }

    #[test]
    fn trap_preservation_rejects_removing_div_trap() {
        let input = vec![StackTy::I32, StackTy::I32];
        let div_u = vec![SemOp::I32DivU];
        let mul = vec![SemOp::I32Mul];
        assert!(!sequences_valid_rewrite_random(&input, &div_u, &mul, 200));
    }

    #[test]
    fn div_u_const1_equivalent_to_add_const0_random() {
        let input = vec![StackTy::I32];
        let div_u = vec![SemOp::I32Const(1), SemOp::I32DivU];
        let add = vec![SemOp::I32Const(0), SemOp::I32Add];
        assert!(sequences_valid_rewrite_random(&input, &div_u, &add, 200));
    }

    #[test]
    fn local_tee_not_equivalent_to_nop_random() {
        let input = vec![StackTy::I32];
        let tee = vec![SemOp::LocalTee(0)];
        let nop = vec![];
        assert!(!sequences_valid_rewrite_random(&input, &tee, &nop, 100));
    }

    #[test]
    fn local_get_not_equivalent_to_const0_random() {
        let input = vec![];
        let get = vec![SemOp::LocalGet(0)];
        let c0 = vec![SemOp::I32Const(0)];
        assert!(!sequences_valid_rewrite_random(&input, &get, &c0, 100));
    }
}
