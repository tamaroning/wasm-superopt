//! Static stack-depth analysis for Wasm operators and SemOps.

use crate::semantics::SemOp;
use wasmparser::Operator;

/// `(init_stack_depth, max_stack_depth)` for a straight-line sequence.
pub fn stack_bounds_ops(ops: &[SemOp]) -> (usize, usize) {
    let mut current = 0usize;
    let mut init = 0usize;
    let mut max = 0usize;
    for op in ops {
        let (pop, push) = semop_stack_effect(op);
        if pop > current {
            let diff = pop - current;
            init += diff;
            current = current + diff - pop + push;
        } else {
            current = current - pop + push;
        }
        max = max.max(current);
    }
    max = max.max(init);
    (init, max)
}

pub fn stack_bounds_operators(ops: &[Operator<'_>]) -> (usize, usize) {
    let mut current = 0usize;
    let mut init = 0usize;
    let mut max = 0usize;
    for op in ops {
        if let Some((pop, push)) = operator_stack_effect(op) {
            if pop > current {
                let diff = pop - current;
                init += diff;
                current = current + diff - pop + push;
            } else {
                current = current - pop + push;
            }
            max = max.max(current);
        }
    }
    max = max.max(init);
    (init, max)
}

pub fn semop_stack_effect(op: &SemOp) -> (usize, usize) {
    match op {
        SemOp::I32Const(_) => (0, 1),
        SemOp::I32Add
        | SemOp::I32Sub
        | SemOp::I32Mul
        | SemOp::I32DivU
        | SemOp::I32DivS
        | SemOp::I32Shl
        | SemOp::I32Eq
        | SemOp::I32Ne
        | SemOp::I32LtS
        | SemOp::I32LeS
        | SemOp::I32GtS => (2, 1),
        SemOp::I32Eqz => (1, 1),
        SemOp::I32Clz | SemOp::I32Ctz | SemOp::I32Popcnt => (1, 1),
        SemOp::LocalGet(_) => (0, 1),
        SemOp::LocalSet(_) => (1, 0),
        SemOp::LocalTee(_) => (1, 1),
        SemOp::I32Load { .. } => (1, 1),
        SemOp::I32Store { .. } => (2, 0),
        SemOp::Call { pops, pushes, .. } => (*pops as usize, *pushes as usize),
        SemOp::GlobalGet { .. } => (0, 1),
        SemOp::GlobalSet { .. } => (1, 0),
    }
}

pub fn operator_stack_effect(op: &Operator<'_>) -> Option<(usize, usize)> {
    Some(match op {
        Operator::I32Const { .. } => (0, 1),
        Operator::I32Add
        | Operator::I32Sub
        | Operator::I32Mul
        | Operator::I32DivU
        | Operator::I32DivS
        | Operator::I32Shl
        | Operator::I32Eq
        | Operator::I32Ne
        | Operator::I32LtS
        | Operator::I32LeS
        | Operator::I32GtS
        | Operator::I32GeS
        | Operator::I32GeU => (2, 1),
        Operator::I32Eqz
        | Operator::I32Clz
        | Operator::I32Ctz
        | Operator::I32Popcnt => (1, 1),
        Operator::LocalGet { .. } => (0, 1),
        Operator::LocalSet { .. } => (1, 0),
        Operator::LocalTee { .. } => (1, 1),
        Operator::Drop => (1, 0),
        Operator::I32Load { .. } | Operator::I32Load8S { .. } | Operator::I32Load8U { .. }
        | Operator::I32Load16S { .. } | Operator::I32Load16U { .. } => (1, 1),
        Operator::I32Store { .. }
        | Operator::I32Store8 { .. }
        | Operator::I32Store16 { .. } => (2, 0),
        Operator::GlobalGet { .. } => (0, 1),
        Operator::GlobalSet { .. } => (1, 0),
        Operator::Call { .. } => (0, 0), // resolved dynamically; conservative below
        Operator::Return => (0, 0),
        _ => return None,
    })
}
