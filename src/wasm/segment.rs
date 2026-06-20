//! Straight-line segment representation.

use crate::sym::SymState;
use crate::semantics::SemOp;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SegmentBounds {
    pub max_local: u32,
    pub max_stack: usize,
}

impl SegmentBounds {
    pub fn new(total_locals: u32, max_stack: usize) -> Self {
        Self {
            max_local: total_locals.saturating_sub(1),
            max_stack: max_stack.saturating_add(5),
        }
    }
}

#[derive(Clone, Debug)]
pub struct StraightSegment {
    pub func_index: u32,
    pub segment_index: usize,
    pub ops: Vec<SemOp>,
    pub init: SymState,
    pub fin: SymState,
    pub bounds: SegmentBounds,
}

impl StraightSegment {
    pub fn original_len(&self) -> usize {
        self.ops.len()
    }
}
