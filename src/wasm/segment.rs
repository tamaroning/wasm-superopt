//! Straight-line segment representation.

use crate::sym::SymState;
use crate::semantics::SemOp;

#[derive(Clone, Debug)]
pub struct StraightSegment {
    pub func_index: u32,
    pub segment_index: usize,
    pub ops: Vec<SemOp>,
    pub init: SymState,
    pub fin: SymState,
}

impl StraightSegment {
    pub fn original_len(&self) -> usize {
        self.ops.len()
    }
}
