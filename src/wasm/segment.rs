//! Straight-line segment representation.

use crate::semantics::SemOp;
use crate::sym::SymState;

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

/// Metadata for an uninterpreted (opaque) instruction in a segment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpaqueMeta {
    pub id: u32,
    pub storage: bool,
    pub result_symbols: Vec<String>,
    pub input_symbols: Vec<String>,
}

impl OpaqueMeta {
    pub fn from_exec(id: u32, storage: bool, inputs: Vec<String>, results: Vec<String>) -> Self {
        Self {
            id,
            storage,
            input_symbols: inputs,
            result_symbols: results,
        }
    }
}

#[derive(Clone, Debug)]
pub struct StraightSegment {
    pub func_index: u32,
    pub segment_index: usize,
    /// When set, this segment is part `0..part_total` of a split parent segment.
    pub split_part: Option<(usize, usize)>,
    pub ops: Vec<SemOp>,
    pub init: SymState,
    pub fin: SymState,
    pub bounds: SegmentBounds,
    pub opaque_meta: Vec<OpaqueMeta>,
    pub dependencies: Vec<(u32, u32)>,
}

impl StraightSegment {
    pub fn original_len(&self) -> usize {
        self.ops.len()
    }

    pub fn label(&self) -> String {
        match self.split_part {
            Some((part, total)) if total > 1 => {
                format!("{} part {}/{}", self.segment_index, part + 1, total)
            }
            _ => self.segment_index.to_string(),
        }
    }

    pub fn storage_ids(&self) -> impl Iterator<Item = u32> + '_ {
        self.ops
            .iter()
            .filter(|op| op.is_storage_boundary())
            .filter_map(|op| op.opaque_id())
    }

    pub fn opaque_meta_for(&self, id: u32) -> Option<&OpaqueMeta> {
        self.opaque_meta.iter().find(|m| m.id == id)
    }

    pub fn has_opaque(&self) -> bool {
        !self.opaque_meta.is_empty()
    }
}
