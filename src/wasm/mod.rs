//! Parse Wasm modules and extract loop/jump-free straight-line segments.

mod deps;
mod parse;
mod segment;
mod split;
mod stack_analysis;
mod superstack_disasm;

pub use deps::{ops_respect_dependencies, storage_ops_preserved};
pub use parse::{parse_wasm_file, print_input_summary};
#[cfg(test)]
pub use parse::parse_wasm_bytes;
pub use segment::{OpaqueMeta, SegmentBounds, StraightSegment};
pub use split::{split_segments, DEFAULT_MAX_SEGMENT_INSTR};
pub use superstack_disasm::{format_op_superstack, format_ops_superstack_csv, operator_disasm};
