//! Parse Wasm modules and extract loop/jump-free straight-line segments.

mod deps;
mod parse;
mod segment;
mod split;
mod stack_analysis;

pub use deps::{ops_respect_dependencies, storage_ops_preserved};
pub use parse::{parse_wasm_bytes, parse_wasm_file, print_input_summary, WasmModuleInfo};
pub use segment::{OpaqueMeta, SegmentBounds, StraightSegment};
pub use split::{split_segment, split_segments, DEFAULT_MAX_SEGMENT_INSTR};
