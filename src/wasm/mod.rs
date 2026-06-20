//! Parse Wasm modules and extract loop/jump-free straight-line segments.

mod parse;
mod segment;
mod stack_analysis;

pub use parse::{parse_wasm_bytes, parse_wasm_file, print_input_summary, WasmModuleInfo};
pub use segment::{SegmentBounds, StraightSegment};
