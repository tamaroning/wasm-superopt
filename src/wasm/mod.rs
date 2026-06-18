//! Parse Wasm modules and extract loop/jump-free straight-line segments.

mod parse;
mod segment;

pub use parse::{parse_wasm_bytes, parse_wasm_file, WasmModuleInfo};
pub use segment::StraightSegment;
