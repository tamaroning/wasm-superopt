//! Parse Wasm modules and extract loop/jump-free straight-line segments.

mod parse;
mod segment;

pub use parse::{WasmModuleInfo, parse_wasm_bytes, parse_wasm_file};
pub use segment::StraightSegment;
