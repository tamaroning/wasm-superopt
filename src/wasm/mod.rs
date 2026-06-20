//! Parse Wasm modules and extract loop/jump-free straight-line segments.

mod parse;
mod segment;

pub use parse::parse_wasm_file;
#[allow(unused_imports)]
pub use parse::parse_wasm_bytes;
pub use segment::StraightSegment;
