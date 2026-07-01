//! Parse Wasm modules and extract loop/jump-free straight-line segments.

#[cfg(test)]
mod bench_parse;
mod deps;
mod materialize;
mod parse;
mod segment;
mod split;
mod stack_analysis;
mod superstack_disasm;

pub use deps::{ops_respect_dependencies, storage_ops_preserved};
pub use materialize::materialize_segments;
#[cfg(test)]
pub use parse::parse_wasm_bytes;
pub use parse::{parse_wasm_file, print_input_summary};
pub use segment::{OpaqueMeta, RawSegment, SegmentBounds, StraightSegment};
pub use split::{DEFAULT_MAX_SEGMENT_INSTR, split_raw_segments, split_segment, split_segments};
pub use superstack_disasm::format_ops_superstack_csv;
