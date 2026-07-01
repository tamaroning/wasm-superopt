//! Split long straight-line segments into smaller chunks (SuperStack `-sp`).

use crate::semantics::SemOp;
use crate::sym::SymMachine;
use crate::wasm::deps::compute_dependencies;
use crate::wasm::segment::{RawSegment, SegmentBounds, StraightSegment};
use crate::wasm::stack_analysis::stack_bounds_ops;
use std::collections::HashMap;

/// Default maximum instructions per optimization chunk (SuperStack smoke eval uses 10).
pub const DEFAULT_MAX_SEGMENT_INSTR: usize = 10;

/// Mechanical split before symbolic execution (SuperStack `split_simple`).
pub fn split_raw_segment(raw: &RawSegment, max_instr: usize) -> Vec<RawSegment> {
    if max_instr == 0 || raw.ops.len() <= max_instr {
        return vec![raw.clone()];
    }
    let part_count = raw.ops.len().div_ceil(max_instr);
    (0..part_count)
        .map(|part| {
            let beg = part * max_instr;
            let end = ((part + 1) * max_instr).min(raw.ops.len());
            let ops = raw.ops[beg..end].to_vec();
            let disasm_by_id: HashMap<u32, String> = ops
                .iter()
                .filter_map(|op| op.opaque_id())
                .filter_map(|id| raw.disasm_by_id.get(&id).map(|d| (id, d.clone())))
                .collect();
            RawSegment {
                func_index: raw.func_index,
                num_params: raw.num_params,
                total_locals: raw.total_locals,
                segment_index: raw.segment_index,
                split_part: Some((part, part_count)),
                bounds_template: raw.bounds_template,
                ops,
                disasm_by_id,
            }
        })
        .collect()
}

pub fn split_raw_segments(raw: &[RawSegment], max_instr: usize) -> Vec<RawSegment> {
    raw.iter()
        .flat_map(|s| split_raw_segment(s, max_instr))
        .collect()
}

fn chunk_bounds(segment: &StraightSegment, ops: &[SemOp]) -> SegmentBounds {
    let (_, max_stack) = stack_bounds_ops(ops);
    let mut bounds = segment.bounds;
    bounds.max_stack = bounds.max_stack.max(max_stack.saturating_add(5));
    bounds
}

/// Split `segment` into chunks of at most `max_instr` instructions.
/// When `max_instr` is 0 or the segment is already short enough, returns a clone.
pub fn split_segment(segment: &StraightSegment, max_instr: usize) -> Vec<StraightSegment> {
    if max_instr == 0 || segment.ops.len() <= max_instr {
        return vec![segment.clone()];
    }

    let mut machine = SymMachine::from_segment_entry(
        segment.num_params,
        &segment.bounds,
        &segment.init,
        segment.bounds.max_stack,
    );

    let part_count = segment.ops.len().div_ceil(max_instr);
    let mut out = Vec::with_capacity(part_count);

    for part in 0..part_count {
        let beg = part * max_instr;
        let end = ((part + 1) * max_instr).min(segment.ops.len());
        let ops = segment.ops[beg..end].to_vec();

        let init = if part == 0 {
            segment.init.clone()
        } else {
            machine.to_carried_init_state()
        };

        if part > 0 {
            machine.begin_segment();
        }

        let mut opaque_meta = Vec::new();
        for op in &ops {
            match machine.exec_with_meta(op) {
                Ok(Some(meta)) => opaque_meta.push(meta),
                Ok(None) => {}
                Err(e) => panic!(
                    "re-exec func {} segment {} part {part}: {e:?}",
                    segment.func_index, segment.segment_index
                ),
            }
        }

        let fin = machine.to_fin_state();
        let bounds = chunk_bounds(segment, &ops);
        if !init.validate_bounds(&bounds) || !fin.validate_bounds(&bounds) {
            return vec![segment.clone()];
        }

        let dependencies = compute_dependencies(&ops, &opaque_meta);
        let disasm_by_id: std::collections::HashMap<u32, String> = ops
            .iter()
            .filter_map(|op| op.opaque_id())
            .filter_map(|id| segment.disasm_by_id.get(&id).map(|d| (id, d.clone())))
            .collect();

        out.push(StraightSegment {
            func_index: segment.func_index,
            num_params: segment.num_params,
            segment_index: segment.segment_index,
            split_part: Some((part, part_count)),
            ops,
            init,
            fin,
            bounds,
            opaque_meta,
            dependencies,
            disasm_by_id,
        });
    }

    out
}

pub fn split_segments(segments: &[StraightSegment], max_instr: usize) -> Vec<StraightSegment> {
    segments
        .iter()
        .flat_map(|s| split_segment(s, max_instr))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::optimize::format_ops;
    use crate::wasm::materialize_segments;
    use crate::wasm::parse_wasm_bytes;

    #[test]
    fn short_segment_not_split() {
        let wasm = wat::parse_str(r#"(module (func (param i32) local.get 0 i32.const 1 i32.add))"#)
            .unwrap();
        let info = parse_wasm_bytes(&wasm).unwrap();
        let seg = &materialize_segments(&info.segments, 1)[0];
        let parts = split_segment(seg, DEFAULT_MAX_SEGMENT_INSTR);
        assert_eq!(parts.len(), 1);
        assert!(parts[0].split_part.is_none());
    }

    #[test]
    fn long_segment_splits_into_ten_instruction_chunks() {
        let wasm = wat::parse_str(
            r#"(module
                (func (param i32 i32 i32 i32 i32 i32 i32) (local i32 i32 i32 i32 i32)
                  i32.const 1
                  local.set 3
                  local.get 2
                  i32.const 1
                  i32.add
                  local.set 2
                  local.get 4
                  i32.const 4
                  i32.add
                  local.set 4
                  local.get 7
                  local.set 5
                  local.get 6
                  i32.const 1
                  i32.add
                  local.tee 6
                  local.get 1
                  i32.lt_s
                )
            )"#,
        )
        .unwrap();
        let info = parse_wasm_bytes(&wasm).unwrap();
        let seg = &materialize_segments(&info.segments, 1)[0];
        assert_eq!(seg.original_len(), 18);
        let parts = split_segment(seg, DEFAULT_MAX_SEGMENT_INSTR);
        assert_eq!(parts.len(), 2);
        assert_eq!(parts[0].ops.len(), 10);
        assert_eq!(parts[1].ops.len(), 8);
        assert_eq!(parts[0].split_part, Some((0, 2)));
        assert_eq!(parts[1].split_part, Some((1, 2)));
        assert_eq!(
            parts.iter().map(|p| p.ops.len()).sum::<usize>(),
            seg.original_len()
        );
    }

    #[test]
    fn split_preserves_concatenated_ops() {
        let wasm = wat::parse_str(
            r#"(module
                (func (param i32 i32 i32 i32 i32 i32 i32) (local i32 i32 i32 i32 i32)
                  i32.const 1
                  local.set 3
                  local.get 2
                  i32.const 1
                  i32.add
                  local.set 2
                  local.get 4
                  i32.const 4
                  i32.add
                  local.set 4
                  local.get 7
                  local.set 5
                  local.get 6
                  i32.const 1
                  i32.add
                  local.tee 6
                  local.get 1
                  i32.lt_s
                )
            )"#,
        )
        .unwrap();
        let info = parse_wasm_bytes(&wasm).unwrap();
        let seg = &materialize_segments(&info.segments, 1)[0];
        let parts = split_segment(seg, DEFAULT_MAX_SEGMENT_INSTR);
        let merged: Vec<_> = parts.iter().flat_map(|p| p.ops.iter()).cloned().collect();
        assert_eq!(format_ops(&merged), format_ops(&seg.ops));
    }
}
