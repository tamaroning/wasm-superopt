//! Deferred symbolic execution and dependency analysis (SuperStack `exec_symbolic_block` phase).

use crate::semantics::SemOp;
use crate::sym::{LocalReq, SymMachine};
use crate::wasm::deps::compute_dependencies;
use crate::wasm::segment::{OpaqueMeta, RawSegment, SegmentBounds, StraightSegment};
use crate::wasm::stack_analysis::stack_bounds_ops;

fn segment_init_state(total_locals: u32, ops: &[SemOp]) -> crate::sym::SymState {
    let (init_stack, _) = stack_bounds_ops(ops);
    let mut locals = std::collections::BTreeMap::new();
    for slot in 0..total_locals {
        locals.insert(slot, LocalReq::Need(SymMachine::local_symbol(slot)));
    }
    crate::sym::SymState {
        stack: SymMachine::implicit_stack_inputs(init_stack),
        locals,
    }
}

/// Run forward symbolic execution and dependency analysis for one raw segment.
pub fn materialize_raw_segment(raw: &RawSegment) -> Option<StraightSegment> {
    if raw.ops.is_empty() {
        return None;
    }
    let (init_stack, block_max_stack) = stack_bounds_ops(&raw.ops);
    let bounds = SegmentBounds::new(
        raw.total_locals,
        block_max_stack.max(raw.bounds_template.max_stack),
    );
    let mut machine = SymMachine::function_entry(raw.num_params, raw.total_locals, bounds.max_stack);
    machine.seed_implicit_stack_inputs(init_stack);
    machine.begin_segment();

    let mut opaque_meta: Vec<OpaqueMeta> = Vec::new();
    let mut executed_ops: Vec<SemOp> = Vec::with_capacity(raw.ops.len());
    for op in &raw.ops {
        match machine.exec_with_meta(op) {
            Ok(Some(meta)) => {
                opaque_meta.push(meta);
                executed_ops.push(op.clone());
            }
            Ok(None) => executed_ops.push(op.clone()),
            Err(_) => break,
        }
    }
    if executed_ops.is_empty() {
        return None;
    }

    let (_, max_stack) = stack_bounds_ops(&executed_ops);
    let mut bounds = bounds;
    bounds.max_stack = bounds.max_stack.max(max_stack + 5);
    let init = segment_init_state(raw.total_locals, &executed_ops);
    let fin = machine.to_fin_state();
    if !init.validate_bounds(&bounds) || !fin.validate_bounds(&bounds) {
        return None;
    }

    let dependencies = compute_dependencies(&executed_ops, &opaque_meta);
    let segment_disasm: std::collections::HashMap<u32, String> = executed_ops
        .iter()
        .filter_map(|op| op.opaque_id())
        .filter_map(|id| raw.disasm_by_id.get(&id).map(|d| (id, d.clone())))
        .collect();

    Some(StraightSegment {
        func_index: raw.func_index,
        num_params: raw.num_params,
        segment_index: raw.segment_index,
        split_part: raw.split_part,
        ops: executed_ops,
        init,
        fin,
        bounds,
        opaque_meta,
        dependencies,
        disasm_by_id: segment_disasm,
    })
}

/// Materialize raw segments (sequential or parallel via `-j`).
pub fn materialize_segments(raw: &[RawSegment], jobs: usize) -> Vec<StraightSegment> {
    if jobs <= 1 {
        return raw.iter().filter_map(materialize_raw_segment).collect();
    }

    crate::parallel::run_with_threads(jobs, || {
        use rayon::prelude::*;
        raw.par_iter().filter_map(materialize_raw_segment).collect()
    })
}
