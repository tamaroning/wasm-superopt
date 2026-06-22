//! Phase 2: backward shortest-path search over straight-line Wasm segments (idea.md §2–§8).

mod canon;
#[cfg(test)]
pub(crate) mod fixtures;
mod heuristic;
mod inverse;
mod search;

pub use search::{
    DEFAULT_MAX_DEPTH, DEFAULT_TIMEOUT_BASE_SECS, DIRECT_TIMEOUT_SECS, SearchConfig,
    format_ops, segment_timeout_secs,
};
use crate::lang::ValueLang;
use crate::semantics::SemOp;
use crate::wasm::StraightSegment;
use egg::Rewrite;
use search::{solve_astar, solve_bfs, solve_greedy_inv};
use std::io::{self, Write};

#[derive(Clone, Copy, Debug, Default)]
pub enum SolverKind {
    Bfs,
    Greedy,
    #[default]
    Astar,
}

#[derive(Clone, Debug)]
pub struct SegmentOptResult {
    pub segment: StraightSegment,
    pub optimized: Option<Vec<SemOp>>,
    pub timed_out: bool,
    pub timeout_secs: u64,
}

impl SegmentOptResult {
    pub fn saved(&self) -> usize {
        let orig = self.segment.original_len();
        self.optimized
            .as_ref()
            .map(|o| orig.saturating_sub(o.len()))
            .unwrap_or(0)
    }
}

pub fn optimize_segment(
    segment: &StraightSegment,
    rules: &[Rewrite<ValueLang, ()>],
    cfg: &SearchConfig,
    solver: SolverKind,
) -> SegmentOptResult {
    let timeout_secs = segment_timeout_secs(segment, cfg.direct_timeout);
    let segment_cfg = cfg.for_segment(segment);
    if segment.ops.is_empty() {
        return SegmentOptResult {
            segment: segment.clone(),
            optimized: None,
            timed_out: false,
            timeout_secs,
        };
    }
    if !segment.init.validate_bounds(&segment.bounds) || !segment.fin.validate_bounds(&segment.bounds) {
        return SegmentOptResult {
            segment: segment.clone(),
            optimized: None,
            timed_out: false,
            timeout_secs,
        };
    }
    let result = match solver {
        SolverKind::Bfs => solve_bfs(segment, rules, &segment_cfg),
        SolverKind::Greedy => solve_greedy_inv(segment, rules, &segment_cfg),
        SolverKind::Astar => solve_astar(segment, rules, &segment_cfg),
    };
    SegmentOptResult {
        segment: segment.clone(),
        optimized: result.ops,
        timed_out: result.timed_out,
        timeout_secs,
    }
}

pub fn optimize_segments(
    segments: &[StraightSegment],
    rules: &[Rewrite<ValueLang, ()>],
    cfg: &SearchConfig,
    solver: SolverKind,
    jobs: usize,
) -> Vec<SegmentOptResult> {
    if jobs <= 1 {
        return segments
            .iter()
            .map(|segment| optimize_segment(segment, rules, cfg, solver))
            .collect();
    }
    crate::parallel::run_with_threads(jobs, || {
        use rayon::prelude::*;
        segments
            .par_iter()
            .map(|segment| optimize_segment(segment, rules, cfg, solver))
            .collect()
    })
}

fn default_timeout_label(cfg: &SearchConfig) -> String {
    if cfg.direct_timeout {
        format!("{DIRECT_TIMEOUT_SECS}s (direct)")
    } else {
        format!("{DEFAULT_TIMEOUT_BASE_SECS}s base (+10s per storage op)")
    }
}

pub fn print_segment_result(result: &SegmentOptResult) {
    let seg = &result.segment;
    print!(
        "func {} segment {} — {} instr",
        seg.func_index,
        seg.label(),
        seg.original_len()
    );
    match &result.optimized {
        Some(ops) if ops.len() < seg.original_len() => {
            println!(
                " -> {} (saved {}){}",
                ops.len(),
                result.saved(),
                if result.timed_out { " [timeout]" } else { "" },
            );
            println!("  in : {}", format_ops(&seg.ops));
            println!("  out: {}", format_ops(ops));
        }
        Some(_) => {
            println!(" (unchanged)");
        }
        None if result.timed_out => {
            println!(" (timeout)");
        }
        None => {
            println!(" (no shorter solution)");
        }
    }
}

/// Optimize segments, printing progress and flushing after each (sequential) or in batch (parallel).
pub fn optimize_and_print_segments(
    segments: &[StraightSegment],
    rules: &[Rewrite<ValueLang, ()>],
    cfg: &SearchConfig,
    solver: SolverKind,
    max_segment_instr: usize,
    jobs: usize,
) -> Vec<SegmentOptResult> {
    let segments = crate::wasm::split_segments(segments, max_segment_instr);
    let total = segments.len();
    let split_note = if max_segment_instr > 0 {
        format!(", max {max_segment_instr} instr/chunk")
    } else {
        String::new()
    };
    let jobs_note = if jobs > 1 {
        format!(", jobs={jobs}")
    } else {
        String::new()
    };
    println!(
        "=== Optimizing {total} segment(s) (solver: {solver:?}, timeout: {}{}{jobs_note}) ===\n",
        default_timeout_label(cfg),
        split_note
    );
    let _ = io::stdout().flush();

    if jobs <= 1 {
        let mut results = Vec::with_capacity(total);
        for (i, segment) in segments.iter().enumerate() {
            eprintln!(
                "[{}/{}] func {} segment {} — {} instr ...",
                i + 1,
                total,
                segment.func_index,
                segment.label(),
                segment.original_len(),
            );
            let _ = io::stderr().flush();

            let result = optimize_segment(segment, rules, cfg, solver);
            print_segment_result(&result);
            let _ = io::stdout().flush();
            results.push(result);
        }
        println!();
        return results;
    }

    eprintln!("optimizing {total} segment(s) with {jobs} threads …");
    let _ = io::stderr().flush();
    let results = optimize_segments(&segments, rules, cfg, solver, jobs);
    for result in &results {
        print_segment_result(result);
    }
    let _ = io::stdout().flush();
    println!();
    results
}

pub fn print_results(results: &[SegmentOptResult], solver: SolverKind) {
    println!("=== Wasm segment optimization (solver: {solver:?}) ===\n");
    for result in results {
        print_segment_result(result);
        println!();
    }
}

pub fn summarize(results: &[SegmentOptResult]) -> (usize, usize, usize) {
    let mut total_orig = 0usize;
    let mut total_opt = 0usize;
    let mut improved = 0usize;
    for r in results {
        total_orig += r.segment.original_len();
        if let Some(ops) = &r.optimized {
            total_opt += ops.len();
            if ops.len() < r.segment.original_len() {
                improved += 1;
            }
        } else {
            total_opt += r.segment.original_len();
        }
    }
    (total_orig, total_opt, improved)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::optimize::search::{validate_solution_ops, SearchConfig};
    use crate::semantics::SemOp;
    use crate::synthesis::{
        TEST_SYNTHESIS_AST_SIZE, load_or_synthesize_rules, synthesized_to_rewrites,
    };
    use crate::wasm::ops_respect_dependencies;
    use crate::wasm::parse_wasm_bytes;

    fn rules() -> Vec<Rewrite<ValueLang, ()>> {
        synthesized_to_rewrites(&load_or_synthesize_rules(TEST_SYNTHESIS_AST_SIZE, 10, 1))
    }

    #[test]
    fn optimizes_example_like_segment() {
        let wasm = wat::parse_str(
            r#"(module
                (func (param i32) (result i32)
                  local.get 0
                  i32.const 1
                  i32.add
                  local.tee 0
                  i32.const 2
                  i32.mul
                  local.get 0
                )
            )"#,
        )
        .unwrap();
        let info = parse_wasm_bytes(&wasm).unwrap();
        assert_eq!(info.segments.len(), 1);
        let results = optimize_segments(
            &info.segments,
            &rules(),
            &SearchConfig::default(),
            SolverKind::Astar,
            1,
        );
        let opt = results[0].optimized.as_ref().expect("optimized");
        assert!(opt.len() <= info.segments[0].original_len());
    }

    #[test]
    fn tee_fusion_segment_parses_eighteen_instructions() {
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
        let info = parse_wasm_bytes(&wasm).expect("parse");
        assert_eq!(info.segments.len(), 1);
        assert_eq!(info.segments[0].original_len(), 18);
    }

    #[test]
    fn optimizes_small_tee_fusion_segment() {
        let wasm = wat::parse_str(
            r#"(module
                (func (param i32 i32)
                  local.get 1
                  i32.const 1
                  i32.add
                  local.set 1
                  local.get 1
                  local.get 0
                  i32.lt_s
                )
            )"#,
        )
        .unwrap();
        let info = parse_wasm_bytes(&wasm).expect("parse");
        assert_eq!(info.segments.len(), 1);
        let orig_len = info.segments[0].original_len();
        assert_eq!(orig_len, 7);
        let results = optimize_segments(
            &info.segments,
            &rules(),
            &SearchConfig::default(),
            SolverKind::Astar,
            1,
        );
        let opt = results[0].optimized.as_ref().expect("optimized");
        assert!(
            opt.len() < orig_len,
            "expected shorter sequence, got: {}",
            format_ops(opt)
        );
    }

    #[test]
    fn default_segment_timeout_matches_superstack_base() {
        let wasm = wat::parse_str(
            r#"(module (func (param i32) local.get 0 i32.const 1 i32.add))"#,
        )
        .unwrap();
        let info = parse_wasm_bytes(&wasm).unwrap();
        assert_eq!(
            segment_timeout_secs(&info.segments[0], false),
            DEFAULT_TIMEOUT_BASE_SECS
        );
    }

    #[test]
    fn storage_ops_preserved_in_optimized_segment() {
        let wasm = wat::parse_str(
            r#"(module
                (memory 1)
                (func (param i32)
                  local.get 0
                  i32.const 1
                  i32.add
                  i32.const 0
                  i32.store
                )
            )"#,
        )
        .unwrap();
        let info = parse_wasm_bytes(&wasm).unwrap();
        assert_eq!(info.segments.len(), 1);
        let segment = &info.segments[0];
        assert!(segment.ops.iter().any(|op| op.is_storage_boundary()));
        let result = optimize_segment(segment, &rules(), &SearchConfig::default(), SolverKind::Astar);
        let opt = result.optimized.as_ref().expect("expected optimized ops");
        assert!(
            crate::wasm::storage_ops_preserved(&segment.ops, opt),
            "optimized: {}",
            format_ops(opt)
        );
        assert!(validate_solution_ops(opt, segment));
    }

    #[test]
    fn dependency_order_respected_in_solution() {
        let load = SemOp::I32Load {
            id: 0,
            mem: 0,
            offset: 0,
        };
        let store = SemOp::I32Store {
            id: 1,
            mem: 0,
            offset: 0,
        };
        let deps = vec![(0, 1)];
        let good = vec![load.clone(), SemOp::I32Add, store.clone()];
        let bad = vec![store.clone(), SemOp::I32Add, load.clone()];
        assert!(ops_respect_dependencies(&good, &deps));
        assert!(!ops_respect_dependencies(&bad, &deps));
    }
}
