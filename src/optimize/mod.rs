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
    let bounds = &segment.bounds;
    let result = match solver {
        SolverKind::Bfs => solve_bfs(&segment.init, &segment.fin, bounds, rules, &segment_cfg),
        SolverKind::Greedy => solve_greedy_inv(&segment.init, &segment.fin, bounds, rules, &segment_cfg),
        SolverKind::Astar => solve_astar(&segment.init, &segment.fin, bounds, rules, &segment_cfg),
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
) -> Vec<SegmentOptResult> {
    segments
        .iter()
        .map(|segment| optimize_segment(segment, rules, cfg, solver))
        .collect()
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
    print!("func {} segment {} — {} instr", seg.func_index, seg.segment_index, seg.original_len());
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

/// Optimize segments one-by-one, printing progress and flushing after each.
pub fn optimize_and_print_segments(
    segments: &[StraightSegment],
    rules: &[Rewrite<ValueLang, ()>],
    cfg: &SearchConfig,
    solver: SolverKind,
) -> Vec<SegmentOptResult> {
    let total = segments.len();
    println!(
        "=== Optimizing {total} segment(s) (solver: {solver:?}, timeout: {}) ===\n",
        default_timeout_label(cfg)
    );
    let _ = io::stdout().flush();

    let mut results = Vec::with_capacity(total);
    for (i, segment) in segments.iter().enumerate() {
        eprintln!(
            "[{}/{}] func {} segment {} — {} instr ...",
            i + 1,
            total,
            segment.func_index,
            segment.segment_index,
            segment.original_len(),
        );
        let _ = io::stderr().flush();

        let result = optimize_segment(segment, rules, cfg, solver);
        print_segment_result(&result);
        let _ = io::stdout().flush();
        results.push(result);
    }
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
    use crate::synthesis::{
        TEST_SYNTHESIS_AST_SIZE, load_or_synthesize_rules, synthesized_to_rewrites,
    };
    use crate::wasm::parse_wasm_bytes;

    fn rules() -> Vec<Rewrite<ValueLang, ()>> {
        synthesized_to_rewrites(&load_or_synthesize_rules(TEST_SYNTHESIS_AST_SIZE, 10))
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
}
