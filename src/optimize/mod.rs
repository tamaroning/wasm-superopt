//! Phase 2: backward shortest-path search over straight-line Wasm segments (idea.md §2–§8).

mod canon;
mod forward;
mod goal;
mod heuristic;
mod inverse;
mod search;

pub use forward::SymMachine;
pub use goal::MachineState;
pub use search::{DEFAULT_MAX_DEPTH, SearchConfig, format_ops};

use crate::lang::ValueLang;
use crate::semantics::SemOp;
use crate::wasm::StraightSegment;
use egg::Rewrite;
use search::{solve_astar, solve_bfs, solve_greedy_inv};

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
) -> Option<Vec<SemOp>> {
    if segment.ops.is_empty() {
        return None;
    }
    if !segment.init.validate_bounds() || !segment.fin.validate_bounds() {
        return None;
    }
    match solver {
        SolverKind::Bfs => solve_bfs(&segment.init, &segment.fin, rules, cfg),
        SolverKind::Greedy => solve_greedy_inv(&segment.init, &segment.fin, rules, cfg),
        SolverKind::Astar => solve_astar(&segment.init, &segment.fin, rules, cfg),
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
        .map(|segment| SegmentOptResult {
            optimized: optimize_segment(segment, rules, cfg, solver),
            segment: segment.clone(),
        })
        .collect()
}

pub fn print_results(results: &[SegmentOptResult], solver: SolverKind) {
    println!("=== Wasm segment optimization (solver: {solver:?}) ===\n");
    for result in results {
        let seg = &result.segment;
        println!(
            "func {} segment {} — original {} instr",
            seg.func_index,
            seg.segment_index,
            seg.original_len()
        );
        println!("  in : {}", format_ops(&seg.ops));
        match &result.optimized {
            Some(ops) => {
                println!("  out: {}", format_ops(ops));
                println!(
                    "  len: {} -> {} (saved {})",
                    seg.original_len(),
                    ops.len(),
                    result.saved()
                );
            }
            None => println!("  out: (no shorter solution within window)"),
        }
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

/// Parsed `examples/example.wat` / `example-opt.wat` for unit tests (idea.md §12).
#[cfg(test)]
pub(crate) mod fixtures {
    use super::MachineState;
    use crate::semantics::SemOp;
    use crate::wasm::{StraightSegment, parse_wasm_bytes};
    use std::sync::OnceLock;

    const BLOATED_WAT: &str = include_str!("../../examples/example.wat");
    const OPT_WAT: &str = include_str!("../../examples/example-opt.wat");

    fn bloated_segment() -> &'static StraightSegment {
        static SEG: OnceLock<StraightSegment> = OnceLock::new();
        SEG.get_or_init(|| {
            let wasm = wat::parse_str(BLOATED_WAT).expect("examples/example.wat must parse");
            let info = parse_wasm_bytes(&wasm).expect("examples/example.wat must yield wasm");
            assert_eq!(info.segments.len(), 1);
            info.segments.into_iter().next().unwrap()
        })
    }

    fn canonical_fin() -> &'static MachineState {
        static FIN: OnceLock<MachineState> = OnceLock::new();
        FIN.get_or_init(|| {
            let wasm = wat::parse_str(OPT_WAT).expect("examples/example-opt.wat must parse");
            let info = parse_wasm_bytes(&wasm).expect("examples/example-opt.wat must yield wasm");
            assert_eq!(info.segments.len(), 1);
            info.segments[0].fin.clone()
        })
    }

    pub fn init() -> MachineState {
        bloated_segment().init.clone()
    }

    pub fn fin() -> MachineState {
        canonical_fin().clone()
    }

    pub fn bloated_ops() -> Vec<SemOp> {
        bloated_segment().ops.clone()
    }
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
}
