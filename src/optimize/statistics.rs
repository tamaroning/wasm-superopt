//! SuperStack-compatible `statistics.csv` rows for benchmark analysis.

use super::SegmentOptResult;
use super::canon::Canonizer;
use super::search::solution_valid;
use crate::lang::ValueLang;
use crate::wasm::StraightSegment;
use crate::wasm::format_ops_superstack_csv;
use serde::Serialize;
use std::io;
use std::path::Path;

/// One row of SuperStack-compatible benchmark statistics (`statistics.csv`).
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct StatisticsRow {
    /// Block identifier (`function_{i}_block_{j}` or `function_{i}_block_{j}_{part}` when split).
    pub block_id: String,
    /// Original instruction sequence before optimization (space-separated).
    pub previous_solution: String,
    /// Per-segment solver timeout in seconds (`10 * (1 + storage)` or 300 with `--direct-timeout`).
    pub timeout: u64,
    /// Wall-clock time spent in A* search for this block, in seconds.
    pub solver_time_in_sec: f64,
    /// Search result label: `optimal`, `non_optimal`, `timeout`, or `no_solution`.
    pub outcome: String,
    /// Instruction count of the input block (same as `initial_length` in SuperStack).
    pub initial_n_instrs: usize,
    /// Whether the search produced a candidate optimized sequence.
    pub model_found: bool,
    /// Whether the result is treated as proven optimal (no timeout, solution found).
    pub shown_optimal: bool,
    /// Length of the original block in instructions.
    pub initial_length: usize,
    /// Best bound used during search (optimized length if found, else original length).
    pub used_bound: usize,
    /// Instructions saved: `initial_length - optimized_length`.
    pub saved_length: usize,
    /// Whether the optimized sequence passes semantic validation (`solution_valid`).
    pub checker: bool,
    /// Which solution was kept: `astar`, `original`, or SuperStack-style tags when applicable.
    pub final_solution_tag: String,
    /// Optimized instruction sequence (space-separated); empty if no model was found.
    pub solution_found: String,
    /// Instruction count of the optimized sequence.
    pub optimized_n_instrs: usize,
    /// Length of the optimized block in instructions (same as `optimized_n_instrs`).
    pub optimized_length: usize,
    /// Rewrites/rules applied during optimization (empty in egraph; reserved for SuperStack parity).
    pub rules: String,
}

#[derive(Serialize)]
struct StatisticsCsvRecord {
    #[serde(rename = "")]
    index: usize,
    block_id: String,
    previous_solution: String,
    timeout: u64,
    solver_time_in_sec: f64,
    outcome: String,
    initial_n_instrs: usize,
    model_found: bool,
    shown_optimal: bool,
    initial_length: usize,
    used_bound: usize,
    saved_length: usize,
    checker: bool,
    final_solution_tag: String,
    solution_found: String,
    optimized_n_instrs: usize,
    optimized_length: usize,
    rules: String,
}

impl StatisticsCsvRecord {
    fn new(index: usize, row: &StatisticsRow) -> Self {
        Self {
            index,
            block_id: row.block_id.clone(),
            previous_solution: row.previous_solution.clone(),
            timeout: row.timeout,
            solver_time_in_sec: row.solver_time_in_sec,
            outcome: row.outcome.clone(),
            initial_n_instrs: row.initial_n_instrs,
            model_found: row.model_found,
            shown_optimal: row.shown_optimal,
            initial_length: row.initial_length,
            used_bound: row.used_bound,
            saved_length: row.saved_length,
            checker: row.checker,
            final_solution_tag: row.final_solution_tag.clone(),
            solution_found: row.solution_found.clone(),
            optimized_n_instrs: row.optimized_n_instrs,
            optimized_length: row.optimized_length,
            rules: row.rules.clone(),
        }
    }
}

pub fn block_id(segment: &StraightSegment) -> String {
    let mut id = format!(
        "function_{}_block_{}",
        segment.func_index, segment.segment_index
    );
    if let Some((part, total)) = segment.split_part {
        if total > 1 {
            id.push('_');
            id.push_str(&part.to_string());
        }
    }
    id
}

fn classify_outcome(
    result: &SegmentOptResult,
    initial_len: usize,
    checker: bool,
) -> (String, bool, bool, String) {
    let Some(ops) = &result.optimized else {
        return (
            if result.timed_out {
                "timeout".to_string()
            } else {
                "no_solution".to_string()
            },
            false,
            false,
            "original".to_string(),
        );
    };

    let opt_len = ops.len();
    let improved = opt_len < initial_len;

    if result.timed_out {
        return (
            "non_optimal".to_string(),
            true,
            false,
            if improved && checker {
                "astar".to_string()
            } else {
                "original".to_string()
            },
        );
    }

    if improved && checker {
        return ("optimal".to_string(), true, true, "astar".to_string());
    }

    (
        "optimal".to_string(),
        true,
        true,
        if checker {
            "original".to_string()
        } else {
            "astar".to_string()
        },
    )
}

pub fn statistics_row(result: &SegmentOptResult, canon: &mut Canonizer) -> StatisticsRow {
    let segment = &result.segment;
    let initial_len = segment.original_len();
    let timeout = result.timeout_secs;

    let checker = result
        .optimized
        .as_ref()
        .is_some_and(|ops| solution_valid(ops, segment, canon));

    let (outcome, model_found, shown_optimal, final_solution_tag) =
        classify_outcome(result, initial_len, checker);

    let (solution_found, optimized_n_instrs, optimized_length, used_bound, saved_length) =
        if let Some(ops) = &result.optimized {
            let opt_len = ops.len();
            let saved = if checker {
                initial_len.saturating_sub(opt_len)
            } else {
                0
            };
            (
                format_ops_superstack_csv(ops, &result.segment.disasm_by_id),
                if checker { opt_len } else { initial_len },
                if checker { opt_len } else { initial_len },
                if checker { opt_len } else { initial_len },
                saved,
            )
        } else {
            (String::new(), 0, 0, initial_len, 0)
        };

    StatisticsRow {
        block_id: block_id(segment),
        previous_solution: format_ops_superstack_csv(&segment.ops, &segment.disasm_by_id),
        timeout,
        solver_time_in_sec: (result.solver_time_secs * 1000.0).round() / 1000.0,
        outcome,
        initial_n_instrs: initial_len,
        model_found,
        shown_optimal,
        initial_length: initial_len,
        used_bound,
        saved_length,
        checker,
        final_solution_tag,
        solution_found,
        optimized_n_instrs,
        optimized_length,
        rules: String::new(),
    }
}

pub fn statistics_rows(
    results: &[SegmentOptResult],
    rules: &[egg::Rewrite<ValueLang, ()>],
) -> Vec<StatisticsRow> {
    let mut canon = Canonizer::new(rules.to_vec());
    results
        .iter()
        .map(|r| statistics_row(r, &mut canon))
        .collect()
}

pub fn write_statistics_csv(path: &Path, rows: &[StatisticsRow]) -> io::Result<()> {
    let file = std::fs::File::create(path)?;
    let mut writer = csv::Writer::from_writer(file);
    for (index, row) in rows.iter().enumerate() {
        writer.serialize(StatisticsCsvRecord::new(index, row))?;
    }
    writer.flush()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::optimize::fixtures::{fin, init};
    use crate::semantics::SemOp;
    use crate::wasm::{SegmentBounds, StraightSegment};

    fn empty_segment(ops: Vec<SemOp>) -> StraightSegment {
        StraightSegment {
            func_index: 0,
            num_params: 1,
            segment_index: 0,
            split_part: None,
            ops,
            init: init(),
            fin: fin(),
            bounds: SegmentBounds::new(1, 4),
            opaque_meta: vec![],
            dependencies: vec![],
            disasm_by_id: Default::default(),
        }
    }

    #[test]
    fn block_id_matches_superstack_naming() {
        let seg = empty_segment(vec![]);
        assert_eq!(block_id(&seg), "function_0_block_0");
    }

    #[test]
    fn csv_header_matches_superstack() {
        use crate::synthesis::test_synthesis_rewrites;
        let mut canon = Canonizer::new(test_synthesis_rewrites());
        let rows = vec![statistics_row(
            &SegmentOptResult {
                segment: empty_segment(vec![SemOp::I32Add, SemOp::I32Mul]),
                optimized: Some(vec![SemOp::I32Add]),
                timed_out: false,
                solver_time_secs: 0.059,
                timeout_secs: 10,
            },
            &mut canon,
        )];
        let path = std::env::temp_dir().join("ewasm-statistics-test.csv");
        write_statistics_csv(&path, &rows).unwrap();
        let contents = std::fs::read_to_string(&path).unwrap();
        let header = contents.lines().next().unwrap();
        assert!(header.starts_with(",block_id,previous_solution,timeout"));
        assert!(contents.contains("function_0_block_0"));
        let _ = std::fs::remove_file(path);
    }
}
