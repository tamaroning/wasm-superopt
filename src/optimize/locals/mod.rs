//! Function-level local allocation via MaxSAT (instruction-count objective).

mod analysis;
mod apply;
mod encode;
mod statistics;

use crate::wasm::{WasmFunction, WasmModuleFunctions, parse_wasm_functions};
use analysis::{Analysis, basic_block_count};
use apply::{AppliedFunction, apply_allocation};
use encode::solve_allocation;
use std::io::{self, Write};
use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

pub use statistics::{LocalsFunctionCsvRow, locals_function_csv_rows, write_locals_function_csv};

pub const DEFAULT_LOCALS_TIMEOUT_MS: u32 = 30_000;
/// Default cap on functions to optimize (0 = all).
pub const DEFAULT_LOCALS_FUNCTION_LIMIT: usize = 0;

#[derive(Clone, Debug)]
pub struct OptLocalsConfig {
    pub timeout_ms: u32,
    /// Maximum number of functions to optimize (0 = no limit).
    pub max_functions: usize,
}

impl Default for OptLocalsConfig {
    fn default() -> Self {
        Self {
            timeout_ms: DEFAULT_LOCALS_TIMEOUT_MS,
            max_functions: DEFAULT_LOCALS_FUNCTION_LIMIT,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct OptLocalsStats {
    pub functions_in_module: usize,
    pub functions_processed: usize,
    pub functions_optimized: usize,
    pub functions_skipped: usize,
    pub instr_before: usize,
    pub instr_after: usize,
    pub local_slots_before: usize,
    pub local_slots_after: usize,
    pub copies_removed: usize,
    pub solver_time_secs: f64,
}

#[derive(Clone, Debug)]
pub struct FunctionOptResult {
    pub func_index: u32,
    pub skipped: bool,
    pub skip_reason: Option<String>,
    pub instr_before: usize,
    pub instr_after: usize,
    pub local_slots_before: usize,
    pub local_slots_after: usize,
    pub copies_removed: usize,
    pub webs: usize,
    pub interferes: usize,
    pub bb_count: usize,
    pub solver_time_secs: f64,
}

const ANSI_GREEN: &str = "\x1b[32m";
const ANSI_YELLOW: &str = "\x1b[33m";
const ANSI_WHITE: &str = "\x1b[37m";
const ANSI_RESET: &str = "\x1b[0m";

fn format_status_bracketed(label: &str) -> String {
    let color = match label {
        "improved" => ANSI_GREEN,
        "timeout" => ANSI_YELLOW,
        "unchanged" | "skipped" => ANSI_WHITE,
        _ => "",
    };
    format!("[{color}{label}{ANSI_RESET}]")
}

fn format_delta(saved: usize) -> String {
    if saved > 0 {
        format!(" {ANSI_GREEN}(-{saved}){ANSI_RESET}")
    } else {
        " (±0)".to_string()
    }
}

fn format_instr_metric(after: usize, saved: usize) -> String {
    format!("{after} instr{}", format_delta(saved))
}

fn format_locals_metric(after: usize, saved: usize) -> String {
    format!("{after} locals{}", format_delta(saved))
}

fn format_bb_metric(bb_count: usize) -> String {
    format!("{bb_count} BBs")
}

fn solver_h4_clauses(webs: usize, interferes: usize) -> usize {
    interferes * webs
}

fn format_problem_metrics(bb_count: usize, webs: usize, interferes: usize) -> String {
    format!(
        "{}, {} webs, {} interferes, ~{} H4",
        format_bb_metric(bb_count),
        webs,
        interferes,
        solver_h4_clauses(webs, interferes),
    )
}

impl FunctionOptResult {
    pub fn h4_clauses(&self) -> usize {
        solver_h4_clauses(self.webs, self.interferes)
    }

    pub fn status_label(&self) -> &'static str {
        if self.skipped {
            if self
                .skip_reason
                .as_deref()
                .is_some_and(|r| r.contains("timeout"))
            {
                "timeout"
            } else {
                "skipped"
            }
        } else {
            let instr_saved = self.instr_before.saturating_sub(self.instr_after);
            let local_saved = self.local_slots_before.saturating_sub(self.local_slots_after);
            if instr_saved > 0 || local_saved > 0 {
                "improved"
            } else {
                "unchanged"
            }
        }
    }

    /// One-line progress / result summary (optimized counts + green `(-N)` savings).
    pub fn progress_summary(&self) -> String {
        let problem = format_problem_metrics(self.bb_count, self.webs, self.interferes);
        if self.skipped {
            let reason = self.skip_reason.as_deref().unwrap_or("?");
            return format!(
                "{problem}, {reason} {} ({:.2}s)",
                format_status_bracketed(self.status_label()),
                self.solver_time_secs,
            );
        }
        let instr_saved = self.instr_before.saturating_sub(self.instr_after);
        let local_saved = self.local_slots_before.saturating_sub(self.local_slots_after);
        format!(
            "{problem}, {}, {} {} ({:.2}s)",
            format_instr_metric(self.instr_after, instr_saved),
            format_locals_metric(self.local_slots_after, local_saved),
            format_status_bracketed(self.status_label()),
            self.solver_time_secs,
        )
    }
}

pub fn optimize_module_functions(
    module: &WasmModuleFunctions,
    cfg: &OptLocalsConfig,
    jobs: usize,
) -> (Vec<FunctionOptResult>, OptLocalsStats) {
    let functions_in_module = module.functions.len();
    let to_process = match cfg.max_functions {
        0 => functions_in_module,
        n => functions_in_module.min(n),
    };

    let mut stats = OptLocalsStats {
        functions_in_module,
        functions_processed: to_process,
        ..Default::default()
    };

    if to_process == 0 {
        return (Vec::new(), stats);
    }

    let jobs_note = if jobs > 1 {
        format!(", jobs={jobs}")
    } else {
        String::new()
    };
    eprintln!(
        "=== Local allocation: optimizing {to_process} of {functions_in_module} function(s){jobs_note} ==="
    );
    let _ = io::stderr().flush();

    let functions: Vec<&WasmFunction> = module.functions.iter().take(to_process).collect();
    let results = if jobs <= 1 {
        optimize_functions_sequential(&functions, cfg, &mut stats)
    } else {
        optimize_functions_parallel(&functions, cfg, jobs, &mut stats)
    };

    (results, stats)
}

fn optimize_functions_sequential(
    functions: &[&WasmFunction],
    cfg: &OptLocalsConfig,
    stats: &mut OptLocalsStats,
) -> Vec<FunctionOptResult> {
    let total = functions.len();
    let mut results = Vec::with_capacity(total);
    for (i, func) in functions.iter().enumerate() {
        eprintln!(
            "[{}/{}] func {} — {} BBs, {} instr, {} locals ...",
            i + 1,
            total,
            func.func_index,
            basic_block_count(&func.instrs),
            func.instr_count(),
            func.local_types.len(),
        );
        let _ = io::stderr().flush();

        let result = optimize_function(func, cfg);
        eprintln!(
            "[{}/{}] func {} — {}",
            i + 1,
            total,
            result.func_index,
            result.progress_summary(),
        );
        let _ = io::stderr().flush();

        accumulate_result(stats, &result);
        results.push(result);
    }
    results
}

fn optimize_functions_parallel(
    functions: &[&WasmFunction],
    cfg: &OptLocalsConfig,
    jobs: usize,
    stats: &mut OptLocalsStats,
) -> Vec<FunctionOptResult> {
    let total = functions.len();
    let done = AtomicUsize::new(0);
    let cfg = cfg.clone();

    let mut results = crate::parallel::run_with_threads(jobs, || {
        use rayon::prelude::*;
        functions
            .par_iter()
            .map(|func| {
                let result = optimize_function(func, &cfg);
                let n = done.fetch_add(1, Ordering::Relaxed) + 1;
                let mut stderr = io::stderr().lock();
                let _ = writeln!(
                    stderr,
                    "[{}/{}] func {} — {}",
                    n,
                    total,
                    result.func_index,
                    result.progress_summary(),
                );
                let _ = stderr.flush();
                drop(stderr);
                result
            })
            .collect::<Vec<_>>()
    });

    results.sort_by_key(|r| r.func_index);
    for result in &results {
        accumulate_result(stats, result);
    }
    results
}

fn accumulate_result(stats: &mut OptLocalsStats, result: &FunctionOptResult) {
    stats.instr_before += result.instr_before;
    stats.instr_after += result.instr_after;
    stats.local_slots_before += result.local_slots_before;
    stats.local_slots_after += result.local_slots_after;
    stats.copies_removed += result.copies_removed;
    stats.solver_time_secs += result.solver_time_secs;
    if result.skipped {
        stats.functions_skipped += 1;
    } else if result.instr_after < result.instr_before
        || result.local_slots_after < result.local_slots_before
    {
        stats.functions_optimized += 1;
    }
}

pub fn optimize_wasm_file(
    path: &Path,
    cfg: &OptLocalsConfig,
    jobs: usize,
) -> Result<(WasmModuleFunctions, Vec<FunctionOptResult>, OptLocalsStats), String> {
    let module = parse_wasm_functions(path)?;
    let (results, stats) = optimize_module_functions(&module, cfg, jobs);
    Ok((module, results, stats))
}

fn optimize_function(func: &WasmFunction, cfg: &OptLocalsConfig) -> FunctionOptResult {
    let instr_before = func.instr_count();
    let local_slots_before = func.local_types.len();
    let bb_count = basic_block_count(&func.instrs);

    let analysis = match Analysis::build(func) {
        Ok(a) => a,
        Err(reason) => {
            return FunctionOptResult {
                func_index: func.func_index,
                skipped: true,
                skip_reason: Some(reason),
                instr_before,
                instr_after: instr_before,
                local_slots_before,
                local_slots_after: local_slots_before,
                copies_removed: 0,
                webs: 0,
                interferes: 0,
                bb_count,
                solver_time_secs: 0.0,
            };
        }
    };

    let t0 = Instant::now();
    let allocation = match solve_allocation(func, &analysis, cfg.timeout_ms) {
        Ok(a) => a,
        Err(reason) => {
            return FunctionOptResult {
                func_index: func.func_index,
                skipped: true,
                skip_reason: Some(reason),
                instr_before,
                instr_after: instr_before,
                local_slots_before,
                local_slots_after: local_slots_before,
                copies_removed: 0,
                webs: analysis.webs.len(),
                interferes: analysis.interferes.len(),
                bb_count,
                solver_time_secs: t0.elapsed().as_secs_f64(),
            };
        }
    };
    let solver_time_secs = t0.elapsed().as_secs_f64();

    let applied = apply_allocation(func, &analysis, &allocation);

    FunctionOptResult {
        func_index: func.func_index,
        skipped: false,
        skip_reason: None,
        instr_before,
        instr_after: applied.instr_count(),
        local_slots_before,
        local_slots_after: applied.local_slots(),
        copies_removed: applied.copies_removed,
        webs: analysis.webs.len(),
        interferes: analysis.interferes.len(),
        bb_count,
        solver_time_secs,
    }
}

pub fn print_locals_summary(
    path: &Path,
    results: &[FunctionOptResult],
    stats: &OptLocalsStats,
    max_functions: usize,
) {
    println!("=== Local allocation (--opt-locals): {} ===", path.display());
    if stats.functions_processed < stats.functions_in_module {
        println!(
            "  processed: {} of {} functions (--locals-limit {})",
            stats.functions_processed,
            stats.functions_in_module,
            if max_functions == 0 {
                "all".to_string()
            } else {
                max_functions.to_string()
            }
        );
    }
    println!(
        "  functions: {} processed, {} improved, {} skipped",
        stats.functions_processed, stats.functions_optimized, stats.functions_skipped
    );
    let instr_saved = stats.instr_before.saturating_sub(stats.instr_after);
    let local_saved = stats.local_slots_before.saturating_sub(stats.local_slots_after);
    println!(
        "  instructions: {}{}",
        stats.instr_after,
        format_delta(instr_saved)
    );
    println!(
        "  local slots: {}{}",
        stats.local_slots_after,
        format_delta(local_saved)
    );
    println!(
        "  copies removed: {}, solver time: {:.2}s",
        stats.copies_removed, stats.solver_time_secs
    );
    println!();

    for r in results {
        let instr_saved = r.instr_before.saturating_sub(r.instr_after);
        let local_saved = r.local_slots_before.saturating_sub(r.local_slots_after);
        if r.skipped {
            println!(
                "func {}: {}, {} {}",
                r.func_index,
                format_problem_metrics(r.bb_count, r.webs, r.interferes),
                r.skip_reason.as_deref().unwrap_or("?"),
                format_status_bracketed(r.status_label()),
            );
            continue;
        }
        println!(
            "func {}: {}, {}, {}, {} copies, {:.2}s {}",
            r.func_index,
            format_problem_metrics(r.bb_count, r.webs, r.interferes),
            format_instr_metric(r.instr_after, instr_saved),
            format_locals_metric(r.local_slots_after, local_saved),
            r.copies_removed,
            r.solver_time_secs,
            format_status_bracketed(r.status_label()),
        );
    }
    println!();
}

pub fn print_locals_function_detail(
    func: &WasmFunction,
    analysis: &Analysis,
    applied: &AppliedFunction,
) {
    println!("func {} detail:", func.func_index);
    println!("  webs: {}", analysis.webs.len());
    for (i, web) in analysis.webs.iter().enumerate() {
        println!(
            "    web {i}: ty={:?} param={} defs={} uses={}",
            web.ty,
            web.param_index.is_some(),
            web.def_sites.len(),
            web.use_sites.len()
        );
    }
    println!("  copies:");
    for c in &analysis.copies {
        println!(
            "    {:?} web{} -> web{} at {} weight {}",
            c.kind, c.src.0, c.dst.0, c.at, c.instr_saved
        );
    }
    println!(
        "  result: {} -> {} instr, {} -> {} locals, {} copies removed",
        func.instr_count(),
        applied.instr_count(),
        func.local_types.len(),
        applied.local_slots(),
        applied.copies_removed
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wasm::parse_wasm_functions_bytes;

    #[test]
    fn removes_self_copy_get_set() {
        let wasm = wat::parse_str(
            r#"(module
                (func (param i32) (local i32)
                  local.get 0
                  local.set 1
                  local.get 1
                  i32.const 0
                  i32.add
                )
            )"#,
        )
        .unwrap();
        let module = parse_wasm_functions_bytes(&wasm).unwrap();
        let (results, stats) = optimize_module_functions(&module, &OptLocalsConfig::default(), 1);
        assert_eq!(results.len(), 1);
        assert!(!results[0].skipped);
        assert_eq!(stats.instr_before, 6);
        assert_eq!(stats.instr_after, 4);
        assert_eq!(stats.copies_removed, 1);
    }

    #[test]
    fn mux1_1_module_parses() {
        let path = std::path::Path::new("benchmarks/wsouper/mux1_1.wasm");
        if !path.exists() {
            return;
        }
        let module = crate::wasm::parse_wasm_functions(path).unwrap();
        assert!(!module.functions.is_empty());
    }
}
