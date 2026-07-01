//! Loop/jump-free WebAssembly basic blocks → backward goal search + e-graph rules.


mod al;
mod lang;
mod optimize;
mod parallel;
mod ruler;
mod semantics;
mod sym;
mod synthesis;
mod value;
mod wasm;

use al::DEFAULT_RANDOM_TESTS;
use clap::Parser;
use std::io::{self, Write};
use synthesis::{load_or_synthesize_rules, synthesized_to_rewrites};
use wasm::{materialize_segments, parse_wasm_file, print_input_summary, split_raw_segments};

#[derive(Parser, Debug)]
#[command(
    name = "ewasm",
    about = "Optimize loop/jump-free Wasm segments via backward goal search"
)]
struct Cli {
    /// Wasm module to optimize.
    #[arg(value_name = "WASM", required_unless_present_any = ["synthesize_only", "print_semantics"])]
    input: Option<std::path::PathBuf>,

    /// Only run synthesis (writes rules-ast{N}.cache).
    #[arg(long)]
    synthesize_only: bool,

    /// Print the centralized Wasm instruction semantics table.
    #[arg(long)]
    print_semantics: bool,

    /// Maximum AST node count for synthesis (1–8; 3 ≈ old 2-instruction sequences).
    #[arg(long, default_value_t = 3)]
    max_ast_size: usize,

    /// Maximum input arity for rule signatures (1–3).
    #[arg(long, default_value_t = 3)]
    max_arity: usize,

    /// Randomized concrete tests per candidate before Z3 (0 skips the fast filter).
    #[arg(long, default_value_t = DEFAULT_RANDOM_TESTS)]
    random_tests: usize,

    /// Only list extracted segments without running the optimizer.
    #[arg(long)]
    segments_only: bool,

    /// Maximum peel depth (instruction window) for backward search.
    #[arg(long, default_value_t = optimize::DEFAULT_MAX_DEPTH)]
    window: usize,

    /// Use 300s timeout per segment (SuperStack `-w` / DIRECT_TIMEOUT).
    #[arg(long, short = 'w')]
    direct_timeout: bool,

    /// Fixed per-segment solver timeout in seconds (overrides storage-based default and `-w`).
    #[arg(long, value_name = "SECS")]
    segment_timeout: Option<u64>,

    /// Split segments longer than N instructions (0 = no split; default 10).
    #[arg(long, default_value_t = wasm::DEFAULT_MAX_SEGMENT_INSTR)]
    split: usize,

    /// Dump A* exploration DAG as Graphviz DOT to this path.
    #[arg(long, value_name = "PATH")]
    dump_search: Option<std::path::PathBuf>,

    /// Write SuperStack-compatible statistics CSV to this path.
    #[arg(long, short = 'c', value_name = "PATH")]
    csv: Option<std::path::PathBuf>,

    /// Number of parallel jobs for rule synthesis and segment optimization.
    #[arg(short = 'j', long = "jobs", default_value_t = 1)]
    jobs: usize,

    /// Solver backend: `astar` (backward A*) or `sat` (descending Pure-SAT).
    #[arg(long, value_enum, default_value_t = SolverArg::Sat)]
    solver: SolverArg,

    /// Classify SAT failure modes for blocks where SuperStack improved but ewasm did not
    /// (reads `combined_blocks.csv` from wasm-bench; requires WASM input for segment lookup).
    #[arg(long, value_name = "CSV", conflicts_with_all = ["synthesize_only", "segments_only", "print_semantics"])]
    classify_sat_gaps: Option<std::path::PathBuf>,

    /// Print CNF scale / timing profile for the given block id(s) (`function_N_block_M[_part]`).
    #[arg(
        long = "sat-profile",
        value_name = "BLOCK_ID",
        num_args = 1..,
        conflicts_with_all = ["synthesize_only", "segments_only", "print_semantics", "classify_sat_gaps"]
    )]
    sat_profile: Vec<String>,
}

#[derive(clap::ValueEnum, Clone, Copy, Debug)]
enum SolverArg {
    Astar,
    Sat,
}

impl From<SolverArg> for optimize::Backend {
    fn from(s: SolverArg) -> Self {
        match s {
            SolverArg::Astar => optimize::Backend::Astar,
            SolverArg::Sat => optimize::Backend::Sat,
        }
    }
}

fn main() {
    let cli = Cli::parse();

    if cli.print_semantics {
        semantics::print_semantics_table();
        if cli.input.is_none() {
            return;
        }
    }

    if cli.synthesize_only {
        let max_ast = cli.max_ast_size.clamp(1, 8);
        let max_arity = cli.max_arity.clamp(1, 3);
        load_or_synthesize_rules(max_ast, max_arity, cli.random_tests, cli.jobs);
        return;
    }

    let path = cli.input.clone().expect("WASM path required");

    if let Some(csv_path) = &cli.classify_sat_gaps {
        run_classify_sat_gaps(&path, csv_path, &cli);
        return;
    }

    if !cli.sat_profile.is_empty() {
        run_sat_profile(&path, &cli);
        return;
    }

    let info = parse_wasm_file(&path).unwrap_or_else(|e| {
        eprintln!("error parsing {}: {e}", path.display());
        std::process::exit(1);
    });
    print_input_summary(&path, &info);
    for warning in &info.warnings {
        eprintln!("warning: {warning}");
    }
    let _ = io::stdout().flush();

    if cli.segments_only {
        use optimize::format_ops;
        for seg in &info.segments {
            println!(
                "func {} segment {} ({} instr): {}",
                seg.func_index,
                seg.segment_index,
                seg.original_len(),
                format_ops(&seg.ops)
            );
        }
        let _ = io::stdout().flush();
        return;
    }

    let max_ast = cli.max_ast_size.clamp(1, 8);
    let max_arity = cli.max_arity.clamp(1, 3);
    let syn = load_or_synthesize_rules(max_ast, max_arity, cli.random_tests, cli.jobs);
    let rules = synthesized_to_rewrites(&syn);

    let raw = split_raw_segments(&info.segments, cli.split);
    eprintln!("materializing {} chunk(s) …", raw.len());
    let _ = io::stderr().flush();
    let segments = materialize_segments(&raw, cli.jobs);
    eprintln!("materialized {} segment(s)", segments.len());
    let _ = io::stderr().flush();

    let cfg = search_config_from_cli(&cli);
    let results = optimize::optimize_and_print_segments(
        &segments,
        &rules,
        &cfg,
        0,
        cli.jobs,
        cli.dump_search.as_deref(),
    );
    let (orig, opt, improved) = optimize::summarize(&results);
    println!(
        "Total: {orig} -> {opt} instructions across {} segment(s) ({} improved)",
        results.len(),
        improved
    );
    if let Some(csv_path) = &cli.csv {
        let rows = optimize::statistics_rows(&results, &rules);
        optimize::write_statistics_csv(csv_path, &rows).unwrap_or_else(|e| {
            eprintln!("error writing {}: {e}", csv_path.display());
            std::process::exit(1);
        });
        eprintln!("wrote statistics to {}", csv_path.display());
    }
    let _ = io::stdout().flush();
}

fn search_config_from_cli(cli: &Cli) -> optimize::SearchConfig {
    optimize::SearchConfig {
        max_depth: cli.window,
        timeout_secs: None,
        direct_timeout: cli.direct_timeout && cli.segment_timeout.is_none(),
        fixed_segment_timeout: cli.segment_timeout,
        backend: cli.solver.into(),
        max_sat_len: optimize::max_sat_len_for_split(cli.split),
    }
}

fn run_sat_profile(path: &std::path::Path, cli: &Cli) {
    use optimize::{block_id, profile_sat};
    use std::collections::HashMap;
    use wasm::{materialize_segments, split_raw_segments};

    let info = parse_wasm_file(path).unwrap_or_else(|e| {
        eprintln!("error parsing {}: {e}", path.display());
        std::process::exit(1);
    });
    let max_ast = cli.max_ast_size.clamp(1, 8);
    let max_arity = cli.max_arity.clamp(1, 3);
    let syn = load_or_synthesize_rules(max_ast, max_arity, cli.random_tests, cli.jobs);
    let rules = synthesized_to_rewrites(&syn);

    let raw = split_raw_segments(&info.segments, cli.split);
    let segments = materialize_segments(&raw, cli.jobs);
    let by_id: HashMap<String, _> = segments.iter().map(|s| (block_id(s), s)).collect();

    let cfg = search_config_from_cli(cli);

    for want in &cli.sat_profile {
        let Some(seg) = by_id.get(want) else {
            eprintln!("block not found: {want} (split={})", cli.split);
            continue;
        };
        let seg_cfg = cfg.for_segment(seg);
        match profile_sat(seg, &rules, &seg_cfg) {
            Ok(p) => p.print(want),
            Err(stage) => eprintln!("profile failed at {stage}: {want}"),
        }
    }
}

fn run_classify_sat_gaps(path: &std::path::Path, csv_path: &std::path::Path, cli: &Cli) {
    use optimize::{
        classify_sat_gaps_parallel, print_gap_summary, problem_blocks_from_csv,
    };
    use wasm::{materialize_segments, split_raw_segments};

    let info = parse_wasm_file(path).unwrap_or_else(|e| {
        eprintln!("error parsing {}: {e}", path.display());
        std::process::exit(1);
    });
    let raw = split_raw_segments(&info.segments, cli.split);
    let segments = materialize_segments(&raw, cli.jobs);
    let problem_ids = problem_blocks_from_csv(csv_path).unwrap_or_else(|e| {
        eprintln!("error reading {}: {e}", csv_path.display());
        std::process::exit(1);
    });
    eprintln!(
        "Classifying {} gap block(s) from {} ({} segments, split={}, jobs={})",
        problem_ids.len(),
        csv_path.display(),
        segments.len(),
        cli.split,
        cli.jobs
    );

    let max_ast = cli.max_ast_size.clamp(1, 8);
    let max_arity = cli.max_arity.clamp(1, 3);
    let syn = load_or_synthesize_rules(max_ast, max_arity, cli.random_tests, cli.jobs);
    let rules = synthesized_to_rewrites(&syn);

    let cfg = search_config_from_cli(cli);

    let rows = classify_sat_gaps_parallel(&segments, &problem_ids, &rules, &cfg, cli.jobs);
    print_gap_summary(&rows);

    let missing = problem_ids.len().saturating_sub(rows.len());
    if missing > 0 {
        eprintln!("warning: {missing} problem block id(s) not found in WASM segments");
    }
}
