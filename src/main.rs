//! Loop/jump-free WebAssembly basic blocks → backward goal search + e-graph rules.

mod al;
mod lang;
mod sym;
mod optimize;
mod semantics;
mod synthesis;
mod value;
mod wasm;

use al::DEFAULT_RANDOM_TESTS;
use clap::{Parser, ValueEnum};
use std::io::{self, Write};
use synthesis::{
    load_or_synthesize_rules, print_synthesized, print_synthesized_json, synthesized_to_rewrites,
};
use wasm::{parse_wasm_file, print_input_summary};

#[derive(Parser, Debug)]
#[command(
    name = "egraph",
    about = "Optimize loop/jump-free Wasm segments via backward goal search"
)]
struct Cli {
    /// Wasm module to optimize.
    #[arg(value_name = "WASM", required_unless_present_any = ["synthesize_only", "print_semantics"])]
    input: Option<std::path::PathBuf>,

    /// Only run synthesis (print verified rules as JSON).
    #[arg(long)]
    synthesize_only: bool,

    /// Print the centralized Wasm instruction semantics table.
    #[arg(long)]
    print_semantics: bool,

    /// Maximum AST node count for synthesis (1–8; 3 ≈ old 2-instruction sequences).
    #[arg(long, default_value_t = 3)]
    max_ast_size: usize,

    /// Randomized concrete tests per candidate before Z3 (0 skips the fast filter).
    #[arg(long, default_value_t = DEFAULT_RANDOM_TESTS)]
    random_tests: usize,

    /// Search strategy for backward search.
    #[arg(long, value_enum, default_value_t = SolverKind::Astar)]
    solver: SolverKind,

    /// Only list extracted segments without running the optimizer.
    #[arg(long)]
    segments_only: bool,

    /// Maximum peel depth (instruction window) for backward search.
    #[arg(long, default_value_t = optimize::DEFAULT_MAX_DEPTH)]
    window: usize,

    /// Use 300s timeout per segment (SuperStack `-w` / DIRECT_TIMEOUT).
    #[arg(long, short = 'w')]
    direct_timeout: bool,
}

impl From<SolverKind> for optimize::SolverKind {
    fn from(k: SolverKind) -> Self {
        match k {
            SolverKind::Bfs => optimize::SolverKind::Bfs,
            SolverKind::Greedy => optimize::SolverKind::Greedy,
            SolverKind::Astar => optimize::SolverKind::Astar,
        }
    }
}

#[derive(Clone, Copy, Debug, Default, ValueEnum)]
enum SolverKind {
    /// Breadth-first search with memoization (shortest path).
    Bfs,
    /// Greedy inverse peel (fast but may fail to find a solution).
    Greedy,
    /// A* with admissible heuristic, pruned by a greedy upper bound.
    #[default]
    Astar,
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
        let syn = load_or_synthesize_rules(max_ast, cli.random_tests);
        print_synthesized_json(&syn, cli.random_tests);
        return;
    }

    let path = cli.input.clone().expect("WASM path required");

    let info = parse_wasm_file(&path).unwrap_or_else(|e| {
        eprintln!("error parsing {}: {e}", path.display());
        std::process::exit(1);
    });
    print_input_summary(&path, &info);
    for warning in &info.warnings {
        eprintln!("warning: {warning}");
    }
    let _ = io::stdout().flush();

    let max_ast = cli.max_ast_size.clamp(1, 8);
    let syn = load_or_synthesize_rules(max_ast, cli.random_tests);
    if !cli.segments_only {
        print_synthesized(&syn, cli.random_tests);
        let _ = io::stdout().flush();
    }
    let rules = synthesized_to_rewrites(&syn);

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

    let cfg = optimize::SearchConfig {
        max_depth: cli.window,
        timeout_secs: None,
        direct_timeout: cli.direct_timeout,
    };
    let results = optimize::optimize_and_print_segments(
        &info.segments,
        &rules,
        &cfg,
        cli.solver.into(),
    );
    let (orig, opt, improved) = optimize::summarize(&results);
    println!(
        "Total: {orig} -> {opt} instructions across {} segment(s) ({} improved)",
        results.len(),
        improved
    );
    let _ = io::stdout().flush();
}
