//! Loop/jump-free WebAssembly basic blocks → backward goal search + e-graph rules.

mod canon;
mod forward;
mod goal;
mod heuristic;
mod inverse;
mod lang;
mod optimize;
mod search;
mod sema;
mod semantics;
mod stack;
mod synthesis;
mod value;
mod wasm;

use clap::{Parser, ValueEnum};
use lang::ValueLang;
use semantics::DEFAULT_RANDOM_TESTS;
use synthesis::{
    load_or_synthesize_rules, print_synthesized, print_synthesized_json, synthesized_to_rewrites,
};

#[derive(Parser, Debug)]
#[command(name = "egraph", about = "Optimize loop/jump-free Wasm segments via backward goal search")]
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

    /// Maximum instruction-sequence length for synthesis (1–4).
    #[arg(long, default_value_t = 2)]
    max_seq_len: usize,

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
    #[arg(long, default_value_t = search::DEFAULT_MAX_DEPTH)]
    window: usize,
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

fn run_wasm(cli: &Cli, path: &std::path::Path, rules: &[egg::Rewrite<ValueLang, ()>]) {
    use search::{format_ops, SearchConfig};
    use wasm::parse_wasm_file;

    let info = parse_wasm_file(path).unwrap_or_else(|e| {
        eprintln!("error parsing {}: {e}", path.display());
        std::process::exit(1);
    });

    println!(
        "Parsed {} — {} straight-line segment(s)\n",
        path.display(),
        info.segments.len()
    );

    if cli.segments_only {
        for seg in &info.segments {
            println!(
                "func {} segment {} ({} instr): {}",
                seg.func_index,
                seg.segment_index,
                seg.original_len(),
                format_ops(&seg.ops)
            );
        }
        return;
    }

    let cfg = SearchConfig {
        max_depth: cli.window,
    };
    let results = optimize::optimize_segments(&info.segments, rules, &cfg, cli.solver.into());
    optimize::print_results(&results, cli.solver.into());
    let (orig, opt, improved) = optimize::summarize(&results);
    println!(
        "Total: {orig} -> {opt} instructions across {} segment(s) ({} improved)",
        results.len(),
        improved
    );
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
        let max_len = cli.max_seq_len.clamp(1, 4);
        let syn = load_or_synthesize_rules(max_len, cli.random_tests);
        print_synthesized_json(&syn, cli.random_tests);
        return;
    }

    let path = cli.input.clone().expect("WASM path required");
    let max_len = cli.max_seq_len.clamp(1, 4);
    let syn = load_or_synthesize_rules(max_len, cli.random_tests);
    if !cli.segments_only {
        print_synthesized(&syn, cli.random_tests);
    }
    let rules = synthesized_to_rewrites(&syn);
    run_wasm(&cli, &path, &rules);
}
