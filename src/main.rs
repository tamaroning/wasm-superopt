//! Loop/jump-free WebAssembly basic blocks → backward goal search + e-graph rules.

mod canon;
mod goal;
mod heuristic;
mod inverse;
mod lang;
mod search;
mod sema;
mod semantics;
mod stack;
mod synthesis;
mod value;

use clap::{Parser, ValueEnum};
use egg::*;
use lang::ValueLang;
use semantics::DEFAULT_RANDOM_TESTS;
use synthesis::{
    load_or_synthesize_rules, print_synthesized, print_synthesized_json, synthesized_to_rewrites,
};
use value::parse_value_expr;

#[derive(Parser, Debug)]
#[command(name = "egraph", about = "Wasm backward goal search + value e-graph rules")]
struct Cli {
    /// Only run synthesis (print verified rules); skip demo examples.
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

    /// Run the built-in backward-search example instead of value-saturation demos.
    #[arg(long)]
    solve_example: bool,

    /// Search strategy when `--solve-example` is set.
    #[arg(long, value_enum, default_value_t = SolverKind::Bfs)]
    solver: SolverKind,

    /// Maximum peel depth (instruction window) for backward search.
    #[arg(long, default_value_t = search::DEFAULT_MAX_DEPTH)]
    window: usize,
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

fn run_example(
    name: &str,
    dag: &RecExpr<ValueLang>,
    rules: &[Rewrite<ValueLang, ()>],
) {
    let before_cost = AstSize.cost_rec(dag);
    let runner = Runner::default().with_expr(dag).run(rules);
    let root = runner.roots[0];
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (after_cost, best_expr) = extractor.find_best(root);

    println!("=== {name} ===");
    println!("Input Value DAG:  {dag}");
    println!("Best cost:  {before_cost} -> {after_cost}");
    println!("Output Value DAG: {best_expr}");
    println!();
}

fn load_rules(cli: &Cli) -> Vec<Rewrite<ValueLang, ()>> {
    let max_len = cli.max_seq_len.clamp(1, 4);
    let syn = load_or_synthesize_rules(max_len, cli.random_tests);
    print_synthesized(&syn, cli.random_tests);
    synthesized_to_rewrites(&syn)
}

fn run_demos(rules: &[Rewrite<ValueLang, ()>]) {
    run_example(
        "Mul-by-4 to Shl-by-2",
        &parse_value_expr("(i32.mul ?a 4)"),
        rules,
    );
    run_example(
        "Add-zero elimination",
        &parse_value_expr("(i32.add ?a 0)"),
        rules,
    );
}

fn run_solve_example(cli: &Cli, rules: &[Rewrite<ValueLang, ()>]) {
    use goal::{example_fin, example_init};
    use search::{format_ops, solve_astar, solve_bfs, solve_greedy_inv, verify_forward, SearchConfig};

    let init = example_init();
    let fin = example_fin();
    let cfg = SearchConfig {
        max_depth: cli.window,
    };
    let ops = match cli.solver {
        SolverKind::Bfs => solve_bfs(&init, &fin, rules, &cfg),
        SolverKind::Greedy => solve_greedy_inv(&init, &fin, rules, &cfg),
        SolverKind::Astar => solve_astar(&init, &fin, rules, &cfg),
    };
    let Some(ops) = ops else {
        println!("No solution within window {}", cli.window);
        return;
    };
    println!("=== solve-example (solver: {:?}) ===", cli.solver);
    println!("Length: {}", ops.len());
    println!("Ops: {}", format_ops(&ops));
    println!("Verify l0=42: {}", verify_forward(&fin, &ops, 42));
}

fn main() {
    let cli = Cli::parse();

    if cli.print_semantics {
        semantics::print_semantics_table();
    }

    // Synthesis-only mode: emit verified rules as JSON and exit.
    if cli.synthesize_only {
        let max_len = cli.max_seq_len.clamp(1, 4);
        let syn = load_or_synthesize_rules(max_len, cli.random_tests);
        print_synthesized_json(&syn, cli.random_tests);
        return;
    }

    // Backward goal search on the built-in init/fin example.
    if cli.solve_example {
        let max_len = cli.max_seq_len.clamp(1, 4);
        let syn = load_or_synthesize_rules(max_len, cli.random_tests);
        let rules = synthesized_to_rewrites(&syn);
        run_solve_example(&cli, &rules);
        return;
    }

    if cli.print_semantics {
        return;
    }

    // Default: load rules and run value-level equality-saturation demos.
    let rules = load_rules(&cli);
    println!("Running demos with {} synthesized rules.\n", rules.len());
    run_demos(&rules);
}
