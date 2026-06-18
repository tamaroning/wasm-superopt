//! Loop/jump-free WebAssembly basic blocks → Acyclic E-graph (AEG) optimization pipeline.

mod lang;
mod sema;
mod semantics;
mod stack;
mod synthesis;
mod value;

use clap::Parser;
use egg::*;
use lang::ValueLang;
use semantics::DEFAULT_RANDOM_TESTS;
use synthesis::{
    load_or_synthesize_rules, print_synthesized, print_synthesized_json, synthesized_to_rewrites,
};
use value::parse_value_expr;

#[derive(Parser, Debug)]
#[command(name = "egraph", about = "Wasm basic-block e-graph optimizer")]
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
        "Mul-by-4 inside add (idea.md stack value shape)",
        &parse_value_expr("(i32.mul (i32.add ?L0 1) 4)"),
        rules,
    );
    run_example(
        "Add-zero elimination",
        &parse_value_expr("(i32.add ?a 0)"),
        rules,
    );
}

fn main() {
    let cli = Cli::parse();

    if cli.print_semantics {
        semantics::print_semantics_table();
    }

    if cli.synthesize_only {
        let max_len = cli.max_seq_len.clamp(1, 4);
        let syn = load_or_synthesize_rules(max_len, cli.random_tests);
        print_synthesized_json(&syn, cli.random_tests);
        return;
    }

    if cli.print_semantics {
        return;
    }

    let rules = load_rules(&cli);
    println!("Running demos with {} synthesized rules.\n", rules.len());
    run_demos(&rules);
}
