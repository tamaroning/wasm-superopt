//! Loop/jump-free WebAssembly basic blocks → Acyclic E-graph (AEG) optimization pipeline.

mod lang;
mod sema;
mod semantics;
mod stack;
mod synthesis;

use clap::Parser;
use egg::*;
use lang::{ConstantFolding, WasmLang};
use semantics::DEFAULT_RANDOM_TESTS;
use stack::{WasmOp, format_wasm_block, parse_dag, stack_to_dag};
use synthesis::{
    print_synthesized, print_synthesized_json, synthesize_rules, synthesized_to_rewrites,
};

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
    wasm: &str,
    dag: &RecExpr<WasmLang>,
    rules: &[Rewrite<WasmLang, ConstantFolding>],
) {
    let before_cost = AstSize.cost_rec(dag);
    let runner = Runner::default().with_expr(dag).run(rules);
    let root = runner.roots[0];
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (after_cost, best_expr) = extractor.find_best(root);

    println!("=== {name} ===");
    println!("Input Wasm: {wasm}");
    println!("Stack DAG:  {dag}");
    println!("Best cost:  {before_cost} -> {after_cost}");
    println!("Best expr:  {best_expr}");
    println!();
}

fn run_example_ops(name: &str, ops: &[WasmOp], rules: &[Rewrite<WasmLang, ConstantFolding>]) {
    run_example(name, &format_wasm_block(ops), &stack_to_dag(ops), rules);
}

fn load_rules(cli: &Cli) -> Vec<Rewrite<WasmLang, ConstantFolding>> {
    let max_len = cli.max_seq_len.clamp(1, 4);
    let syn = synthesize_rules(max_len, cli.random_tests);
    print_synthesized(&syn, cli.random_tests);
    synthesized_to_rewrites(&syn)
}

fn run_demos(rules: &[Rewrite<WasmLang, ConstantFolding>]) {
    run_example_ops(
        "Stack-to-DAG",
        &[WasmOp::I32Const(0), WasmOp::I32Const(1), WasmOp::I32Add],
        rules,
    );

    run_example_ops(
        "Arithmetic Optimization",
        &[
            WasmOp::I32Const(0),
            WasmOp::I32Const(2),
            WasmOp::I32Mul,
            WasmOp::I32Const(3),
            WasmOp::I32Const(4),
            WasmOp::I32Add,
            WasmOp::I32Add,
        ],
        rules,
    );

    run_example_ops(
        "Pure Drop Elimination",
        &[
            WasmOp::I32Const(3),
            WasmOp::I32Const(4),
            WasmOp::I32Add,
            WasmOp::Drop,
        ],
        rules,
    );

    run_example(
        "Impure Drop (preserved)",
        "call f; drop",
        &parse_dag("(drop init (call f init))"),
        rules,
    );

    run_example_ops(
        "Self Division (non-zero constant)",
        &[WasmOp::I32Const(42), WasmOp::I32Const(42), WasmOp::I32DivU],
        rules,
    );

    run_example_ops(
        "Self Division (zero — trap preserved, no rewrite)",
        &[WasmOp::I32Const(0), WasmOp::I32Const(0), WasmOp::I32DivU],
        rules,
    );

    run_example(
        "Self Division (unknown — no rewrite)",
        "?x; ?x; i32.div_s",
        &parse_dag("(i32.div_s ?x ?x)"),
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
        let syn = synthesize_rules(max_len, cli.random_tests);
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
