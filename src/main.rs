//! Loop/jump-free WebAssembly basic blocks → Acyclic E-graph (AEG) optimization pipeline.

mod lang;
mod semantics;
mod stack;
mod synthesis;

use clap::{Parser, ValueEnum};
use egg::*;
use lang::{ConstantFolding, WasmLang, arith_rules, effect_rules, manual_rules};
use semantics::DEFAULT_RANDOM_TESTS;
use stack::{WasmOp, format_wasm_block, parse_dag, stack_to_dag};
use synthesis::{
    print_synthesized, print_synthesized_json, synthesize_rules, synthesized_to_rewrites,
};

#[derive(Clone, Debug, ValueEnum, PartialEq, Eq)]
enum RulesMode {
    /// Hand-coded rewrite rules in `lang::manual_rules`.
    Manual,
    /// Z3-verified rules synthesized from 1–4 instruction sequences.
    Synthesize,
}

#[derive(Parser, Debug)]
#[command(name = "egraph", about = "Wasm basic-block e-graph optimizer")]
struct Cli {
    /// Rewrite rule source: hand-coded or Z3-synthesized.
    #[arg(long, value_enum, default_value_t = RulesMode::Manual)]
    rules: RulesMode,

    /// Only run synthesis (print verified rules); skip demo examples.
    #[arg(long)]
    synthesize_only: bool,

    /// Print the centralized Wasm instruction semantics table.
    #[arg(long)]
    print_semantics: bool,

    /// Maximum instruction-sequence length for synthesis (1–4).
    #[arg(long, default_value_t = 3)]
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
    match cli.rules {
        RulesMode::Manual => manual_rules(),
        RulesMode::Synthesize => {
            let max_len = cli.max_seq_len.clamp(1, 4);
            let syn = synthesize_rules(max_len, cli.random_tests);
            print_synthesized(&syn, cli.random_tests);
            synthesized_to_rewrites(&syn)
        }
    }
}

fn run_demos(rules: &[Rewrite<WasmLang, ConstantFolding>]) {
    run_example_ops(
        "Stack-to-DAG",
        &[WasmOp::LocalGet(0), WasmOp::I32Const(1), WasmOp::I32Add],
        rules,
    );

    run_example_ops(
        "Arithmetic Optimization",
        &[
            WasmOp::LocalGet(0),
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
        "Set-Get / Dead Store",
        &[
            WasmOp::I32Const(1),
            WasmOp::LocalSet(0),
            WasmOp::I32Const(2),
            WasmOp::LocalSet(0),
            WasmOp::LocalGet(0),
        ],
        rules,
    );

    run_example_ops(
        "Pure Drop Elimination",
        &[
            WasmOp::I32Const(3),
            WasmOp::I32Const(4),
            WasmOp::I32Add,
            WasmOp::LocalSet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32Const(2),
            WasmOp::I32Mul,
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
        "Memory Dead Store",
        &[
            WasmOp::I32Const(0),
            WasmOp::I32Const(10),
            WasmOp::I32Store,
            WasmOp::I32Const(0),
            WasmOp::I32Const(20),
            WasmOp::I32Store,
            WasmOp::I32Const(0),
            WasmOp::I32Load,
        ],
        rules,
    );

    run_example(
        "Memory + Local State Chain",
        "local.set 0, 1; i32.store 0, 2; local.get 0; i32.store 1, 3; i32.load 1; i32.add",
        &parse_dag(
            "(i32.add
                (local.get local:0 (i32.store 0 2 (local.set local:0 1 init)))
                (i32.load 1 (i32.store 1 3 init))
            )",
        ),
        rules,
    );

    let simultaneous_wasm = "local.get 0; i32.const 2; i32.mul; local.set 1; \
                             i32.const 3; i32.const 4; i32.add; local.set 1; local.get 1; \
                             local.get 2; i32.const 2; i32.mul; i32.add";
    let simultaneous_dag = parse_dag(
        "(i32.add
            (local.get local:1 (local.set local:1 (i32.add 3 4) (local.set local:1 (i32.mul (local.get local:0 init) 2) init)))
            (i32.mul (local.get local:2 init) 2)
        )",
    );

    run_example(
        "Simultaneous Optimization / Arithmetic rules only",
        simultaneous_wasm,
        &simultaneous_dag,
        &arith_rules(),
    );
    run_example(
        "Simultaneous Optimization / Effect rules only",
        simultaneous_wasm,
        &simultaneous_dag,
        &effect_rules(),
    );
    run_example(
        "Simultaneous Optimization / All rules together",
        simultaneous_wasm,
        &simultaneous_dag,
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

    run_example_ops(
        "Self Division (unknown — no rewrite)",
        &[WasmOp::LocalGet(0), WasmOp::LocalGet(0), WasmOp::I32DivS],
        rules,
    );

    run_example_ops(
        "Strict Memory Chain (addr 0 then 1)",
        &[
            WasmOp::I32Const(0),
            WasmOp::I32Const(10),
            WasmOp::I32Store,
            WasmOp::I32Const(1),
            WasmOp::I32Const(20),
            WasmOp::I32Store,
            WasmOp::I32Const(1),
            WasmOp::I32Load,
        ],
        rules,
    );

    run_example(
        "StateSeq Barrier",
        "i32.store 0, 10; i32.store 1, 20; i32.load 1  (state_seq inserted at lowering)",
        &parse_dag(
            "(i32.load 1
                (state_seq
                    (i32.store 1 20 init)
                    (i32.store 0 10 init)
                )
            )",
        ),
        rules,
    );

    run_example_ops(
        "Phase Ordering / Ex1 Local Spill (register-friendly)",
        &[
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32Add,
            WasmOp::LocalSet(2),
            WasmOp::LocalGet(3),
            WasmOp::LocalGet(4),
            WasmOp::I32Add,
            WasmOp::LocalGet(2),
            WasmOp::I32Mul,
        ],
        rules,
    );

    run_example_ops(
        "Phase Ordering / Ex1 Deep Stack (SuperStack-like)",
        &[
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32Add,
            WasmOp::LocalGet(3),
            WasmOp::LocalGet(4),
            WasmOp::I32Add,
            WasmOp::I32Mul,
        ],
        rules,
    );

    run_example_ops(
        "Phase Ordering / Ex2 Contiguous Add+Load (folding-friendly)",
        &[
            WasmOp::LocalGet(0),
            WasmOp::I32Const(16),
            WasmOp::I32Add,
            WasmOp::I32Load,
        ],
        rules,
    );

    run_example_ops(
        "Phase Ordering / Ex2 Interleaved (folding-unfriendly)",
        &[
            WasmOp::LocalGet(0),
            WasmOp::I32Const(16),
            WasmOp::LocalSet(2),
            WasmOp::I32Const(0),
            WasmOp::I32Const(42),
            WasmOp::I32Store,
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(2),
            WasmOp::I32Add,
            WasmOp::I32Load,
        ],
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
    if matches!(cli.rules, RulesMode::Synthesize) {
        println!("Running demos with {} synthesized rules.\n", rules.len());
    }
    run_demos(&rules);
}
