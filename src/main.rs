//! Loop/jump-free WebAssembly basic blocks → Acyclic E-graph (AEG) optimization pipeline.
//!
//! 1. Stack-to-DAG: emulate the Wasm stack, building AST node references instead of values.
//! 2. E-graph registration + equivalence saturation + cost-based extraction.
//! 3. Code generation (DAG-to-target) is left pluggable via the cost model.

use egg::{rewrite as rw, *};
use std::fmt::{self, Display};
use std::str::FromStr;

// ---------------------------------------------------------------------------
// §1 Wasm stack → DAG (stack emulation)
// ---------------------------------------------------------------------------

/// Constant index for `local.get` / `local.set`.
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
struct LocalIdx(u32);

impl Display for LocalIdx {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "local:{}", self.0)
    }
}

impl FromStr for LocalIdx {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let n = s
            .strip_prefix("local:")
            .ok_or_else(|| format!("expected local:N, got {s}"))?;
        n.parse()
            .map(LocalIdx)
            .map_err(|e| format!("invalid local index {n}: {e}"))
    }
}

/// Minimal Wasm opcode set for straight-line basic blocks.
#[derive(Clone, Debug)]
enum WasmOp {
    I32Const(i32),
    LocalGet(u32),
    LocalSet(u32),
    I32Add,
    I32Mul,
    I32DivU,
    I32DivS,
    I32Load,
    I32Store,
    Drop,
}

impl Display for WasmOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WasmOp::I32Const(n) => write!(f, "i32.const {n}"),
            WasmOp::LocalGet(i) => write!(f, "local.get {i}"),
            WasmOp::LocalSet(i) => write!(f, "local.set {i}"),
            WasmOp::I32Add => write!(f, "i32.add"),
            WasmOp::I32Mul => write!(f, "i32.mul"),
            WasmOp::I32DivU => write!(f, "i32.div_u"),
            WasmOp::I32DivS => write!(f, "i32.div_s"),
            WasmOp::I32Load => write!(f, "i32.load"),
            WasmOp::I32Store => write!(f, "i32.store"),
            WasmOp::Drop => write!(f, "drop"),
        }
    }
}

fn format_wasm_block(ops: &[WasmOp]) -> String {
    ops.iter()
        .map(WasmOp::to_string)
        .collect::<Vec<_>>()
        .join("; ")
}

/// Stack emulator: values on the stack are `Id`s into a growing `RecExpr`.
struct StackToDag {
    expr: RecExpr<WasmLang>,
    stack: Vec<Id>,
    state: Id,
}

impl StackToDag {
    fn new() -> Self {
        let mut expr = RecExpr::default();
        let state = expr.add(WasmLang::Init);
        Self {
            expr,
            stack: Vec::new(),
            state,
        }
    }

    fn local_idx(&mut self, n: u32) -> Id {
        self.expr.add(WasmLang::LocalIdx(LocalIdx(n)))
    }

    fn apply(&mut self, op: &WasmOp) {
        match op {
            WasmOp::I32Const(n) => {
                self.stack.push(self.expr.add(WasmLang::I32Const(*n)));
            }
            WasmOp::LocalGet(idx) => {
                let idx = self.local_idx(*idx);
                let node = self.expr.add(WasmLang::LocalGet([idx, self.state]));
                self.stack.push(node);
            }
            WasmOp::LocalSet(idx) => {
                let value = self.stack.pop().expect("local.set: stack underflow");
                let idx = self.local_idx(*idx);
                self.state = self.expr.add(WasmLang::LocalSet([idx, value, self.state]));
            }
            WasmOp::I32Add => {
                let b = self.stack.pop().expect("i32.add: stack underflow");
                let a = self.stack.pop().expect("i32.add: stack underflow");
                self.stack.push(self.expr.add(WasmLang::I32Add([a, b])));
            }
            WasmOp::I32Mul => {
                let b = self.stack.pop().expect("i32.mul: stack underflow");
                let a = self.stack.pop().expect("i32.mul: stack underflow");
                self.stack.push(self.expr.add(WasmLang::I32Mul([a, b])));
            }
            WasmOp::I32DivU => {
                let b = self.stack.pop().expect("i32.div_u: stack underflow");
                let a = self.stack.pop().expect("i32.div_u: stack underflow");
                self.stack.push(self.expr.add(WasmLang::I32DivU([a, b])));
            }
            WasmOp::I32DivS => {
                let b = self.stack.pop().expect("i32.div_s: stack underflow");
                let a = self.stack.pop().expect("i32.div_s: stack underflow");
                self.stack.push(self.expr.add(WasmLang::I32DivS([a, b])));
            }
            WasmOp::I32Load => {
                let addr = self.stack.pop().expect("i32.load: stack underflow");
                self.stack
                    .push(self.expr.add(WasmLang::I32Load([addr, self.state])));
            }
            WasmOp::I32Store => {
                let value = self.stack.pop().expect("i32.store: stack underflow");
                let addr = self.stack.pop().expect("i32.store: stack underflow");
                self.state = self
                    .expr
                    .add(WasmLang::I32Store([addr, value, self.state]));
            }
            WasmOp::Drop => {
                let value = self.stack.pop().expect("drop: stack underflow");
                self.state = self.expr.add(WasmLang::Drop([self.state, value]));
            }
        }
    }

    fn build(mut self, ops: &[WasmOp]) -> RecExpr<WasmLang> {
        for op in ops {
            self.apply(op);
        }
        self.expr
    }
}

fn stack_to_dag(ops: &[WasmOp]) -> RecExpr<WasmLang> {
    StackToDag::new().build(ops)
}

fn parse_dag(s: &str) -> RecExpr<WasmLang> {
    s.parse().expect("invalid RecExpr")
}

// ---------------------------------------------------------------------------
// §2 E-graph language, analysis, and rewrite rules
// ---------------------------------------------------------------------------

define_language! {
    pub enum WasmLang {
        // --- Pure arithmetic ---
        // Bare i32 literal in s-expr (egg does not support `"i32.const" = …(i32)`).
        I32Const(i32),
        "i32.add"   = I32Add([Id; 2]),
        "i32.mul"   = I32Mul([Id; 2]),
        "i32.div_u" = I32DivU([Id; 2]),
        "i32.div_s" = I32DivS([Id; 2]),
        "i32.shl"   = I32Shl([Id; 2]),

        // --- SSA value / local index ---
        Symbol(Symbol),
        LocalIdx(LocalIdx),

        // --- State token (effect threading) ---
        // init: function-entry state (removed during lowering to Wasm)
        "init" = Init,
        "state_seq" = StateSeq([Id; 2]), // barrier: (state_seq s_after s_before) preserves order
        "drop" = Drop([Id; 2]),          // (drop state value) -> state

        // --- Side-effecting ops (state token is last operand) ---
        "local.get" = LocalGet([Id; 2]),   // [local_idx, state] -> value
        "local.set" = LocalSet([Id; 3]),   // [local_idx, value, state] -> state
        "i32.store" = I32Store([Id; 3]), // [addr, value, state] -> state
        "i32.load"  = I32Load([Id; 2]),  // [addr, state] -> value
        "call" = Call([Id; 2]),          // [callee, state] -> state
    }
}

type EGraph = egg::EGraph<WasmLang, ConstantFolding>;

#[derive(Default)]
pub struct ConstantFolding;

impl Analysis<WasmLang> for ConstantFolding {
    type Data = Option<i32>;

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        egg::merge_max(to, from)
    }

    fn make(egraph: &mut EGraph, enode: &WasmLang, _id: Id) -> Self::Data {
        let x = |i: &Id| egraph[*i].data;
        match enode {
            WasmLang::I32Const(c) => Some(*c),
            WasmLang::I32Add([a, b]) => Some(x(a)? + x(b)?),
            WasmLang::I32Mul([a, b]) => Some(x(a)? * x(b)?),
            WasmLang::I32DivU([a, b]) => {
                let divisor = x(b)?;
                if divisor == 0 {
                    None
                } else {
                    Some((x(a)? as u32 / divisor as u32) as i32)
                }
            }
            WasmLang::I32DivS([a, b]) => {
                let divisor = x(b)?;
                if divisor == 0 {
                    None
                } else {
                    Some(x(a)? / divisor)
                }
            }
            WasmLang::I32Shl([a, b]) => Some(x(a)? << x(b)?),
            _ => None,
        }
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        if let Some(c) = egraph[id].data {
            let const_node = egraph.add(WasmLang::I32Const(c));
            egraph.union(id, const_node);
        }
    }
}

/// Self-division `x / x => 1` is valid only when `x != 0` (Wasm traps on divide-by-zero).
fn is_nonzero(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| matches!(egraph[subst[var]].data, Some(n) if n != 0)
}

fn is_pure_computation(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        egraph[subst[var]].nodes.iter().all(|n| {
            matches!(
                n,
                WasmLang::I32Add(_)
                    | WasmLang::I32Mul(_)
                    | WasmLang::I32DivU(_)
                    | WasmLang::I32DivS(_)
                    | WasmLang::I32Shl(_)
                    | WasmLang::I32Const(_)
                    | WasmLang::Symbol(_)
            )
        })
    }
}

fn arith_rules() -> Vec<Rewrite<WasmLang, ConstantFolding>> {
    vec![
        rw!("add-comm"; "(i32.add ?a ?b)" => "(i32.add ?b ?a)"),
        rw!("mul-comm"; "(i32.mul ?a ?b)" => "(i32.mul ?b ?a)"),
        rw!("mul-to-shl"; "(i32.mul ?x 2)" => "(i32.shl ?x 1)"),
        rw!("div-u-self"; "(i32.div_u ?x ?x)" => "1" if is_nonzero("?x")),
        rw!("div-s-self"; "(i32.div_s ?x ?x)" => "1" if is_nonzero("?x")),
    ]
}

fn effect_rules() -> Vec<Rewrite<WasmLang, ConstantFolding>> {
    vec![
        rw!("eliminate-pure-drop"; "(drop ?s ?val)" => "?s" if is_pure_computation("?val")),
        // Do NOT rewrite (local.get ?idx (local.set ?idx ?val ?s)) => ?val:
        // that equates a pure value with an effectful read and breaks extraction.
        rw!(
            "dead-local-store";
            "(local.set ?idx ?v2 (local.set ?idx ?v1 ?s))"
            => "(local.set ?idx ?v2 (drop ?s ?v1))"
        ),
        rw!(
            "mem-dead-store";
            "(i32.store ?ptr ?v2 (i32.store ?ptr ?v1 ?s))"
            => "(i32.store ?ptr ?v2 ?s)"
        ),
        // state_seq is a no-op for semantics but blocks illegal reordering during extraction.
        rw!("state-seq-id"; "(state_seq ?s ?s)" => "?s"),
    ]
}

fn rules() -> Vec<Rewrite<WasmLang, ConstantFolding>> {
    let mut all = arith_rules();
    all.extend(effect_rules());
    all
}

// ---------------------------------------------------------------------------
// §3 Saturation + extraction
// ---------------------------------------------------------------------------

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

fn run_example_ops(
    name: &str,
    ops: &[WasmOp],
    rules: &[Rewrite<WasmLang, ConstantFolding>],
) {
    run_example(name, &format_wasm_block(ops), &stack_to_dag(ops), rules);
}

fn main() {
    let rules = rules();

    run_example_ops(
        "Stack-to-DAG",
        &[
            WasmOp::LocalGet(0),
            WasmOp::I32Const(1),
            WasmOp::I32Add,
        ],
        &rules,
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
        &rules,
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
        &rules,
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
        &rules,
    );

    run_example(
        "Impure Drop (preserved)",
        "call f; drop",
        &parse_dag("(drop init (call f init))"),
        &rules,
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
        &rules,
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
        &rules,
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
        &rules,
    );

    run_example_ops(
        "Self Division (non-zero constant)",
        &[
            WasmOp::I32Const(42),
            WasmOp::I32Const(42),
            WasmOp::I32DivU,
        ],
        &rules,
    );

    run_example_ops(
        "Self Division (zero — trap preserved, no rewrite)",
        &[
            WasmOp::I32Const(0),
            WasmOp::I32Const(0),
            WasmOp::I32DivU,
        ],
        &rules,
    );

    run_example_ops(
        "Self Division (unknown — no rewrite)",
        &[
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(0),
            WasmOp::I32DivS,
        ],
        &rules,
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
        &rules,
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
        &rules,
    );

    // -----------------------------------------------------------------------
    // Phase Ordering: SuperStack vs downstream AOT/JIT (register spill)
    // (a+b)*(c+d) with local spill — register-friendly for single-pass compilers
    // -----------------------------------------------------------------------
    run_example_ops(
        "Phase Ordering / Ex1 Local Spill (register-friendly)",
        &[
            WasmOp::LocalGet(0), // a
            WasmOp::LocalGet(1), // b
            WasmOp::I32Add,
            WasmOp::LocalSet(2), // tmp1 = a+b
            WasmOp::LocalGet(3), // c
            WasmOp::LocalGet(4), // d
            WasmOp::I32Add,
            WasmOp::LocalGet(2), // reload tmp1
            WasmOp::I32Mul,
        ],
        &rules,
    );

    // Same semantics; SuperStack removes local.set/local.get → deep operand stack
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
        &rules,
    );

    // -----------------------------------------------------------------------
    // Phase Ordering: instruction folding (base + offset → load)
    // -----------------------------------------------------------------------
    run_example_ops(
        "Phase Ordering / Ex2 Contiguous Add+Load (folding-friendly)",
        &[
            WasmOp::LocalGet(0), // base_ptr
            WasmOp::I32Const(16),
            WasmOp::I32Add,
            WasmOp::I32Load,
        ],
        &rules,
    );

    // SuperStack may route the offset through a local and interleave unrelated effects,
    // breaking the contiguous add→load pattern that single-pass backends pattern-match.
    run_example_ops(
        "Phase Ordering / Ex2 Interleaved (folding-unfriendly)",
        &[
            WasmOp::LocalGet(0), // base_ptr
            WasmOp::I32Const(16),
            WasmOp::LocalSet(2), // offset routed to local
            WasmOp::I32Const(0),
            WasmOp::I32Const(42),
            WasmOp::I32Store, // unrelated side effect
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(2),
            WasmOp::I32Add,
            WasmOp::I32Load,
        ],
        &rules,
    );
}
