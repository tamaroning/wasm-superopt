//! Stack-to-DAG conversion driven by centralized semantics.

use crate::lang::WasmLang;
use crate::semantics::{SemOp, StackTy, spec_for};
use egg::{Id, Language, RecExpr};
use std::fmt::{self, Display};
use std::str::FromStr;

/// Constant index for `local.get` / `local.set`.
#[derive(Clone, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct LocalIdx(pub u32);

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
pub enum WasmOp {
    I32Const(i32),
    LocalGet(u32),
    LocalSet(u32),
    I32Add,
    I32Mul,
    I32DivU,
    I32DivS,
    I32Shl,
    I32Load,
    I32Store,
    Drop,
}

impl From<&SemOp> for WasmOp {
    fn from(op: &SemOp) -> Self {
        match op {
            SemOp::I32Const(n) => WasmOp::I32Const(*n),
            SemOp::LocalGet(i) => WasmOp::LocalGet(*i),
            SemOp::LocalSet(i) => WasmOp::LocalSet(*i),
            SemOp::I32Add => WasmOp::I32Add,
            SemOp::I32Mul => WasmOp::I32Mul,
            SemOp::I32DivU => WasmOp::I32DivU,
            SemOp::I32DivS => WasmOp::I32DivS,
            SemOp::I32Shl => WasmOp::I32Shl,
            SemOp::I32Load => WasmOp::I32Load,
            SemOp::I32Store => WasmOp::I32Store,
            SemOp::Drop => WasmOp::Drop,
        }
    }
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
            WasmOp::I32Shl => write!(f, "i32.shl"),
            WasmOp::I32Load => write!(f, "i32.load"),
            WasmOp::I32Store => write!(f, "i32.store"),
            WasmOp::Drop => write!(f, "drop"),
        }
    }
}

pub fn format_wasm_block(ops: &[WasmOp]) -> String {
    ops.iter()
        .map(WasmOp::to_string)
        .collect::<Vec<_>>()
        .join("; ")
}

pub fn sem_ops_to_wasm(ops: &[SemOp]) -> Vec<WasmOp> {
    ops.iter().map(WasmOp::from).collect()
}

/// Stack emulator: values on the stack are `Id`s into a growing `RecExpr`.
pub struct StackToDag {
    expr: RecExpr<WasmLang>,
    stack: Vec<Id>,
    state: Id,
}

impl StackToDag {
    pub fn new() -> Self {
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

    pub fn apply(&mut self, op: &WasmOp) {
        let sem: SemOp = match op {
            WasmOp::I32Const(n) => SemOp::I32Const(*n),
            WasmOp::LocalGet(i) => SemOp::LocalGet(*i),
            WasmOp::LocalSet(i) => SemOp::LocalSet(*i),
            WasmOp::I32Add => SemOp::I32Add,
            WasmOp::I32Mul => SemOp::I32Mul,
            WasmOp::I32DivU => SemOp::I32DivU,
            WasmOp::I32DivS => SemOp::I32DivS,
            WasmOp::I32Shl => SemOp::I32Shl,
            WasmOp::I32Load => SemOp::I32Load,
            WasmOp::I32Store => SemOp::I32Store,
            WasmOp::Drop => SemOp::Drop,
        };
        self.apply_sem(&sem);
    }

    /// Apply using semantics table for stack signature validation.
    pub fn apply_sem(&mut self, op: &SemOp) {
        let spec = spec_for(op);
        assert!(
            spec.pops.len() <= self.stack.len(),
            "stack underflow applying {:?}",
            op
        );

        match op {
            SemOp::I32Const(n) => {
                self.stack.push(self.expr.add(WasmLang::I32Const(*n)));
            }
            SemOp::LocalGet(idx) => {
                let idx = self.local_idx(*idx);
                let node = self.expr.add(WasmLang::LocalGet([idx, self.state]));
                self.stack.push(node);
            }
            SemOp::LocalSet(idx) => {
                let value = self.stack.pop().expect("local.set");
                let idx = self.local_idx(*idx);
                self.state = self.expr.add(WasmLang::LocalSet([idx, value, self.state]));
            }
            SemOp::I32Add => {
                let b = self.stack.pop().expect("i32.add");
                let a = self.stack.pop().expect("i32.add");
                self.stack.push(self.expr.add(WasmLang::I32Add([a, b])));
            }
            SemOp::I32Mul => {
                let b = self.stack.pop().expect("i32.mul");
                let a = self.stack.pop().expect("i32.mul");
                self.stack.push(self.expr.add(WasmLang::I32Mul([a, b])));
            }
            SemOp::I32DivU => {
                let b = self.stack.pop().expect("i32.div_u");
                let a = self.stack.pop().expect("i32.div_u");
                self.stack.push(self.expr.add(WasmLang::I32DivU([a, b])));
            }
            SemOp::I32DivS => {
                let b = self.stack.pop().expect("i32.div_s");
                let a = self.stack.pop().expect("i32.div_s");
                self.stack.push(self.expr.add(WasmLang::I32DivS([a, b])));
            }
            SemOp::I32Shl => {
                let b = self.stack.pop().expect("i32.shl");
                let a = self.stack.pop().expect("i32.shl");
                self.stack.push(self.expr.add(WasmLang::I32Shl([a, b])));
            }
            SemOp::I32Load => {
                let addr = self.stack.pop().expect("i32.load");
                self.stack
                    .push(self.expr.add(WasmLang::I32Load([addr, self.state])));
            }
            SemOp::I32Store => {
                let value = self.stack.pop().expect("i32.store");
                let addr = self.stack.pop().expect("i32.store");
                self.state = self
                    .expr
                    .add(WasmLang::I32Store([addr, value, self.state]));
            }
            SemOp::Drop => {
                let value = self.stack.pop().expect("drop");
                self.state = self.expr.add(WasmLang::Drop([self.state, value]));
            }
        }
    }

    pub fn build(mut self, ops: &[WasmOp]) -> RecExpr<WasmLang> {
        for op in ops {
            self.apply(op);
        }
        self.expr
    }

    pub fn build_sem(mut self, ops: &[SemOp]) -> RecExpr<WasmLang> {
        for op in ops {
            self.apply_sem(op);
        }
        self.expr
    }

    /// Seed the stack with pattern variables `?a`, `?b`, … for synthesis.
    pub fn seed_symbolic_i32(&mut self, count: usize) -> Vec<String> {
        (0..count)
            .map(|i| {
                let name = format!("?{}", (b'a' + i as u8) as char);
                let id = self.expr.add(WasmLang::Symbol(name.parse().unwrap()));
                self.stack.push(id);
                name
            })
            .collect()
    }

    fn seed_state_symbol(&mut self) {
        let id = self.expr.add(WasmLang::Symbol("?s".parse().unwrap()));
        self.state = id;
    }

    /// Build an s-expression pattern for the value on top of the operand stack.
    pub fn pattern_from_stack_top(&self) -> Option<String> {
        let id = *self.stack.last()?;
        Some(enode_to_pattern(&self.expr, id))
    }

    /// Pattern for the current implicit state token (after effectful sequence).
    pub fn pattern_from_state(&self) -> Option<String> {
        Some(format!("{}", self.expr[self.state]))
    }
}

pub fn stack_to_dag(ops: &[WasmOp]) -> RecExpr<WasmLang> {
    StackToDag::new().build(ops)
}

fn enode_to_pattern(expr: &RecExpr<WasmLang>, id: Id) -> String {
    let node = &expr[id];
    if node.is_leaf() {
        node.to_string()
    } else {
        let children = node
            .children()
            .iter()
            .map(|&child| enode_to_pattern(expr, child))
            .collect::<Vec<_>>()
            .join(" ");
        format!("({node} {children})")
    }
}

pub fn sem_sequence_to_pattern(input: &[StackTy], ops: &[SemOp]) -> Option<String> {
    let mut dag = StackToDag::new();
    dag.seed_state_symbol();
    for _ in input {
        dag.seed_symbolic_i32(1);
    }
    for op in ops {
        dag.apply_sem(op);
    }
    let out = crate::semantics::simulate_stack_effect(input, ops)?;
    if out.len() == 1 {
        dag.pattern_from_stack_top()
    } else if out.is_empty() {
        dag.pattern_from_state()
    } else {
        None
    }
}


pub fn parse_dag(s: &str) -> RecExpr<WasmLang> {
    s.parse().expect("invalid RecExpr")
}
