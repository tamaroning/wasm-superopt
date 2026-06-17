//! Stack-to-DAG conversion driven by centralized semantics.

use crate::lang::WasmLang;
use crate::semantics::{SemOp, StackTy, spec_for};
use egg::{Id, Language, RecExpr};
use std::fmt::{self, Display};

/// Minimal Wasm opcode set for straight-line basic blocks.
#[derive(Clone, Debug)]
pub enum WasmOp {
    I32Const(i32),
    I32Add,
    I32Mul,
    I32DivU,
    I32DivS,
    I32Shl,
}

impl From<&SemOp> for WasmOp {
    fn from(op: &SemOp) -> Self {
        match op {
            SemOp::I32Const(n) => WasmOp::I32Const(*n),
            SemOp::I32Add => WasmOp::I32Add,
            SemOp::I32Mul => WasmOp::I32Mul,
            SemOp::I32DivU => WasmOp::I32DivU,
            SemOp::I32DivS => WasmOp::I32DivS,
            SemOp::I32Shl => WasmOp::I32Shl,
        }
    }
}

impl Display for WasmOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WasmOp::I32Const(n) => write!(f, "i32.const {n}"),
            WasmOp::I32Add => write!(f, "i32.add"),
            WasmOp::I32Mul => write!(f, "i32.mul"),
            WasmOp::I32DivU => write!(f, "i32.div_u"),
            WasmOp::I32DivS => write!(f, "i32.div_s"),
            WasmOp::I32Shl => write!(f, "i32.shl"),
        }
    }
}

pub fn format_wasm_block(ops: &[WasmOp]) -> String {
    ops.iter()
        .map(WasmOp::to_string)
        .collect::<Vec<_>>()
        .join("; ")
}

/// Stack emulator: values on the stack are `Id`s into a growing `RecExpr`.
pub struct StackToDag {
    expr: RecExpr<WasmLang>,
    stack: Vec<Id>,
}

impl StackToDag {
    pub fn new() -> Self {
        Self {
            expr: RecExpr::default(),
            stack: Vec::new(),
        }
    }

    pub fn apply(&mut self, op: &WasmOp) {
        match op {
            WasmOp::I32Const(n) => self.apply_sem(&SemOp::I32Const(*n)),
            WasmOp::I32Add => self.apply_sem(&SemOp::I32Add),
            WasmOp::I32Mul => self.apply_sem(&SemOp::I32Mul),
            WasmOp::I32DivU => self.apply_sem(&SemOp::I32DivU),
            WasmOp::I32DivS => self.apply_sem(&SemOp::I32DivS),
            WasmOp::I32Shl => self.apply_sem(&SemOp::I32Shl),
        }
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
        }
    }

    pub fn build(mut self, ops: &[WasmOp]) -> RecExpr<WasmLang> {
        for op in ops {
            self.apply(op);
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

    /// Build an s-expression pattern for the value on top of the operand stack.
    pub fn pattern_from_stack_top(&self) -> Option<String> {
        let id = *self.stack.last()?;
        Some(enode_to_pattern(&self.expr, id))
    }

}

pub fn stack_to_dag(ops: &[WasmOp]) -> RecExpr<WasmLang> {
    StackToDag::new().build(ops)
}

/// Convert a `RecExpr` root back to a Wasm basic-block instruction sequence.
pub fn dag_to_stack(expr: &RecExpr<WasmLang>) -> Vec<WasmOp> {
    let mut ops = Vec::new();
    emit_dag(expr, expr.root(), &mut ops);
    ops
}

fn emit_dag(expr: &RecExpr<WasmLang>, id: Id, ops: &mut Vec<WasmOp>) {
    match &expr[id] {
        WasmLang::I32Const(n) => ops.push(WasmOp::I32Const(*n)),
        WasmLang::I32Add([a, b]) => {
            emit_dag(expr, *a, ops);
            emit_dag(expr, *b, ops);
            ops.push(WasmOp::I32Add);
        }
        WasmLang::I32Mul([a, b]) => {
            emit_dag(expr, *a, ops);
            emit_dag(expr, *b, ops);
            ops.push(WasmOp::I32Mul);
        }
        WasmLang::I32DivU([a, b]) => {
            emit_dag(expr, *a, ops);
            emit_dag(expr, *b, ops);
            ops.push(WasmOp::I32DivU);
        }
        WasmLang::I32DivS([a, b]) => {
            emit_dag(expr, *a, ops);
            emit_dag(expr, *b, ops);
            ops.push(WasmOp::I32DivS);
        }
        WasmLang::I32Shl([a, b]) => {
            emit_dag(expr, *a, ops);
            emit_dag(expr, *b, ops);
            ops.push(WasmOp::I32Shl);
        }
        WasmLang::Symbol(sym) => panic!("cannot lower symbolic node {sym}"),
    }
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
    for _ in input {
        dag.seed_symbolic_i32(1);
    }
    for op in ops {
        dag.apply_sem(op);
    }
    let out = crate::semantics::simulate_stack_effect(input, ops)?;
    if out.len() == 1 {
        dag.pattern_from_stack_top()
    } else {
        None
    }
}

pub fn parse_dag(s: &str) -> RecExpr<WasmLang> {
    s.parse().expect("invalid RecExpr")
}
