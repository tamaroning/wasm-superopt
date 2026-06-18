//! Stack-to-DAG conversion driven by centralized semantics.

use crate::lang::WasmLang;
use crate::semantics::{SemOp, StackTy, spec_for};
use egg::{Id, Language, RecExpr};
use std::fmt::{self, Display};

/// Minimal Wasm opcode set for straight-line basic blocks.
#[derive(Clone, Debug, PartialEq, Eq)]
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
            SemOp::LocalGet(_) | SemOp::LocalSet(_) | SemOp::LocalTee(_) => {
                panic!("effectful local ops are not supported in WasmOp conversion")
            }
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
            SemOp::LocalGet(_) | SemOp::LocalSet(_) | SemOp::LocalTee(_) => {
                panic!("effectful local ops are not supported in DAG conversion");
            }
        }
    }

    pub fn build(mut self, ops: &[WasmOp]) -> RecExpr<WasmLang> {
        for op in ops {
            self.apply(op);
        }
        self.finish_stack_root();
        self.expr
    }

    /// Wrap the current operand stack as the `RecExpr` root (bottom-to-top `stack.slot` chain).
    fn finish_stack_root(&mut self) {
        let _ = self.build_stack_chain(&self.stack.clone());
    }

    fn build_stack_chain(&mut self, slots: &[Id]) -> Id {
        if slots.is_empty() {
            return self.expr.add(WasmLang::StackEnd);
        }
        let rest = self.build_stack_chain(&slots[1..]);
        self.expr.add(WasmLang::StackSlot([slots[0], rest]))
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

    /// Build an s-expression pattern for the full operand stack state.
    pub fn pattern_from_stack(&self) -> String {
        stack_ids_to_pattern(&self.expr, &self.stack)
    }

}

pub fn stack_to_dag(ops: &[WasmOp]) -> RecExpr<WasmLang> {
    StackToDag::new().build(ops)
}

/// Convert a `RecExpr` root back to a Wasm basic-block instruction sequence.
pub fn dag_to_stack(expr: &RecExpr<WasmLang>) -> Vec<WasmOp> {
    let mut ops = Vec::new();
    match &expr[expr.root()] {
        WasmLang::StackEnd | WasmLang::StackSlot(_) => emit_stack(expr, expr.root(), &mut ops),
        _ => emit_dag(expr, expr.root(), &mut ops),
    }
    ops
}

fn emit_stack(expr: &RecExpr<WasmLang>, id: Id, ops: &mut Vec<WasmOp>) {
    match &expr[id] {
        WasmLang::StackEnd => {}
        WasmLang::StackSlot([bottom, rest]) => {
            emit_dag(expr, *bottom, ops);
            emit_stack(expr, *rest, ops);
        }
        other => panic!("expected stack.end / stack.slot, got {other}"),
    }
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
        WasmLang::StackEnd | WasmLang::StackSlot(_) => {
            panic!("stack nodes must be lowered via emit_stack, not emit_dag")
        }
        WasmLang::Symbol(sym) => panic!("cannot lower symbolic node {sym}"),
    }
}

fn stack_ids_to_pattern(expr: &RecExpr<WasmLang>, slots: &[Id]) -> String {
    if slots.is_empty() {
        return "stack.end".to_string();
    }
    let bottom = enode_to_pattern(expr, slots[0]);
    let rest = stack_ids_to_pattern(expr, &slots[1..]);
    format!("(stack.slot {bottom} {rest})")
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

/// Replace the rightmost `stack.end` with `?rest` so a rule matches any stack suffix.
pub fn pattern_with_rest(pattern: &str) -> String {
    match pattern.rfind("stack.end") {
        Some(pos) => {
            let mut out = pattern.to_string();
            out.replace_range(pos..pos + "stack.end".len(), "?rest");
            out
        }
        None => pattern.to_string(),
    }
}

pub fn sem_sequence_to_pattern(input: &[StackTy], ops: &[SemOp]) -> Option<String> {
    if ops.iter().any(|op| op.is_effectful()) {
        return None;
    }
    let mut dag = StackToDag::new();
    for _ in input {
        dag.seed_symbolic_i32(1);
    }
    for op in ops {
        dag.apply_sem(op);
    }
    crate::semantics::simulate_stack_effect(input, ops)?;
    Some(pattern_with_rest(&dag.pattern_from_stack()))
}

pub fn parse_dag(s: &str) -> RecExpr<WasmLang> {
    s.parse().expect("invalid RecExpr")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stack_to_dag_wraps_full_stack_state() {
        let ops = [
            WasmOp::I32Const(42),
            WasmOp::I32Const(0),
            WasmOp::I32Add,
            WasmOp::I32Const(42),
            WasmOp::I32Const(0),
            WasmOp::I32Add,
        ];
        let dag = stack_to_dag(&ops);
        assert!(matches!(&dag[dag.root()], WasmLang::StackSlot(_)));
        assert_eq!(
            dag.to_string(),
            "(stack.slot (i32.add 42 0) (stack.slot (i32.add 42 0) stack.end))"
        );
    }

    #[test]
    fn pattern_with_rest_generalizes_stack_tail() {
        assert_eq!(
            pattern_with_rest("(stack.slot (i32.add ?a 0) stack.end)"),
            "(stack.slot (i32.add ?a 0) ?rest)"
        );
        assert_eq!(
            pattern_with_rest("(stack.slot ?a (stack.slot (i32.add ?b 0) stack.end))"),
            "(stack.slot ?a (stack.slot (i32.add ?b 0) ?rest))"
        );
    }

    #[test]
    fn dag_to_stack_round_trips_multi_slot_stack() {
        let ops = [
            WasmOp::I32Const(1),
            WasmOp::I32Const(2),
            WasmOp::I32Add,
            WasmOp::I32Const(3),
        ];
        let round = dag_to_stack(&stack_to_dag(&ops));
        assert_eq!(round, ops.as_slice());
    }
}
