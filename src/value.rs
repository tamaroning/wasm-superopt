//! Pure i32 value DAG (no stack/local containers) for equality saturation.

use crate::lang::ValueLang;
use crate::semantics::{
    DagStackStep, SemOp, StackTy, dag_stack_step, spec_for, simulate_stack_effect,
    value_lang_from_kind,
};
use crate::stack::WasmOp;
use egg::{Id, Language, RecExpr};

/// Stack emulator building a `ValueLang` DAG; the final root is the stack top.
pub struct ValueToDag {
    expr: RecExpr<ValueLang>,
    stack: Vec<Id>,
}

impl ValueToDag {
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

    pub fn apply_sem(&mut self, op: &SemOp) {
        let spec = spec_for(op);
        let step = dag_stack_step(op, &spec, &mut self.stack).unwrap_or_else(|| {
            panic!("effectful or unsupported op in value DAG conversion: {op:?}")
        });
        match step {
            DagStackStep::PushConst(n) => {
                self.stack.push(self.expr.add(ValueLang::I32Const(n)));
            }
            DagStackStep::Push { kind, args } => {
                self.stack
                    .push(self.expr.add(value_lang_from_kind(kind, &args)));
            }
        }
    }

    /// Seed the stack with pattern variables `?a`, `?b`, … for synthesis.
    pub fn seed_symbolic_i32(&mut self, count: usize) -> Vec<String> {
        (0..count)
            .map(|i| {
                let name = format!("?{}", (b'a' + i as u8) as char);
                let id = self.expr.add(ValueLang::Symbol(name.parse().unwrap()));
                self.stack.push(id);
                name
            })
            .collect()
    }

    /// S-expression pattern for the stack top (single value root).
    pub fn top_pattern(&self) -> Option<String> {
        let top = self.stack.last()?;
        Some(enode_to_pattern(&self.expr, *top))
    }

    pub fn finish(self) -> RecExpr<ValueLang> {
        assert_eq!(
            self.stack.len(),
            1,
            "value DAG expects exactly one stack slot at finish, got {}",
            self.stack.len()
        );
        self.expr
    }

    pub fn build(mut self, ops: &[WasmOp]) -> RecExpr<ValueLang> {
        for op in ops {
            self.apply(op);
        }
        self.finish()
    }
}

pub fn ops_to_value_expr(ops: &[WasmOp]) -> RecExpr<ValueLang> {
    ValueToDag::new().build(ops)
}

pub fn sem_sequence_to_value_pattern(input: &[StackTy], ops: &[SemOp]) -> Option<String> {
    if ops.iter().any(|op| op.is_effectful()) {
        return None;
    }
    let output = simulate_stack_effect(input, ops)?;
    if output.len() != 1 {
        return None;
    }
    let mut dag = ValueToDag::new();
    for _ in input {
        dag.seed_symbolic_i32(1);
    }
    for op in ops {
        dag.apply_sem(op);
    }
    dag.top_pattern()
}

pub fn parse_value_expr(s: &str) -> RecExpr<ValueLang> {
    s.parse().expect("invalid ValueLang RecExpr")
}

fn enode_to_pattern(expr: &RecExpr<ValueLang>, id: Id) -> String {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ops_to_value_expr_builds_single_root() {
        let ops = [
            WasmOp::I32Const(42),
            WasmOp::I32Const(0),
            WasmOp::I32Add,
        ];
        let expr = ops_to_value_expr(&ops);
        assert_eq!(expr.to_string(), "(i32.add 42 0)");
        assert!(!expr.to_string().contains("stack.slot"));
    }

    #[test]
    fn top_pattern_has_no_stack_nodes() {
        let input = [StackTy::I32];
        let ops = [SemOp::I32Const(2), SemOp::I32Mul];
        let pat = sem_sequence_to_value_pattern(&input, &ops).expect("pattern");
        assert_eq!(pat, "(i32.mul ?a 2)");
        assert!(!pat.contains("stack"));
    }

    #[test]
    fn sem_sequence_to_value_pattern_rejects_multi_output_stack() {
        let input = [StackTy::I32];
        let ops = [SemOp::I32Const(0)];
        assert!(sem_sequence_to_value_pattern(&input, &ops).is_none());

        let input2 = [StackTy::I32, StackTy::I32];
        let ops2 = [];
        assert!(sem_sequence_to_value_pattern(&input2, &ops2).is_none());

        let input3 = [StackTy::I32];
        let ops3 = [SemOp::I32Const(2), SemOp::I32Mul];
        assert!(sem_sequence_to_value_pattern(&input3, &ops3).is_some());
    }
}
