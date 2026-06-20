//! Symbolic machine state and forward execution (shared by wasm parsing and optimization).

use crate::lang::ValueLang;
use crate::semantics::SemOp;
use crate::value::parse_value_expr;
use egg::{Id, RecExpr};
use std::collections::{BTreeMap, HashMap};

pub const MAX_STACK_HEIGHT: usize = 4;
pub const MAX_LOCAL_SLOT: u32 = 2;

pub type ValueExpr = RecExpr<ValueLang>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum LocalReq {
    DontCare,
    Need(ValueExpr),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SymState {
    pub stack: Vec<ValueExpr>,
    pub locals: BTreeMap<u32, LocalReq>,
}

impl SymState {
    pub fn validate_bounds(&self) -> bool {
        self.stack.len() <= MAX_STACK_HEIGHT && self.locals.keys().all(|&s| s <= MAX_LOCAL_SLOT)
    }

    pub fn top(&self) -> Option<&ValueExpr> {
        self.stack.last()
    }
}

pub fn subtree_expr(expr: &ValueExpr, node: Id) -> ValueExpr {
    let mut dst = RecExpr::default();
    let mut memo = HashMap::new();
    go_subtree(expr, node, &mut dst, &mut memo);
    dst
}

fn go_subtree(
    src: &ValueExpr,
    id: Id,
    dst: &mut RecExpr<ValueLang>,
    memo: &mut HashMap<Id, Id>,
) -> Id {
    if let Some(&mapped) = memo.get(&id) {
        return mapped;
    }
    let mapped = match &src[id] {
        ValueLang::I32Const(n) => dst.add(ValueLang::I32Const(*n)),
        ValueLang::Symbol(s) => dst.add(ValueLang::Symbol(s.clone())),
        ValueLang::I32Add([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I32Add([a, b]))
        }
        ValueLang::I32Mul([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I32Mul([a, b]))
        }
        ValueLang::I32Shl([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I32Shl([a, b]))
        }
        ValueLang::I32DivU([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I32DivU([a, b]))
        }
        ValueLang::I32DivS([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I32DivS([a, b]))
        }
    };
    memo.insert(id, mapped);
    mapped
}

pub fn all_subtree_exprs(expr: &ValueExpr) -> Vec<ValueExpr> {
    (0..expr.len())
        .map(|i| subtree_expr(expr, Id::from(i)))
        .collect()
}

#[derive(Debug, Clone)]
pub struct SymMachine {
    stack: Vec<ValueExpr>,
    locals: BTreeMap<u32, ValueExpr>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ForwardError {
    StackUnderflow,
    UnknownLocal(u32),
    StackTooHigh,
    LocalOutOfRange,
}

impl SymMachine {
    pub fn local_symbol(slot: u32) -> ValueExpr {
        parse_value_expr(&format!("?L{slot}"))
    }

    pub fn function_entry(num_params: u32, total_locals: u32) -> Self {
        let mut locals = BTreeMap::new();
        for slot in 0..total_locals.min(MAX_LOCAL_SLOT + 1) {
            let init = if slot < num_params {
                Self::local_symbol(slot)
            } else {
                parse_value_expr("0")
            };
            locals.insert(slot, init);
        }
        Self {
            stack: Vec::new(),
            locals,
        }
    }

    pub fn exec(&mut self, op: &SemOp) -> Result<(), ForwardError> {
        match op {
            SemOp::I32Const(n) => {
                self.push_expr(parse_value_expr(&n.to_string()))?;
            }
            SemOp::I32Add | SemOp::I32Mul | SemOp::I32DivU | SemOp::I32DivS | SemOp::I32Shl => {
                let b = self.pop()?;
                let a = self.pop()?;
                let expr = match op {
                    SemOp::I32Add => parse_value_expr(&format!("(i32.add {a} {b})")),
                    SemOp::I32Mul => parse_value_expr(&format!("(i32.mul {a} {b})")),
                    SemOp::I32DivU => parse_value_expr(&format!("(i32.div_u {a} {b})")),
                    SemOp::I32DivS => parse_value_expr(&format!("(i32.div_s {a} {b})")),
                    SemOp::I32Shl => parse_value_expr(&format!("(i32.shl {a} {b})")),
                    _ => unreachable!(),
                };
                self.push_expr(expr)?;
            }
            SemOp::LocalGet(slot) => {
                if *slot > MAX_LOCAL_SLOT {
                    return Err(ForwardError::LocalOutOfRange);
                }
                let v = self
                    .locals
                    .get(slot)
                    .cloned()
                    .ok_or(ForwardError::UnknownLocal(*slot))?;
                self.push_expr(v)?;
            }
            SemOp::LocalSet(slot) => {
                if *slot > MAX_LOCAL_SLOT {
                    return Err(ForwardError::LocalOutOfRange);
                }
                let v = self.pop()?;
                self.locals.insert(*slot, v);
            }
            SemOp::LocalTee(slot) => {
                if *slot > MAX_LOCAL_SLOT {
                    return Err(ForwardError::LocalOutOfRange);
                }
                let v = self
                    .stack
                    .last()
                    .cloned()
                    .ok_or(ForwardError::StackUnderflow)?;
                self.locals.insert(*slot, v);
            }
        }
        Ok(())
    }

    pub fn pop(&mut self) -> Result<ValueExpr, ForwardError> {
        self.stack.pop().ok_or(ForwardError::StackUnderflow)
    }

    pub fn to_init_state(&self) -> SymState {
        self.snapshot()
    }

    pub fn to_fin_state(&self) -> SymState {
        self.snapshot()
    }

    fn snapshot(&self) -> SymState {
        SymState {
            stack: self.stack.clone(),
            locals: self
                .locals
                .iter()
                .filter(|&(&slot, _)| slot <= MAX_LOCAL_SLOT)
                .map(|(&slot, v)| (slot, LocalReq::Need(v.clone())))
                .collect(),
        }
    }

    fn push_expr(&mut self, expr: ValueExpr) -> Result<(), ForwardError> {
        if self.stack.len() >= MAX_STACK_HEIGHT {
            return Err(ForwardError::StackTooHigh);
        }
        self.stack.push(expr);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::optimize::fixtures::init;

    #[test]
    fn function_entry_matches_running_example_init() {
        let entry = SymMachine::function_entry(1, 1);
        let init_state = entry.to_init_state();
        let expected = init();
        assert_eq!(init_state.stack, expected.stack);
        assert_eq!(init_state.locals, expected.locals);
    }
}
