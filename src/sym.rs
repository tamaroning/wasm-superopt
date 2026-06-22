//! Symbolic machine state and forward execution (shared by wasm parsing and optimization).

use crate::lang::ValueLang;
use crate::semantics::SemOp;
use crate::value::parse_value_expr;
use crate::wasm::{OpaqueMeta, SegmentBounds};
use egg::{Id, RecExpr};
use std::collections::{BTreeMap, HashMap};

pub type ValueExpr = RecExpr<ValueLang>;

pub fn expr_name(expr: &ValueExpr) -> String {
    expr.to_string()
}

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
    pub fn validate_bounds(&self, bounds: &SegmentBounds) -> bool {
        self.stack.len() <= bounds.max_stack
            && self
                .locals
                .keys()
                .all(|&s| s <= bounds.max_local)
    }

    pub fn top(&self) -> Option<&ValueExpr> {
        self.stack.last()
    }

    pub fn local_slots(&self) -> impl Iterator<Item = u32> + '_ {
        self.locals.keys().copied()
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
        ValueLang::I32Sub([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I32Sub([a, b]))
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
        ValueLang::I32Eq([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I32Eq([a, b]))
        }
        ValueLang::I32Ne([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I32Ne([a, b]))
        }
        ValueLang::I32LtS([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I32LtS([a, b]))
        }
        ValueLang::I32LeS([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I32LeS([a, b]))
        }
        ValueLang::I32GtS([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I32GtS([a, b]))
        }
        ValueLang::I32Eqz([a]) => {
            let a = go_subtree(src, *a, dst, memo);
            dst.add(ValueLang::I32Eqz([a]))
        }
        ValueLang::I32Clz([a]) => {
            let a = go_subtree(src, *a, dst, memo);
            dst.add(ValueLang::I32Clz([a]))
        }
        ValueLang::I32Ctz([a]) => {
            let a = go_subtree(src, *a, dst, memo);
            dst.add(ValueLang::I32Ctz([a]))
        }
        ValueLang::I32Popcnt([a]) => {
            let a = go_subtree(src, *a, dst, memo);
            dst.add(ValueLang::I32Popcnt([a]))
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
    total_locals: u32,
    num_params: u32,
    max_stack: usize,
    segment_start_locals: BTreeMap<u32, ValueExpr>,
    fresh_counter: u32,
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

    pub fn function_entry(num_params: u32, total_locals: u32, max_stack: usize) -> Self {
        let mut locals = BTreeMap::new();
        for slot in 0..total_locals {
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
            total_locals,
            num_params,
            max_stack,
            segment_start_locals: BTreeMap::new(),
            fresh_counter: 0,
        }
    }

    pub fn begin_segment(&mut self) {
        self.segment_start_locals = self.locals.clone();
    }

    pub fn to_init_state(&self) -> SymState {
        let mut locals = BTreeMap::new();
        for slot in 0..self.num_params {
            locals.insert(slot, LocalReq::Need(Self::local_symbol(slot)));
        }
        SymState {
            stack: self.stack.clone(),
            locals,
        }
    }

    pub fn to_fin_state(&self) -> SymState {
        let mut locals = BTreeMap::new();
        for (&slot, cur) in &self.locals {
            if slot >= self.total_locals {
                continue;
            }
            match self.segment_start_locals.get(&slot) {
                Some(start) if start != cur => {
                    locals.insert(slot, LocalReq::Need(cur.clone()));
                }
                None => {
                    locals.insert(slot, LocalReq::Need(cur.clone()));
                }
                _ => {}
            }
        }
        SymState {
            stack: self.stack.clone(),
            locals,
        }
    }

    /// Init state for a sub-chunk starting at the current machine position.
    pub fn to_chunk_init_state(&self) -> SymState {
        SymState {
            stack: self.stack.clone(),
            locals: BTreeMap::new(),
        }
    }

    pub fn exec(&mut self, op: &SemOp) -> Result<(), ForwardError> {
        self.exec_with_meta(op).map(|_| ())
    }

    pub fn exec_with_meta(&mut self, op: &SemOp) -> Result<Option<OpaqueMeta>, ForwardError> {
        match op {
            SemOp::I32Const(n) => {
                self.push_expr(parse_value_expr(&n.to_string()))?;
                Ok(None)
            }
            SemOp::I32Add
            | SemOp::I32Sub
            | SemOp::I32Mul
            | SemOp::I32DivU
            | SemOp::I32DivS
            | SemOp::I32Shl
            | SemOp::I32Eq
            | SemOp::I32Ne
            | SemOp::I32LtS
            | SemOp::I32LeS
            | SemOp::I32GtS => {
                let b = self.pop()?;
                let a = self.pop()?;
                let expr = match op {
                    SemOp::I32Add => parse_value_expr(&format!("(i32.add {a} {b})")),
                    SemOp::I32Sub => parse_value_expr(&format!("(i32.sub {a} {b})")),
                    SemOp::I32Mul => parse_value_expr(&format!("(i32.mul {a} {b})")),
                    SemOp::I32DivU => parse_value_expr(&format!("(i32.div_u {a} {b})")),
                    SemOp::I32DivS => parse_value_expr(&format!("(i32.div_s {a} {b})")),
                    SemOp::I32Shl => parse_value_expr(&format!("(i32.shl {a} {b})")),
                    SemOp::I32Eq => parse_value_expr(&format!("(i32.eq {a} {b})")),
                    SemOp::I32Ne => parse_value_expr(&format!("(i32.ne {a} {b})")),
                    SemOp::I32LtS => parse_value_expr(&format!("(i32.lt_s {a} {b})")),
                    SemOp::I32LeS => parse_value_expr(&format!("(i32.le_s {a} {b})")),
                    SemOp::I32GtS => parse_value_expr(&format!("(i32.gt_s {a} {b})")),
                    _ => unreachable!(),
                };
                self.push_expr(expr)?;
                Ok(None)
            }
            SemOp::I32Eqz | SemOp::I32Clz | SemOp::I32Ctz | SemOp::I32Popcnt => {
                let a = self.pop()?;
                let expr = match op {
                    SemOp::I32Eqz => parse_value_expr(&format!("(i32.eqz {a})")),
                    SemOp::I32Clz => parse_value_expr(&format!("(i32.clz {a})")),
                    SemOp::I32Ctz => parse_value_expr(&format!("(i32.ctz {a})")),
                    SemOp::I32Popcnt => parse_value_expr(&format!("(i32.popcnt {a})")),
                    _ => unreachable!(),
                };
                self.push_expr(expr)?;
                Ok(None)
            }
            SemOp::LocalGet(slot) => {
                if *slot >= self.total_locals {
                    return Err(ForwardError::LocalOutOfRange);
                }
                let v = self
                    .locals
                    .get(slot)
                    .cloned()
                    .ok_or(ForwardError::UnknownLocal(*slot))?;
                self.push_expr(v)?;
                Ok(None)
            }
            SemOp::LocalSet(slot) => {
                if *slot >= self.total_locals {
                    return Err(ForwardError::LocalOutOfRange);
                }
                let v = self.pop()?;
                self.locals.insert(*slot, v);
                Ok(None)
            }
            SemOp::LocalTee(slot) => {
                if *slot >= self.total_locals {
                    return Err(ForwardError::LocalOutOfRange);
                }
                let v = self
                    .stack
                    .last()
                    .cloned()
                    .ok_or(ForwardError::StackUnderflow)?;
                self.locals.insert(*slot, v);
                Ok(None)
            }
            SemOp::I32Load { id, .. } => {
                let addr = self.pop()?;
                let sym = format!("?load_{id}");
                let results = vec![sym.clone()];
                self.push_expr(parse_value_expr(&sym))?;
                Ok(Some(OpaqueMeta::from_exec(
                    *id,
                    false,
                    vec![expr_name(&addr)],
                    results,
                )))
            }
            SemOp::I32Store { id, .. } => {
                let value = self.pop()?;
                let addr = self.pop()?;
                Ok(Some(OpaqueMeta::from_exec(
                    *id,
                    true,
                    vec![expr_name(&value), expr_name(&addr)],
                    vec![],
                )))
            }
            SemOp::Call {
                id,
                pops,
                pushes,
                ..
            } => {
                let mut inputs = Vec::with_capacity(*pops as usize);
                for _ in 0..*pops {
                    inputs.push(expr_name(&self.pop()?));
                }
                inputs.reverse();
                let mut results = Vec::with_capacity(*pushes as usize);
                for i in 0..*pushes {
                    let sym = format!("?call_{id}_{i}");
                    results.push(sym.clone());
                    self.push_expr(parse_value_expr(&sym))?;
                }
                Ok(Some(OpaqueMeta::from_exec(
                    *id,
                    true,
                    inputs,
                    results,
                )))
            }
            SemOp::GlobalGet { id, .. } => {
                let sym = format!("?global_get_{id}");
                let results = vec![sym.clone()];
                self.push_expr(parse_value_expr(&sym))?;
                Ok(Some(OpaqueMeta::from_exec(
                    *id,
                    false,
                    vec![],
                    results,
                )))
            }
            SemOp::GlobalSet { id, .. } => {
                let value = self.pop()?;
                Ok(Some(OpaqueMeta::from_exec(
                    *id,
                    true,
                    vec![expr_name(&value)],
                    vec![],
                )))
            }
        }
    }

    pub fn pop(&mut self) -> Result<ValueExpr, ForwardError> {
        self.stack.pop().ok_or(ForwardError::StackUnderflow)
    }

    pub fn apply_boundary_stack(&mut self, pop: usize, push: usize) -> Result<(), ForwardError> {
        for _ in 0..pop {
            self.pop()?;
        }
        for _ in 0..push {
            self.push_fresh_symbolic()?;
        }
        Ok(())
    }

    fn push_fresh_symbolic(&mut self) -> Result<(), ForwardError> {
        let name = format!("?S{}", self.fresh_counter);
        self.fresh_counter += 1;
        self.push_expr(parse_value_expr(&name))
    }

    fn push_expr(&mut self, expr: ValueExpr) -> Result<(), ForwardError> {
        if self.stack.len() >= self.max_stack {
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
    use crate::wasm::SegmentBounds;

    #[test]
    fn function_entry_matches_running_example_init() {
        let bounds = SegmentBounds::new(1, 4);
        let mut entry = SymMachine::function_entry(1, 1, bounds.max_stack);
        entry.begin_segment();
        let init_state = entry.to_init_state();
        let expected = init();
        assert_eq!(init_state.stack, expected.stack);
        assert_eq!(init_state.locals, expected.locals);
    }
}
