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
        ValueLang::I32RemU([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I32RemU([a, b]))
        }
        ValueLang::I32RemS([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I32RemS([a, b]))
        }
        ValueLang::I32And([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I32And([a, b]))
        }
        ValueLang::I32Or([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I32Or([a, b]))
        }
        ValueLang::I32Xor([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I32Xor([a, b]))
        }
        ValueLang::I32ShrU([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I32ShrU([a, b]))
        }
        ValueLang::I32ShrS([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I32ShrS([a, b]))
        }
        ValueLang::I32Rotl([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I32Rotl([a, b]))
        }
        ValueLang::I32Rotr([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I32Rotr([a, b]))
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
        ValueLang::I64Const(n) => dst.add(ValueLang::I64Const(*n)),
        ValueLang::I64Add([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I64Add([a, b]))
        }
        ValueLang::I64Sub([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I64Sub([a, b]))
        }
        ValueLang::I64Mul([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I64Mul([a, b]))
        }
        ValueLang::I64Shl([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I64Shl([a, b]))
        }
        ValueLang::I64DivU([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I64DivU([a, b]))
        }
        ValueLang::I64DivS([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I64DivS([a, b]))
        }
        ValueLang::I64RemU([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I64RemU([a, b]))
        }
        ValueLang::I64RemS([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I64RemS([a, b]))
        }
        ValueLang::I64And([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I64And([a, b]))
        }
        ValueLang::I64Or([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I64Or([a, b]))
        }
        ValueLang::I64Xor([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I64Xor([a, b]))
        }
        ValueLang::I64ShrU([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I64ShrU([a, b]))
        }
        ValueLang::I64ShrS([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I64ShrS([a, b]))
        }
        ValueLang::I64Rotl([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I64Rotl([a, b]))
        }
        ValueLang::I64Rotr([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I64Rotr([a, b]))
        }
        ValueLang::I64Eq([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I64Eq([a, b]))
        }
        ValueLang::I64Ne([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I64Ne([a, b]))
        }
        ValueLang::I64LtS([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I64LtS([a, b]))
        }
        ValueLang::I64LeS([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I64LeS([a, b]))
        }
        ValueLang::I64GtS([a, b]) => {
            let a = go_subtree(src, *a, dst, memo);
            let b = go_subtree(src, *b, dst, memo);
            dst.add(ValueLang::I64GtS([a, b]))
        }
        ValueLang::I64Eqz([a]) => {
            let a = go_subtree(src, *a, dst, memo);
            dst.add(ValueLang::I64Eqz([a]))
        }
        ValueLang::I64Clz([a]) => {
            let a = go_subtree(src, *a, dst, memo);
            dst.add(ValueLang::I64Clz([a]))
        }
        ValueLang::I64Ctz([a]) => {
            let a = go_subtree(src, *a, dst, memo);
            dst.add(ValueLang::I64Ctz([a]))
        }
        ValueLang::I64Popcnt([a]) => {
            let a = go_subtree(src, *a, dst, memo);
            dst.add(ValueLang::I64Popcnt([a]))
        }
        ValueLang::I64ExtendI32S([a]) => {
            let a = go_subtree(src, *a, dst, memo);
            dst.add(ValueLang::I64ExtendI32S([a]))
        }
        ValueLang::I64ExtendI32U([a]) => {
            let a = go_subtree(src, *a, dst, memo);
            dst.add(ValueLang::I64ExtendI32U([a]))
        }
        ValueLang::I32WrapI64([a]) => {
            let a = go_subtree(src, *a, dst, memo);
            dst.add(ValueLang::I32WrapI64([a]))
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

    /// Unknown stack slot entering a straight-line block (`?in_0`, …; SuperStack `in_0`).
    pub fn stack_input_symbol(index: usize) -> ValueExpr {
        parse_value_expr(&format!("?in_{index}"))
    }

    pub fn implicit_stack_inputs(count: usize) -> Vec<ValueExpr> {
        (0..count).map(Self::stack_input_symbol).collect()
    }

    /// Pre-seed the stack with `count` implicit inputs (bottom to top).
    pub fn seed_implicit_stack_inputs(&mut self, count: usize) {
        self.stack = Self::implicit_stack_inputs(count);
    }

    /// SuperStack-style entry: every local is an unknown `?L{i}` (not zero-initialized).
    pub fn function_entry(num_params: u32, total_locals: u32, max_stack: usize) -> Self {
        let mut locals = BTreeMap::new();
        for slot in 0..total_locals {
            locals.insert(slot, Self::local_symbol(slot));
        }
        Self {
            stack: Vec::new(),
            locals,
            total_locals,
            num_params,
            max_stack,
            segment_start_locals: BTreeMap::new(),
        }
    }

    /// Machine at segment/chunk entry: symbolic locals plus optional initial stack.
    pub fn from_segment_entry(
        num_params: u32,
        bounds: &SegmentBounds,
        init: &SymState,
        max_stack: usize,
    ) -> Self {
        let total_locals = bounds.max_local + 1;
        let mut m = Self::function_entry(num_params, total_locals, max_stack);
        m.stack = init.stack.clone();
        m.begin_segment();
        m
    }

    pub fn begin_segment(&mut self) {
        self.segment_start_locals = self.locals.clone();
    }

    pub fn to_init_state(&self) -> SymState {
        let mut locals = BTreeMap::new();
        for slot in 0..self.total_locals {
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

    /// Init state for a sub-chunk: carried stack plus every local as `?L{i}` (SuperStack per-chunk frame).
    pub fn to_chunk_init_state(&self) -> SymState {
        let mut locals = BTreeMap::new();
        for slot in 0..self.total_locals {
            locals.insert(slot, LocalReq::Need(Self::local_symbol(slot)));
        }
        SymState {
            stack: self.stack.clone(),
            locals,
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
            | SemOp::I32RemU
            | SemOp::I32RemS
            | SemOp::I32Shl
            | SemOp::I32And
            | SemOp::I32Or
            | SemOp::I32Xor
            | SemOp::I32ShrU
            | SemOp::I32ShrS
            | SemOp::I32Rotl
            | SemOp::I32Rotr
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
                    SemOp::I32RemU => parse_value_expr(&format!("(i32.rem_u {a} {b})")),
                    SemOp::I32RemS => parse_value_expr(&format!("(i32.rem_s {a} {b})")),
                    SemOp::I32Shl => parse_value_expr(&format!("(i32.shl {a} {b})")),
                    SemOp::I32And => parse_value_expr(&format!("(i32.and {a} {b})")),
                    SemOp::I32Or => parse_value_expr(&format!("(i32.or {a} {b})")),
                    SemOp::I32Xor => parse_value_expr(&format!("(i32.xor {a} {b})")),
                    SemOp::I32ShrU => parse_value_expr(&format!("(i32.shr_u {a} {b})")),
                    SemOp::I32ShrS => parse_value_expr(&format!("(i32.shr_s {a} {b})")),
                    SemOp::I32Rotl => parse_value_expr(&format!("(i32.rotl {a} {b})")),
                    SemOp::I32Rotr => parse_value_expr(&format!("(i32.rotr {a} {b})")),
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
            SemOp::Drop => {
                self.pop()?;
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
            SemOp::Opaque {
                id,
                pops,
                pushes,
                storage,
            } => {
                let mut inputs = Vec::with_capacity(*pops as usize);
                for _ in 0..*pops {
                    inputs.push(expr_name(&self.pop()?));
                }
                inputs.reverse();
                let mut results = Vec::with_capacity(*pushes as usize);
                for i in 0..*pushes {
                    let sym = format!("?opaque_{id}_{i}");
                    results.push(sym.clone());
                    self.push_expr(parse_value_expr(&sym))?;
                }
                Ok(Some(OpaqueMeta::from_exec(
                    *id,
                    *storage,
                    inputs,
                    results,
                )))
            }
        }
    }

    pub fn pop(&mut self) -> Result<ValueExpr, ForwardError> {
        self.stack.pop().ok_or(ForwardError::StackUnderflow)
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

    #[test]
    fn implicit_stack_inputs_seed_local_tee() {
        let bounds = SegmentBounds::new(3, 4);
        let mut machine = SymMachine::function_entry(0, 3, bounds.max_stack);
        machine.seed_implicit_stack_inputs(1);
        machine.begin_segment();
        machine.exec(&SemOp::LocalTee(2)).expect("local.tee with implicit input");
        let fin = machine.to_fin_state();
        assert_eq!(fin.stack.len(), 1);
        assert!(matches!(
            fin.locals.get(&2),
            Some(LocalReq::Need(v)) if v.to_string() == "?in_0"
        ));
    }
}
