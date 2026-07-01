//! Symbolic machine state and forward execution (shared by wasm parsing and optimization).

use crate::lang::{F32Bits, F64Bits, ValueLang};
use crate::semantics::{sem_to_value_op, SemOp};
use crate::value::ValueOp;
use crate::wasm::{OpaqueMeta, SegmentBounds};
use egg::{Id, RecExpr, Symbol};
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
        self.stack.len() <= bounds.max_stack && self.locals.keys().all(|&s| s <= bounds.max_local)
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
    memo: &mut HashMap<(*const ValueExpr, Id), Id>,
) -> Id {
    let key = (std::ptr::from_ref(src), id);
    if let Some(&mapped) = memo.get(&key) {
        return mapped;
    }
    let mapped = match &src[id] {
        ValueLang::I32Const(n) => dst.add(ValueLang::I32Const(*n)),
        ValueLang::I64Const(n) => dst.add(ValueLang::I64Const(*n)),
        ValueLang::F32Const(n) => dst.add(ValueLang::F32Const(*n)),
        ValueLang::F64Const(n) => dst.add(ValueLang::F64Const(*n)),
        ValueLang::Symbol(s) => dst.add(ValueLang::Symbol(s.clone())),
        node => {
            let (op, child_ids) = crate::value::ValueOp::from_lang(node)
                .unwrap_or_else(|| panic!("unsupported ValueLang: {node:?}"));
            let kids: Vec<Id> = child_ids
                .iter()
                .map(|&c| go_subtree(src, c, dst, memo))
                .collect();
            dst.add(op.to_enode(&kids))
        }
    };
    memo.insert(key, mapped);
    mapped
}

pub fn all_subtree_exprs(expr: &ValueExpr) -> Vec<ValueExpr> {
    (0..expr.len())
        .map(|i| subtree_expr(expr, Id::from(i)))
        .collect()
}

fn expr_root(expr: &ValueExpr) -> Id {
    Id::from(expr.len() - 1)
}

fn symbol_expr(name: &str) -> ValueExpr {
    let mut dst = RecExpr::default();
    dst.add(ValueLang::Symbol(Symbol::from(name)));
    dst
}

fn i32_const_expr(n: i32) -> ValueExpr {
    let mut dst = RecExpr::default();
    dst.add(ValueLang::I32Const(n));
    dst
}

fn i64_const_expr(n: i64) -> ValueExpr {
    let mut dst = RecExpr::default();
    dst.add(ValueLang::I64Const(n));
    dst
}

fn apply_value_op(vop: ValueOp, args: &[ValueExpr]) -> ValueExpr {
    let mut dst = RecExpr::default();
    let mut memo = HashMap::new();
    let arg_ids: Vec<Id> = args
        .iter()
        .map(|arg| go_subtree(arg, expr_root(arg), &mut dst, &mut memo))
        .collect();
    dst.add(vop.to_enode(&arg_ids));
    dst
}

#[derive(Debug, Clone)]
pub struct SymMachine {
    stack: Vec<ValueExpr>,
    locals: BTreeMap<u32, ValueExpr>,
    total_locals: u32,
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
        symbol_expr(&format!("?L{slot}"))
    }

    /// Unknown stack slot entering a straight-line block (`?in_0`, …; SuperStack `in_0`).
    pub fn stack_input_symbol(index: usize) -> ValueExpr {
        symbol_expr(&format!("?in_{index}"))
    }

    pub fn implicit_stack_inputs(count: usize) -> Vec<ValueExpr> {
        (0..count).map(Self::stack_input_symbol).collect()
    }

    /// Pre-seed the stack with `count` implicit inputs (bottom to top).
    pub fn seed_implicit_stack_inputs(&mut self, count: usize) {
        self.stack = Self::implicit_stack_inputs(count);
    }

    /// SuperStack-style entry: every local is an unknown `?L{i}` (not zero-initialized).
    pub fn function_entry(_num_params: u32, total_locals: u32, max_stack: usize) -> Self {
        let mut locals = BTreeMap::new();
        for slot in 0..total_locals {
            locals.insert(slot, Self::local_symbol(slot));
        }
        Self {
            stack: Vec::new(),
            locals,
            total_locals,
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
        for (&slot, req) in &init.locals {
            if slot >= total_locals {
                continue;
            }
            if let LocalReq::Need(v) = req {
                m.locals.insert(slot, v.clone());
            }
        }
        m.begin_segment();
        m
    }

    pub fn begin_segment(&mut self) {
        self.segment_start_locals = self.locals.clone();
    }

    #[cfg(test)]
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

    /// Init state for a split sub-chunk: carried stack and actual symbolic local values.
    pub fn to_carried_init_state(&self) -> SymState {
        let mut locals = BTreeMap::new();
        for slot in 0..self.total_locals {
            if let Some(v) = self.locals.get(&slot) {
                locals.insert(slot, LocalReq::Need(v.clone()));
            }
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
                self.push_expr(i32_const_expr(*n))?;
                Ok(None)
            }
            SemOp::I64Const(n) => {
                self.push_expr(i64_const_expr(*n))?;
                Ok(None)
            }
            SemOp::F32Const(bits) => {
                let mut expr = RecExpr::default();
                expr.add(ValueLang::F32Const(F32Bits(*bits)));
                self.push_expr(expr)?;
                Ok(None)
            }
            SemOp::F64Const(bits) => {
                let mut expr = RecExpr::default();
                expr.add(ValueLang::F64Const(F64Bits(*bits)));
                self.push_expr(expr)?;
                Ok(None)
            }
            SemOp::Pure(_)
            | SemOp::I32Add
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
            | SemOp::I32GtS
            | SemOp::I32Eqz
            | SemOp::I32Clz
            | SemOp::I32Ctz
            | SemOp::I32Popcnt => {
                let vop = sem_to_value_op(op).expect("pure op");
                let expr = if vop.pops().len() == 2 {
                    let b = self.pop()?;
                    let a = self.pop()?;
                    apply_value_op(vop, &[a, b])
                } else {
                    let a = self.pop()?;
                    apply_value_op(vop, &[a])
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
                self.push_expr(symbol_expr(&sym))?;
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
                id, pops, pushes, ..
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
                    self.push_expr(symbol_expr(&sym))?;
                }
                Ok(Some(OpaqueMeta::from_exec(*id, true, inputs, results)))
            }
            SemOp::GlobalGet { id, .. } => {
                let sym = format!("?global_get_{id}");
                let results = vec![sym.clone()];
                self.push_expr(symbol_expr(&sym))?;
                Ok(Some(OpaqueMeta::from_exec(*id, false, vec![], results)))
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
                    self.push_expr(symbol_expr(&sym))?;
                }
                Ok(Some(OpaqueMeta::from_exec(*id, *storage, inputs, results)))
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
    use crate::value::parse_value_expr;
    use crate::wasm::SegmentBounds;

    #[test]
    fn apply_value_op_preserves_distinct_single_node_roots() {
        let a = SymMachine::local_symbol(0);
        let b = i32_const_expr(1);
        let got = apply_value_op(ValueOp::I32Shl, &[a, b]);
        assert_eq!(got.to_string(), "(i32.shl ?L0 1)");
    }

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
    fn from_segment_entry_applies_carried_locals() {
        let bounds = SegmentBounds::new(5, 4);
        let mut init_locals = BTreeMap::new();
        for slot in 0..=4 {
            init_locals.insert(slot, LocalReq::Need(SymMachine::local_symbol(slot)));
        }
        init_locals.insert(
            3,
            LocalReq::Need(parse_value_expr("(i32.add (i32.add (i32.add ?L3 1) 1) 1)")),
        );
        let init = SymState {
            stack: vec![],
            locals: init_locals,
        };
        let mut m = SymMachine::from_segment_entry(0, &bounds, &init, bounds.max_stack);
        m.exec(&SemOp::LocalGet(3)).unwrap();
        m.exec(&SemOp::I32Const(1)).unwrap();
        m.exec(&SemOp::I32Add).unwrap();
        m.exec(&SemOp::LocalSet(3)).unwrap();
        let fin = m.to_fin_state();
        assert!(matches!(
            fin.locals.get(&3),
            Some(LocalReq::Need(v)) if v.to_string().contains("?L3")
        ));
        let got = fin.locals.get(&3).unwrap();
        let expected = parse_value_expr("(i32.add (i32.add (i32.add (i32.add ?L3 1) 1) 1) 1)");
        assert_eq!(got, &LocalReq::Need(expected));
    }

    #[test]
    fn i64_add_builds_expr_tree_not_opaque() {
        let bounds = SegmentBounds::new(1, 8);
        let mut m = SymMachine::function_entry(0, 1, bounds.max_stack);
        m.begin_segment();
        m.exec(&SemOp::I64Const(1)).unwrap();
        m.exec(&SemOp::I64Const(2)).unwrap();
        m.exec(&SemOp::Pure(crate::value::ValueOp::I64Add))
            .unwrap();
        let top = m.to_fin_state().stack.last().expect("top").to_string();
        assert!(top.contains("i64.add"), "expected expr tree, got {top}");
        assert!(!top.contains("?opaque_"), "i64.add must not be opaque: {top}");
    }

    #[test]
    fn implicit_stack_inputs_seed_local_tee() {
        let bounds = SegmentBounds::new(3, 4);
        let mut machine = SymMachine::function_entry(0, 3, bounds.max_stack);
        machine.seed_implicit_stack_inputs(1);
        machine.begin_segment();
        machine
            .exec(&SemOp::LocalTee(2))
            .expect("local.tee with implicit input");
        let fin = machine.to_fin_state();
        assert_eq!(fin.stack.len(), 1);
        assert!(matches!(
            fin.locals.get(&2),
            Some(LocalReq::Need(v)) if v.to_string() == "?in_0"
        ));
    }
}
