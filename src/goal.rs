//! Machine goals for backward search (stack + locals).

use crate::canon::Canonizer;
use crate::lang::ValueLang;
use crate::value::parse_value_expr;
use egg::{Id, RecExpr};
use std::collections::{BTreeMap, HashMap};

pub const MAX_STACK_HEIGHT: usize = 4;
pub const MAX_LOCAL_SLOT: u32 = 2;

pub type ValueExpr = RecExpr<ValueLang>;

/// Local slot requirement in a residual goal: don't-care (⋆) or a needed value expression.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LocalReq {
    /// Slot may hold any value (⋆).
    DontCare,
    /// Slot must hold this value (compared via canonicalization).
    Need(ValueExpr),
}

/// Residual goal: operand stack (bottom-to-top) plus local slot requirements.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineState {
    pub stack: Vec<ValueExpr>,
    pub locals: BTreeMap<u32, LocalReq>,
}

impl MachineState {
    pub fn validate_bounds(&self) -> bool {
        self.stack.len() <= MAX_STACK_HEIGHT
            && self
                .locals
                .keys()
                .all(|&s| s <= MAX_LOCAL_SLOT)
    }

    pub fn top(&self) -> Option<&ValueExpr> {
        self.stack.last()
    }

    pub fn is_grounded(&self, init: &MachineState, canon: &mut Canonizer) -> bool {
        if self.stack.len() != init.stack.len() {
            return false;
        }
        for (a, b) in self.stack.iter().zip(init.stack.iter()) {
            if canon.canon(a) != canon.canon(b) {
                return false;
            }
        }
        for slot in 0..=MAX_LOCAL_SLOT {
            let cur = self.locals.get(&slot);
            let expected = init.locals.get(&slot);
            match (cur, expected) {
                (None | Some(LocalReq::DontCare), None) => {}
                (Some(LocalReq::DontCare), _) | (None, Some(LocalReq::DontCare)) => {}
                (Some(LocalReq::Need(v)), Some(LocalReq::Need(init_v))) => {
                    if canon.canon(v) != canon.canon(init_v) {
                        return false;
                    }
                }
                _ => return false,
            }
        }
        true
    }
}

/// Concrete evaluation for forward verification (`?L0` only).
pub fn eval_value(expr: &ValueExpr, l0: i32) -> i32 {
    eval_id(expr, expr.root(), l0)
}

fn eval_id(expr: &ValueExpr, id: Id, l0: i32) -> i32 {
    match &expr[id] {
        ValueLang::I32Const(n) => *n,
        ValueLang::Symbol(sym) => {
            if sym.to_string() == "?L0" {
                l0
            } else {
                panic!("unknown symbol {sym}")
            }
        }
        ValueLang::I32Add([a, b]) => eval_id(expr, *a, l0).wrapping_add(eval_id(expr, *b, l0)),
        ValueLang::I32Mul([a, b]) => eval_id(expr, *a, l0).wrapping_mul(eval_id(expr, *b, l0)),
        ValueLang::I32DivU([a, b]) => {
            let d = eval_id(expr, *b, l0);
            if d == 0 {
                0
            } else {
                eval_id(expr, *a, l0).wrapping_div(d)
            }
        }
        ValueLang::I32DivS([a, b]) => {
            let d = eval_id(expr, *b, l0);
            if d == 0 {
                0
            } else {
                eval_id(expr, *a, l0).wrapping_div(d)
            }
        }
        ValueLang::I32Shl([a, b]) => {
            let s = eval_id(expr, *b, l0) & 31;
            eval_id(expr, *a, l0).wrapping_shl(s as u32)
        }
    }
}

pub fn concrete_stack(state: &MachineState, l0: i32) -> Vec<i32> {
    state
        .stack
        .iter()
        .map(|e| eval_value(e, l0))
        .collect()
}

pub fn concrete_local(state: &MachineState, slot: u32, l0: i32) -> Option<i32> {
    match state.locals.get(&slot)? {
        LocalReq::DontCare => None,
        LocalReq::Need(e) => Some(eval_value(e, l0)),
    }
}

/// Build a `RecExpr` containing only the subtree at `node`.
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

