//! Meta-level AL AST (instantiation-time only).
//!
//! Types for representing SpecTec AL steps and expressions before lowering to
//! flat [`AlSpec`](super::ir::AlSpec). Definitions live in [`super::binop_defs`].

use super::ir::{BinOpKind, NumType, Sign, WasmBinOp};

/// Argument to a meta-level `$fn(...)` call.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[allow(dead_code)] // Nat, Sign used when more binop.al defs are wired in
pub enum AlMetaArg {
    NumType(NumType),
    BinOp(WasmBinOp),
    Var(&'static str),
    Nat(u32),
    Sign(Sign),
}

/// Meta-level expression.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AlMetaExpr {
    /// `$name(args...)`
    Call(&'static str, Vec<AlMetaArg>),
    /// `|expr| <= 0` — optional/list is empty (ε).
    OptionalLen(Box<AlMetaExpr>),
    /// `choose(expr)` — extract value from singleton optional.
    Choose(Box<AlMetaExpr>),
    /// `top_value(nt)` — stack type assertion.
    TopValue(NumType),
}

/// Typed pop pattern (`numtype_0.CONST name` in AL).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PopPattern {
    NumConst(&'static str),
}

/// Meta-level step (`Step_pure/...` templates).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AlMetaStep {
    Assert(AlMetaExpr),
    Pop(PopPattern),
    Let {
        name: &'static str,
        expr: AlMetaExpr,
    },
    If {
        cond: AlMetaExpr,
        then_steps: Vec<AlMetaStep>,
        else_steps: Vec<AlMetaStep>,
    },
    Push(AlMetaExpr),
    Trap,
}

/// Result of partially evaluating `$binop_(nt, binop, c_1, c_2)` for fixed `nt`/`binop`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BinopInstantiation {
    pub kind: BinOpKind,
    pub is_partial: bool,
    pub lhs: &'static str,
    pub rhs: &'static str,
}
