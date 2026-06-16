//! Meta-level AL AST (instantiation-time only).
//!
//! Types for representing SpecTec AL steps and expressions before lowering to
//! flat [`AlSpec`](super::ir::AlSpec). Definitions live in [`super::binop_defs`].
//!
//! [`AlMetaExpr`] arithmetic/bitwise variants (`Add`, `Sub`, `Mul`, `Mod`, `Rem`,
//! `Shl`, `BitAnd`, `BitOr`, …) encode only what `Language.md` treats as primitive
//! `binop` / `unop` — not thin spectec helper `$fn`s like `$iadd_`.

use super::ir::{NumType, Sign, WasmBinOp};

/// Wasm value type for `$size` (binop.al L17–34).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ValType {
    I32,
    I64,
    F32,
    F64,
    V128,
}

/// Argument to a meta-level `$fn(...)` call.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AlMetaArg {
    NumType(NumType),
    ValType(ValType),
    BinOp(WasmBinOp),
    Var(&'static str),
    Nat(u32),
    Sign(Sign),
    Expr(Box<AlMetaExpr>),
}

/// Meta-level expression (steps and `$fn` bodies).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AlMetaExpr {
    /// `$name(args...)`
    Call(&'static str, Vec<AlMetaArg>),
    /// `|expr| <= 0` — optional/list is empty (ε).
    OptionalLen(Box<AlMetaExpr>),
    /// `choose(expr)` — extract value from singleton optional/list.
    Choose(Box<AlMetaExpr>),
    /// `top_value(nt)` — stack type assertion.
    TopValue(NumType),
    /// Formal parameter reference.
    Param(&'static str),
    NatLit(u32),
    IntLit(i32),
    ValTypeLit(ValType),
    SignLit(Sign),
    BinOpLit(WasmBinOp),
    /// `?()` — empty optional.
    EmptyOpt,
    /// `?(expr)` — singleton optional.
    SomeOpt(Box<AlMetaExpr>),
    /// `[]` — empty list.
    EmptyList,
    /// `[expr]` — singleton list.
    SingletonList(Box<AlMetaExpr>),
    /// `$int$(e)`
    IntCoerce(Box<AlMetaExpr>),
    /// `$nat$(e)`
    NatCoerce(Box<AlMetaExpr>),
    /// `$rat$(e)`
    RatCoerce(Box<AlMetaExpr>),
    /// `$truncz$(e)`
    TruncZ(Box<AlMetaExpr>),
    Add(Box<AlMetaExpr>, Box<AlMetaExpr>),
    Sub(Box<AlMetaExpr>, Box<AlMetaExpr>),
    Mul(Box<AlMetaExpr>, Box<AlMetaExpr>),
    Div(Box<AlMetaExpr>, Box<AlMetaExpr>),
    /// `a \ b` — natural modulus.
    Mod(Box<AlMetaExpr>, Box<AlMetaExpr>),
    /// `a % b` — natural remainder (bit-width mask for shifts).
    Rem(Box<AlMetaExpr>, Box<AlMetaExpr>),
    /// `a << b` — natural left shift.
    Shl(Box<AlMetaExpr>, Box<AlMetaExpr>),
    /// `a & b` — bitwise and (Language.md `binop`).
    BitAnd(Box<AlMetaExpr>, Box<AlMetaExpr>),
    /// `a | b` — bitwise or (Language.md `binop`).
    BitOr(Box<AlMetaExpr>, Box<AlMetaExpr>),
    /// `a ^ b` — bitwise xor (`$ixor_`, spectec builtin).
    BitXor(Box<AlMetaExpr>, Box<AlMetaExpr>),
    Pow(Box<AlMetaExpr>, Box<AlMetaExpr>),
    Neg(Box<AlMetaExpr>),
    /// Extract `sx` from `(DIV sx)` / `(REM sx)` / `(SHR sx)`.
    BinOpSignOf(Box<AlMetaExpr>),
}

/// Meta-level predicate in `If` / `Assert`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AlMetaPred {
    Eq(AlMetaExpr, AlMetaExpr),
    Lt(AlMetaExpr, AlMetaExpr),
    Le(AlMetaExpr, AlMetaExpr),
    And(Box<AlMetaPred>, Box<AlMetaPred>),
    /// `~(expr != None)` — optional is empty.
    OptIsNone(AlMetaExpr),
    /// `type(param) == Inn`
    TypeIsInn(AlMetaExpr),
    /// `type(param) == Fnn`
    TypeIsFnn(AlMetaExpr),
    /// `param = ADD` etc.
    BinOpEq(AlMetaExpr, WasmBinOp),
    /// `case(param) == DIV|REM|SHR`
    BinOpCaseIs(AlMetaExpr, BinOpCase),
}

/// `case(binop_)` variants used in binop.al.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOpCase {
    Div,
    Rem,
    Shr,
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

/// Meta-level step in a `$fn` body (binop.al L17+).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AlMetaFnStep {
    If {
        cond: AlMetaPred,
        then_steps: Vec<AlMetaFnStep>,
        else_steps: Vec<AlMetaFnStep>,
    },
    Assert(AlMetaPred),
    Let {
        name: &'static str,
        expr: AlMetaExpr,
    },
    /// `Let (DIV sx) = binop_` — bind sign from a case binop.
    LetBinOpCase {
        case: BinOpCase,
        sx_name: &'static str,
        binop: AlMetaExpr,
    },
    Return(AlMetaExpr),
    Fail,
}

/// Spectec type of a formal parameter in a `$fn` definition.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AlMetaParamType {
    Nat,
    Int,
    ValType,
    NumType,
    Sign,
    BinOp,
    /// Polymorphic / pass-through (e.g. `X`, `X_opt` in `$list_`).
    Any,
}

/// Named formal parameter of a `$fn` definition.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AlMetaParam {
    pub name: &'static str,
    pub ty: AlMetaParamType,
}

/// SpecTec AL function definition (`name params { ... }`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AlMetaFnDef {
    pub name: &'static str,
    pub params: &'static [AlMetaParam],
    pub body: Vec<AlMetaFnStep>,
}

/// Pretty-print `Step_pure/binop` meta template with `$binop_` call visible.
pub fn format_meta_binop_pretty(nt: NumType, binop: WasmBinOp) -> String {
    let partial = if binop.is_partial() { "yes" } else { "no" };
    format!(
        "Step_pure/binop {nt:?} {binop:?}\n\
           assert top_value({nt:?})\n\
           pop c_2\n\
           assert top_value({nt:?})\n\
           pop c_1\n\
           if |$binop_({nt:?}, {binop:?}, c_1, c_2)| <= 0 then\n\
             trap\n\
           else\n\
             let c = choose($binop_({nt:?}, {binop:?}, c_1, c_2))\n\
             push const({nt:?}, c)\n\
         (partial via $binop_: {partial})"
    )
}
