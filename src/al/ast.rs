//! AL AST — mirrors [`spectec/src/al/ast.ml`](../../spectec/spectec/src/al/ast.ml).
//!
//! Flattened instruction specs live in [`super::ir`](super::ir) (`AlSpec` / `AlStep`).

#![allow(dead_code)] // mirrors spectec/*.al; not every node is wired to the live pipeline yet

pub use super::defs::{
    BinOpCase, NumType, RelOpCase, Sign, UnOpCase, ValType, WasmBinOp, WasmRelOp, WasmTestOp,
    WasmUnOp,
};

/// Formal parameter of a [`FuncA`] (`arg list` in OCaml; name + type for transcribed defs).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Param {
    /// Parameter name in AL source (e.g. `N`, `i_1`, `numtype`).
    pub name: &'static str,
    /// Spectec type used when binding arguments at call sites.
    pub ty: ParamType,
}

/// Spectec type of a [`Param`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParamType {
    /// Non-negative integer (`nat`).
    Nat,
    /// Mathematical integer (`int`).
    Int,
    /// Wasm value type (`I32`, `F64`, …).
    ValType,
    /// Wasm numeric type (`I32`, `I64`, …).
    NumType,
    /// Signedness flag (`S` / `U`) for div/rem/shr.
    Sign,
    /// Wasm binary operator case (`ADD`, `DIV S`, …).
    BinOp,
    /// Wasm relational operator case (`EQ`, `LT S`, …).
    RelOp,
    /// Wasm test operator case (`EQZ`, …).
    TestOp,
    /// Wasm unary operator case (`CLZ`, `ABS`, …).
    UnOp,
    /// Polymorphic / pass-through (e.g. `X`, `X_opt` in `$list_`).
    Any,
}

/// Call / rule argument (`arg'` in OCaml).
///
/// Literal variants are shorthand for [`Arg::ExpA`]; OCaml uses only `ExpA` / `TypA` / `DefA`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Arg {
    /// `ExpA` — numeric type literal.
    NumType(NumType),
    /// `ExpA` — value type literal.
    ValType(ValType),
    /// `ExpA` — binop case literal.
    BinOp(WasmBinOp),
    /// `ExpA` — relop case literal.
    RelOp(WasmRelOp),
    /// `ExpA` — testop case literal.
    TestOp(WasmTestOp),
    /// `ExpA` — unop case literal.
    UnOp(WasmUnOp),
    /// `ExpA` — `VarE` reference.
    Var(&'static str),
    /// `ExpA` — `NumE` (nat).
    Nat(u32),
    /// `ExpA` — sign literal.
    Sign(Sign),
    /// `ExpA` — arbitrary nested expression (`arg'` = `ExpA of expr`).
    ExpA(Box<Expr>),
}

/// AL expression (`expr'` in OCaml; subset used by transcribed `binop.al`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    /// `CallE` — call helper or builtin (`$binop_(…)`, `const(…)`, …).
    Call(&'static str, Vec<Arg>),
    /// `LenE` — `|expr|`; used as `|…| <= 0` empty optional/list test in rules.
    OptionalLen(Box<Expr>),
    /// `ChooseE` — extract the element of a singleton optional/list.
    Choose(Box<Expr>),
    /// `TopValueE` — stack-top type assertion (`top_value(nt)`).
    TopValue(NumType),
    /// `TopValueE` with no type — `top_value()`.
    TopValueAny,
    /// `CaseE` — Wasm instruction or constructor (`LOCAL.SET x`, …).
    CaseE(&'static str, Vec<Expr>),
    /// `VarE` — bound variable reference.
    VarE(&'static str),
    /// `NumE` — natural literal.
    NatLit(u32),
    /// `NumE` — integer literal.
    IntLit(i32),
    /// Value-type literal (e.g. `I32` in `$size(I32)`).
    ValTypeLit(ValType),
    /// Sign literal (`S` / `U`).
    SignLit(Sign),
    /// Binop case literal (`ADD`, `DIV S`, …).
    BinOpLit(WasmBinOp),
    /// Relop case literal (`EQ`, `LT S`, …).
    RelOpLit(WasmRelOp),
    /// Testop case literal (`EQZ`, …).
    TestOpLit(WasmTestOp),
    /// Unop case literal (`CLZ`, `ABS`, …).
    UnOpLit(WasmUnOp),
    /// Boolean literal (`true` / `false` in `$bool`).
    BoolLit(bool),
    /// Boolean equality (`a = b` inside `$bool(…)`).
    Eq(Box<Expr>, Box<Expr>),
    /// Boolean inequality (`a =/= b` inside `$bool(…)`).
    Ne(Box<Expr>, Box<Expr>),
    /// Boolean less-than (`a < b` inside `$bool(…)`).
    LtCmp(Box<Expr>, Box<Expr>),
    /// Boolean less-or-equal (`a <= b` inside `$bool(…)`).
    LeCmp(Box<Expr>, Box<Expr>),
    /// Boolean greater-than (`a > b` inside `$bool(…)`).
    GtCmp(Box<Expr>, Box<Expr>),
    /// Boolean greater-or-equal (`a >= b` inside `$bool(…)`).
    GeCmp(Box<Expr>, Box<Expr>),
    /// Empty optional `ε` (`?()`).
    EmptyOpt,
    /// Singleton optional (`?(value)`).
    SomeOpt(Box<Expr>),
    /// Empty list `[]`.
    EmptyList,
    /// Singleton list `[value]`.
    SingletonList(Box<Expr>),
    /// `$int$(e)` — `CvtE` to `int`.
    IntCoerce(Box<Expr>),
    /// `$nat$(e)` — `CvtE` to `nat`.
    NatCoerce(Box<Expr>),
    /// `$rat$(e)` — `CvtE` to `rat`.
    RatCoerce(Box<Expr>),
    /// `$truncz$(e)` — truncate rational toward zero.
    TruncZ(Box<Expr>),
    /// `BinE Add`.
    Add(Box<Expr>, Box<Expr>),
    /// `BinE Sub`.
    Sub(Box<Expr>, Box<Expr>),
    /// `BinE Mul`.
    Mul(Box<Expr>, Box<Expr>),
    /// `BinE Div` on rationals.
    Div(Box<Expr>, Box<Expr>),
    /// `a \ b` — natural modulus.
    Mod(Box<Expr>, Box<Expr>),
    /// `a % b` — natural remainder (bit-width mask for shifts).
    Rem(Box<Expr>, Box<Expr>),
    /// `a << b` — natural left shift.
    Shl(Box<Expr>, Box<Expr>),
    /// Bitwise and.
    BitAnd(Box<Expr>, Box<Expr>),
    /// Bitwise or.
    BitOr(Box<Expr>, Box<Expr>),
    /// Bitwise xor (`$ixor_`).
    BitXor(Box<Expr>, Box<Expr>),
    /// Logical right shift (`$ishr_` U).
    LShr(Box<Expr>, Box<Expr>),
    /// Arithmetic right shift (`$ishr_` S).
    AShr(Box<Expr>, Box<Expr>),
    /// Rotate left (`$irotl_`).
    Rotl(Box<Expr>, Box<Expr>),
    /// Rotate right (`$irotr_`).
    Rotr(Box<Expr>, Box<Expr>),
    /// `BinE Pow` — exponentiation.
    Pow(Box<Expr>, Box<Expr>),
    /// `UnE` negation on integers.
    Neg(Box<Expr>),
    /// Extract `sx` from a case binop (`DIV sx`, `REM sx`, `SHR sx`).
    BinOpSignOf(Box<Expr>),
    /// Field / index access (`expr.path` / `expr[idx]`).
    AccE(Box<Expr>, Path),
}

/// Path segment in [`Expr::AccE`] (`f.LOCALS`, `arr[i]`, …).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Path {
    /// `.atom`
    Dot(&'static str),
    /// `[expr]`
    Idx(Box<Expr>),
}

/// Predicate for [`FuncA`] `IfI` / `AssertI` conditions.
///
/// In OCaml these are plain `expr` inside `IfI` / `AssertI`; egraph keeps a separate
/// `Pred` for transcribed helper definitions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Pred {
    /// `expr = expr`.
    Eq(Expr, Expr),
    /// `expr < expr`.
    Lt(Expr, Expr),
    /// `expr <= expr`.
    Le(Expr, Expr),
    /// `expr > expr`.
    Gt(Expr, Expr),
    /// `expr >= expr`.
    Ge(Expr, Expr),
    /// `expr =/= expr`.
    Ne(Expr, Expr),
    /// Conjunction of two predicates.
    And(Box<Pred>, Box<Pred>),
    /// Optional/list is empty (`|expr| <= 0` / `~(expr != None)`).
    OptIsNone(Expr),
    /// `type(expr) == Inn`.
    TypeIsInn(Expr),
    /// `type(expr) == Fnn`.
    TypeIsFnn(Expr),
    /// `expr` is a specific [`NumType`] literal.
    NumTypeEq(Expr, NumType),
    /// Binop parameter equals a case (`param = ADD`).
    BinOpEq(Expr, WasmBinOp),
    /// Binop parameter is a signed div/rem/shr case.
    BinOpCaseIs(Expr, BinOpCase),
    /// Relop parameter equals a case (`param = EQ`).
    RelOpEq(Expr, WasmRelOp),
    /// Relop parameter is a signed lt/gt/le/ge case.
    RelOpCaseIs(Expr, RelOpCase),
    /// Testop parameter equals a case (`param = EQZ`).
    TestOpEq(Expr, WasmTestOp),
    /// Unop parameter equals a case (`param = CLZ`).
    UnOpEq(Expr, WasmUnOp),
    /// Unop parameter is an extend case.
    UnOpCaseIs(Expr, UnOpCase),
}

/// Condition operand for [`Instr::IfI`] and [`Instr::AssertI`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InstrCond {
    /// Boolean/numeric expression (used in [`Algorithm::RuleA`] bodies).
    Expr(Expr),
    /// Predicate (used in [`FuncA`] bodies).
    Pred(Pred),
}

/// Left-hand side of [`Instr::LetI`] (`let lhs = expr` in AL; OCaml `LetI of expr * expr`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LetLhs {
    /// Simple variable binding (`let c = …`).
    Var(&'static str),
    /// Destructure sign from a case binop (`let (DIV sx) = binop_`).
    BinOpCase(BinOpCase, &'static str),
    /// Destructure sign from a case relop (`let (LT sx) = relop_`).
    RelOpCase(RelOpCase, &'static str),
    /// Destructure width from a case unop (`let (EXTEND M) = unop_`).
    UnOpCase(UnOpCase, &'static str),
}

/// Operand of [`Instr::PopI`] (`PopI of expr` in OCaml).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PopTarget {
    /// Pop a numeric stack value into `name` (`numtype_0.CONST name`).
    NumConst(&'static str),
    /// Pop any stack value into `name` (`Pop val`).
    Val(&'static str),
}

/// AL instruction (`instr'` in OCaml). Shared by [`Algorithm::RuleA`] and [`FuncA`] bodies.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Instr {
    /// `if cond then … else …` (`IfI of expr * instr list * instr list`).
    IfI {
        /// Branch condition (expression in rules, predicate in helpers).
        cond: InstrCond,
        /// Steps executed when the condition is true (or empty-list / trap branch).
        then_steps: Vec<Instr>,
        /// Steps executed when the condition is false.
        else_steps: Vec<Instr>,
    },
    /// `assert cond` (`AssertI of expr`).
    AssertI(InstrCond),
    /// `pop pattern` (`PopI of expr`).
    PopI(PopTarget),
    /// `let lhs = expr` (`LetI of expr * expr`).
    LetI {
        /// Variable or case pattern to bind.
        lhs: LetLhs,
        /// Right-hand side expression.
        expr: Expr,
    },
    /// `push expr` (`PushI of expr`).
    PushI(Expr),
    /// `execute expr` (`ExecuteI of expr`) — e.g. `Execute (LOCAL.SET x)`.
    ExecuteI(Expr),
    /// `perform id args` (`PerformI`) — e.g. `$with_local(z, x, val)`.
    PerformI(&'static str, Vec<Arg>),
    /// `replace expr -> path with expr` (`ReplaceI`) — e.g. `f.LOCALS[x] := v`.
    ReplaceI {
        target: Expr,
        path: Path,
        value: Expr,
    },
    /// `trap` — abort execution (`TrapI`).
    TrapI,
    /// `return expr` (`ReturnI of expr option`; expression always present here).
    ReturnI(Expr),
    /// `fail` — undefined helper input (`FailI`).
    FailI,
}

/// Helper function (`FuncA of id * arg list * instr list` in OCaml).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FuncA {
    /// Function name (`signed_`, `binop_`, `size`, …).
    pub id: &'static str,
    /// Formal parameters (`arg list` in OCaml).
    pub params: &'static [Param],
    /// Function body (`instr list`).
    pub body: Vec<Instr>,
}

/// Pretty-print `Step_pure/binop` with `$binop_` call visible.
pub fn format_rule_binop_pretty(nt: NumType, binop: WasmBinOp) -> String {
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

/// Pretty-print `Step_pure/relop` with `$relop_` call visible.
pub fn format_rule_relop_pretty(nt: NumType, relop: WasmRelOp) -> String {
    format!(
        "Step_pure/relop {nt:?} {relop:?}\n\
           assert top_value({nt:?})\n\
           pop c_2\n\
           assert top_value({nt:?})\n\
           pop c_1\n\
           let c = $relop_({nt:?}, {relop:?}, c_1, c_2)\n\
           push I32.CONST c"
    )
}

/// Pretty-print `Step_pure/testop` with `$testop_` call visible.
pub fn format_rule_testop_pretty(nt: NumType, testop: WasmTestOp) -> String {
    format!(
        "Step_pure/testop {nt:?} {testop:?}\n\
           assert top_value({nt:?})\n\
           pop c_1\n\
           let c = $testop_({nt:?}, {testop:?}, c_1)\n\
           push I32.CONST c"
    )
}

/// Pretty-print `Step_pure/unop` with `$unop_` call visible.
pub fn format_rule_unop_pretty(nt: NumType, unop: WasmUnOp) -> String {
    let partial = if unop.is_partial() { "yes" } else { "no" };
    format!(
        "Step_pure/unop {nt:?} {unop:?}\n\
           assert top_value({nt:?})\n\
           pop c_1\n\
           if |$unop_({nt:?}, {unop:?}, c_1)| <= 0 then\n\
             trap\n\
           else\n\
             let c = choose($unop_({nt:?}, {unop:?}, c_1))\n\
             push const({nt:?}, c)\n\
         (partial via $unop_: {partial})"
    )
}
