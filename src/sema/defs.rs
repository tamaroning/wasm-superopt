//! SpecTec AL definitions transcribed from [`spectec/binop.al`](../../spectec/binop.al)
//! and [`spectec/local.al`](../../spectec/local.al).
//!
//! Types and `$fn` bodies from those files live here. Step templates use
//! [`Expr`](super::ast::Expr) for primitive `binop` (`+`, `-`, `*`, …).
//! Lowering to flat [`AlSpec`](super::ir::AlSpec) is for hand-written step specs only;
//! binop / local `SemOp`s use [`super::symbolic::func`] and [`super::symbolic::instr`].

#![allow(dead_code)] // mirrors spectec/*.al; not every def is wired to instantiate yet

pub mod types {
    use crate::semantics::I32_BITS;
    use z3::Context;
    use z3::ast::{Ast, BV, Bool};

    /// Wasm numeric type parameter (`nt` / `valtype` in SpecTec AL).
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub enum NumType {
        I32,
    }

    impl NumType {
        /// `size` / `sizenn` from binop.al (L44–65).
        pub const fn bit_width(self) -> u32 {
            match self {
                NumType::I32 => 32,
            }
        }
    }

    /// Wasm value type for `$size` (binop.al L44–61).
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub enum ValType {
        I32,
        I64,
        F32,
        F64,
        V128,
    }

    /// Signedness flag for `DIV` / `REM` / `SHR` variants (`S` or `U`).
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub enum Sign {
        U,
        S,
    }

    /// Wasm `binop` variant from instruction syntax (e.g. `DIV S`, `ADD`).
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub enum WasmBinOp {
        Add,
        Sub,
        Mul,
        Shl,
        Div(Sign),
        Rem(Sign),
        And,
        Or,
    }

    impl WasmBinOp {
        pub const fn to_binop_kind(self) -> Option<BinOpKind> {
            match self {
                WasmBinOp::Add => Some(BinOpKind::Add),
                WasmBinOp::Sub => Some(BinOpKind::Sub),
                WasmBinOp::Mul => Some(BinOpKind::Mul),
                WasmBinOp::Shl => Some(BinOpKind::Shl),
                WasmBinOp::Div(Sign::U) => Some(BinOpKind::DivU),
                WasmBinOp::Div(Sign::S) => Some(BinOpKind::DivS),
                WasmBinOp::Rem(Sign::U) => Some(BinOpKind::RemU),
                WasmBinOp::Rem(Sign::S) => Some(BinOpKind::RemS),
                WasmBinOp::And => Some(BinOpKind::And),
                WasmBinOp::Or => Some(BinOpKind::Or),
            }
        }

        /// Whether `$binop_` may return ε (via `$idiv_` / `$irem_` / `$list_`).
        pub const fn is_partial(self) -> bool {
            matches!(self, WasmBinOp::Div(_) | WasmBinOp::Rem(_))
        }
    }

    /// `case(binop_)` variants used in binop.al.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    pub enum BinOpCase {
        Div,
        Rem,
        Shr,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub enum BinOpKind {
        Add,
        Sub,
        Mul,
        DivU,
        DivS,
        RemU,
        RemS,
        Shl,
        And,
        Or,
    }

    impl BinOpKind {
        pub fn label(self) -> &'static str {
            match self {
                BinOpKind::Add => "Add",
                BinOpKind::Sub => "Sub",
                BinOpKind::Mul => "Mul",
                BinOpKind::DivU => "DivU",
                BinOpKind::DivS => "DivS",
                BinOpKind::RemU => "RemU",
                BinOpKind::RemS => "RemS",
                BinOpKind::Shl => "Shl",
                BinOpKind::And => "And",
                BinOpKind::Or => "Or",
            }
        }

        /// `binop(a, b) = ε` (Wasm partiality): may the operation trap?
        pub fn binop_empty_concrete(self, a: i32, b: i32) -> bool {
            match self {
                BinOpKind::DivU | BinOpKind::RemU => b == 0,
                BinOpKind::DivS => b == 0 || (b == -1 && a == i32::MIN),
                BinOpKind::RemS => b == 0,
                BinOpKind::Add
                | BinOpKind::Sub
                | BinOpKind::Mul
                | BinOpKind::Shl
                | BinOpKind::And
                | BinOpKind::Or => false,
            }
        }

        pub fn binop_empty_z3<'ctx>(
            self,
            ctx: &'ctx Context,
            a: &BV<'ctx>,
            b: &BV<'ctx>,
        ) -> Bool<'ctx> {
            match self {
                BinOpKind::DivU | BinOpKind::RemU => b._eq(&BV::from_i64(ctx, 0, I32_BITS)),
                BinOpKind::DivS => Bool::or(
                    ctx,
                    &[
                        &b._eq(&BV::from_i64(ctx, 0, I32_BITS)),
                        &Bool::and(
                            ctx,
                            &[
                                &b._eq(&BV::from_i64(ctx, -1, I32_BITS)),
                                &a._eq(&BV::from_i64(ctx, i32::MIN as i64, I32_BITS)),
                            ],
                        ),
                    ],
                ),
                BinOpKind::RemS => b._eq(&BV::from_i64(ctx, 0, I32_BITS)),
                BinOpKind::Add
                | BinOpKind::Sub
                | BinOpKind::Mul
                | BinOpKind::Shl
                | BinOpKind::And
                | BinOpKind::Or => Bool::from_bool(ctx, false),
            }
        }
    }
}

pub use types::*;

use super::ast::{
    Arg, Expr, FuncA, Instr, InstrCond, LetLhs, Param, ParamType, Path, Pred, PopTarget,
};

const fn mp(name: &'static str, ty: ParamType) -> Param {
    Param { name, ty }
}

const SIZE_PARAMS: &[Param] = &[mp("valtype", ParamType::ValType)];
const SIZENN_PARAMS: &[Param] = &[mp("nt", ParamType::NumType)];
const SIGNED_PARAMS: &[Param] = &[
    mp("N", ParamType::Nat),
    mp("i", ParamType::Nat),
];
const INV_SIGNED_PARAMS: &[Param] = &[
    mp("N", ParamType::Nat),
    mp("i", ParamType::Int),
];
const LIST_PARAMS: &[Param] = &[
    mp("X", ParamType::Any),
    mp("X_opt", ParamType::Any),
];
const IDIV_PARAMS: &[Param] = &[
    mp("N", ParamType::Nat),
    mp("sx", ParamType::Sign),
    mp("i_1", ParamType::Nat),
    mp("i_2", ParamType::Nat),
];
const IREM_PARAMS: &[Param] = &[
    mp("N", ParamType::Nat),
    mp("sx", ParamType::Sign),
    mp("i_1", ParamType::Nat),
    mp("i_2", ParamType::Nat),
];
const BINOP_PARAMS: &[Param] = &[
    mp("numtype", ParamType::NumType),
    mp("binop_", ParamType::BinOp),
    mp("iN_1", ParamType::Nat),
    mp("iN_2", ParamType::Nat),
];
const LOCAL_PARAMS: &[Param] = &[
    mp("s", ParamType::Any),
    mp("f", ParamType::Any),
    mp("x", ParamType::Nat),
];
const WITH_LOCAL_PARAMS: &[Param] = &[
    mp("s", ParamType::Any),
    mp("f", ParamType::Any),
    mp("x", ParamType::Nat),
    mp("v", ParamType::Any),
];

/// Store parameter in [`local.al`](../../spectec/local.al) step rules (`z`).
pub const STORE_PARAM: &str = "z";

fn p(name: &'static str) -> Expr {
    Expr::VarE(name)
}

fn nat(n: u32) -> Expr {
    Expr::NatLit(n)
}

fn int(n: i32) -> Expr {
    Expr::IntLit(n)
}

fn call(name: &'static str, args: Vec<Arg>) -> Expr {
    Expr::Call(name, args)
}

fn int_coerce(expr: Expr) -> Expr {
    Expr::IntCoerce(Box::new(expr))
}

fn nat_coerce(expr: Expr) -> Expr {
    Expr::NatCoerce(Box::new(expr))
}

fn rat_coerce(expr: Expr) -> Expr {
    Expr::RatCoerce(Box::new(expr))
}

fn truncz(expr: Expr) -> Expr {
    Expr::TruncZ(Box::new(expr))
}

fn pow2(exp: Expr) -> Expr {
    Expr::Pow(Box::new(nat(2)), Box::new(exp))
}

fn n_minus_1(n: Expr) -> Expr {
    nat_coerce(Expr::Sub(
        Box::new(int_coerce(n)),
        Box::new(int(1)),
    ))
}

fn half_modulus(n: Expr) -> Expr {
    pow2(n_minus_1(n))
}

fn full_modulus(n: Expr) -> Expr {
    pow2(n)
}

fn eq(a: Expr, b: Expr) -> Pred {
    Pred::Eq(a, b)
}

fn lt(a: Expr, b: Expr) -> Pred {
    Pred::Lt(a, b)
}

fn le(a: Expr, b: Expr) -> Pred {
    Pred::Le(a, b)
}

fn and(a: Pred, b: Pred) -> Pred {
    Pred::And(Box::new(a), Box::new(b))
}

fn wrap_mod(nat_expr: Expr, modulus: Expr) -> Expr {
    Expr::Mod(Box::new(nat_expr), Box::new(modulus))
}

/// `$((i_1 + i_2) \ (2 ^ N))` — spectec equation, not a separate `$fn` def.
fn inn_iadd(n: Expr, i_1: Expr, i_2: Expr) -> Expr {
    wrap_mod(
        Expr::Add(Box::new(i_1), Box::new(i_2)),
        full_modulus(n),
    )
}

/// `$((2^N + i_1 - i_2) \ 2^N)` — spectec equation.
fn inn_isub(n: Expr, i_1: Expr, i_2: Expr) -> Expr {
    let modulus = full_modulus(n);
    nat_coerce(wrap_mod(
        Expr::Sub(
            Box::new(int_coerce(Expr::Add(
                Box::new(modulus.clone()),
                Box::new(i_1),
            ))),
            Box::new(int_coerce(i_2)),
        ),
        int_coerce(modulus),
    ))
}

/// `$((i_1 * i_2) \ (2 ^ N))` — spectec equation.
fn inn_imul(n: Expr, i_1: Expr, i_2: Expr) -> Expr {
    wrap_mod(
        Expr::Mul(Box::new(i_1), Box::new(i_2)),
        full_modulus(n),
    )
}

/// `$iand_` / `$ior_` — spectec `hint(builtin)`: `(m op n) & mask(N)`.
fn inn_iand(n: Expr, i_1: Expr, i_2: Expr) -> Expr {
    wrap_mod(
        Expr::BitAnd(Box::new(i_1), Box::new(i_2)),
        full_modulus(n),
    )
}

fn inn_ior(n: Expr, i_1: Expr, i_2: Expr) -> Expr {
    wrap_mod(
        Expr::BitOr(Box::new(i_1), Box::new(i_2)),
        full_modulus(n),
    )
}

fn inn_ishl(n: Expr, i_1: Expr, i_2: Expr) -> Expr {
    wrap_mod(
        Expr::Shl(
            Box::new(i_1),
            Box::new(Expr::Rem(Box::new(i_2), Box::new(n.clone()))),
        ),
        full_modulus(n),
    )
}

// =============================================================================
// Step_pure/binop nt binop  (binop.al L5–15)
// =============================================================================

pub fn step_pure_binop_template(nt: NumType, binop: WasmBinOp) -> Vec<Instr> {
    let binop_call = Expr::Call(
        "binop_",
        vec![
            Arg::NumType(nt),
            Arg::BinOp(binop),
            Arg::Var("c_1"),
            Arg::Var("c_2"),
        ],
    );
    vec![
        Instr::AssertI(InstrCond::Expr(Expr::TopValue(nt))),
        Instr::PopI(PopTarget::NumConst("c_2")),
        Instr::AssertI(InstrCond::Expr(Expr::TopValue(nt))),
        Instr::PopI(PopTarget::NumConst("c_1")),
        Instr::IfI {
            cond: InstrCond::Expr(Expr::OptionalLen(Box::new(binop_call.clone()))),
            then_steps: vec![Instr::TrapI],
            else_steps: vec![
                Instr::LetI { lhs: LetLhs::Var("c"), expr: Expr::Choose(Box::new(binop_call)) },
                Instr::PushI(Expr::Call(
                    "const",
                    vec![Arg::NumType(nt), Arg::Var("c")],
                )),
            ],
        },
    ]
}

// =============================================================================
// Step_read/local.get, Step_pure/local.tee, Step/local.set  (local.al L1–18)
// =============================================================================

fn case_e(op: &'static str, args: Vec<Expr>) -> Expr {
    Expr::CaseE(op, args)
}

fn frame_locals(frame: &'static str) -> Expr {
    Expr::AccE(
        Box::new(Expr::VarE(frame)),
        Path::Dot("LOCALS"),
    )
}

fn frame_local_at(frame: &'static str, idx: Expr) -> Expr {
    Expr::AccE(
        Box::new(frame_locals(frame)),
        Path::Idx(Box::new(idx)),
    )
}

fn local_call_args(x: u32) -> Vec<Arg> {
    vec![Arg::Var(STORE_PARAM), Arg::Nat(x)]
}

fn with_local_call_args(x: u32) -> Vec<Arg> {
    vec![Arg::Var(STORE_PARAM), Arg::Nat(x), Arg::Var("val")]
}

/// `Step_read/local.get x { Push $local(z, x) }` (local.al L1–3)
pub fn step_read_local_get_template(x: u32) -> Vec<Instr> {
    vec![Instr::PushI(Expr::Call(
        "local",
        local_call_args(x),
    ))]
}

/// `Step_pure/local.tee x { … }` (local.al L6–12)
pub fn step_pure_local_tee_template(x: u32) -> Vec<Instr> {
    vec![
        Instr::AssertI(InstrCond::Expr(Expr::TopValueAny)),
        Instr::PopI(PopTarget::Val("val")),
        Instr::PushI(Expr::VarE("val")),
        Instr::PushI(Expr::VarE("val")),
        Instr::ExecuteI(case_e("LOCAL.SET", vec![Expr::NatLit(x)])),
    ]
}

/// `Step/local.set x { Assert (top_value()); Pop val; $with_local(z, x, val) }` (local.al L14–18)
pub fn step_local_set_template(x: u32) -> Vec<Instr> {
    vec![
        Instr::AssertI(InstrCond::Expr(Expr::TopValueAny)),
        Instr::PopI(PopTarget::Val("val")),
        Instr::PerformI("with_local", with_local_call_args(x)),
    ]
}

// =============================================================================
// with_local, local  (local.al L20–26)
// =============================================================================

/// `with_local (s, f) x v { f.LOCALS[x] := v }` (local.al L20–22)
pub fn with_local_def() -> FuncA {
    FuncA {
        id: "with_local",
        params: WITH_LOCAL_PARAMS,
        body: vec![Instr::ReplaceI {
            target: frame_locals("f"),
            path: Path::Idx(Box::new(p("x"))),
            value: p("v"),
        }],
    }
}

/// `local (s, f) x { Return f.LOCALS[x] }` (local.al L24–26)
pub fn local_def() -> FuncA {
    FuncA {
        id: "local",
        params: LOCAL_PARAMS,
        body: vec![Instr::ReturnI(frame_local_at("f", p("x")))],
    }
}

/// Pretty-print local step templates (for `--print-semantics`).
pub fn format_rule_local_pretty(op: &crate::semantics::SemOp) -> String {
    use crate::semantics::SemOp;
    match op {
        SemOp::LocalGet(x) => format!(
            "Step_read/local.get {x}\n  push $local(z, {x})"
        ),
        SemOp::LocalSet(x) => format!(
            "Step/local.set {x}\n  assert top_value()\n  pop val\n  $with_local(z, {x}, val)"
        ),
        SemOp::LocalTee(x) => format!(
            "Step_pure/local.tee {x}\n  assert top_value()\n  pop val\n  push val\n  push val\n  execute (LOCAL.SET {x})"
        ),
        _ => panic!("not a local op: {op:?}"),
    }
}

// =============================================================================
// size valtype  (binop.al L17–34)
// =============================================================================

pub fn size_def() -> FuncA {
    fn ret(v: u32) -> Instr {
        Instr::ReturnI(nat(v))
    }
    fn if_valtype(vt: ValType, n: u32) -> Instr {
        Instr::IfI {
            cond: InstrCond::Pred(eq(p("valtype"), Expr::ValTypeLit(vt))),
            then_steps: vec![ret(n)],
            else_steps: vec![],
        }
    }
    FuncA {
        id: "size",
        params: &SIZE_PARAMS,
        body: vec![
            if_valtype(ValType::I32, 32),
            if_valtype(ValType::I64, 64),
            if_valtype(ValType::F32, 32),
            if_valtype(ValType::F64, 64),
            if_valtype(ValType::V128, 128),
            Instr::FailI,
        ],
    }
}

// =============================================================================
// sizenn nt  (binop.al L36–38)
// =============================================================================

pub fn sizenn_def() -> FuncA {
    FuncA {
        id: "sizenn",
        params: &SIZENN_PARAMS,
        body: vec![Instr::ReturnI(call(
            "size",
            vec![Arg::ExpA(Box::new(p("nt")))],
        ))],
    }
}

// =============================================================================
// signed_ N i  (binop.al L41–48)
// =============================================================================

pub fn signed_def() -> FuncA {
    let threshold = half_modulus(p("N"));
    FuncA {
        id: "signed_",
        params: &SIGNED_PARAMS,
        body: vec![
            Instr::IfI {
            cond: InstrCond::Pred(lt(p("i"), threshold.clone())),
                then_steps: vec![Instr::ReturnI(int_coerce(p("i")))],
                else_steps: vec![],
            },
            Instr::AssertI(InstrCond::Pred(le(threshold, p("i")))),
            Instr::AssertI(InstrCond::Pred(lt(p("i"), full_modulus(p("N"))))),
            Instr::ReturnI(Expr::Sub(
                Box::new(int_coerce(p("i"))),
                Box::new(int_coerce(full_modulus(p("N")))),
            )),
        ],
    }
}

// =============================================================================
// inv_signed_ N i  (binop.al L51–58)
// =============================================================================

pub fn inv_signed_def() -> FuncA {
    let threshold = half_modulus(p("N"));
    FuncA {
        id: "inv_signed_",
        params: &INV_SIGNED_PARAMS,
        body: vec![
            Instr::IfI {
                cond: InstrCond::Pred(and(
                    le(int(0), p("i")),
                    lt(p("i"), threshold.clone()),
                )),
                then_steps: vec![Instr::ReturnI(nat_coerce(p("i")))],
                else_steps: vec![],
            },
            Instr::AssertI(InstrCond::Pred(le(
                Expr::Sub(Box::new(int(0)), Box::new(threshold.clone())),
                p("i"),
            ))),
            Instr::AssertI(InstrCond::Pred(lt(p("i"), int(0)))),
            Instr::ReturnI(nat_coerce(Expr::Add(
                Box::new(p("i")),
                Box::new(full_modulus(p("N"))),
            ))),
        ],
    }
}

// =============================================================================
// list_ X X?{X <- X}  (binop.al L60–66)
// =============================================================================

pub fn list_def() -> FuncA {
    FuncA {
        id: "list_",
        params: &LIST_PARAMS,
        body: vec![
            Instr::IfI {
            cond: InstrCond::Pred(Pred::OptIsNone(p("X_opt"))),
                then_steps: vec![Instr::ReturnI(Expr::EmptyList)],
                else_steps: vec![
                    Instr::LetI { lhs: LetLhs::Var("w"), expr: Expr::Choose(Box::new(p("X_opt"))) },
                    Instr::ReturnI(Expr::SingletonList(Box::new(p("w")))),
                ],
            },
        ],
    }
}

// =============================================================================
// idiv_ N sx i_1 i_2  (wasm-2.0.al L1445–1459)
// =============================================================================

pub fn idiv_def() -> FuncA {
    let trunc_div = |i_1: Expr, i_2: Expr| {
        truncz(Expr::Div(
            Box::new(rat_coerce(i_1)),
            Box::new(rat_coerce(i_2)),
        ))
    };
    let signed_overflow = eq(
        Expr::Div(
            Box::new(rat_coerce(call(
                "signed_",
                vec![
                    Arg::ExpA(Box::new(p("N"))),
                    Arg::ExpA(Box::new(p("i_1"))),
                ],
            ))),
            Box::new(rat_coerce(call(
                "signed_",
                vec![
                    Arg::ExpA(Box::new(p("N"))),
                    Arg::ExpA(Box::new(p("i_2"))),
                ],
            ))),
        ),
        rat_coerce(half_modulus(p("N"))),
    );
    FuncA {
        id: "idiv_",
        params: IDIV_PARAMS,
        body: vec![
            Instr::IfI {
            cond: InstrCond::Pred(eq(p("sx"), Expr::SignLit(Sign::U))),
                then_steps: vec![
                    Instr::IfI {
            cond: InstrCond::Pred(eq(p("i_2"), nat(0))),
                        then_steps: vec![Instr::ReturnI(Expr::EmptyOpt)],
                        else_steps: vec![Instr::ReturnI(Expr::SomeOpt(Box::new(
                            nat_coerce(trunc_div(p("i_1"), p("i_2"))),
                        )))],
                    },
                ],
                else_steps: vec![],
            },
            Instr::AssertI(InstrCond::Pred(eq(p("sx"), Expr::SignLit(Sign::S)))),
            Instr::IfI {
            cond: InstrCond::Pred(eq(p("i_2"), nat(0))),
                then_steps: vec![Instr::ReturnI(Expr::EmptyOpt)],
                else_steps: vec![],
            },
            Instr::IfI {
                cond: InstrCond::Pred(signed_overflow),
                then_steps: vec![Instr::ReturnI(Expr::EmptyOpt)],
                else_steps: vec![Instr::ReturnI(Expr::SomeOpt(Box::new(call(
                    "inv_signed_",
                    vec![
                        Arg::ExpA(Box::new(p("N"))),
                        Arg::ExpA(Box::new(trunc_div(
                            call(
                                "signed_",
                                vec![
                                    Arg::ExpA(Box::new(p("N"))),
                                    Arg::ExpA(Box::new(p("i_1"))),
                                ],
                            ),
                            call(
                                "signed_",
                                vec![
                                    Arg::ExpA(Box::new(p("N"))),
                                    Arg::ExpA(Box::new(p("i_2"))),
                                ],
                            ),
                        ))),
                    ],
                ))))],
            },
        ],
    }
}

// =============================================================================
// irem_ N sx i_1 i_2  (wasm-2.0.al L1466–1479; spectec 3-numerics)
// =============================================================================

pub fn irem_def() -> FuncA {
    let trunc_div = |a: Expr, b: Expr| {
        truncz(Expr::Div(
            Box::new(rat_coerce(a)),
            Box::new(rat_coerce(b)),
        ))
    };
    FuncA {
        id: "irem_",
        params: IREM_PARAMS,
        body: vec![
            Instr::IfI {
            cond: InstrCond::Pred(eq(p("sx"), Expr::SignLit(Sign::U))),
                then_steps: vec![
                    Instr::IfI {
            cond: InstrCond::Pred(eq(p("i_2"), nat(0))),
                        then_steps: vec![Instr::ReturnI(Expr::EmptyOpt)],
                        else_steps: vec![Instr::ReturnI(Expr::SomeOpt(Box::new(
                            nat_coerce(Expr::Sub(
                                Box::new(int_coerce(p("i_1"))),
                                Box::new(int_coerce(Expr::Mul(
                                    Box::new(p("i_2")),
                                    Box::new(nat_coerce(trunc_div(p("i_1"), p("i_2")))),
                                ))),
                            )),
                        )))],
                    },
                ],
                else_steps: vec![],
            },
            Instr::AssertI(InstrCond::Pred(eq(p("sx"), Expr::SignLit(Sign::S)))),
            Instr::IfI {
            cond: InstrCond::Pred(eq(p("i_2"), nat(0))),
                then_steps: vec![Instr::ReturnI(Expr::EmptyOpt)],
                else_steps: vec![
                    Instr::LetI {
                        lhs: LetLhs::Var("j_1"),
                        expr: call(
                            "signed_",
                            vec![
                                Arg::ExpA(Box::new(p("N"))),
                                Arg::ExpA(Box::new(p("i_1"))),
                            ],
                        ),
                    },
                    Instr::LetI {
                        lhs: LetLhs::Var("j_2"),
                        expr: call(
                            "signed_",
                            vec![
                                Arg::ExpA(Box::new(p("N"))),
                                Arg::ExpA(Box::new(p("i_2"))),
                            ],
                        ),
                    },
                    Instr::ReturnI(Expr::SomeOpt(Box::new(call(
                        "inv_signed_",
                        vec![
                            Arg::ExpA(Box::new(p("N"))),
                            Arg::ExpA(Box::new(Expr::Sub(
                                Box::new(int_coerce(p("j_1"))),
                                Box::new(int_coerce(Expr::Mul(
                                    Box::new(int_coerce(p("j_2"))),
                                    Box::new(int_coerce(trunc_div(p("j_1"), p("j_2")))),
                                ))),
                            ))),
                        ],
                    )))),
                ],
            },
        ],
    }
}

// =============================================================================
// binop_ numtype binop_ iN_1 iN_2  (wasm-2.0.al L1486–1526)
// =============================================================================

fn singleton_binop(call_expr: Expr) -> Instr {
    Instr::ReturnI(Expr::SingletonList(Box::new(call_expr)))
}

pub fn binop_def() -> FuncA {
    let sizenn_nt = call("sizenn", vec![Arg::ExpA(Box::new(p("numtype")))]);
    let list_partial = |partial_call: Expr| {
        Instr::ReturnI(call(
            "list_",
            vec![
                Arg::ExpA(Box::new(p("numtype"))),
                Arg::ExpA(Box::new(partial_call)),
            ],
        ))
    };
    let list_idiv = list_partial(call(
        "idiv_",
        vec![
            Arg::ExpA(Box::new(sizenn_nt.clone())),
            Arg::ExpA(Box::new(p("sx"))),
            Arg::ExpA(Box::new(p("iN_1"))),
            Arg::ExpA(Box::new(p("iN_2"))),
        ],
    ));
    let list_irem = list_partial(call(
        "irem_",
        vec![
            Arg::ExpA(Box::new(sizenn_nt.clone())),
            Arg::ExpA(Box::new(p("sx"))),
            Arg::ExpA(Box::new(p("iN_1"))),
            Arg::ExpA(Box::new(p("iN_2"))),
        ],
    ));
    let i_1 = p("iN_1");
    let i_2 = p("iN_2");
    let inn_branch = vec![
        Instr::IfI {
            cond: InstrCond::Pred(Pred::BinOpEq(p("binop_"), WasmBinOp::Add)),
            then_steps: vec![singleton_binop(inn_iadd(
                sizenn_nt.clone(),
                i_1.clone(),
                i_2.clone(),
            ))],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::BinOpEq(p("binop_"), WasmBinOp::Sub)),
            then_steps: vec![singleton_binop(inn_isub(
                sizenn_nt.clone(),
                i_1.clone(),
                i_2.clone(),
            ))],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::BinOpEq(p("binop_"), WasmBinOp::Mul)),
            then_steps: vec![singleton_binop(inn_imul(
                sizenn_nt.clone(),
                i_1.clone(),
                i_2.clone(),
            ))],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::BinOpCaseIs(p("binop_"), BinOpCase::Div)),
            then_steps: vec![
                Instr::LetI { lhs: LetLhs::BinOpCase(BinOpCase::Div, "sx"), expr: p("binop_") },
                list_idiv,
            ],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::BinOpCaseIs(p("binop_"), BinOpCase::Rem)),
            then_steps: vec![
                Instr::LetI { lhs: LetLhs::BinOpCase(BinOpCase::Rem, "sx"), expr: p("binop_") },
                list_irem,
            ],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::BinOpEq(p("binop_"), WasmBinOp::And)),
            then_steps: vec![singleton_binop(inn_iand(
                sizenn_nt.clone(),
                i_1.clone(),
                i_2.clone(),
            ))],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::BinOpEq(p("binop_"), WasmBinOp::Or)),
            then_steps: vec![singleton_binop(inn_ior(
                sizenn_nt.clone(),
                i_1.clone(),
                i_2.clone(),
            ))],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::BinOpEq(p("binop_"), WasmBinOp::Shl)),
            then_steps: vec![singleton_binop(inn_ishl(
                sizenn_nt.clone(),
                i_1.clone(),
                i_2.clone(),
            ))],
            else_steps: vec![],
        },
    ];
    FuncA {
        id: "binop_",
        params: BINOP_PARAMS,
        body: vec![
            Instr::IfI {
            cond: InstrCond::Pred(Pred::TypeIsInn(p("numtype"))),
                then_steps: inn_branch,
                else_steps: vec![Instr::AssertI(InstrCond::Pred(Pred::TypeIsFnn(p("numtype"))))],
            },
        ],
    }
}

/// Look up a SpecTec `$fn` definition by name.
pub fn lookup_func(name: &str) -> Option<FuncA> {
    Some(match name {
        "size" => size_def(),
        "sizenn" => sizenn_def(),
        "signed_" => signed_def(),
        "inv_signed_" => inv_signed_def(),
        "list_" => list_def(),
        "idiv_" => idiv_def(),
        "irem_" => irem_def(),
        "binop_" => binop_def(),
        "local" => local_def(),
        "with_local" => with_local_def(),
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn size_def_matches_binop_al() {
        let def = size_def();
        assert_eq!(def.id, "size");
        assert_eq!(def.params, SIZE_PARAMS);
        assert!(matches!(def.body.last(), Some(Instr::FailI)));
    }

    #[test]
    fn local_def_matches_local_al() {
        let def = local_def();
        assert_eq!(def.id, "local");
        assert_eq!(def.params, LOCAL_PARAMS);
        assert!(matches!(def.body.last(), Some(Instr::ReturnI(_))));
    }

    #[test]
    fn with_local_def_matches_local_al() {
        let def = with_local_def();
        assert_eq!(def.id, "with_local");
        assert_eq!(def.params, WITH_LOCAL_PARAMS);
        assert!(matches!(def.body.last(), Some(Instr::ReplaceI { .. })));
    }

    #[test]
    fn binop_i32_div_s_is_partial() {
        assert!(WasmBinOp::Div(Sign::S).is_partial());
    }

    #[test]
    fn binop_i32_add_is_total() {
        assert!(!WasmBinOp::Add.is_partial());
    }
}
