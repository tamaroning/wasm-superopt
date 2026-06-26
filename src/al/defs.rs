//! SpecTec AL definitions transcribed from [`spectec/binop.al`](../../spectec/binop.al),
//! [`spectec/local.al`](../../spectec/local.al), and [`spectec/wasm-2.0.al`](../../spectec/wasm-2.0.al)
//! (relop / testop / unop sections).
//!
//! Types and `$fn` bodies from those files live here. Step templates use
//! [`Expr`](super::ast::Expr) for primitive `binop` (`+`, `-`, `*`, …).
//! Lowering to flat [`AlSpec`](super::ir::AlSpec) is for hand-written step specs only;
//! binop / local `SemOp`s use [`super::symbolic::func`] and [`super::symbolic::instr`].

#![allow(dead_code)] // mirrors spectec/*.al; not every def is wired to instantiate yet

pub mod types {
    use crate::al::I32_BITS;
    use z3::Context;
    use z3::ast::{Ast, BV, Bool};

    /// Wasm numeric type parameter (`nt` / `valtype` in SpecTec AL).
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub enum NumType {
        I32,
        I64,
        F32,
        F64,
    }

    impl NumType {
        /// `size` / `sizenn` from wasm-2.0.al (L1121–1137, L1168–1169).
        pub const fn bit_width(self) -> u32 {
            match self {
                NumType::I32 | NumType::F32 => 32,
                NumType::I64 | NumType::F64 => 64,
            }
        }

        pub const fn is_inn(self) -> bool {
            matches!(self, NumType::I32 | NumType::I64)
        }

        pub const fn is_fnn(self) -> bool {
            matches!(self, NumType::F32 | NumType::F64)
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
        Xor,
        Shr(Sign),
        Rotl,
        Rotr,
        /// Float-only (`Fnn` branch in wasm-2.0.al L1541–1548).
        Min,
        Max,
        Copysign,
        /// Float division (`DIV` without signedness in wasm-2.0.al L1538–1539).
        FloatDiv,
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
                WasmBinOp::Xor => Some(BinOpKind::Xor),
                WasmBinOp::Shr(Sign::U) => Some(BinOpKind::ShrU),
                WasmBinOp::Shr(Sign::S) => Some(BinOpKind::ShrS),
                WasmBinOp::Rotl => Some(BinOpKind::Rotl),
                WasmBinOp::Rotr => Some(BinOpKind::Rotr),
                WasmBinOp::Min | WasmBinOp::Max | WasmBinOp::Copysign | WasmBinOp::FloatDiv => {
                    None
                }
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
        Xor,
        ShrU,
        ShrS,
        Rotl,
        Rotr,
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
                BinOpKind::Xor => "Xor",
                BinOpKind::ShrU => "ShrU",
                BinOpKind::ShrS => "ShrS",
                BinOpKind::Rotl => "Rotl",
                BinOpKind::Rotr => "Rotr",
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
                | BinOpKind::Or
                | BinOpKind::Xor
                | BinOpKind::ShrU
                | BinOpKind::ShrS
                | BinOpKind::Rotl
                | BinOpKind::Rotr => false,
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
                | BinOpKind::Or
                | BinOpKind::Xor
                | BinOpKind::ShrU
                | BinOpKind::ShrS
                | BinOpKind::Rotl
                | BinOpKind::Rotr => Bool::from_bool(ctx, false),
            }
        }
    }

    /// Relational operator case for signed lt/gt/le/ge (`LT`, `GT`, …).
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub enum RelOpCase {
        Lt,
        Gt,
        Le,
        Ge,
    }

    /// Wasm `relop` variant from instruction syntax (e.g. `LT S`, `EQ`).
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub enum WasmRelOp {
        Eq,
        Ne,
        Lt(Sign),
        Gt(Sign),
        Le(Sign),
        Ge(Sign),
        Flt,
        Fgt,
        Fle,
        Fge,
    }

    /// Wasm `testop` variant (`EQZ`, …).
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub enum WasmTestOp {
        Eqz,
    }

    /// Unary operator case for `EXTEND M`.
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub enum UnOpCase {
        Extend,
    }

    /// Wasm `unop` variant from instruction syntax (e.g. `CLZ`, `ABS`).
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub enum WasmUnOp {
        Clz,
        Ctz,
        Popcnt,
        Extend,
        Abs,
        Neg,
        Sqrt,
        Ceil,
        Floor,
        Trunc,
        Nearest,
    }

    impl WasmUnOp {
        /// Whether `$unop_` may return ε (via float builtins / `$list_`).
        pub const fn is_partial(self) -> bool {
            matches!(
                self,
                WasmUnOp::Sqrt | WasmUnOp::Trunc | WasmUnOp::Nearest
            )
        }
    }
}

pub use types::*;

use super::ast::{
    Arg, Expr, FuncA, Instr, InstrCond, LetLhs, Param, ParamType, Path, PopTarget, Pred,
};

const fn mp(name: &'static str, ty: ParamType) -> Param {
    Param { name, ty }
}

const SIZE_PARAMS: &[Param] = &[mp("valtype", ParamType::ValType)];
const SIZENN_PARAMS: &[Param] = &[mp("nt", ParamType::NumType)];
const SIGNED_PARAMS: &[Param] = &[mp("N", ParamType::Nat), mp("i", ParamType::Nat)];
const INV_SIGNED_PARAMS: &[Param] = &[mp("N", ParamType::Nat), mp("i", ParamType::Int)];
const LIST_PARAMS: &[Param] = &[mp("X", ParamType::Any), mp("X_opt", ParamType::Any)];
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
const RELOP_PARAMS: &[Param] = &[
    mp("numtype", ParamType::NumType),
    mp("relop_", ParamType::RelOp),
    mp("iN_1", ParamType::Nat),
    mp("iN_2", ParamType::Nat),
];
const TESTOP_PARAMS: &[Param] = &[
    mp("numtype", ParamType::NumType),
    mp("testop_", ParamType::TestOp),
    mp("iN", ParamType::Nat),
];
const UNOP_PARAMS: &[Param] = &[
    mp("numtype", ParamType::NumType),
    mp("unop_", ParamType::UnOp),
    mp("iN", ParamType::Nat),
];
const BOOL_PARAMS: &[Param] = &[mp("b", ParamType::Any)];
const IEQZ_PARAMS: &[Param] = &[mp("N", ParamType::Nat), mp("i_1", ParamType::Nat)];
const IEQ_PARAMS: &[Param] = &[
    mp("N", ParamType::Nat),
    mp("i_1", ParamType::Nat),
    mp("i_2", ParamType::Nat),
];
const IORDERED_PARAMS: &[Param] = &[
    mp("N", ParamType::Nat),
    mp("sx", ParamType::Sign),
    mp("i_1", ParamType::Nat),
    mp("i_2", ParamType::Nat),
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
    nat_coerce(Expr::Sub(Box::new(int_coerce(n)), Box::new(int(1))))
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

fn ge(a: Expr, b: Expr) -> Pred {
    Pred::Ge(a, b)
}

fn and(a: Pred, b: Pred) -> Pred {
    Pred::And(Box::new(a), Box::new(b))
}

fn cmp_eq(a: Expr, b: Expr) -> Expr {
    Expr::Eq(Box::new(a), Box::new(b))
}

fn cmp_ne(a: Expr, b: Expr) -> Expr {
    Expr::Ne(Box::new(a), Box::new(b))
}

fn cmp_lt(a: Expr, b: Expr) -> Expr {
    Expr::LtCmp(Box::new(a), Box::new(b))
}

fn cmp_le(a: Expr, b: Expr) -> Expr {
    Expr::LeCmp(Box::new(a), Box::new(b))
}

fn cmp_gt(a: Expr, b: Expr) -> Expr {
    Expr::GtCmp(Box::new(a), Box::new(b))
}

fn cmp_ge(a: Expr, b: Expr) -> Expr {
    Expr::GeCmp(Box::new(a), Box::new(b))
}

fn bool_of(cmp: Expr) -> Expr {
    call("bool", vec![Arg::ExpA(Box::new(cmp))])
}

fn push_i32_const(name: &'static str) -> Instr {
    Instr::PushI(Expr::Call(
        "const",
        vec![Arg::NumType(NumType::I32), Arg::Var(name)],
    ))
}

fn wrap_mod(nat_expr: Expr, modulus: Expr) -> Expr {
    Expr::Mod(Box::new(nat_expr), Box::new(modulus))
}

/// `$((i_1 + i_2) \ (2 ^ N))` — spectec equation, not a separate `$fn` def.
fn inn_iadd(n: Expr, i_1: Expr, i_2: Expr) -> Expr {
    wrap_mod(Expr::Add(Box::new(i_1), Box::new(i_2)), full_modulus(n))
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
    wrap_mod(Expr::Mul(Box::new(i_1), Box::new(i_2)), full_modulus(n))
}

/// `$iand_` / `$ior_` — spectec `hint(builtin)`: `(m op n) & mask(N)`.
fn inn_iand(n: Expr, i_1: Expr, i_2: Expr) -> Expr {
    wrap_mod(Expr::BitAnd(Box::new(i_1), Box::new(i_2)), full_modulus(n))
}

fn inn_ior(n: Expr, i_1: Expr, i_2: Expr) -> Expr {
    wrap_mod(Expr::BitOr(Box::new(i_1), Box::new(i_2)), full_modulus(n))
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

fn inn_ixor(n: Expr, i_1: Expr, i_2: Expr) -> Expr {
    wrap_mod(Expr::BitXor(Box::new(i_1), Box::new(i_2)), full_modulus(n))
}

fn inn_ishr(n: Expr, sx: Sign, i_1: Expr, i_2: Expr) -> Expr {
    let amount = Expr::Rem(Box::new(i_2), Box::new(n.clone()));
    let shifted = match sx {
        Sign::U => Expr::LShr(Box::new(i_1), Box::new(amount)),
        Sign::S => Expr::AShr(Box::new(i_1), Box::new(amount)),
    };
    wrap_mod(shifted, full_modulus(n))
}

fn inn_irotl(n: Expr, i_1: Expr, i_2: Expr) -> Expr {
    wrap_mod(
        Expr::Rotl(
            Box::new(i_1),
            Box::new(Expr::Rem(Box::new(i_2), Box::new(n.clone()))),
        ),
        full_modulus(n),
    )
}

fn inn_irotr(n: Expr, i_1: Expr, i_2: Expr) -> Expr {
    wrap_mod(
        Expr::Rotr(
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
                Instr::LetI {
                    lhs: LetLhs::Var("c"),
                    expr: Expr::Choose(Box::new(binop_call)),
                },
                Instr::PushI(Expr::Call("const", vec![Arg::NumType(nt), Arg::Var("c")])),
            ],
        },
    ]
}

// =============================================================================
// Step_pure/unop, Step_pure/testop, Step_pure/relop  (wasm-2.0.al L257–293)
// =============================================================================

pub fn step_pure_unop_template(nt: NumType, unop: WasmUnOp) -> Vec<Instr> {
    let unop_call = Expr::Call(
        "unop_",
        vec![
            Arg::NumType(nt),
            Arg::UnOp(unop),
            Arg::Var("c_1"),
        ],
    );
    vec![
        Instr::AssertI(InstrCond::Expr(Expr::TopValue(nt))),
        Instr::PopI(PopTarget::NumConst("c_1")),
        Instr::IfI {
            cond: InstrCond::Expr(Expr::OptionalLen(Box::new(unop_call.clone()))),
            then_steps: vec![Instr::TrapI],
            else_steps: vec![
                Instr::LetI {
                    lhs: LetLhs::Var("c"),
                    expr: Expr::Choose(Box::new(unop_call)),
                },
                Instr::PushI(Expr::Call("const", vec![Arg::NumType(nt), Arg::Var("c")])),
            ],
        },
    ]
}

pub fn step_pure_testop_template(nt: NumType, testop: WasmTestOp) -> Vec<Instr> {
    vec![
        Instr::AssertI(InstrCond::Expr(Expr::TopValue(nt))),
        Instr::PopI(PopTarget::NumConst("c_1")),
        Instr::LetI {
            lhs: LetLhs::Var("c"),
            expr: Expr::Call(
                "testop_",
                vec![
                    Arg::NumType(nt),
                    Arg::TestOp(testop),
                    Arg::Var("c_1"),
                ],
            ),
        },
        push_i32_const("c"),
    ]
}

pub fn step_pure_relop_template(nt: NumType, relop: WasmRelOp) -> Vec<Instr> {
    vec![
        Instr::AssertI(InstrCond::Expr(Expr::TopValue(nt))),
        Instr::PopI(PopTarget::NumConst("c_2")),
        Instr::AssertI(InstrCond::Expr(Expr::TopValue(nt))),
        Instr::PopI(PopTarget::NumConst("c_1")),
        Instr::LetI {
            lhs: LetLhs::Var("c"),
            expr: Expr::Call(
                "relop_",
                vec![
                    Arg::NumType(nt),
                    Arg::RelOp(relop),
                    Arg::Var("c_1"),
                    Arg::Var("c_2"),
                ],
            ),
        },
        push_i32_const("c"),
    ]
}

// =============================================================================
// Step_read/local.get, Step_pure/local.tee, Step/local.set  (local.al L1–18)
// =============================================================================

fn case_e(op: &'static str, args: Vec<Expr>) -> Expr {
    Expr::CaseE(op, args)
}

fn frame_locals(frame: &'static str) -> Expr {
    Expr::AccE(Box::new(Expr::VarE(frame)), Path::Dot("LOCALS"))
}

fn frame_local_at(frame: &'static str, idx: Expr) -> Expr {
    Expr::AccE(Box::new(frame_locals(frame)), Path::Idx(Box::new(idx)))
}

fn local_call_args(x: u32) -> Vec<Arg> {
    vec![Arg::Var(STORE_PARAM), Arg::Nat(x)]
}

fn with_local_call_args(x: u32) -> Vec<Arg> {
    vec![Arg::Var(STORE_PARAM), Arg::Nat(x), Arg::Var("val")]
}

/// `Step_read/local.get x { Push $local(z, x) }` (local.al L1–3)
pub fn step_read_local_get_template(x: u32) -> Vec<Instr> {
    vec![Instr::PushI(Expr::Call("local", local_call_args(x)))]
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
        SemOp::LocalGet(x) => format!("Step_read/local.get {x}\n  push $local(z, {x})"),
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
    fn ret_bits(nt: NumType) -> Instr {
        Instr::ReturnI(nat(nt.bit_width()))
    }
    fn if_nt(nt: NumType) -> Instr {
        Instr::IfI {
            cond: InstrCond::Pred(Pred::NumTypeEq(p("nt"), nt)),
            then_steps: vec![ret_bits(nt)],
            else_steps: vec![],
        }
    }
    FuncA {
        id: "sizenn",
        params: &SIZENN_PARAMS,
        body: vec![
            if_nt(NumType::I32),
            if_nt(NumType::I64),
            if_nt(NumType::F32),
            if_nt(NumType::F64),
            Instr::FailI,
        ],
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
                cond: InstrCond::Pred(and(le(int(0), p("i")), lt(p("i"), threshold.clone()))),
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
        body: vec![Instr::IfI {
            cond: InstrCond::Pred(Pred::OptIsNone(p("X_opt"))),
            then_steps: vec![Instr::ReturnI(Expr::EmptyList)],
            else_steps: vec![
                Instr::LetI {
                    lhs: LetLhs::Var("w"),
                    expr: Expr::Choose(Box::new(p("X_opt"))),
                },
                Instr::ReturnI(Expr::SingletonList(Box::new(p("w")))),
            ],
        }],
    }
}

// =============================================================================
// bool b  (wasm-2.0.al L1356–1362)
// =============================================================================

pub fn bool_def() -> FuncA {
    FuncA {
        id: "bool",
        params: BOOL_PARAMS,
        body: vec![
            Instr::IfI {
                cond: InstrCond::Pred(eq(p("b"), Expr::BoolLit(false))),
                then_steps: vec![Instr::ReturnI(nat(0))],
                else_steps: vec![],
            },
            Instr::AssertI(InstrCond::Pred(eq(p("b"), Expr::BoolLit(true)))),
            Instr::ReturnI(nat(1)),
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
                vec![Arg::ExpA(Box::new(p("N"))), Arg::ExpA(Box::new(p("i_1")))],
            ))),
            Box::new(rat_coerce(call(
                "signed_",
                vec![Arg::ExpA(Box::new(p("N"))), Arg::ExpA(Box::new(p("i_2")))],
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
                then_steps: vec![Instr::IfI {
                    cond: InstrCond::Pred(eq(p("i_2"), nat(0))),
                    then_steps: vec![Instr::ReturnI(Expr::EmptyOpt)],
                    else_steps: vec![Instr::ReturnI(Expr::SomeOpt(Box::new(nat_coerce(
                        trunc_div(p("i_1"), p("i_2")),
                    ))))],
                }],
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
                                vec![Arg::ExpA(Box::new(p("N"))), Arg::ExpA(Box::new(p("i_1")))],
                            ),
                            call(
                                "signed_",
                                vec![Arg::ExpA(Box::new(p("N"))), Arg::ExpA(Box::new(p("i_2")))],
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
    let trunc_div =
        |a: Expr, b: Expr| truncz(Expr::Div(Box::new(rat_coerce(a)), Box::new(rat_coerce(b))));
    FuncA {
        id: "irem_",
        params: IREM_PARAMS,
        body: vec![
            Instr::IfI {
                cond: InstrCond::Pred(eq(p("sx"), Expr::SignLit(Sign::U))),
                then_steps: vec![Instr::IfI {
                    cond: InstrCond::Pred(eq(p("i_2"), nat(0))),
                    then_steps: vec![Instr::ReturnI(Expr::EmptyOpt)],
                    else_steps: vec![Instr::ReturnI(Expr::SomeOpt(Box::new(nat_coerce(
                        Expr::Sub(
                            Box::new(int_coerce(p("i_1"))),
                            Box::new(int_coerce(Expr::Mul(
                                Box::new(p("i_2")),
                                Box::new(nat_coerce(trunc_div(p("i_1"), p("i_2")))),
                            ))),
                        ),
                    ))))],
                }],
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
                            vec![Arg::ExpA(Box::new(p("N"))), Arg::ExpA(Box::new(p("i_1")))],
                        ),
                    },
                    Instr::LetI {
                        lhs: LetLhs::Var("j_2"),
                        expr: call(
                            "signed_",
                            vec![Arg::ExpA(Box::new(p("N"))), Arg::ExpA(Box::new(p("i_2")))],
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
                Instr::LetI {
                    lhs: LetLhs::BinOpCase(BinOpCase::Div, "sx"),
                    expr: p("binop_"),
                },
                list_idiv,
            ],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::BinOpCaseIs(p("binop_"), BinOpCase::Rem)),
            then_steps: vec![
                Instr::LetI {
                    lhs: LetLhs::BinOpCase(BinOpCase::Rem, "sx"),
                    expr: p("binop_"),
                },
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
            cond: InstrCond::Pred(Pred::BinOpEq(p("binop_"), WasmBinOp::Xor)),
            then_steps: vec![singleton_binop(inn_ixor(
                sizenn_nt.clone(),
                i_1.clone(),
                i_2.clone(),
            ))],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::BinOpCaseIs(p("binop_"), BinOpCase::Shr)),
            then_steps: vec![
                Instr::LetI {
                    lhs: LetLhs::BinOpCase(BinOpCase::Shr, "sx"),
                    expr: p("binop_"),
                },
                Instr::IfI {
                    cond: InstrCond::Pred(eq(p("sx"), Expr::SignLit(Sign::U))),
                    then_steps: vec![singleton_binop(inn_ishr(
                        sizenn_nt.clone(),
                        Sign::U,
                        i_1.clone(),
                        i_2.clone(),
                    ))],
                    else_steps: vec![Instr::AssertI(InstrCond::Pred(eq(
                        p("sx"),
                        Expr::SignLit(Sign::S),
                    ))), singleton_binop(inn_ishr(
                        sizenn_nt.clone(),
                        Sign::S,
                        i_1.clone(),
                        i_2.clone(),
                    ))],
                },
            ],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::BinOpEq(p("binop_"), WasmBinOp::Rotl)),
            then_steps: vec![singleton_binop(inn_irotl(
                sizenn_nt.clone(),
                i_1.clone(),
                i_2.clone(),
            ))],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::BinOpEq(p("binop_"), WasmBinOp::Rotr)),
            then_steps: vec![singleton_binop(inn_irotr(
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
    let fnn_return = |name: &'static str| {
        Instr::ReturnI(call(
            name,
            vec![
                Arg::ExpA(Box::new(sizenn_nt.clone())),
                Arg::ExpA(Box::new(i_1.clone())),
                Arg::ExpA(Box::new(i_2.clone())),
            ],
        ))
    };
    let fnn_branch = vec![
        Instr::IfI {
            cond: InstrCond::Pred(Pred::BinOpEq(p("binop_"), WasmBinOp::Add)),
            then_steps: vec![fnn_return("fadd_")],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::BinOpEq(p("binop_"), WasmBinOp::Sub)),
            then_steps: vec![fnn_return("fsub_")],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::BinOpEq(p("binop_"), WasmBinOp::Mul)),
            then_steps: vec![fnn_return("fmul_")],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::BinOpEq(p("binop_"), WasmBinOp::FloatDiv)),
            then_steps: vec![fnn_return("fdiv_")],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::BinOpEq(p("binop_"), WasmBinOp::Min)),
            then_steps: vec![fnn_return("fmin_")],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::BinOpEq(p("binop_"), WasmBinOp::Max)),
            then_steps: vec![fnn_return("fmax_")],
            else_steps: vec![],
        },
        Instr::AssertI(InstrCond::Pred(Pred::BinOpEq(
            p("binop_"),
            WasmBinOp::Copysign,
        ))),
        fnn_return("fcopysign_"),
    ];
    FuncA {
        id: "binop_",
        params: BINOP_PARAMS,
        body: {
            let mut body = vec![Instr::IfI {
                cond: InstrCond::Pred(Pred::TypeIsInn(p("numtype"))),
                then_steps: inn_branch,
                else_steps: vec![],
            }];
            body.push(Instr::AssertI(InstrCond::Pred(Pred::TypeIsFnn(p("numtype")))));
            body.extend(fnn_branch);
            body
        },
    }
}

// =============================================================================
// ieqz_, ieq_, ine_, ilt_, igt_, ile_, ige_  (wasm-2.0.al L1551–1597)
// =============================================================================

pub fn ieqz_def() -> FuncA {
    FuncA {
        id: "ieqz_",
        params: IEQZ_PARAMS,
        body: vec![Instr::ReturnI(bool_of(cmp_eq(p("i_1"), nat(0))))],
    }
}

pub fn ieq_def() -> FuncA {
    FuncA {
        id: "ieq_",
        params: IEQ_PARAMS,
        body: vec![Instr::ReturnI(bool_of(cmp_eq(p("i_1"), p("i_2"))))],
    }
}

pub fn ine_def() -> FuncA {
    FuncA {
        id: "ine_",
        params: IEQ_PARAMS,
        body: vec![Instr::ReturnI(bool_of(cmp_ne(p("i_1"), p("i_2"))))],
    }
}

fn signed_i(n: Expr, i: Expr) -> Expr {
    call(
        "signed_",
        vec![Arg::ExpA(Box::new(n)), Arg::ExpA(Box::new(i))],
    )
}

pub fn ilt_def() -> FuncA {
    FuncA {
        id: "ilt_",
        params: IORDERED_PARAMS,
        body: vec![
            Instr::IfI {
                cond: InstrCond::Pred(eq(p("sx"), Expr::SignLit(Sign::U))),
                then_steps: vec![Instr::ReturnI(bool_of(cmp_lt(p("i_1"), p("i_2"))))],
                else_steps: vec![],
            },
            Instr::AssertI(InstrCond::Pred(eq(p("sx"), Expr::SignLit(Sign::S)))),
            Instr::ReturnI(bool_of(cmp_lt(
                int_coerce(signed_i(p("N"), p("i_1"))),
                int_coerce(signed_i(p("N"), p("i_2"))),
            ))),
        ],
    }
}

pub fn igt_def() -> FuncA {
    FuncA {
        id: "igt_",
        params: IORDERED_PARAMS,
        body: vec![
            Instr::IfI {
                cond: InstrCond::Pred(eq(p("sx"), Expr::SignLit(Sign::U))),
                then_steps: vec![Instr::ReturnI(bool_of(cmp_gt(p("i_1"), p("i_2"))))],
                else_steps: vec![],
            },
            Instr::AssertI(InstrCond::Pred(eq(p("sx"), Expr::SignLit(Sign::S)))),
            Instr::ReturnI(bool_of(cmp_gt(
                int_coerce(signed_i(p("N"), p("i_1"))),
                int_coerce(signed_i(p("N"), p("i_2"))),
            ))),
        ],
    }
}

pub fn ile_def() -> FuncA {
    FuncA {
        id: "ile_",
        params: IORDERED_PARAMS,
        body: vec![
            Instr::IfI {
                cond: InstrCond::Pred(eq(p("sx"), Expr::SignLit(Sign::U))),
                then_steps: vec![Instr::ReturnI(bool_of(cmp_le(p("i_1"), p("i_2"))))],
                else_steps: vec![],
            },
            Instr::AssertI(InstrCond::Pred(eq(p("sx"), Expr::SignLit(Sign::S)))),
            Instr::ReturnI(bool_of(cmp_le(
                int_coerce(signed_i(p("N"), p("i_1"))),
                int_coerce(signed_i(p("N"), p("i_2"))),
            ))),
        ],
    }
}

pub fn ige_def() -> FuncA {
    FuncA {
        id: "ige_",
        params: IORDERED_PARAMS,
        body: vec![
            Instr::IfI {
                cond: InstrCond::Pred(eq(p("sx"), Expr::SignLit(Sign::U))),
                then_steps: vec![Instr::ReturnI(bool_of(cmp_ge(p("i_1"), p("i_2"))))],
                else_steps: vec![],
            },
            Instr::AssertI(InstrCond::Pred(eq(p("sx"), Expr::SignLit(Sign::S)))),
            Instr::ReturnI(bool_of(cmp_ge(
                int_coerce(signed_i(p("N"), p("i_1"))),
                int_coerce(signed_i(p("N"), p("i_2"))),
            ))),
        ],
    }
}

// =============================================================================
// testop_ numtype testop_ iN  (wasm-2.0.al L1555–1557)
// =============================================================================

pub fn testop_def() -> FuncA {
    FuncA {
        id: "testop_",
        params: TESTOP_PARAMS,
        body: vec![
            Instr::AssertI(InstrCond::Pred(Pred::TypeIsInn(p("numtype")))),
            Instr::AssertI(InstrCond::Pred(Pred::TestOpEq(
                p("testop_"),
                WasmTestOp::Eqz,
            ))),
            Instr::ReturnI(call(
                "ieqz_",
                vec![
                    Arg::ExpA(Box::new(call(
                        "sizenn",
                        vec![Arg::ExpA(Box::new(p("numtype")))],
                    ))),
                    Arg::ExpA(Box::new(p("iN"))),
                ],
            )),
        ],
    }
}

// =============================================================================
// relop_ numtype relop_ iN_1 iN_2  (wasm-2.0.al L1599–1642)
// =============================================================================

fn relop_inn_branch(sizenn_nt: Expr, i_1: Expr, i_2: Expr) -> Vec<Instr> {
    let ieq_call = |i_1: Expr, i_2: Expr| {
        call(
            "ieq_",
            vec![
                Arg::ExpA(Box::new(sizenn_nt.clone())),
                Arg::ExpA(Box::new(i_1)),
                Arg::ExpA(Box::new(i_2)),
            ],
        )
    };
    let ordered_call = |name: &'static str, sx: Expr, i_1: Expr, i_2: Expr| {
        call(
            name,
            vec![
                Arg::ExpA(Box::new(sizenn_nt.clone())),
                Arg::ExpA(Box::new(sx)),
                Arg::ExpA(Box::new(i_1)),
                Arg::ExpA(Box::new(i_2)),
            ],
        )
    };
    vec![
        Instr::IfI {
            cond: InstrCond::Pred(Pred::RelOpEq(p("relop_"), WasmRelOp::Eq)),
            then_steps: vec![Instr::ReturnI(ieq_call(i_1.clone(), i_2.clone()))],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::RelOpEq(p("relop_"), WasmRelOp::Ne)),
            then_steps: vec![Instr::ReturnI(call(
                "ine_",
                vec![
                    Arg::ExpA(Box::new(sizenn_nt.clone())),
                    Arg::ExpA(Box::new(i_1.clone())),
                    Arg::ExpA(Box::new(i_2.clone())),
                ],
            ))],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::RelOpCaseIs(p("relop_"), RelOpCase::Lt)),
            then_steps: vec![
                Instr::LetI {
                    lhs: LetLhs::RelOpCase(RelOpCase::Lt, "sx"),
                    expr: p("relop_"),
                },
                Instr::ReturnI(ordered_call("ilt_", p("sx"), i_1.clone(), i_2.clone())),
            ],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::RelOpCaseIs(p("relop_"), RelOpCase::Gt)),
            then_steps: vec![
                Instr::LetI {
                    lhs: LetLhs::RelOpCase(RelOpCase::Gt, "sx"),
                    expr: p("relop_"),
                },
                Instr::ReturnI(ordered_call("igt_", p("sx"), i_1.clone(), i_2.clone())),
            ],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::RelOpCaseIs(p("relop_"), RelOpCase::Le)),
            then_steps: vec![
                Instr::LetI {
                    lhs: LetLhs::RelOpCase(RelOpCase::Le, "sx"),
                    expr: p("relop_"),
                },
                Instr::ReturnI(ordered_call("ile_", p("sx"), i_1.clone(), i_2.clone())),
            ],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::RelOpCaseIs(p("relop_"), RelOpCase::Ge)),
            then_steps: vec![
                Instr::LetI {
                    lhs: LetLhs::RelOpCase(RelOpCase::Ge, "sx"),
                    expr: p("relop_"),
                },
                Instr::ReturnI(ordered_call("ige_", p("sx"), i_1, i_2)),
            ],
            else_steps: vec![],
        },
    ]
}

pub fn relop_def() -> FuncA {
    let sizenn_nt = call("sizenn", vec![Arg::ExpA(Box::new(p("numtype")))]);
    let i_1 = p("iN_1");
    let i_2 = p("iN_2");
    let fnn_branch = vec![
        Instr::IfI {
            cond: InstrCond::Pred(Pred::RelOpEq(p("relop_"), WasmRelOp::Eq)),
            then_steps: vec![Instr::ReturnI(call(
                "feq_",
                vec![
                    Arg::ExpA(Box::new(sizenn_nt.clone())),
                    Arg::ExpA(Box::new(i_1.clone())),
                    Arg::ExpA(Box::new(i_2.clone())),
                ],
            ))],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::RelOpEq(p("relop_"), WasmRelOp::Ne)),
            then_steps: vec![Instr::ReturnI(call(
                "fne_",
                vec![
                    Arg::ExpA(Box::new(sizenn_nt.clone())),
                    Arg::ExpA(Box::new(i_1.clone())),
                    Arg::ExpA(Box::new(i_2.clone())),
                ],
            ))],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::RelOpEq(p("relop_"), WasmRelOp::Flt)),
            then_steps: vec![Instr::ReturnI(call(
                "flt_",
                vec![
                    Arg::ExpA(Box::new(sizenn_nt.clone())),
                    Arg::ExpA(Box::new(i_1.clone())),
                    Arg::ExpA(Box::new(i_2.clone())),
                ],
            ))],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::RelOpEq(p("relop_"), WasmRelOp::Fgt)),
            then_steps: vec![Instr::ReturnI(call(
                "fgt_",
                vec![
                    Arg::ExpA(Box::new(sizenn_nt.clone())),
                    Arg::ExpA(Box::new(i_1.clone())),
                    Arg::ExpA(Box::new(i_2.clone())),
                ],
            ))],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::RelOpEq(p("relop_"), WasmRelOp::Fle)),
            then_steps: vec![Instr::ReturnI(call(
                "fle_",
                vec![
                    Arg::ExpA(Box::new(sizenn_nt.clone())),
                    Arg::ExpA(Box::new(i_1.clone())),
                    Arg::ExpA(Box::new(i_2.clone())),
                ],
            ))],
            else_steps: vec![],
        },
        Instr::AssertI(InstrCond::Pred(Pred::RelOpEq(p("relop_"), WasmRelOp::Fge))),
        Instr::ReturnI(call(
            "fge_",
            vec![
                Arg::ExpA(Box::new(sizenn_nt.clone())),
                Arg::ExpA(Box::new(i_1.clone())),
                Arg::ExpA(Box::new(i_2.clone())),
            ],
        )),
    ];
    FuncA {
        id: "relop_",
        params: RELOP_PARAMS,
        body: {
            let mut body = vec![Instr::IfI {
                cond: InstrCond::Pred(Pred::TypeIsInn(p("numtype"))),
                then_steps: relop_inn_branch(sizenn_nt.clone(), i_1.clone(), i_2.clone()),
                else_steps: vec![],
            }];
            body.push(Instr::AssertI(InstrCond::Pred(Pred::TypeIsFnn(p("numtype")))));
            body.extend(fnn_branch);
            body
        },
    }
}

// =============================================================================
// unop_ numtype unop_ iN  (wasm-2.0.al L1402–1439)
// =============================================================================

pub fn unop_def() -> FuncA {
    let sizenn_nt = call("sizenn", vec![Arg::ExpA(Box::new(p("numtype")))]);
    let inn_branch = vec![
        Instr::IfI {
            cond: InstrCond::Pred(Pred::UnOpEq(p("unop_"), WasmUnOp::Clz)),
            then_steps: vec![Instr::ReturnI(Expr::SingletonList(Box::new(call(
                "iclz_",
                vec![
                    Arg::ExpA(Box::new(sizenn_nt.clone())),
                    Arg::ExpA(Box::new(p("iN"))),
                ],
            ))))],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::UnOpEq(p("unop_"), WasmUnOp::Ctz)),
            then_steps: vec![Instr::ReturnI(Expr::SingletonList(Box::new(call(
                "ictz_",
                vec![
                    Arg::ExpA(Box::new(sizenn_nt.clone())),
                    Arg::ExpA(Box::new(p("iN"))),
                ],
            ))))],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::UnOpEq(p("unop_"), WasmUnOp::Popcnt)),
            then_steps: vec![Instr::ReturnI(Expr::SingletonList(Box::new(call(
                "ipopcnt_",
                vec![
                    Arg::ExpA(Box::new(sizenn_nt.clone())),
                    Arg::ExpA(Box::new(p("iN"))),
                ],
            ))))],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::UnOpCaseIs(p("unop_"), UnOpCase::Extend)),
            then_steps: vec![
                Instr::LetI {
                    lhs: LetLhs::UnOpCase(UnOpCase::Extend, "M"),
                    expr: p("unop_"),
                },
                Instr::ReturnI(Expr::SingletonList(Box::new(call(
                    "extend__",
                    vec![
                        Arg::ExpA(Box::new(p("M"))),
                        Arg::ExpA(Box::new(sizenn_nt.clone())),
                        Arg::ExpA(Box::new(Expr::SignLit(Sign::S))),
                        Arg::ExpA(Box::new(call(
                            "wrap__",
                            vec![
                                Arg::ExpA(Box::new(sizenn_nt.clone())),
                                Arg::ExpA(Box::new(p("M"))),
                                Arg::ExpA(Box::new(p("iN"))),
                            ],
                        ))),
                    ],
                )))),
            ],
            else_steps: vec![],
        },
    ];
    let fnn_return = |name: &'static str| {
        Instr::ReturnI(call(
            name,
            vec![
                Arg::ExpA(Box::new(sizenn_nt.clone())),
                Arg::ExpA(Box::new(p("iN"))),
            ],
        ))
    };
    let fnn_branch = vec![
        Instr::IfI {
            cond: InstrCond::Pred(Pred::UnOpEq(p("unop_"), WasmUnOp::Abs)),
            then_steps: vec![fnn_return("fabs_")],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::UnOpEq(p("unop_"), WasmUnOp::Neg)),
            then_steps: vec![fnn_return("fneg_")],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::UnOpEq(p("unop_"), WasmUnOp::Sqrt)),
            then_steps: vec![fnn_return("fsqrt_")],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::UnOpEq(p("unop_"), WasmUnOp::Ceil)),
            then_steps: vec![fnn_return("fceil_")],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::UnOpEq(p("unop_"), WasmUnOp::Floor)),
            then_steps: vec![fnn_return("ffloor_")],
            else_steps: vec![],
        },
        Instr::IfI {
            cond: InstrCond::Pred(Pred::UnOpEq(p("unop_"), WasmUnOp::Trunc)),
            then_steps: vec![fnn_return("ftrunc_")],
            else_steps: vec![],
        },
        Instr::AssertI(InstrCond::Pred(Pred::UnOpEq(p("unop_"), WasmUnOp::Nearest))),
        fnn_return("fnearest_"),
    ];
    FuncA {
        id: "unop_",
        params: UNOP_PARAMS,
        body: {
            let mut body = vec![Instr::IfI {
                cond: InstrCond::Pred(Pred::TypeIsInn(p("numtype"))),
                then_steps: inn_branch,
                else_steps: vec![],
            }];
            body.push(Instr::AssertI(InstrCond::Pred(Pred::TypeIsFnn(p("numtype")))));
            body.extend(fnn_branch);
            body
        },
    }
}

const ICLZ_PARAMS: &[Param] = &[mp("N", ParamType::Nat), mp("iN", ParamType::Nat)];
const ICTZ_PARAMS: &[Param] = &[mp("N", ParamType::Nat), mp("iN", ParamType::Nat)];
const IPOPCNT_PARAMS: &[Param] = &[mp("N", ParamType::Nat), mp("iN", ParamType::Nat)];
const TRUNCZ_PARAMS: &[Param] = &[mp("r", ParamType::Any)];

/// `iclz_` / `ictz_` / `ipopcnt_` are `hint(builtin)` in spectec; bodies live in the evaluator.
pub fn iclz_def() -> FuncA {
    FuncA {
        id: "iclz_",
        params: ICLZ_PARAMS,
        body: vec![Instr::FailI],
    }
}

pub fn ictz_def() -> FuncA {
    FuncA {
        id: "ictz_",
        params: ICTZ_PARAMS,
        body: vec![Instr::FailI],
    }
}

pub fn ipopcnt_def() -> FuncA {
    FuncA {
        id: "ipopcnt_",
        params: IPOPCNT_PARAMS,
        body: vec![Instr::FailI],
    }
}

pub fn truncz_def() -> FuncA {
    FuncA {
        id: "truncz",
        params: TRUNCZ_PARAMS,
        body: vec![Instr::FailI],
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
        "bool" => bool_def(),
        "ieqz_" => ieqz_def(),
        "ieq_" => ieq_def(),
        "ine_" => ine_def(),
        "ilt_" => ilt_def(),
        "igt_" => igt_def(),
        "ile_" => ile_def(),
        "ige_" => ige_def(),
        "testop_" => testop_def(),
        "relop_" => relop_def(),
        "unop_" => unop_def(),
        "idiv_" => idiv_def(),
        "irem_" => irem_def(),
        "binop_" => binop_def(),
        "iclz_" => iclz_def(),
        "ictz_" => ictz_def(),
        "ipopcnt_" => ipopcnt_def(),
        "truncz" => truncz_def(),
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

    #[test]
    fn bool_def_returns_i32() {
        let def = bool_def();
        assert_eq!(def.id, "bool");
        assert_eq!(def.params, BOOL_PARAMS);
    }

    #[test]
    fn relop_def_has_inn_and_fnn_paths() {
        let def = relop_def();
        assert_eq!(def.id, "relop_");
        assert_eq!(def.params, RELOP_PARAMS);
        assert!(def.body.len() >= 2);
    }

    #[test]
    fn unop_def_has_inn_and_fnn_paths() {
        let def = unop_def();
        assert_eq!(def.id, "unop_");
        assert_eq!(def.params, UNOP_PARAMS);
        assert!(def.body.len() >= 2);
    }

    #[test]
    fn lookup_includes_relop_helpers() {
        assert!(lookup_func("ieq_").is_some());
        assert!(lookup_func("relop_").is_some());
        assert!(lookup_func("testop_").is_some());
        assert!(lookup_func("unop_").is_some());
        assert!(lookup_func("iclz_").is_some());
        assert!(lookup_func("ictz_").is_some());
        assert!(lookup_func("ipopcnt_").is_some());
        assert!(lookup_func("truncz").is_some());
    }
}
