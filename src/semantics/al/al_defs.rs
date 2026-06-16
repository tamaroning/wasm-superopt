//! SpecTec AL definitions transcribed from [`binop.al`](../../../../binop.al).
//!
//! Types and `$fn` bodies from `binop.al` live here. Step templates use
//! [`AlMetaExpr`](super::meta::AlMetaExpr) for primitive `binop` (`+`, `-`, `*`, …).
//! Lowering to flat [`AlSpec`](super::ir::AlSpec) is for hand-written step specs only;
//! binop `SemOp`s use the meta encoder ([`super::encode_sym`], [`super::exec_step_z3`]).

#![allow(dead_code)] // mirrors binop.al; not every def is wired to instantiate yet

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

use super::meta::{
    AlMetaArg, AlMetaExpr, AlMetaFnDef, AlMetaFnStep, AlMetaParam, AlMetaParamType, AlMetaPred,
    AlMetaStep, PopPattern,
};

const fn mp(name: &'static str, ty: AlMetaParamType) -> AlMetaParam {
    AlMetaParam { name, ty }
}

const SIZE_PARAMS: &[AlMetaParam] = &[mp("valtype", AlMetaParamType::ValType)];
const SIZENN_PARAMS: &[AlMetaParam] = &[mp("nt", AlMetaParamType::NumType)];
const SIGNED_PARAMS: &[AlMetaParam] = &[
    mp("N", AlMetaParamType::Nat),
    mp("i", AlMetaParamType::Nat),
];
const INV_SIGNED_PARAMS: &[AlMetaParam] = &[
    mp("N", AlMetaParamType::Nat),
    mp("i", AlMetaParamType::Int),
];
const LIST_PARAMS: &[AlMetaParam] = &[
    mp("X", AlMetaParamType::Any),
    mp("X_opt", AlMetaParamType::Any),
];
const IDIV_PARAMS: &[AlMetaParam] = &[
    mp("N", AlMetaParamType::Nat),
    mp("sx", AlMetaParamType::Sign),
    mp("i_1", AlMetaParamType::Nat),
    mp("i_2", AlMetaParamType::Nat),
];
const IREM_PARAMS: &[AlMetaParam] = &[
    mp("N", AlMetaParamType::Nat),
    mp("sx", AlMetaParamType::Sign),
    mp("i_1", AlMetaParamType::Nat),
    mp("i_2", AlMetaParamType::Nat),
];
const BINOP_PARAMS: &[AlMetaParam] = &[
    mp("numtype", AlMetaParamType::NumType),
    mp("binop_", AlMetaParamType::BinOp),
    mp("iN_1", AlMetaParamType::Nat),
    mp("iN_2", AlMetaParamType::Nat),
];

fn p(name: &'static str) -> AlMetaExpr {
    AlMetaExpr::Param(name)
}

fn nat(n: u32) -> AlMetaExpr {
    AlMetaExpr::NatLit(n)
}

fn int(n: i32) -> AlMetaExpr {
    AlMetaExpr::IntLit(n)
}

fn call(name: &'static str, args: Vec<AlMetaArg>) -> AlMetaExpr {
    AlMetaExpr::Call(name, args)
}

fn int_coerce(expr: AlMetaExpr) -> AlMetaExpr {
    AlMetaExpr::IntCoerce(Box::new(expr))
}

fn nat_coerce(expr: AlMetaExpr) -> AlMetaExpr {
    AlMetaExpr::NatCoerce(Box::new(expr))
}

fn rat_coerce(expr: AlMetaExpr) -> AlMetaExpr {
    AlMetaExpr::RatCoerce(Box::new(expr))
}

fn truncz(expr: AlMetaExpr) -> AlMetaExpr {
    AlMetaExpr::TruncZ(Box::new(expr))
}

fn pow2(exp: AlMetaExpr) -> AlMetaExpr {
    AlMetaExpr::Pow(Box::new(nat(2)), Box::new(exp))
}

fn n_minus_1(n: AlMetaExpr) -> AlMetaExpr {
    nat_coerce(AlMetaExpr::Sub(
        Box::new(int_coerce(n)),
        Box::new(int(1)),
    ))
}

fn half_modulus(n: AlMetaExpr) -> AlMetaExpr {
    pow2(n_minus_1(n))
}

fn full_modulus(n: AlMetaExpr) -> AlMetaExpr {
    pow2(n)
}

fn eq(a: AlMetaExpr, b: AlMetaExpr) -> AlMetaPred {
    AlMetaPred::Eq(a, b)
}

fn lt(a: AlMetaExpr, b: AlMetaExpr) -> AlMetaPred {
    AlMetaPred::Lt(a, b)
}

fn le(a: AlMetaExpr, b: AlMetaExpr) -> AlMetaPred {
    AlMetaPred::Le(a, b)
}

fn and(a: AlMetaPred, b: AlMetaPred) -> AlMetaPred {
    AlMetaPred::And(Box::new(a), Box::new(b))
}

fn wrap_mod(nat_expr: AlMetaExpr, modulus: AlMetaExpr) -> AlMetaExpr {
    AlMetaExpr::Mod(Box::new(nat_expr), Box::new(modulus))
}

/// `$((i_1 + i_2) \ (2 ^ N))` — spectec equation, not a separate `$fn` def.
fn inn_iadd(n: AlMetaExpr, i_1: AlMetaExpr, i_2: AlMetaExpr) -> AlMetaExpr {
    wrap_mod(
        AlMetaExpr::Add(Box::new(i_1), Box::new(i_2)),
        full_modulus(n),
    )
}

/// `$((2^N + i_1 - i_2) \ 2^N)` — spectec equation.
fn inn_isub(n: AlMetaExpr, i_1: AlMetaExpr, i_2: AlMetaExpr) -> AlMetaExpr {
    let modulus = full_modulus(n);
    nat_coerce(wrap_mod(
        AlMetaExpr::Sub(
            Box::new(int_coerce(AlMetaExpr::Add(
                Box::new(modulus.clone()),
                Box::new(i_1),
            ))),
            Box::new(int_coerce(i_2)),
        ),
        int_coerce(modulus),
    ))
}

/// `$((i_1 * i_2) \ (2 ^ N))` — spectec equation.
fn inn_imul(n: AlMetaExpr, i_1: AlMetaExpr, i_2: AlMetaExpr) -> AlMetaExpr {
    wrap_mod(
        AlMetaExpr::Mul(Box::new(i_1), Box::new(i_2)),
        full_modulus(n),
    )
}

/// `$iand_` / `$ior_` — spectec `hint(builtin)`: `(m op n) & mask(N)`.
fn inn_iand(n: AlMetaExpr, i_1: AlMetaExpr, i_2: AlMetaExpr) -> AlMetaExpr {
    wrap_mod(
        AlMetaExpr::BitAnd(Box::new(i_1), Box::new(i_2)),
        full_modulus(n),
    )
}

fn inn_ior(n: AlMetaExpr, i_1: AlMetaExpr, i_2: AlMetaExpr) -> AlMetaExpr {
    wrap_mod(
        AlMetaExpr::BitOr(Box::new(i_1), Box::new(i_2)),
        full_modulus(n),
    )
}

fn inn_ishl(n: AlMetaExpr, i_1: AlMetaExpr, i_2: AlMetaExpr) -> AlMetaExpr {
    wrap_mod(
        AlMetaExpr::Shl(
            Box::new(i_1),
            Box::new(AlMetaExpr::Rem(Box::new(i_2), Box::new(n.clone()))),
        ),
        full_modulus(n),
    )
}

// =============================================================================
// Step_pure/binop nt binop  (binop.al L5–15)
// =============================================================================

pub fn step_pure_binop_template(nt: NumType, binop: WasmBinOp) -> Vec<AlMetaStep> {
    let binop_call = AlMetaExpr::Call(
        "binop_",
        vec![
            AlMetaArg::NumType(nt),
            AlMetaArg::BinOp(binop),
            AlMetaArg::Var("c_1"),
            AlMetaArg::Var("c_2"),
        ],
    );
    vec![
        AlMetaStep::Assert(AlMetaExpr::TopValue(nt)),
        AlMetaStep::Pop(PopPattern::NumConst("c_2")),
        AlMetaStep::Assert(AlMetaExpr::TopValue(nt)),
        AlMetaStep::Pop(PopPattern::NumConst("c_1")),
        AlMetaStep::If {
            cond: AlMetaExpr::OptionalLen(Box::new(binop_call.clone())),
            then_steps: vec![AlMetaStep::Trap],
            else_steps: vec![
                AlMetaStep::Let {
                    name: "c",
                    expr: AlMetaExpr::Choose(Box::new(binop_call)),
                },
                AlMetaStep::Push(AlMetaExpr::Call(
                    "const",
                    vec![AlMetaArg::NumType(nt), AlMetaArg::Var("c")],
                )),
            ],
        },
    ]
}

// =============================================================================
// size valtype  (binop.al L17–34)
// =============================================================================

pub fn size_def() -> AlMetaFnDef {
    fn ret(v: u32) -> AlMetaFnStep {
        AlMetaFnStep::Return(nat(v))
    }
    fn if_valtype(vt: ValType, n: u32) -> AlMetaFnStep {
        AlMetaFnStep::If {
            cond: eq(p("valtype"), AlMetaExpr::ValTypeLit(vt)),
            then_steps: vec![ret(n)],
            else_steps: vec![],
        }
    }
    AlMetaFnDef {
        name: "size",
        params: &SIZE_PARAMS,
        body: vec![
            if_valtype(ValType::I32, 32),
            if_valtype(ValType::I64, 64),
            if_valtype(ValType::F32, 32),
            if_valtype(ValType::F64, 64),
            if_valtype(ValType::V128, 128),
            AlMetaFnStep::Fail,
        ],
    }
}

// =============================================================================
// sizenn nt  (binop.al L36–38)
// =============================================================================

pub fn sizenn_def() -> AlMetaFnDef {
    AlMetaFnDef {
        name: "sizenn",
        params: &SIZENN_PARAMS,
        body: vec![AlMetaFnStep::Return(call(
            "size",
            vec![AlMetaArg::Expr(Box::new(p("nt")))],
        ))],
    }
}

// =============================================================================
// signed_ N i  (binop.al L41–48)
// =============================================================================

pub fn signed_def() -> AlMetaFnDef {
    let threshold = half_modulus(p("N"));
    AlMetaFnDef {
        name: "signed_",
        params: &SIGNED_PARAMS,
        body: vec![
            AlMetaFnStep::If {
                cond: lt(p("i"), threshold.clone()),
                then_steps: vec![AlMetaFnStep::Return(int_coerce(p("i")))],
                else_steps: vec![],
            },
            AlMetaFnStep::Assert(le(threshold, p("i"))),
            AlMetaFnStep::Assert(lt(p("i"), full_modulus(p("N")))),
            AlMetaFnStep::Return(AlMetaExpr::Sub(
                Box::new(int_coerce(p("i"))),
                Box::new(int_coerce(full_modulus(p("N")))),
            )),
        ],
    }
}

// =============================================================================
// inv_signed_ N i  (binop.al L51–58)
// =============================================================================

pub fn inv_signed_def() -> AlMetaFnDef {
    let threshold = half_modulus(p("N"));
    AlMetaFnDef {
        name: "inv_signed_",
        params: &INV_SIGNED_PARAMS,
        body: vec![
            AlMetaFnStep::If {
                cond: and(
                    le(int(0), p("i")),
                    lt(p("i"), threshold.clone()),
                ),
                then_steps: vec![AlMetaFnStep::Return(nat_coerce(p("i")))],
                else_steps: vec![],
            },
            AlMetaFnStep::Assert(le(
                AlMetaExpr::Sub(Box::new(int(0)), Box::new(threshold.clone())),
                p("i"),
            )),
            AlMetaFnStep::Assert(lt(p("i"), int(0))),
            AlMetaFnStep::Return(nat_coerce(AlMetaExpr::Add(
                Box::new(p("i")),
                Box::new(full_modulus(p("N"))),
            ))),
        ],
    }
}

// =============================================================================
// list_ X X?{X <- X}  (binop.al L60–66)
// =============================================================================

pub fn list_def() -> AlMetaFnDef {
    AlMetaFnDef {
        name: "list_",
        params: &LIST_PARAMS,
        body: vec![
            AlMetaFnStep::If {
                cond: AlMetaPred::OptIsNone(p("X_opt")),
                then_steps: vec![AlMetaFnStep::Return(AlMetaExpr::EmptyList)],
                else_steps: vec![
                    AlMetaFnStep::Let {
                        name: "w",
                        expr: AlMetaExpr::Choose(Box::new(p("X_opt"))),
                    },
                    AlMetaFnStep::Return(AlMetaExpr::SingletonList(Box::new(p("w")))),
                ],
            },
        ],
    }
}

// =============================================================================
// idiv_ N sx i_1 i_2  (wasm-2.0.al L1445–1459)
// =============================================================================

pub fn idiv_def() -> AlMetaFnDef {
    let trunc_div = |i_1: AlMetaExpr, i_2: AlMetaExpr| {
        truncz(AlMetaExpr::Div(
            Box::new(rat_coerce(i_1)),
            Box::new(rat_coerce(i_2)),
        ))
    };
    let signed_overflow = eq(
        AlMetaExpr::Div(
            Box::new(rat_coerce(call(
                "signed_",
                vec![
                    AlMetaArg::Expr(Box::new(p("N"))),
                    AlMetaArg::Expr(Box::new(p("i_1"))),
                ],
            ))),
            Box::new(rat_coerce(call(
                "signed_",
                vec![
                    AlMetaArg::Expr(Box::new(p("N"))),
                    AlMetaArg::Expr(Box::new(p("i_2"))),
                ],
            ))),
        ),
        rat_coerce(half_modulus(p("N"))),
    );
    AlMetaFnDef {
        name: "idiv_",
        params: IDIV_PARAMS,
        body: vec![
            AlMetaFnStep::If {
                cond: eq(p("sx"), AlMetaExpr::SignLit(Sign::U)),
                then_steps: vec![
                    AlMetaFnStep::If {
                        cond: eq(p("i_2"), nat(0)),
                        then_steps: vec![AlMetaFnStep::Return(AlMetaExpr::EmptyOpt)],
                        else_steps: vec![AlMetaFnStep::Return(AlMetaExpr::SomeOpt(Box::new(
                            nat_coerce(trunc_div(p("i_1"), p("i_2"))),
                        )))],
                    },
                ],
                else_steps: vec![],
            },
            AlMetaFnStep::Assert(eq(p("sx"), AlMetaExpr::SignLit(Sign::S))),
            AlMetaFnStep::If {
                cond: eq(p("i_2"), nat(0)),
                then_steps: vec![AlMetaFnStep::Return(AlMetaExpr::EmptyOpt)],
                else_steps: vec![],
            },
            AlMetaFnStep::If {
                cond: signed_overflow,
                then_steps: vec![AlMetaFnStep::Return(AlMetaExpr::EmptyOpt)],
                else_steps: vec![AlMetaFnStep::Return(AlMetaExpr::SomeOpt(Box::new(call(
                    "inv_signed_",
                    vec![
                        AlMetaArg::Expr(Box::new(p("N"))),
                        AlMetaArg::Expr(Box::new(trunc_div(
                            call(
                                "signed_",
                                vec![
                                    AlMetaArg::Expr(Box::new(p("N"))),
                                    AlMetaArg::Expr(Box::new(p("i_1"))),
                                ],
                            ),
                            call(
                                "signed_",
                                vec![
                                    AlMetaArg::Expr(Box::new(p("N"))),
                                    AlMetaArg::Expr(Box::new(p("i_2"))),
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

pub fn irem_def() -> AlMetaFnDef {
    let trunc_div = |a: AlMetaExpr, b: AlMetaExpr| {
        truncz(AlMetaExpr::Div(
            Box::new(rat_coerce(a)),
            Box::new(rat_coerce(b)),
        ))
    };
    AlMetaFnDef {
        name: "irem_",
        params: IREM_PARAMS,
        body: vec![
            AlMetaFnStep::If {
                cond: eq(p("sx"), AlMetaExpr::SignLit(Sign::U)),
                then_steps: vec![
                    AlMetaFnStep::If {
                        cond: eq(p("i_2"), nat(0)),
                        then_steps: vec![AlMetaFnStep::Return(AlMetaExpr::EmptyOpt)],
                        else_steps: vec![AlMetaFnStep::Return(AlMetaExpr::SomeOpt(Box::new(
                            nat_coerce(AlMetaExpr::Sub(
                                Box::new(int_coerce(p("i_1"))),
                                Box::new(int_coerce(AlMetaExpr::Mul(
                                    Box::new(p("i_2")),
                                    Box::new(nat_coerce(trunc_div(p("i_1"), p("i_2")))),
                                ))),
                            )),
                        )))],
                    },
                ],
                else_steps: vec![],
            },
            AlMetaFnStep::Assert(eq(p("sx"), AlMetaExpr::SignLit(Sign::S))),
            AlMetaFnStep::If {
                cond: eq(p("i_2"), nat(0)),
                then_steps: vec![AlMetaFnStep::Return(AlMetaExpr::EmptyOpt)],
                else_steps: vec![
                    AlMetaFnStep::Let {
                        name: "j_1",
                        expr: call(
                            "signed_",
                            vec![
                                AlMetaArg::Expr(Box::new(p("N"))),
                                AlMetaArg::Expr(Box::new(p("i_1"))),
                            ],
                        ),
                    },
                    AlMetaFnStep::Let {
                        name: "j_2",
                        expr: call(
                            "signed_",
                            vec![
                                AlMetaArg::Expr(Box::new(p("N"))),
                                AlMetaArg::Expr(Box::new(p("i_2"))),
                            ],
                        ),
                    },
                    AlMetaFnStep::Return(AlMetaExpr::SomeOpt(Box::new(call(
                        "inv_signed_",
                        vec![
                            AlMetaArg::Expr(Box::new(p("N"))),
                            AlMetaArg::Expr(Box::new(AlMetaExpr::Sub(
                                Box::new(int_coerce(p("j_1"))),
                                Box::new(int_coerce(AlMetaExpr::Mul(
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

fn singleton_binop(call_expr: AlMetaExpr) -> AlMetaFnStep {
    AlMetaFnStep::Return(AlMetaExpr::SingletonList(Box::new(call_expr)))
}

pub fn binop_def() -> AlMetaFnDef {
    let sizenn_nt = call("sizenn", vec![AlMetaArg::Expr(Box::new(p("numtype")))]);
    let list_partial = |partial_call: AlMetaExpr| {
        AlMetaFnStep::Return(call(
            "list_",
            vec![
                AlMetaArg::Expr(Box::new(p("numtype"))),
                AlMetaArg::Expr(Box::new(partial_call)),
            ],
        ))
    };
    let list_idiv = list_partial(call(
        "idiv_",
        vec![
            AlMetaArg::Expr(Box::new(sizenn_nt.clone())),
            AlMetaArg::Expr(Box::new(p("sx"))),
            AlMetaArg::Expr(Box::new(p("iN_1"))),
            AlMetaArg::Expr(Box::new(p("iN_2"))),
        ],
    ));
    let list_irem = list_partial(call(
        "irem_",
        vec![
            AlMetaArg::Expr(Box::new(sizenn_nt.clone())),
            AlMetaArg::Expr(Box::new(p("sx"))),
            AlMetaArg::Expr(Box::new(p("iN_1"))),
            AlMetaArg::Expr(Box::new(p("iN_2"))),
        ],
    ));
    let i_1 = p("iN_1");
    let i_2 = p("iN_2");
    let inn_branch = vec![
        AlMetaFnStep::If {
            cond: AlMetaPred::BinOpEq(p("binop_"), WasmBinOp::Add),
            then_steps: vec![singleton_binop(inn_iadd(
                sizenn_nt.clone(),
                i_1.clone(),
                i_2.clone(),
            ))],
            else_steps: vec![],
        },
        AlMetaFnStep::If {
            cond: AlMetaPred::BinOpEq(p("binop_"), WasmBinOp::Sub),
            then_steps: vec![singleton_binop(inn_isub(
                sizenn_nt.clone(),
                i_1.clone(),
                i_2.clone(),
            ))],
            else_steps: vec![],
        },
        AlMetaFnStep::If {
            cond: AlMetaPred::BinOpEq(p("binop_"), WasmBinOp::Mul),
            then_steps: vec![singleton_binop(inn_imul(
                sizenn_nt.clone(),
                i_1.clone(),
                i_2.clone(),
            ))],
            else_steps: vec![],
        },
        AlMetaFnStep::If {
            cond: AlMetaPred::BinOpCaseIs(p("binop_"), BinOpCase::Div),
            then_steps: vec![
                AlMetaFnStep::LetBinOpCase {
                    case: BinOpCase::Div,
                    sx_name: "sx",
                    binop: p("binop_"),
                },
                list_idiv,
            ],
            else_steps: vec![],
        },
        AlMetaFnStep::If {
            cond: AlMetaPred::BinOpCaseIs(p("binop_"), BinOpCase::Rem),
            then_steps: vec![
                AlMetaFnStep::LetBinOpCase {
                    case: BinOpCase::Rem,
                    sx_name: "sx",
                    binop: p("binop_"),
                },
                list_irem,
            ],
            else_steps: vec![],
        },
        AlMetaFnStep::If {
            cond: AlMetaPred::BinOpEq(p("binop_"), WasmBinOp::And),
            then_steps: vec![singleton_binop(inn_iand(
                sizenn_nt.clone(),
                i_1.clone(),
                i_2.clone(),
            ))],
            else_steps: vec![],
        },
        AlMetaFnStep::If {
            cond: AlMetaPred::BinOpEq(p("binop_"), WasmBinOp::Or),
            then_steps: vec![singleton_binop(inn_ior(
                sizenn_nt.clone(),
                i_1.clone(),
                i_2.clone(),
            ))],
            else_steps: vec![],
        },
        AlMetaFnStep::If {
            cond: AlMetaPred::BinOpEq(p("binop_"), WasmBinOp::Shl),
            then_steps: vec![singleton_binop(inn_ishl(
                sizenn_nt.clone(),
                i_1.clone(),
                i_2.clone(),
            ))],
            else_steps: vec![],
        },
    ];
    AlMetaFnDef {
        name: "binop_",
        params: BINOP_PARAMS,
        body: vec![
            AlMetaFnStep::If {
                cond: AlMetaPred::TypeIsInn(p("numtype")),
                then_steps: inn_branch,
                else_steps: vec![AlMetaFnStep::Assert(AlMetaPred::TypeIsFnn(p("numtype")))],
            },
        ],
    }
}

/// Look up a SpecTec `$fn` definition by name.
pub fn lookup_fn(name: &str) -> Option<AlMetaFnDef> {
    Some(match name {
        "size" => size_def(),
        "sizenn" => sizenn_def(),
        "signed_" => signed_def(),
        "inv_signed_" => inv_signed_def(),
        "list_" => list_def(),
        "idiv_" => idiv_def(),
        "irem_" => irem_def(),
        "binop_" => binop_def(),
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn size_def_matches_binop_al() {
        let def = size_def();
        assert_eq!(def.name, "size");
        assert_eq!(def.params, SIZE_PARAMS);
        assert!(matches!(def.body.last(), Some(AlMetaFnStep::Fail)));
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
