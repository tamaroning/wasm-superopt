//! SpecTec AL definitions transcribed from [`binop.al`](../../../../binop.al).
//!
//! This file contains **definitions only** — step templates and `$fn` helpers.
//! Primitive `binop` from `Language.md` (`+`, `-`, `*`, `&`, `|`, `<<`, `\`, …) are
//! encoded inline via [`AlMetaExpr`](super::meta::AlMetaExpr), not as separate `$fn`s.
//! Lowering to flat [`AlSpec`](super::ir::AlSpec) is for hand-written step specs only;
//! binop `SemOp`s use the meta encoder ([`super::sym`], [`super::meta_z3`]).

#![allow(dead_code)] // mirrors binop.al; not every def is wired to instantiate yet

use super::ir::{BinOpKind, NumType, Sign, WasmBinOp};
use super::meta::{
    AlMetaArg, AlMetaExpr, AlMetaFnDef, AlMetaFnStep, AlMetaParam, AlMetaParamType, AlMetaPred,
    AlMetaStep, BinOpCase, PopPattern, ValType,
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
    use crate::semantics::al::eval::{binop_concrete, idiv_is_empty, size, sizenn};

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

    #[test]
    fn idiv_empty_matches_binop_kind_div_s() {
        assert!(idiv_is_empty(32, Sign::S, 0, 0));
        assert!(idiv_is_empty(
            32,
            Sign::S,
            i32::MIN as u32,
            (-1i32) as u32
        ));
        assert!(!idiv_is_empty(32, Sign::S, 4, 2));
        assert_eq!(
            BinOpKind::DivS.binop_empty_concrete(0, 0),
            idiv_is_empty(32, Sign::S, 0, 0)
        );
        assert_eq!(
            BinOpKind::DivS.binop_empty_concrete(i32::MIN, -1),
            idiv_is_empty(32, Sign::S, i32::MIN as u32, (-1i32) as u32)
        );
    }

    #[test]
    fn size_matches_binop_al() {
        assert_eq!(size(ValType::I32), Some(32));
        assert_eq!(size(ValType::V128), Some(128));
        assert_eq!(sizenn(NumType::I32), 32);
    }

    #[test]
    fn binop_concrete_sub_and_and_or() {
        assert_eq!(
            binop_concrete(NumType::I32, WasmBinOp::Sub, 10, 3),
            Some(7)
        );
        assert_eq!(
            binop_concrete(NumType::I32, WasmBinOp::Sub, 0, 1),
            Some((-1i32) as u32)
        );
        assert_eq!(
            binop_concrete(NumType::I32, WasmBinOp::Sub, 3, 5),
            Some((-2i32) as u32)
        );
        assert_eq!(
            binop_concrete(NumType::I32, WasmBinOp::And, 0b1100, 0b1010),
            Some(0b1000)
        );
        assert_eq!(
            binop_concrete(NumType::I32, WasmBinOp::Or, 0b1100, 0b1010),
            Some(0b1110)
        );
    }

    #[test]
    fn binop_concrete_fuzz_no_panic() {
        use crate::semantics::al::ir::{NumType, Sign, WasmBinOp};
        let ops = [
            WasmBinOp::Add,
            WasmBinOp::Sub,
            WasmBinOp::Mul,
            WasmBinOp::Shl,
            WasmBinOp::And,
            WasmBinOp::Or,
            WasmBinOp::Div(Sign::U),
            WasmBinOp::Div(Sign::S),
            WasmBinOp::Rem(Sign::U),
            WasmBinOp::Rem(Sign::S),
        ];
        let samples: [u32; 16] = [
            0,
            1,
            2,
            3,
            5,
            10,
            0x7fff_ffff,
            0x8000_0000,
            0x8000_0001,
            0xffff_ffff,
            0xffff_fffe,
            100,
            50,
            0x1234_5678,
            0xdead_beef,
            0x0000_0007,
        ];
        for op in ops {
            for &a in &samples {
                for &b in &samples {
                    let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                        binop_concrete(NumType::I32, op, a, b)
                    }))
                    .unwrap_or_else(|_| {
                        panic!("binop_concrete panicked: {op:?} {a} {b}");
                    });
                }
            }
        }
    }

    #[test]
    fn binop_concrete_div_u_and_rem_u() {
        assert_eq!(
            binop_concrete(NumType::I32, WasmBinOp::Div(Sign::U), 0x8000_0000, 1),
            Some(0x8000_0000)
        );
        assert_eq!(
            binop_concrete(NumType::I32, WasmBinOp::Rem(Sign::U), 10, 0),
            None
        );
        assert_eq!(
            binop_concrete(NumType::I32, WasmBinOp::Rem(Sign::U), 10, 3),
            Some(1)
        );
    }

    #[test]
    fn binop_concrete_div_s_matches_idiv() {
        assert_eq!(
            binop_concrete(NumType::I32, WasmBinOp::Div(Sign::S), 8, 2),
            Some(4)
        );
        assert_eq!(
            binop_concrete(NumType::I32, WasmBinOp::Div(Sign::S), 8, 0),
            None
        );
    }
}
