//! Embedded SpecTec AL definitions from [`binop.al`](../../../../binop.al).
//!
//! Meta-level step templates and partial evaluation of helper functions
//! (`binop_`, `idiv_`, etc.) used by [`super::instantiate::step_pure_binop`].

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

/// Meta-level expression (instantiation-time only).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AlMetaExpr {
    /// `$name(args...)`
    Call(&'static str, Vec<AlMetaArg>),
    /// `|expr| <= 0` — optional/list is empty (ε).
    OptionalLen(Box<AlMetaExpr>),
    /// `choose(expr)` — extract value from singleton optional.
    Choose(Box<AlMetaExpr>),
    /// `top_value(nt)` — stack type assertion (no-op at runtime for i32).
    TopValue(NumType),
}

/// Typed pop pattern (`numtype_0.CONST name` in AL).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PopPattern {
    NumConst(&'static str),
}

/// Meta-level step from `Step_pure/binop` and similar templates.
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

/// `Step_pure/binop nt binop` from binop.al L5–15 (parameters `nt`, `binop` substituted at instantiate).
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
        // L6: Assert (top_value(nt))
        AlMetaStep::Assert(AlMetaExpr::TopValue(nt)),
        // L7: Pop (numtype_0.CONST c_2)
        AlMetaStep::Pop(PopPattern::NumConst("c_2")),
        // L8: Assert (top_value(num)) — no-op for i32-only
        AlMetaStep::Assert(AlMetaExpr::TopValue(nt)),
        // L9: Pop (numtype_0.CONST c_1)
        AlMetaStep::Pop(PopPattern::NumConst("c_1")),
        // L10–12: If ((|$binop_(...)| <= 0)) { Trap }
        AlMetaStep::If {
            cond: AlMetaExpr::OptionalLen(Box::new(binop_call.clone())),
            then_steps: vec![AlMetaStep::Trap],
            else_steps: vec![
                // L13: Let c = choose($binop_(...))
                AlMetaStep::Let {
                    name: "c",
                    expr: AlMetaExpr::Choose(Box::new(binop_call)),
                },
                // L14: Push (nt.CONST c)
                AlMetaStep::Push(AlMetaExpr::Call(
                    "const",
                    vec![AlMetaArg::NumType(nt), AlMetaArg::Var("c")],
                )),
            ],
        },
    ]
}

/// Partially evaluate `$binop_(numtype, binop, iN_1, iN_2)` for Inn / i32.
///
/// Encodes the dispatch in binop.al L119–134 and partiality via `$idiv_` (L81–101).
pub fn instantiate_binop_(nt: NumType, binop: WasmBinOp) -> BinopInstantiation {
    let kind = binop
        .to_binop_kind()
        .unwrap_or_else(|| panic!("unsupported binop for {nt:?}: {binop:?}"));
    assert_eq!(nt, NumType::I32, "only I32 supported in this phase");
    debug_assert_eq!(sizenn(nt), nt.bit_width());
    BinopInstantiation {
        kind,
        is_partial: binop.is_partial(),
        lhs: "c1",
        rhs: "c2",
    }
}

/// `size` / `sizenn` from binop.al L17–38.
pub const fn sizenn(nt: NumType) -> u32 {
    nt.bit_width()
}

/// Whether `$idiv_(N, sx, i_1, i_2)` returns ε — binop.al L81–101.
pub fn idiv_empty_concrete(n: u32, sx: Sign, i_1: u32, i_2: u32) -> bool {
    if i_2 == 0 {
        return true;
    }
    if sx == Sign::U {
        return false;
    }
    let signed_1 = signed_nat(n, i_1);
    let signed_2 = signed_nat(n, i_2);
    (signed_1 as i64) / (signed_2 as i64) == (1i64 << (n - 1))
}

/// `$signed_(N, i)` for concrete `nat` values — binop.al L41–48.
fn signed_nat(n: u32, i: u32) -> i32 {
    let threshold = 1u32 << (n - 1);
    if i < threshold {
        i as i32
    } else {
        (i as i64 - (1i64 << n)) as i32
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::semantics::al::ir::BinOpKind;

    #[test]
    fn instantiate_binop_i32_div_s_is_partial() {
        let inst = instantiate_binop_(NumType::I32, WasmBinOp::Div(Sign::S));
        assert_eq!(inst.kind, BinOpKind::DivS);
        assert!(inst.is_partial);
    }

    #[test]
    fn instantiate_binop_i32_add_is_total() {
        let inst = instantiate_binop_(NumType::I32, WasmBinOp::Add);
        assert_eq!(inst.kind, BinOpKind::Add);
        assert!(!inst.is_partial);
    }

    #[test]
    fn idiv_empty_matches_binop_kind_div_s() {
        assert!(idiv_empty_concrete(32, Sign::S, 0, 0));
        assert!(idiv_empty_concrete(
            32,
            Sign::S,
            i32::MIN as u32,
            (-1i32) as u32
        ));
        assert!(!idiv_empty_concrete(32, Sign::S, 4, 2));
        assert_eq!(
            BinOpKind::DivS.binop_empty_concrete(0, 0),
            idiv_empty_concrete(32, Sign::S, 0, 0)
        );
        assert_eq!(
            BinOpKind::DivS.binop_empty_concrete(i32::MIN, -1),
            idiv_empty_concrete(32, Sign::S, i32::MIN as u32, (-1i32) as u32)
        );
    }
}
