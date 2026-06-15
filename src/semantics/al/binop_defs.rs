//! SpecTec AL definitions transcribed from [`binop.al`](../../../../binop.al).
//!
//! This file contains **definitions only** — step templates and `$fn` helpers.
//! Lowering to flat [`AlSpec`](super::ir::AlSpec) is in [`super::instantiate`].

#![allow(dead_code)] // mirrors binop.al; not every def is wired to instantiate yet

use super::ir::{BinOpKind, NumType, Sign, WasmBinOp};
use super::meta::{AlMetaArg, AlMetaExpr, AlMetaStep, BinopInstantiation, PopPattern};

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
        // L6: Assert (top_value(nt))
        AlMetaStep::Assert(AlMetaExpr::TopValue(nt)),
        // L7: Pop (numtype_0.CONST c_2)
        AlMetaStep::Pop(PopPattern::NumConst("c_2")),
        // L8: Assert (top_value(num))
        AlMetaStep::Assert(AlMetaExpr::TopValue(nt)),
        // L9: Pop (numtype_0.CONST c_1)
        AlMetaStep::Pop(PopPattern::NumConst("c_1")),
        // L10–12: If ((|$binop_(nt, binop, c_1, c_2)| <= 0)) { Trap }
        AlMetaStep::If {
            cond: AlMetaExpr::OptionalLen(Box::new(binop_call.clone())),
            then_steps: vec![AlMetaStep::Trap],
            else_steps: vec![
                // L13: Let c = choose($binop_(nt, binop, c_1, c_2))
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

// =============================================================================
// size valtype  (binop.al L17–34)
// =============================================================================

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ValType {
    I32,
    I64,
    F32,
    F64,
    V128,
}

pub const fn size(valtype: ValType) -> Option<u32> {
    match valtype {
        ValType::I32 => Some(32),
        ValType::I64 => Some(64),
        ValType::F32 => Some(32),
        ValType::F64 => Some(64),
        ValType::V128 => Some(128),
    }
}

// =============================================================================
// sizenn nt  (binop.al L36–38)
// =============================================================================

pub const fn sizenn(nt: NumType) -> u32 {
    size(valtype_of(nt)).expect("size(nt) defined for supported numtypes")
}

const fn valtype_of(nt: NumType) -> ValType {
    match nt {
        NumType::I32 => ValType::I32,
    }
}

// =============================================================================
// signed_ N i  (binop.al L41–48)
// =============================================================================

pub fn signed_(n: u32, i: u32) -> i32 {
    let threshold = 1u32 << (n - 1);
    if i < threshold {
        i as i32
    } else {
        (i as i64 - (1i64 << n)) as i32
    }
}

// =============================================================================
// inv_signed_ N i  (binop.al L51–58)
// =============================================================================

pub fn inv_signed_(n: u32, i: i32) -> u32 {
    let threshold = 1i32 << (n - 1);
    if (0..threshold).contains(&i) {
        i as u32
    } else {
        (i as i64 + (1i64 << n)) as u32
    }
}

// =============================================================================
// list_ X X?{X <- X}  (binop.al L60–66)
// =============================================================================

/// Whether optional `opt` is ε (empty list).
pub fn list_is_empty<T>(opt: Option<T>) -> bool {
    opt.is_none()
}

// =============================================================================
// iadd_ N i_1 i_2  (binop.al L68–70)
// =============================================================================

pub fn iadd_(n: u32, i_1: u32, i_2: u32) -> u32 {
    (i_1.wrapping_add(i_2)) % (1u32 << n)
}

// =============================================================================
// isub_ N i_1 i_2  (binop.al L72–74)
// =============================================================================

pub fn isub_(n: u32, i_1: u32, i_2: u32) -> u32 {
    let modulus = 1u64 << n;
    let extended = modulus + i_1 as u64;
    (extended.wrapping_sub(i_2 as u64) % modulus) as u32
}

// =============================================================================
// imul_ N i_1 i_2  (binop.al L76–78)
// =============================================================================

pub fn imul_(n: u32, i_1: u32, i_2: u32) -> u32 {
    (i_1.wrapping_mul(i_2)) % (1u32 << n)
}

// =============================================================================
// idiv_ N sx i_1 i_2  (binop.al L81–101)
// =============================================================================

/// Whether `$idiv_(N, sx, i_1, i_2)` returns ε.
pub fn idiv_is_empty(n: u32, sx: Sign, i_1: u32, i_2: u32) -> bool {
    if i_2 == 0 {
        return true;
    }
    if sx == Sign::U {
        return false;
    }
    let j_1 = signed_(n, i_1);
    let j_2 = signed_(n, i_2);
    (j_1 as i64) / (j_2 as i64) == (1i64 << (n - 1))
}

pub fn idiv_(n: u32, sx: Sign, i_1: u32, i_2: u32) -> Option<u32> {
    if idiv_is_empty(n, sx, i_1, i_2) {
        return None;
    }
    match sx {
        Sign::U => {
            let q = (i_1 as u64) / (i_2 as u64);
            Some(q as u32)
        }
        Sign::S => {
            let j_1 = signed_(n, i_1);
            let j_2 = signed_(n, i_2);
            let q = j_1 / j_2;
            Some(inv_signed_(n, q))
        }
    }
}

// =============================================================================
// irem_ N sx i_1 i_2  (binop.al L103–117)
// =============================================================================

pub fn irem_is_empty(_n: u32, _sx: Sign, _i_1: u32, i_2: u32) -> bool {
    i_2 == 0
}

pub fn irem_(n: u32, sx: Sign, i_1: u32, i_2: u32) -> Option<u32> {
    if irem_is_empty(n, sx, i_1, i_2) {
        return None;
    }
    match sx {
        Sign::U => {
            let q = (i_1 as u64) / (i_2 as u64);
            let r = i_1.wrapping_sub(i_2.wrapping_mul(q as u32));
            Some(r)
        }
        Sign::S => {
            let j_1 = signed_(n, i_1);
            let j_2 = signed_(n, i_2);
            let q = j_1 / j_2;
            let r = j_1 - j_2 * q;
            Some(inv_signed_(n, r))
        }
    }
}

// =============================================================================
// binop_ numtype binop_ iN_1 iN_2  (binop.al L119–183)
// =============================================================================

/// Partial evaluation of `$binop_(numtype, binop, iN_1, iN_2)` for fixed `nt`/`binop`.
///
/// Inn branch (L120–161): ADD, SUB, MUL, DIV sx, REM sx, AND, OR, XOR, SHL, SHR sx, ROTL, ROTR.
/// Fnn branch (L162–182): ADD, SUB, MUL, DIV, MIN, MAX, COPYSIGN — not yet instantiated.
pub fn instantiate_binop_(nt: NumType, binop: WasmBinOp) -> BinopInstantiation {
    let kind = binop
        .to_binop_kind()
        .unwrap_or_else(|| panic!("unsupported binop for {nt:?}: {binop:?}"));
    assert_eq!(nt, NumType::I32, "only I32 Inn binops supported in this phase");
    debug_assert_eq!(sizenn(nt), nt.bit_width());
    BinopInstantiation {
        kind,
        is_partial: binop.is_partial(),
        lhs: "c1",
        rhs: "c2",
    }
}

/// Concrete `$binop_(I32, binop, iN_1, iN_2)` for supported integer binops.
pub fn binop_concrete(nt: NumType, binop: WasmBinOp, i_1: u32, i_2: u32) -> Option<u32> {
    assert_eq!(nt, NumType::I32);
    let n = sizenn(nt);
    match binop {
        WasmBinOp::Add => Some(iadd_(n, i_1, i_2)),
        WasmBinOp::Mul => Some(imul_(n, i_1, i_2)),
        WasmBinOp::Shl => Some(i_1.wrapping_shl(i_2 % n) & ((1u32 << n) - 1)),
        WasmBinOp::Div(sx) => idiv_(n, sx, i_1, i_2),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
