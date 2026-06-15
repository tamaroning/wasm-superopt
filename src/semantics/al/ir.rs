//! AL IR types and binop partiality (`binop(a,b) = ε`).

use super::super::I32_BITS;
use z3::Context;
use z3::ast::{Ast, BV, Bool};

/// Wasm numeric type parameter (`nt` / `valtype` in SpecTec AL).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum NumType {
    I32,
}

impl NumType {
    /// `size` / `sizenn` from binop.al (L17–38).
    pub const fn bit_width(self) -> u32 {
        match self {
            NumType::I32 => 32,
        }
    }
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AlSpec {
    pub steps: Vec<AlStep>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AlStep {
    Pop(&'static str),
    Push(AlExpr),
    SetLocal {
        idx: u32,
        var: &'static str,
    },
    StoreMem {
        addr: &'static str,
        val: &'static str,
    },
    If {
        cond: AlCond,
        then_steps: Vec<AlStep>,
        else_steps: Vec<AlStep>,
    },
    Trap,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AlExpr {
    ConstI32(i32),
    #[allow(dead_code)]
    Var(&'static str),
    BinOp(BinOpKind, &'static str, &'static str),
    LocalGet(u32),
    MemLoad(&'static str),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AlCond {
    BinOpEmpty(BinOpKind, &'static str, &'static str),
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
