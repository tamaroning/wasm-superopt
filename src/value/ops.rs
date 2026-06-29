//! Typed Wasm value-op catalog for rule synthesis.

use crate::al::NumType;
use crate::lang::ValueLang;
use crate::semantics::StackTy;
use egg::Id;
use serde::{Deserialize, Serialize};
use std::fmt;

const POPS_2_I32: &[StackTy] = &[StackTy::I32, StackTy::I32];
const POPS_2_I64: &[StackTy] = &[StackTy::I64, StackTy::I64];
const POPS_2_F32: &[StackTy] = &[StackTy::F32, StackTy::F32];
const POPS_2_F64: &[StackTy] = &[StackTy::F64, StackTy::F64];
const POPS_1_I32: &[StackTy] = &[StackTy::I32];
const POPS_1_I64: &[StackTy] = &[StackTy::I64];
const POPS_1_F32: &[StackTy] = &[StackTy::F32];
const POPS_1_F64: &[StackTy] = &[StackTy::F64];

/// Rule context: free-variable types and the root expression type.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct RuleSignature {
    pub inputs: Vec<StackTy>,
    pub output: StackTy,
}

impl RuleSignature {
    pub fn new(inputs: Vec<StackTy>, output: StackTy) -> Self {
        Self { inputs, output }
    }
}

impl fmt::Display for RuleSignature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for (i, ty) in self.inputs.iter().enumerate() {
            if i > 0 {
                write!(f, ",")?;
            }
            write!(f, "{ty:?}")?;
        }
        write!(f, "]->{:?}", self.output)
    }
}

/// Synthesis instruction with a fixed pop/push stack signature.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ValueOp {
    I32Add,
    I32Sub,
    I32Mul,
    I32DivU,
    I32DivS,
    I32RemU,
    I32RemS,
    I32Shl,
    I32And,
    I32Or,
    I32Xor,
    I32ShrU,
    I32ShrS,
    I32Rotl,
    I32Rotr,
    I32Eq,
    I32Ne,
    I32LtS,
    I32LeS,
    I32GtS,
    I32Eqz,
    I32Clz,
    I32Ctz,
    I32Popcnt,
    I64Add,
    I64Sub,
    I64Mul,
    I64DivU,
    I64DivS,
    I64RemU,
    I64RemS,
    I64Shl,
    I64And,
    I64Or,
    I64Xor,
    I64ShrU,
    I64ShrS,
    I64Rotl,
    I64Rotr,
    I64Eq,
    I64Ne,
    I64LtS,
    I64LeS,
    I64GtS,
    I64Eqz,
    I64Clz,
    I64Ctz,
    I64Popcnt,
    I64ExtendI32S,
    I64ExtendI32U,
    I32WrapI64,
    F32Add,
    F32Sub,
    F32Mul,
    F32Div,
    F32Min,
    F32Max,
    F32Copysign,
    F32Eq,
    F32Ne,
    F32Lt,
    F32Le,
    F32Gt,
    F32Ge,
    F32Abs,
    F32Neg,
    F32Sqrt,
    F32Ceil,
    F32Floor,
    F32Trunc,
    F32Nearest,
    F64Add,
    F64Sub,
    F64Mul,
    F64Div,
    F64Min,
    F64Max,
    F64Copysign,
    F64Eq,
    F64Ne,
    F64Lt,
    F64Le,
    F64Gt,
    F64Ge,
    F64Abs,
    F64Neg,
    F64Sqrt,
    F64Ceil,
    F64Floor,
    F64Trunc,
    F64Nearest,
}

impl StackTy {
    pub fn bit_width(self) -> u32 {
        match self {
            Self::I32 | Self::F32 => 32,
            Self::I64 | Self::F64 => 64,
        }
    }

    pub fn al_num_type(self) -> NumType {
        match self {
            Self::I32 => NumType::I32,
            Self::I64 => NumType::I64,
            Self::F32 => NumType::F32,
            Self::F64 => NumType::F64,
        }
    }

    pub fn is_float(self) -> bool {
        matches!(self, Self::F32 | Self::F64)
    }
}

impl ValueOp {
    pub fn all() -> &'static [Self] {
        use ValueOp::*;
        const OPS: &[ValueOp] = &[
            I32Add,
            I32Sub,
            I32Mul,
            I32DivU,
            I32DivS,
            I32RemU,
            I32RemS,
            I32Shl,
            I32And,
            I32Or,
            I32Xor,
            I32ShrU,
            I32ShrS,
            I32Rotl,
            I32Rotr,
            I32Eq,
            I32Ne,
            I32LtS,
            I32LeS,
            I32GtS,
            I32Eqz,
            I32Clz,
            I32Ctz,
            I32Popcnt,
            I64Add,
            I64Sub,
            I64Mul,
            I64DivU,
            I64DivS,
            I64RemU,
            I64RemS,
            I64Shl,
            I64And,
            I64Or,
            I64Xor,
            I64ShrU,
            I64ShrS,
            I64Rotl,
            I64Rotr,
            I64Eq,
            I64Ne,
            I64LtS,
            I64LeS,
            I64GtS,
            I64Eqz,
            I64Clz,
            I64Ctz,
            I64Popcnt,
            I64ExtendI32S,
            I64ExtendI32U,
            I32WrapI64,
            F32Add,
            F32Sub,
            F32Mul,
            F32Div,
            F32Min,
            F32Max,
            F32Copysign,
            F32Eq,
            F32Ne,
            F32Lt,
            F32Le,
            F32Gt,
            F32Ge,
            F32Abs,
            F32Neg,
            F32Sqrt,
            F32Ceil,
            F32Floor,
            F32Trunc,
            F32Nearest,
            F64Add,
            F64Sub,
            F64Mul,
            F64Div,
            F64Min,
            F64Max,
            F64Copysign,
            F64Eq,
            F64Ne,
            F64Lt,
            F64Le,
            F64Gt,
            F64Ge,
            F64Abs,
            F64Neg,
            F64Sqrt,
            F64Ceil,
            F64Floor,
            F64Trunc,
            F64Nearest,
        ];
        OPS
    }

    pub fn pops(self) -> &'static [StackTy] {
        use ValueOp::*;
        match self {
            I32Add | I32Sub | I32Mul | I32DivU | I32DivS | I32RemU | I32RemS | I32Shl
            | I32And | I32Or | I32Xor | I32ShrU | I32ShrS | I32Rotl | I32Rotr | I32Eq
            | I32Ne | I32LtS | I32LeS | I32GtS => POPS_2_I32,
            I32Eqz | I32Clz | I32Ctz | I32Popcnt => POPS_1_I32,
            I64Add | I64Sub | I64Mul | I64DivU | I64DivS | I64RemU | I64RemS | I64Shl
            | I64And | I64Or | I64Xor | I64ShrU | I64ShrS | I64Rotl | I64Rotr | I64Eq
            | I64Ne | I64LtS | I64LeS | I64GtS => POPS_2_I64,
            I64Eqz | I64Clz | I64Ctz | I64Popcnt => POPS_1_I64,
            F32Add | F32Sub | F32Mul | F32Div | F32Min | F32Max | F32Copysign | F32Eq
            | F32Ne | F32Lt | F32Le | F32Gt | F32Ge => POPS_2_F32,
            F32Abs | F32Neg | F32Sqrt | F32Ceil | F32Floor | F32Trunc | F32Nearest => {
                POPS_1_F32
            }
            F64Add | F64Sub | F64Mul | F64Div | F64Min | F64Max | F64Copysign | F64Eq
            | F64Ne | F64Lt | F64Le | F64Gt | F64Ge => POPS_2_F64,
            F64Abs | F64Neg | F64Sqrt | F64Ceil | F64Floor | F64Trunc | F64Nearest => {
                POPS_1_F64
            }
            I64ExtendI32S | I64ExtendI32U => POPS_1_I32,
            I32WrapI64 => POPS_1_I64,
        }
    }

    pub fn push(self) -> StackTy {
        use ValueOp::*;
        match self {
            I32Add | I32Sub | I32Mul | I32DivU | I32DivS | I32RemU | I32RemS | I32Shl
            | I32And | I32Or | I32Xor | I32ShrU | I32ShrS | I32Rotl | I32Rotr | I32Clz
            | I32Ctz | I32Popcnt => StackTy::I32,
            I32Eq | I32Ne | I32LtS | I32LeS | I32GtS | I32Eqz => StackTy::I32,
            I64Add | I64Sub | I64Mul | I64DivU | I64DivS | I64RemU | I64RemS | I64Shl
            | I64And | I64Or | I64Xor | I64ShrU | I64ShrS | I64Rotl | I64Rotr | I64Clz
            | I64Ctz | I64Popcnt | I64ExtendI32S | I64ExtendI32U => StackTy::I64,
            I64Eq | I64Ne | I64LtS | I64LeS | I64GtS | I64Eqz => StackTy::I32,
            F32Add | F32Sub | F32Mul | F32Div | F32Min | F32Max | F32Copysign | F32Abs
            | F32Neg | F32Sqrt | F32Ceil | F32Floor | F32Trunc | F32Nearest => StackTy::F32,
            F32Eq | F32Ne | F32Lt | F32Le | F32Gt | F32Ge => StackTy::I32,
            F64Add | F64Sub | F64Mul | F64Div | F64Min | F64Max | F64Copysign | F64Abs
            | F64Neg | F64Sqrt | F64Ceil | F64Floor | F64Trunc | F64Nearest => StackTy::F64,
            F64Eq | F64Ne | F64Lt | F64Le | F64Gt | F64Ge => StackTy::I32,
            I32WrapI64 => StackTy::I32,
        }
    }

    pub fn pattern_name(self) -> &'static str {
        use ValueOp::*;
        match self {
            I32Add => "i32.add",
            I32Sub => "i32.sub",
            I32Mul => "i32.mul",
            I32DivU => "i32.div_u",
            I32DivS => "i32.div_s",
            I32RemU => "i32.rem_u",
            I32RemS => "i32.rem_s",
            I32Shl => "i32.shl",
            I32And => "i32.and",
            I32Or => "i32.or",
            I32Xor => "i32.xor",
            I32ShrU => "i32.shr_u",
            I32ShrS => "i32.shr_s",
            I32Rotl => "i32.rotl",
            I32Rotr => "i32.rotr",
            I32Eq => "i32.eq",
            I32Ne => "i32.ne",
            I32LtS => "i32.lt_s",
            I32LeS => "i32.le_s",
            I32GtS => "i32.gt_s",
            I32Eqz => "i32.eqz",
            I32Clz => "i32.clz",
            I32Ctz => "i32.ctz",
            I32Popcnt => "i32.popcnt",
            I64Add => "i64.add",
            I64Sub => "i64.sub",
            I64Mul => "i64.mul",
            I64DivU => "i64.div_u",
            I64DivS => "i64.div_s",
            I64RemU => "i64.rem_u",
            I64RemS => "i64.rem_s",
            I64Shl => "i64.shl",
            I64And => "i64.and",
            I64Or => "i64.or",
            I64Xor => "i64.xor",
            I64ShrU => "i64.shr_u",
            I64ShrS => "i64.shr_s",
            I64Rotl => "i64.rotl",
            I64Rotr => "i64.rotr",
            I64Eq => "i64.eq",
            I64Ne => "i64.ne",
            I64LtS => "i64.lt_s",
            I64LeS => "i64.le_s",
            I64GtS => "i64.gt_s",
            I64Eqz => "i64.eqz",
            I64Clz => "i64.clz",
            I64Ctz => "i64.ctz",
            I64Popcnt => "i64.popcnt",
            I64ExtendI32S => "i64.extend_i32_s",
            I64ExtendI32U => "i64.extend_i32_u",
            I32WrapI64 => "i32.wrap_i64",
            F32Add => "f32.add",
            F32Sub => "f32.sub",
            F32Mul => "f32.mul",
            F32Div => "f32.div",
            F32Min => "f32.min",
            F32Max => "f32.max",
            F32Copysign => "f32.copysign",
            F32Eq => "f32.eq",
            F32Ne => "f32.ne",
            F32Lt => "f32.lt",
            F32Le => "f32.le",
            F32Gt => "f32.gt",
            F32Ge => "f32.ge",
            F32Abs => "f32.abs",
            F32Neg => "f32.neg",
            F32Sqrt => "f32.sqrt",
            F32Ceil => "f32.ceil",
            F32Floor => "f32.floor",
            F32Trunc => "f32.trunc",
            F32Nearest => "f32.nearest",
            F64Add => "f64.add",
            F64Sub => "f64.sub",
            F64Mul => "f64.mul",
            F64Div => "f64.div",
            F64Min => "f64.min",
            F64Max => "f64.max",
            F64Copysign => "f64.copysign",
            F64Eq => "f64.eq",
            F64Ne => "f64.ne",
            F64Lt => "f64.lt",
            F64Le => "f64.le",
            F64Gt => "f64.gt",
            F64Ge => "f64.ge",
            F64Abs => "f64.abs",
            F64Neg => "f64.neg",
            F64Sqrt => "f64.sqrt",
            F64Ceil => "f64.ceil",
            F64Floor => "f64.floor",
            F64Trunc => "f64.trunc",
            F64Nearest => "f64.nearest",
        }
    }

    pub fn ops_with_result(ty: StackTy) -> impl Iterator<Item = ValueOp> {
        Self::all().iter().copied().filter(move |op| op.push() == ty)
    }

    pub fn is_commutative(self) -> bool {
        matches!(
            self,
            ValueOp::I32Add
                | ValueOp::I32Mul
                | ValueOp::I32And
                | ValueOp::I32Or
                | ValueOp::I32Xor
                | ValueOp::I32Eq
                | ValueOp::I32Ne
                | ValueOp::I64Add
                | ValueOp::I64Mul
                | ValueOp::I64And
                | ValueOp::I64Or
                | ValueOp::I64Xor
                | ValueOp::I64Eq
                | ValueOp::I64Ne
                | ValueOp::F32Add
                | ValueOp::F32Mul
                | ValueOp::F32Eq
                | ValueOp::F32Ne
                | ValueOp::F64Add
                | ValueOp::F64Mul
                | ValueOp::F64Eq
                | ValueOp::F64Ne
        )
    }

    pub fn to_enode(self, args: &[Id]) -> ValueLang {
        use ValueOp::*;
        match (self, args) {
            (I32Add, [l, r]) => ValueLang::I32Add([*l, *r]),
            (I32Sub, [l, r]) => ValueLang::I32Sub([*l, *r]),
            (I32Mul, [l, r]) => ValueLang::I32Mul([*l, *r]),
            (I32DivU, [l, r]) => ValueLang::I32DivU([*l, *r]),
            (I32DivS, [l, r]) => ValueLang::I32DivS([*l, *r]),
            (I32RemU, [l, r]) => ValueLang::I32RemU([*l, *r]),
            (I32RemS, [l, r]) => ValueLang::I32RemS([*l, *r]),
            (I32Shl, [l, r]) => ValueLang::I32Shl([*l, *r]),
            (I32And, [l, r]) => ValueLang::I32And([*l, *r]),
            (I32Or, [l, r]) => ValueLang::I32Or([*l, *r]),
            (I32Xor, [l, r]) => ValueLang::I32Xor([*l, *r]),
            (I32ShrU, [l, r]) => ValueLang::I32ShrU([*l, *r]),
            (I32ShrS, [l, r]) => ValueLang::I32ShrS([*l, *r]),
            (I32Rotl, [l, r]) => ValueLang::I32Rotl([*l, *r]),
            (I32Rotr, [l, r]) => ValueLang::I32Rotr([*l, *r]),
            (I32Eq, [l, r]) => ValueLang::I32Eq([*l, *r]),
            (I32Ne, [l, r]) => ValueLang::I32Ne([*l, *r]),
            (I32LtS, [l, r]) => ValueLang::I32LtS([*l, *r]),
            (I32LeS, [l, r]) => ValueLang::I32LeS([*l, *r]),
            (I32GtS, [l, r]) => ValueLang::I32GtS([*l, *r]),
            (I32Eqz, [c]) => ValueLang::I32Eqz([*c]),
            (I32Clz, [c]) => ValueLang::I32Clz([*c]),
            (I32Ctz, [c]) => ValueLang::I32Ctz([*c]),
            (I32Popcnt, [c]) => ValueLang::I32Popcnt([*c]),
            (I64Add, [l, r]) => ValueLang::I64Add([*l, *r]),
            (I64Sub, [l, r]) => ValueLang::I64Sub([*l, *r]),
            (I64Mul, [l, r]) => ValueLang::I64Mul([*l, *r]),
            (I64DivU, [l, r]) => ValueLang::I64DivU([*l, *r]),
            (I64DivS, [l, r]) => ValueLang::I64DivS([*l, *r]),
            (I64RemU, [l, r]) => ValueLang::I64RemU([*l, *r]),
            (I64RemS, [l, r]) => ValueLang::I64RemS([*l, *r]),
            (I64Shl, [l, r]) => ValueLang::I64Shl([*l, *r]),
            (I64And, [l, r]) => ValueLang::I64And([*l, *r]),
            (I64Or, [l, r]) => ValueLang::I64Or([*l, *r]),
            (I64Xor, [l, r]) => ValueLang::I64Xor([*l, *r]),
            (I64ShrU, [l, r]) => ValueLang::I64ShrU([*l, *r]),
            (I64ShrS, [l, r]) => ValueLang::I64ShrS([*l, *r]),
            (I64Rotl, [l, r]) => ValueLang::I64Rotl([*l, *r]),
            (I64Rotr, [l, r]) => ValueLang::I64Rotr([*l, *r]),
            (I64Eq, [l, r]) => ValueLang::I64Eq([*l, *r]),
            (I64Ne, [l, r]) => ValueLang::I64Ne([*l, *r]),
            (I64LtS, [l, r]) => ValueLang::I64LtS([*l, *r]),
            (I64LeS, [l, r]) => ValueLang::I64LeS([*l, *r]),
            (I64GtS, [l, r]) => ValueLang::I64GtS([*l, *r]),
            (I64Eqz, [c]) => ValueLang::I64Eqz([*c]),
            (I64Clz, [c]) => ValueLang::I64Clz([*c]),
            (I64Ctz, [c]) => ValueLang::I64Ctz([*c]),
            (I64Popcnt, [c]) => ValueLang::I64Popcnt([*c]),
            (I64ExtendI32S, [c]) => ValueLang::I64ExtendI32S([*c]),
            (I64ExtendI32U, [c]) => ValueLang::I64ExtendI32U([*c]),
            (I32WrapI64, [c]) => ValueLang::I32WrapI64([*c]),
            (F32Add, [l, r]) => ValueLang::F32Add([*l, *r]),
            (F32Sub, [l, r]) => ValueLang::F32Sub([*l, *r]),
            (F32Mul, [l, r]) => ValueLang::F32Mul([*l, *r]),
            (F32Div, [l, r]) => ValueLang::F32Div([*l, *r]),
            (F32Min, [l, r]) => ValueLang::F32Min([*l, *r]),
            (F32Max, [l, r]) => ValueLang::F32Max([*l, *r]),
            (F32Copysign, [l, r]) => ValueLang::F32Copysign([*l, *r]),
            (F32Eq, [l, r]) => ValueLang::F32Eq([*l, *r]),
            (F32Ne, [l, r]) => ValueLang::F32Ne([*l, *r]),
            (F32Lt, [l, r]) => ValueLang::F32Lt([*l, *r]),
            (F32Le, [l, r]) => ValueLang::F32Le([*l, *r]),
            (F32Gt, [l, r]) => ValueLang::F32Gt([*l, *r]),
            (F32Ge, [l, r]) => ValueLang::F32Ge([*l, *r]),
            (F32Abs, [c]) => ValueLang::F32Abs([*c]),
            (F32Neg, [c]) => ValueLang::F32Neg([*c]),
            (F32Sqrt, [c]) => ValueLang::F32Sqrt([*c]),
            (F32Ceil, [c]) => ValueLang::F32Ceil([*c]),
            (F32Floor, [c]) => ValueLang::F32Floor([*c]),
            (F32Trunc, [c]) => ValueLang::F32Trunc([*c]),
            (F32Nearest, [c]) => ValueLang::F32Nearest([*c]),
            (F64Add, [l, r]) => ValueLang::F64Add([*l, *r]),
            (F64Sub, [l, r]) => ValueLang::F64Sub([*l, *r]),
            (F64Mul, [l, r]) => ValueLang::F64Mul([*l, *r]),
            (F64Div, [l, r]) => ValueLang::F64Div([*l, *r]),
            (F64Min, [l, r]) => ValueLang::F64Min([*l, *r]),
            (F64Max, [l, r]) => ValueLang::F64Max([*l, *r]),
            (F64Copysign, [l, r]) => ValueLang::F64Copysign([*l, *r]),
            (F64Eq, [l, r]) => ValueLang::F64Eq([*l, *r]),
            (F64Ne, [l, r]) => ValueLang::F64Ne([*l, *r]),
            (F64Lt, [l, r]) => ValueLang::F64Lt([*l, *r]),
            (F64Le, [l, r]) => ValueLang::F64Le([*l, *r]),
            (F64Gt, [l, r]) => ValueLang::F64Gt([*l, *r]),
            (F64Ge, [l, r]) => ValueLang::F64Ge([*l, *r]),
            (F64Abs, [c]) => ValueLang::F64Abs([*c]),
            (F64Neg, [c]) => ValueLang::F64Neg([*c]),
            (F64Sqrt, [c]) => ValueLang::F64Sqrt([*c]),
            (F64Ceil, [c]) => ValueLang::F64Ceil([*c]),
            (F64Floor, [c]) => ValueLang::F64Floor([*c]),
            (F64Trunc, [c]) => ValueLang::F64Trunc([*c]),
            (F64Nearest, [c]) => ValueLang::F64Nearest([*c]),
            _ => panic!("wrong arity for {:?}", self),
        }
    }

    pub fn from_lang(node: &ValueLang) -> Option<(Self, Vec<Id>)> {
        use ValueLang as VL;
        Some(match node {
            VL::I32Add([l, r]) => (ValueOp::I32Add, vec![*l, *r]),
            VL::I32Sub([l, r]) => (ValueOp::I32Sub, vec![*l, *r]),
            VL::I32Mul([l, r]) => (ValueOp::I32Mul, vec![*l, *r]),
            VL::I32DivU([l, r]) => (ValueOp::I32DivU, vec![*l, *r]),
            VL::I32DivS([l, r]) => (ValueOp::I32DivS, vec![*l, *r]),
            VL::I32RemU([l, r]) => (ValueOp::I32RemU, vec![*l, *r]),
            VL::I32RemS([l, r]) => (ValueOp::I32RemS, vec![*l, *r]),
            VL::I32Shl([l, r]) => (ValueOp::I32Shl, vec![*l, *r]),
            VL::I32And([l, r]) => (ValueOp::I32And, vec![*l, *r]),
            VL::I32Or([l, r]) => (ValueOp::I32Or, vec![*l, *r]),
            VL::I32Xor([l, r]) => (ValueOp::I32Xor, vec![*l, *r]),
            VL::I32ShrU([l, r]) => (ValueOp::I32ShrU, vec![*l, *r]),
            VL::I32ShrS([l, r]) => (ValueOp::I32ShrS, vec![*l, *r]),
            VL::I32Rotl([l, r]) => (ValueOp::I32Rotl, vec![*l, *r]),
            VL::I32Rotr([l, r]) => (ValueOp::I32Rotr, vec![*l, *r]),
            VL::I32Eq([l, r]) => (ValueOp::I32Eq, vec![*l, *r]),
            VL::I32Ne([l, r]) => (ValueOp::I32Ne, vec![*l, *r]),
            VL::I32LtS([l, r]) => (ValueOp::I32LtS, vec![*l, *r]),
            VL::I32LeS([l, r]) => (ValueOp::I32LeS, vec![*l, *r]),
            VL::I32GtS([l, r]) => (ValueOp::I32GtS, vec![*l, *r]),
            VL::I32Eqz([c]) => (ValueOp::I32Eqz, vec![*c]),
            VL::I32Clz([c]) => (ValueOp::I32Clz, vec![*c]),
            VL::I32Ctz([c]) => (ValueOp::I32Ctz, vec![*c]),
            VL::I32Popcnt([c]) => (ValueOp::I32Popcnt, vec![*c]),
            VL::I64Add([l, r]) => (ValueOp::I64Add, vec![*l, *r]),
            VL::I64Sub([l, r]) => (ValueOp::I64Sub, vec![*l, *r]),
            VL::I64Mul([l, r]) => (ValueOp::I64Mul, vec![*l, *r]),
            VL::I64DivU([l, r]) => (ValueOp::I64DivU, vec![*l, *r]),
            VL::I64DivS([l, r]) => (ValueOp::I64DivS, vec![*l, *r]),
            VL::I64RemU([l, r]) => (ValueOp::I64RemU, vec![*l, *r]),
            VL::I64RemS([l, r]) => (ValueOp::I64RemS, vec![*l, *r]),
            VL::I64Shl([l, r]) => (ValueOp::I64Shl, vec![*l, *r]),
            VL::I64And([l, r]) => (ValueOp::I64And, vec![*l, *r]),
            VL::I64Or([l, r]) => (ValueOp::I64Or, vec![*l, *r]),
            VL::I64Xor([l, r]) => (ValueOp::I64Xor, vec![*l, *r]),
            VL::I64ShrU([l, r]) => (ValueOp::I64ShrU, vec![*l, *r]),
            VL::I64ShrS([l, r]) => (ValueOp::I64ShrS, vec![*l, *r]),
            VL::I64Rotl([l, r]) => (ValueOp::I64Rotl, vec![*l, *r]),
            VL::I64Rotr([l, r]) => (ValueOp::I64Rotr, vec![*l, *r]),
            VL::I64Eq([l, r]) => (ValueOp::I64Eq, vec![*l, *r]),
            VL::I64Ne([l, r]) => (ValueOp::I64Ne, vec![*l, *r]),
            VL::I64LtS([l, r]) => (ValueOp::I64LtS, vec![*l, *r]),
            VL::I64LeS([l, r]) => (ValueOp::I64LeS, vec![*l, *r]),
            VL::I64GtS([l, r]) => (ValueOp::I64GtS, vec![*l, *r]),
            VL::I64Eqz([c]) => (ValueOp::I64Eqz, vec![*c]),
            VL::I64Clz([c]) => (ValueOp::I64Clz, vec![*c]),
            VL::I64Ctz([c]) => (ValueOp::I64Ctz, vec![*c]),
            VL::I64Popcnt([c]) => (ValueOp::I64Popcnt, vec![*c]),
            VL::I64ExtendI32S([c]) => (ValueOp::I64ExtendI32S, vec![*c]),
            VL::I64ExtendI32U([c]) => (ValueOp::I64ExtendI32U, vec![*c]),
            VL::I32WrapI64([c]) => (ValueOp::I32WrapI64, vec![*c]),
            VL::F32Add([l, r]) => (ValueOp::F32Add, vec![*l, *r]),
            VL::F32Sub([l, r]) => (ValueOp::F32Sub, vec![*l, *r]),
            VL::F32Mul([l, r]) => (ValueOp::F32Mul, vec![*l, *r]),
            VL::F32Div([l, r]) => (ValueOp::F32Div, vec![*l, *r]),
            VL::F32Min([l, r]) => (ValueOp::F32Min, vec![*l, *r]),
            VL::F32Max([l, r]) => (ValueOp::F32Max, vec![*l, *r]),
            VL::F32Copysign([l, r]) => (ValueOp::F32Copysign, vec![*l, *r]),
            VL::F32Eq([l, r]) => (ValueOp::F32Eq, vec![*l, *r]),
            VL::F32Ne([l, r]) => (ValueOp::F32Ne, vec![*l, *r]),
            VL::F32Lt([l, r]) => (ValueOp::F32Lt, vec![*l, *r]),
            VL::F32Le([l, r]) => (ValueOp::F32Le, vec![*l, *r]),
            VL::F32Gt([l, r]) => (ValueOp::F32Gt, vec![*l, *r]),
            VL::F32Ge([l, r]) => (ValueOp::F32Ge, vec![*l, *r]),
            VL::F32Abs([c]) => (ValueOp::F32Abs, vec![*c]),
            VL::F32Neg([c]) => (ValueOp::F32Neg, vec![*c]),
            VL::F32Sqrt([c]) => (ValueOp::F32Sqrt, vec![*c]),
            VL::F32Ceil([c]) => (ValueOp::F32Ceil, vec![*c]),
            VL::F32Floor([c]) => (ValueOp::F32Floor, vec![*c]),
            VL::F32Trunc([c]) => (ValueOp::F32Trunc, vec![*c]),
            VL::F32Nearest([c]) => (ValueOp::F32Nearest, vec![*c]),
            VL::F64Add([l, r]) => (ValueOp::F64Add, vec![*l, *r]),
            VL::F64Sub([l, r]) => (ValueOp::F64Sub, vec![*l, *r]),
            VL::F64Mul([l, r]) => (ValueOp::F64Mul, vec![*l, *r]),
            VL::F64Div([l, r]) => (ValueOp::F64Div, vec![*l, *r]),
            VL::F64Min([l, r]) => (ValueOp::F64Min, vec![*l, *r]),
            VL::F64Max([l, r]) => (ValueOp::F64Max, vec![*l, *r]),
            VL::F64Copysign([l, r]) => (ValueOp::F64Copysign, vec![*l, *r]),
            VL::F64Eq([l, r]) => (ValueOp::F64Eq, vec![*l, *r]),
            VL::F64Ne([l, r]) => (ValueOp::F64Ne, vec![*l, *r]),
            VL::F64Lt([l, r]) => (ValueOp::F64Lt, vec![*l, *r]),
            VL::F64Le([l, r]) => (ValueOp::F64Le, vec![*l, *r]),
            VL::F64Gt([l, r]) => (ValueOp::F64Gt, vec![*l, *r]),
            VL::F64Ge([l, r]) => (ValueOp::F64Ge, vec![*l, *r]),
            VL::F64Abs([c]) => (ValueOp::F64Abs, vec![*c]),
            VL::F64Neg([c]) => (ValueOp::F64Neg, vec![*c]),
            VL::F64Sqrt([c]) => (ValueOp::F64Sqrt, vec![*c]),
            VL::F64Ceil([c]) => (ValueOp::F64Ceil, vec![*c]),
            VL::F64Floor([c]) => (ValueOp::F64Floor, vec![*c]),
            VL::F64Trunc([c]) => (ValueOp::F64Trunc, vec![*c]),
            VL::F64Nearest([c]) => (ValueOp::F64Nearest, vec![*c]),
            _ => return None,
        })
    }
}

/// Enumerate candidate rule signatures up to `max_arity` input variables.
pub fn enumerate_signatures(max_arity: usize) -> Vec<RuleSignature> {
    let sorts = [StackTy::I32, StackTy::I64, StackTy::F32, StackTy::F64];
    let mut out = Vec::new();
    for arity in 1..=max_arity {
        let n = sorts.len().pow(arity as u32);
        for idx in 0..n {
            let mut inputs = Vec::with_capacity(arity);
            let mut x = idx;
            for _ in 0..arity {
                inputs.push(sorts[x % sorts.len()]);
                x /= sorts.len();
            }
            for &output in &sorts {
                out.push(RuleSignature {
                    inputs: inputs.clone(),
                    output,
                });
            }
        }
    }
    out
}

/// Whether `sig.output` is reachable from `sig.inputs` using [`ValueOp::all`].
pub fn is_reachable(sig: &RuleSignature) -> bool {
    use std::collections::HashSet;
    let mut available: HashSet<StackTy> = sig.inputs.iter().copied().collect();
    loop {
        let before = available.len();
        for op in ValueOp::all() {
            if op.pops().iter().all(|t| available.contains(t)) {
                available.insert(op.push());
            }
        }
        if available.len() == before {
            break;
        }
    }
    available.contains(&sig.output)
}


/// Canonical `i64` carrier for an `f32` bit pattern (sign-extended).
pub fn f32_bits_to_i64(bits: u32) -> i64 {
    bits as i32 as i64
}

/// Canonical `i64` carrier for an `f64` bit pattern.
pub fn f64_bits_to_i64(bits: u64) -> i64 {
    bits as i64
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn i32_to_i64_reachable_via_extend() {
        let sig = RuleSignature {
            inputs: vec![StackTy::I32],
            output: StackTy::I64,
        };
        assert!(is_reachable(&sig));
    }

    #[test]
    fn i64_to_i32_reachable_via_wrap() {
        let sig = RuleSignature {
            inputs: vec![StackTy::I64],
            output: StackTy::I32,
        };
        assert!(is_reachable(&sig));
    }
}
