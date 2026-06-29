//! E-graph language.

use egg::*;
use std::str::FromStr;

/// IEEE-754 `f32` bit pattern for e-graph literals and patterns.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct F32Bits(pub u32);

impl F32Bits {
    pub fn from_i64_carrier(v: i64) -> Self {
        Self(v as u32)
    }

    pub fn to_i64_carrier(self) -> i64 {
        self.0 as i32 as i64
    }
}

impl std::fmt::Display for F32Bits {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", format_float32(f32::from_bits(self.0)))
    }
}

impl FromStr for F32Bits {
    type Err = std::num::ParseFloatError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self(f32::to_bits(s.parse::<f32>()?)))
    }
}

/// IEEE-754 `f64` bit pattern for e-graph literals and patterns.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct F64Bits(pub u64);

impl F64Bits {
    pub fn from_i64_carrier(v: i64) -> Self {
        Self(v as u64)
    }

    pub fn to_i64_carrier(self) -> i64 {
        self.0 as i64
    }
}

impl std::fmt::Display for F64Bits {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", format_float64(f64::from_bits(self.0)))
    }
}

impl FromStr for F64Bits {
    type Err = std::num::ParseFloatError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self(f64::to_bits(s.parse::<f64>()?)))
    }
}

fn format_float32(v: f32) -> String {
    if v.fract() == 0.0 && v.is_finite() {
        format!("{v:.1}")
    } else {
        format!("{v}")
    }
}

fn format_float64(v: f64) -> String {
    if v.fract() == 0.0 && v.is_finite() {
        format!("{v:.1}")
    } else {
        format!("{v}")
    }
}

define_language! {
    pub enum ValueLang {
        I32Const(i32),
        "i32.add"   = I32Add([Id; 2]),
        "i32.sub"   = I32Sub([Id; 2]),
        "i32.mul"   = I32Mul([Id; 2]),
        "i32.div_u" = I32DivU([Id; 2]),
        "i32.div_s" = I32DivS([Id; 2]),
        "i32.rem_u" = I32RemU([Id; 2]),
        "i32.rem_s" = I32RemS([Id; 2]),
        "i32.shl"   = I32Shl([Id; 2]),
        "i32.and"   = I32And([Id; 2]),
        "i32.or"    = I32Or([Id; 2]),
        "i32.xor"   = I32Xor([Id; 2]),
        "i32.shr_u" = I32ShrU([Id; 2]),
        "i32.shr_s" = I32ShrS([Id; 2]),
        "i32.rotl"  = I32Rotl([Id; 2]),
        "i32.rotr"  = I32Rotr([Id; 2]),
        "i32.eq"    = I32Eq([Id; 2]),
        "i32.ne"    = I32Ne([Id; 2]),
        "i32.lt_s"  = I32LtS([Id; 2]),
        "i32.le_s"  = I32LeS([Id; 2]),
        "i32.gt_s"  = I32GtS([Id; 2]),
        "i32.eqz"   = I32Eqz([Id; 1]),
        "i32.clz"   = I32Clz([Id; 1]),
        "i32.ctz"   = I32Ctz([Id; 1]),
        "i32.popcnt" = I32Popcnt([Id; 1]),
        I64Const(i64),
        "i64.add"   = I64Add([Id; 2]),
        "i64.sub"   = I64Sub([Id; 2]),
        "i64.mul"   = I64Mul([Id; 2]),
        "i64.div_u" = I64DivU([Id; 2]),
        "i64.div_s" = I64DivS([Id; 2]),
        "i64.rem_u" = I64RemU([Id; 2]),
        "i64.rem_s" = I64RemS([Id; 2]),
        "i64.shl"   = I64Shl([Id; 2]),
        "i64.and"   = I64And([Id; 2]),
        "i64.or"    = I64Or([Id; 2]),
        "i64.xor"   = I64Xor([Id; 2]),
        "i64.shr_u" = I64ShrU([Id; 2]),
        "i64.shr_s" = I64ShrS([Id; 2]),
        "i64.rotl"  = I64Rotl([Id; 2]),
        "i64.rotr"  = I64Rotr([Id; 2]),
        "i64.eq"    = I64Eq([Id; 2]),
        "i64.ne"    = I64Ne([Id; 2]),
        "i64.lt_s"  = I64LtS([Id; 2]),
        "i64.le_s"  = I64LeS([Id; 2]),
        "i64.gt_s"  = I64GtS([Id; 2]),
        "i64.eqz"   = I64Eqz([Id; 1]),
        "i64.clz"   = I64Clz([Id; 1]),
        "i64.ctz"   = I64Ctz([Id; 1]),
        "i64.popcnt" = I64Popcnt([Id; 1]),
        "i64.extend_i32_s" = I64ExtendI32S([Id; 1]),
        "i64.extend_i32_u" = I64ExtendI32U([Id; 1]),
        "i32.wrap_i64" = I32WrapI64([Id; 1]),
        F32Const(F32Bits),
        "f32.add" = F32Add([Id; 2]),
        "f32.sub" = F32Sub([Id; 2]),
        "f32.mul" = F32Mul([Id; 2]),
        "f32.div" = F32Div([Id; 2]),
        "f32.min" = F32Min([Id; 2]),
        "f32.max" = F32Max([Id; 2]),
        "f32.copysign" = F32Copysign([Id; 2]),
        "f32.eq" = F32Eq([Id; 2]),
        "f32.ne" = F32Ne([Id; 2]),
        "f32.lt" = F32Lt([Id; 2]),
        "f32.le" = F32Le([Id; 2]),
        "f32.gt" = F32Gt([Id; 2]),
        "f32.ge" = F32Ge([Id; 2]),
        "f32.abs" = F32Abs([Id; 1]),
        "f32.neg" = F32Neg([Id; 1]),
        "f32.sqrt" = F32Sqrt([Id; 1]),
        "f32.ceil" = F32Ceil([Id; 1]),
        "f32.floor" = F32Floor([Id; 1]),
        "f32.trunc" = F32Trunc([Id; 1]),
        "f32.nearest" = F32Nearest([Id; 1]),
        F64Const(F64Bits),
        "f64.add" = F64Add([Id; 2]),
        "f64.sub" = F64Sub([Id; 2]),
        "f64.mul" = F64Mul([Id; 2]),
        "f64.div" = F64Div([Id; 2]),
        "f64.min" = F64Min([Id; 2]),
        "f64.max" = F64Max([Id; 2]),
        "f64.copysign" = F64Copysign([Id; 2]),
        "f64.eq" = F64Eq([Id; 2]),
        "f64.ne" = F64Ne([Id; 2]),
        "f64.lt" = F64Lt([Id; 2]),
        "f64.le" = F64Le([Id; 2]),
        "f64.gt" = F64Gt([Id; 2]),
        "f64.ge" = F64Ge([Id; 2]),
        "f64.abs" = F64Abs([Id; 1]),
        "f64.neg" = F64Neg([Id; 1]),
        "f64.sqrt" = F64Sqrt([Id; 1]),
        "f64.ceil" = F64Ceil([Id; 1]),
        "f64.floor" = F64Floor([Id; 1]),
        "f64.trunc" = F64Trunc([Id; 1]),
        "f64.nearest" = F64Nearest([Id; 1]),
        Symbol(Symbol),
    }
}
