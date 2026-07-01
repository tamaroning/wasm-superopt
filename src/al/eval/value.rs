//! Runtime values for the AL interpreter.

use crate::al::ast::{NumType, Sign, ValType, WasmBinOp, WasmRelOp, WasmTestOp, WasmUnOp};

/// Rational number for AL `rat` sort.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Rat {
    pub num: i128,
    pub den: i128,
}

impl Rat {
    pub fn new(num: i128, den: i128) -> Self {
        if den == 0 {
            panic!("Rat: zero denominator");
        }
        let neg = den < 0;
        let (mut num, mut den) = (num, den);
        if neg {
            num = -num;
            den = -den;
        }
        let g = gcd_i128(num.abs(), den);
        Self {
            num: num / g,
            den: den / g,
        }
    }

    pub fn from_int(n: i64) -> Self {
        Self {
            num: n as i128,
            den: 1,
        }
    }

    pub fn trunc_toward_zero(self) -> i64 {
        (self.num / self.den) as i64
    }
}

fn gcd_i128(mut a: i128, mut b: i128) -> i128 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a.abs()
}

/// AL runtime value (concrete).
#[derive(Clone, Debug, PartialEq)]
pub enum AlValue {
    Nat(u64),
    Int(i64),
    Rat(Rat),
    Bool(bool),
    Opt(Option<Box<AlValue>>),
    List(Vec<AlValue>),
    NumType(NumType),
    ValType(ValType),
    Sign(Sign),
    BinOp(WasmBinOp),
    RelOp(WasmRelOp),
    TestOp(WasmTestOp),
    UnOp(WasmUnOp),
}

impl AlValue {
    pub fn as_nat(&self) -> Option<u64> {
        match self {
            Self::Nat(n) => Some(*n),
            _ => None,
        }
    }

    pub fn as_int(&self) -> Option<i64> {
        match self {
            Self::Int(n) => Some(*n),
            _ => None,
        }
    }

    pub fn as_list(&self) -> Option<&[AlValue]> {
        match self {
            Self::List(v) => Some(v),
            _ => None,
        }
    }

    pub fn list_len(&self) -> usize {
        self.as_list().map_or(0, |v| v.len())
    }

    pub fn is_empty_list_or_opt(&self) -> bool {
        match self {
            Self::List(v) => v.is_empty(),
            Self::Opt(None) => true,
            Self::Opt(Some(_)) => false,
            _ => false,
        }
    }

    pub fn choose_singleton(&self) -> Option<AlValue> {
        match self {
            Self::List(v) if v.len() == 1 => Some(v[0].clone()),
            Self::Opt(Some(v)) => Some((**v).clone()),
            _ => None,
        }
    }
}

/// Result of evaluating a partial AL op for ValueAst.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValueAstResult {
    pub value: i64,
    pub trap: bool,
}

pub fn value_to_nat(v: i64, bits: u32) -> u64 {
    match bits {
        32 => v as u32 as u64,
        64 => v as u64,
        _ => v as u64,
    }
}

pub fn nat_to_value(n: u64, bits: u32) -> i64 {
    match bits {
        32 => n as u32 as i32 as i64,
        64 => n as i64,
        _ => n as i64,
    }
}
