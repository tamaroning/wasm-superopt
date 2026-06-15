//! Concrete evaluator for meta-level AL `$fn` definitions.

use super::al_defs::{
    binop_def, idiv_def, inv_signed_def, irem_def, list_def, signed_def, size_def, sizenn_def,
};
use super::ir::{NumType, Sign, WasmBinOp};
use super::meta::{
    AlMetaArg, AlMetaExpr, AlMetaFnDef, AlMetaFnStep, AlMetaPred, BinOpCase, ValType,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AlValue {
    Nat(u32),
    Int(i32),
    Rat(i64, i64),
    NumType(NumType),
    ValType(ValType),
    Sign(Sign),
    BinOp(WasmBinOp),
    Opt(Option<Box<AlValue>>),
    List(Vec<AlValue>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EvalError {
    Fail,
    Assert,
}

type EvalResult = Result<AlValue, EvalError>;

pub fn eval_size(valtype: ValType) -> Option<u32> {
    match eval_fn(
        &size_def(),
        &[("valtype", AlValue::ValType(valtype))],
    ) {
        Ok(AlValue::Nat(n)) => Some(n),
        Err(EvalError::Fail) => None,
        other => panic!("size returned unexpected {other:?}"),
    }
}

pub fn eval_sizenn(nt: NumType) -> u32 {
    match eval_fn(&sizenn_def(), &[("nt", AlValue::NumType(nt))]) {
        Ok(AlValue::Nat(n)) => n,
        other => panic!("sizenn returned unexpected {other:?}"),
    }
}

pub fn eval_signed_(n: u32, i: u32) -> i32 {
    match eval_fn(
        &signed_def(),
        &[("N", AlValue::Nat(n)), ("i", AlValue::Nat(i))],
    ) {
        Ok(AlValue::Int(j)) => j,
        other => panic!("signed_ returned unexpected {other:?}"),
    }
}

pub fn eval_inv_signed_(n: u32, i: i32) -> u32 {
    match eval_fn(
        &inv_signed_def(),
        &[("N", AlValue::Nat(n)), ("i", AlValue::Int(i))],
    ) {
        Ok(AlValue::Nat(j)) => j,
        other => panic!("inv_signed_ returned unexpected {other:?}"),
    }
}

pub fn eval_list_is_empty<T>(opt: Option<T>) -> bool {
    let val = match opt {
        None => AlValue::Opt(None),
        Some(_) => AlValue::Opt(Some(Box::new(AlValue::Nat(0)))),
    };
    matches!(
        eval_fn(
            &list_def(),
            &[("X", AlValue::Nat(0)), ("X_opt", val)],
        ),
        Ok(AlValue::List(items)) if items.is_empty()
    )
}

pub fn eval_idiv_(n: u32, sx: Sign, i_1: u32, i_2: u32) -> Option<u32> {
    opt_nat_result(&idiv_def(), n, sx, i_1, i_2)
}

pub fn eval_idiv_is_empty(n: u32, sx: Sign, i_1: u32, i_2: u32) -> bool {
    eval_idiv_(n, sx, i_1, i_2).is_none()
}

pub fn eval_irem_(n: u32, sx: Sign, i_1: u32, i_2: u32) -> Option<u32> {
    opt_nat_result(&irem_def(), n, sx, i_1, i_2)
}

pub fn eval_binop_(
    nt: NumType,
    binop: WasmBinOp,
    i_1: u32,
    i_2: u32,
) -> Option<u32> {
    match eval_fn(
        &binop_def(),
        &[
            ("numtype", AlValue::NumType(nt)),
            ("binop_", AlValue::BinOp(binop)),
            ("iN_1", AlValue::Nat(i_1)),
            ("iN_2", AlValue::Nat(i_2)),
        ],
    ) {
        Ok(AlValue::List(items)) if items.is_empty() => None,
        Ok(AlValue::List(items)) => match items.as_slice() {
            [AlValue::Nat(n)] => Some(*n),
            other => panic!("binop_ singleton list expected Nat, got {other:?}"),
        },
        Ok(AlValue::Opt(None)) => None,
        Ok(AlValue::Opt(Some(v))) => match *v {
            AlValue::Nat(n) => Some(n),
            other => panic!("binop_ optional expected Nat, got {other:?}"),
        },
        Err(EvalError::Fail) => None,
        other => panic!("binop_ returned unexpected {other:?}"),
    }
}

fn opt_nat_result(def: &AlMetaFnDef, n: u32, sx: Sign, i_1: u32, i_2: u32) -> Option<u32> {
    match eval_fn(
        def,
        &[
            ("N", AlValue::Nat(n)),
            ("sx", AlValue::Sign(sx)),
            ("i_1", AlValue::Nat(i_1)),
            ("i_2", AlValue::Nat(i_2)),
        ],
    ) {
        Ok(AlValue::Opt(None)) => None,
        Ok(AlValue::Opt(Some(v))) => match *v {
            AlValue::Nat(n) => Some(n),
            other => panic!("{} optional expected Nat, got {other:?}", def.name),
        },
        Err(EvalError::Fail) => None,
        other => panic!("{} returned unexpected {other:?}", def.name),
    }
}

pub fn eval_fn(def: &AlMetaFnDef, args: &[(&str, AlValue)]) -> EvalResult {
    let mut env = FnEnv::new(def.params, args);
    eval_fn_steps(&def.body, &mut env)
}

struct FnEnv {
    vars: Vec<(&'static str, AlValue)>,
}

impl FnEnv {
    fn new(params: &[&'static str], args: &[(&str, AlValue)]) -> Self {
        let mut vars = Vec::new();
        for name in params {
            let val = args
                .iter()
                .find(|(n, _)| n == name)
                .map(|(_, v)| v.clone())
                .unwrap_or_else(|| panic!("missing arg {name} for AL fn"));
            vars.push((*name, val));
        }
        Self { vars }
    }

    fn bind(&mut self, name: &'static str, val: AlValue) {
        if let Some(slot) = self.vars.iter_mut().find(|(n, _)| *n == name) {
            slot.1 = val;
        } else {
            self.vars.push((name, val));
        }
    }

    fn get(&self, name: &str) -> &AlValue {
        self.vars
            .iter()
            .find(|(n, _)| *n == name)
            .map(|(_, v)| v)
            .unwrap_or_else(|| panic!("unbound AL variable: {name}"))
    }
}

fn eval_fn_steps(steps: &[AlMetaFnStep], env: &mut FnEnv) -> EvalResult {
    for step in steps {
        if let Some(val) = eval_fn_step(step, env)? {
            return Ok(val);
        }
    }
    Err(EvalError::Fail)
}

fn eval_fn_step(step: &AlMetaFnStep, env: &mut FnEnv) -> Result<Option<AlValue>, EvalError> {
    match step {
        AlMetaFnStep::Return(expr) => Ok(Some(eval_expr(expr, env)?)),
        AlMetaFnStep::Fail => Err(EvalError::Fail),
        AlMetaFnStep::Assert(pred) => {
            if !eval_pred(pred, env)? {
                return Err(EvalError::Assert);
            }
            Ok(None)
        }
        AlMetaFnStep::Let { name, expr } => {
            env.bind(name, eval_expr(expr, env)?);
            Ok(None)
        }
        AlMetaFnStep::LetBinOpCase {
            case,
            sx_name,
            binop,
        } => {
            let sx = binop_sign(eval_expr(binop, env)?, *case)?;
            env.bind(sx_name, AlValue::Sign(sx));
            Ok(None)
        }
        AlMetaFnStep::If {
            cond,
            then_steps,
            else_steps,
        } => {
            if eval_pred(cond, env)? {
                eval_fn_steps(then_steps, env).map(Some)
            } else if else_steps.is_empty() {
                Ok(None)
            } else {
                eval_fn_steps(else_steps, env).map(Some)
            }
        }
    }
}

fn eval_expr(expr: &AlMetaExpr, env: &FnEnv) -> EvalResult {
    match expr {
        AlMetaExpr::Param(name) => Ok(env.get(name).clone()),
        AlMetaExpr::NatLit(n) => Ok(AlValue::Nat(*n)),
        AlMetaExpr::IntLit(n) => Ok(AlValue::Int(*n)),
        AlMetaExpr::ValTypeLit(vt) => Ok(AlValue::ValType(*vt)),
        AlMetaExpr::SignLit(sx) => Ok(AlValue::Sign(*sx)),
        AlMetaExpr::BinOpLit(op) => Ok(AlValue::BinOp(*op)),
        AlMetaExpr::EmptyOpt => Ok(AlValue::Opt(None)),
        AlMetaExpr::SomeOpt(inner) => Ok(AlValue::Opt(Some(Box::new(eval_expr(inner, env)?)))),
        AlMetaExpr::EmptyList => Ok(AlValue::List(vec![])),
        AlMetaExpr::SingletonList(inner) => Ok(AlValue::List(vec![eval_expr(inner, env)?])),
        AlMetaExpr::IntCoerce(inner) => Ok(AlValue::Int(as_int(eval_expr(inner, env)?)?)),
        AlMetaExpr::NatCoerce(inner) => match eval_expr(inner, env)? {
            AlValue::Nat(n) => Ok(AlValue::Nat(n)),
            AlValue::Int(n) if n >= 0 => Ok(AlValue::Nat(n as u32)),
            AlValue::Rat(n, d) => Ok(AlValue::Nat((n / d) as u32)),
            other => panic!("nat coerce on {other:?}"),
        },
        AlMetaExpr::RatCoerce(inner) => as_rat(eval_expr(inner, env)?),
        AlMetaExpr::TruncZ(inner) => {
            let r = as_rat_pair(eval_expr(inner, env)?)?;
            Ok(AlValue::Int(trunc_rat(r)))
        }
        AlMetaExpr::Add(a, b) => eval_add(eval_expr(a, env)?, eval_expr(b, env)?),
        AlMetaExpr::Sub(a, b) => eval_sub(eval_expr(a, env)?, eval_expr(b, env)?),
        AlMetaExpr::Mul(a, b) => eval_mul(eval_expr(a, env)?, eval_expr(b, env)?),
        AlMetaExpr::Div(a, b) => eval_div(eval_expr(a, env)?, eval_expr(b, env)?),
        AlMetaExpr::Mod(a, b) => eval_mod(eval_expr(a, env)?, eval_expr(b, env)?),
        AlMetaExpr::Rem(a, b) => eval_rem(eval_expr(a, env)?, eval_expr(b, env)?),
        AlMetaExpr::Shl(a, b) => eval_shl(eval_expr(a, env)?, eval_expr(b, env)?),
        AlMetaExpr::BitAnd(a, b) => eval_bitand(eval_expr(a, env)?, eval_expr(b, env)?),
        AlMetaExpr::BitOr(a, b) => eval_bitor(eval_expr(a, env)?, eval_expr(b, env)?),
        AlMetaExpr::BitXor(a, b) => eval_bitxor(eval_expr(a, env)?, eval_expr(b, env)?),
        AlMetaExpr::Pow(a, b) => eval_pow(eval_expr(a, env)?, eval_expr(b, env)?),
        AlMetaExpr::Neg(inner) => Ok(AlValue::Int(-as_int(eval_expr(inner, env)?)?)),
        AlMetaExpr::Choose(inner) => eval_choose(eval_expr(inner, env)?),
        AlMetaExpr::BinOpSignOf(inner) => {
            Ok(AlValue::Sign(binop_sign_value(as_binop(eval_expr(inner, env)?)?)))
        }
        AlMetaExpr::Call(name, args) => eval_call(name, args, env),
        AlMetaExpr::OptionalLen(inner) => {
            Ok(AlValue::Nat(match eval_expr(inner, env)? {
                AlValue::List(items) if items.is_empty() => 0,
                AlValue::Opt(None) => 0,
                _ => 1,
            }))
        }
        AlMetaExpr::TopValue(_) => panic!("step-only TopValue in fn eval: {expr:?}"),
    }
}

fn eval_call(name: &str, args: &[AlMetaArg], env: &FnEnv) -> EvalResult {
    let mut bound = Vec::new();
    for arg in args {
        bound.push(match arg {
            AlMetaArg::Var(name) => env.get(name).clone(),
            AlMetaArg::Nat(n) => AlValue::Nat(*n),
            AlMetaArg::NumType(nt) => AlValue::NumType(*nt),
            AlMetaArg::ValType(vt) => AlValue::ValType(*vt),
            AlMetaArg::Sign(sx) => AlValue::Sign(*sx),
            AlMetaArg::BinOp(op) => AlValue::BinOp(*op),
            AlMetaArg::Expr(expr) => eval_expr(expr, env)?,
        });
    }

    match name {
        "size" => eval_fn(
            &size_def(),
            &[(
                "valtype",
                AlValue::ValType(as_valtype(bound[0].clone())?),
            )],
        ),
        "sizenn" => eval_fn(
            &sizenn_def(),
            &[("nt", AlValue::NumType(as_numtype(bound[0].clone())?))],
        ),
        "signed_" => eval_fn(
            &signed_def(),
            &[
                ("N", AlValue::Nat(as_nat(bound[0].clone())?)),
                ("i", AlValue::Nat(as_nat(bound[1].clone())?)),
            ],
        ),
        "inv_signed_" => eval_fn(
            &inv_signed_def(),
            &[
                ("N", AlValue::Nat(as_nat(bound[0].clone())?)),
                ("i", AlValue::Int(as_int(bound[1].clone())?)),
            ],
        ),
        "list_" => eval_fn(
            &list_def(),
            &[("X", bound[0].clone()), ("X_opt", bound[1].clone())],
        ),
        "idiv_" => eval_fn(
            &idiv_def(),
            &[
                ("N", AlValue::Nat(as_nat(bound[0].clone())?)),
                ("sx", AlValue::Sign(as_sign(bound[1].clone())?)),
                ("i_1", AlValue::Nat(as_nat(bound[2].clone())?)),
                ("i_2", AlValue::Nat(as_nat(bound[3].clone())?)),
            ],
        ),
        "irem_" => eval_fn(
            &irem_def(),
            &[
                ("N", AlValue::Nat(as_nat(bound[0].clone())?)),
                ("sx", AlValue::Sign(as_sign(bound[1].clone())?)),
                ("i_1", AlValue::Nat(as_nat(bound[2].clone())?)),
                ("i_2", AlValue::Nat(as_nat(bound[3].clone())?)),
            ],
        ),
        other => panic!("unsupported AL call in fn eval: {other}"),
    }
}

fn eval_pred(pred: &AlMetaPred, env: &FnEnv) -> Result<bool, EvalError> {
    match pred {
        AlMetaPred::Eq(a, b) => Ok(eval_eq(eval_expr(a, env)?, eval_expr(b, env)?)),
        AlMetaPred::Lt(a, b) => cmp_lt(eval_expr(a, env)?, eval_expr(b, env)?),
        AlMetaPred::Le(a, b) => {
            let av = eval_expr(a, env)?;
            let bv = eval_expr(b, env)?;
            Ok(cmp_lt(av.clone(), bv.clone())? || cmp_eq(av, bv))
        }
        AlMetaPred::And(a, b) => {
            let left = eval_pred(a, env)?;
            let right = eval_pred(b, env)?;
            Ok(left && right)
        }
        AlMetaPred::OptIsNone(expr) => Ok(matches!(eval_expr(expr, env)?, AlValue::Opt(None))),
        AlMetaPred::TypeIsInn(expr) => Ok(matches!(eval_expr(expr, env)?, AlValue::NumType(_))),
        AlMetaPred::TypeIsFnn(_) => Ok(false),
        AlMetaPred::BinOpEq(expr, op) => Ok(as_binop(eval_expr(expr, env)?)? == *op),
        AlMetaPred::BinOpCaseIs(expr, case) => {
            Ok(binop_case(as_binop(eval_expr(expr, env)?)?, *case))
        }
    }
}

fn eval_eq(a: AlValue, b: AlValue) -> bool {
    match (a, b) {
        (AlValue::Nat(x), AlValue::Nat(y)) => x == y,
        (AlValue::Int(x), AlValue::Int(y)) => x == y,
        (AlValue::ValType(x), AlValue::ValType(y)) => x == y,
        (AlValue::Sign(x), AlValue::Sign(y)) => x == y,
        (AlValue::BinOp(x), AlValue::BinOp(y)) => x == y,
        (AlValue::NumType(x), AlValue::NumType(y)) => x == y,
        (AlValue::Rat(x, xd), AlValue::Rat(y, yd)) => x * yd == y * xd,
        _ => false,
    }
}

fn eval_add(a: AlValue, b: AlValue) -> EvalResult {
    match (a, b) {
        (AlValue::Nat(x), AlValue::Nat(y)) => Ok(AlValue::Nat(x.wrapping_add(y))),
        (AlValue::Int(x), AlValue::Int(y)) => Ok(AlValue::Int(x.wrapping_add(y))),
        (AlValue::Int(x), AlValue::Nat(y)) => Ok(AlValue::Nat((x as i64 + y as i64) as u32)),
        (AlValue::Nat(x), AlValue::Int(y)) => Ok(AlValue::Nat((x as i64 + y as i64) as u32)),
        (AlValue::Rat(x, xd), AlValue::Rat(y, yd)) => Ok(rat(add_rat((x, xd), (y, yd)))),
        _ => panic!("add on incompatible values"),
    }
}

fn eval_sub(a: AlValue, b: AlValue) -> EvalResult {
    match (a, b) {
        (AlValue::Nat(x), AlValue::Nat(y)) => Ok(AlValue::Nat(x.wrapping_sub(y))),
        (AlValue::Int(x), AlValue::Int(y)) => Ok(AlValue::Int(x.wrapping_sub(y))),
        (AlValue::Int(x), AlValue::Nat(y)) => Ok(AlValue::Int(x.wrapping_sub(y as i32))),
        (AlValue::Nat(x), AlValue::Int(y)) => Ok(AlValue::Int((x as i64 - y as i64) as i32)),
        (AlValue::Rat(x, xd), AlValue::Rat(y, yd)) => Ok(rat(sub_rat((x, xd), (y, yd)))),
        _ => panic!("sub on incompatible values"),
    }
}

fn eval_mul(a: AlValue, b: AlValue) -> EvalResult {
    match (a, b) {
        (AlValue::Nat(x), AlValue::Nat(y)) => Ok(AlValue::Nat(x.wrapping_mul(y))),
        (AlValue::Int(x), AlValue::Int(y)) => Ok(AlValue::Int(x.wrapping_mul(y))),
        (AlValue::Rat(x, xd), AlValue::Rat(y, yd)) => Ok(rat(mul_rat((x, xd), (y, yd)))),
        _ => panic!("mul on incompatible values"),
    }
}

fn eval_div(a: AlValue, b: AlValue) -> EvalResult {
    match (a, b) {
        (AlValue::Rat(x, xd), AlValue::Rat(y, yd)) => Ok(rat(div_rat((x, xd), (y, yd)))),
        _ => panic!("div on incompatible values"),
    }
}

fn eval_mod(a: AlValue, b: AlValue) -> EvalResult {
    match (a, b) {
        (AlValue::Nat(x), AlValue::Nat(0)) => Ok(AlValue::Nat(x)),
        (AlValue::Nat(x), AlValue::Nat(y)) => Ok(AlValue::Nat(x % y.max(1))),
        (AlValue::Int(x), AlValue::Int(0)) => Ok(AlValue::Int(x)),
        (AlValue::Int(x), AlValue::Int(y)) => {
            let m = y.max(1);
            Ok(AlValue::Int(x.rem_euclid(m)))
        }
        _ => panic!("mod on incompatible values"),
    }
}

fn eval_rem(a: AlValue, b: AlValue) -> EvalResult {
    Ok(AlValue::Nat(as_nat(a)? % as_nat(b)?.max(1)))
}

fn eval_shl(a: AlValue, b: AlValue) -> EvalResult {
    Ok(AlValue::Nat(as_nat(a)?.wrapping_shl(as_nat(b)?)))
}

fn eval_bitand(a: AlValue, b: AlValue) -> EvalResult {
    Ok(AlValue::Nat(as_nat(a)? & as_nat(b)?))
}

fn eval_bitor(a: AlValue, b: AlValue) -> EvalResult {
    Ok(AlValue::Nat(as_nat(a)? | as_nat(b)?))
}

fn eval_bitxor(a: AlValue, b: AlValue) -> EvalResult {
    Ok(AlValue::Nat(as_nat(a)? ^ as_nat(b)?))
}

fn eval_choose(v: AlValue) -> EvalResult {
    match v {
        AlValue::Opt(Some(inner)) => Ok(*inner),
        AlValue::List(items) if items.len() == 1 => Ok(items[0].clone()),
        other => panic!("choose on {other:?}"),
    }
}

fn eval_pow(a: AlValue, b: AlValue) -> EvalResult {
    let base = as_nat(a)?;
    let exp = as_nat(b)?;
    let result = match (base, exp) {
        // binop.al: (2 ^ N); for N=32 treat as 2^32 (u32 wrap) via modulus 0 sentinel.
        (2, e) if e >= 32 => 0,
        (2, e) => 1u32.checked_shl(e).unwrap_or(0),
        _ => panic!("unsupported pow({base}, {exp})"),
    };
    Ok(AlValue::Nat(result))
}

fn cmp_lt(a: AlValue, b: AlValue) -> Result<bool, EvalError> {
    // binop.al: (2 ^ 32) — u32 wrap sentinel in eval_pow.
    if matches!((&a, &b), (AlValue::Nat(_), AlValue::Nat(0))) {
        return Ok(true);
    }
    Ok(cmp_values(a, b)?.0)
}

fn cmp_eq(a: AlValue, b: AlValue) -> bool {
    eval_eq(a, b)
}

fn cmp_values(a: AlValue, b: AlValue) -> Result<(bool, bool), EvalError> {
    let ai = to_i64(a)?;
    let bi = to_i64(b)?;
    Ok((ai < bi, ai == bi))
}

fn to_i64(v: AlValue) -> Result<i64, EvalError> {
    Ok(match v {
        AlValue::Nat(n) => n as i64,
        AlValue::Int(n) => n as i64,
        AlValue::Rat(n, d) => n / d,
        other => panic!("cmp expected numeric, got {other:?}"),
    })
}

fn as_nat(v: AlValue) -> Result<u32, EvalError> {
    match v {
        AlValue::Nat(n) => Ok(n),
        AlValue::Int(n) if n >= 0 => Ok(n as u32),
        other => panic!("expected nat, got {other:?}"),
    }
}

fn as_int(v: AlValue) -> Result<i32, EvalError> {
    match v {
        AlValue::Int(n) => Ok(n),
        AlValue::Nat(n) => Ok(n as i32),
        other => panic!("expected int, got {other:?}"),
    }
}

fn as_valtype(v: AlValue) -> Result<ValType, EvalError> {
    match v {
        AlValue::ValType(vt) => Ok(vt),
        AlValue::NumType(NumType::I32) => Ok(ValType::I32),
        other => panic!("expected valtype, got {other:?}"),
    }
}

fn as_numtype(v: AlValue) -> Result<NumType, EvalError> {
    match v {
        AlValue::NumType(nt) => Ok(nt),
        other => panic!("expected numtype, got {other:?}"),
    }
}

fn as_sign(v: AlValue) -> Result<Sign, EvalError> {
    match v {
        AlValue::Sign(sx) => Ok(sx),
        other => panic!("expected sign, got {other:?}"),
    }
}

fn as_binop(v: AlValue) -> Result<WasmBinOp, EvalError> {
    match v {
        AlValue::BinOp(op) => Ok(op),
        other => panic!("expected binop, got {other:?}"),
    }
}

fn as_rat(v: AlValue) -> EvalResult {
    Ok(match v {
        AlValue::Rat(n, d) => AlValue::Rat(n, d),
        AlValue::Nat(n) => AlValue::Rat(n as i64, 1),
        AlValue::Int(n) => AlValue::Rat(n as i64, 1),
        other => panic!("expected rat, got {other:?}"),
    })
}

fn as_rat_pair(v: AlValue) -> Result<(i64, i64), EvalError> {
    match v {
        AlValue::Rat(n, d) => Ok((n, d)),
        other => panic!("expected rat, got {other:?}"),
    }
}

fn rat((n, d): (i64, i64)) -> AlValue {
    AlValue::Rat(n, d)
}

fn add_rat(a: (i64, i64), b: (i64, i64)) -> (i64, i64) {
    (a.0 * b.1 + b.0 * a.1, a.1 * b.1)
}

fn sub_rat(a: (i64, i64), b: (i64, i64)) -> (i64, i64) {
    (a.0 * b.1 - b.0 * a.1, a.1 * b.1)
}

fn mul_rat(a: (i64, i64), b: (i64, i64)) -> (i64, i64) {
    (a.0 * b.0, a.1 * b.1)
}

fn div_rat(a: (i64, i64), b: (i64, i64)) -> (i64, i64) {
    (a.0 * b.1, a.1 * b.0)
}

fn trunc_rat((n, d): (i64, i64)) -> i32 {
    (n / d) as i32
}

fn binop_case(op: WasmBinOp, case: BinOpCase) -> bool {
    matches!(
        (op, case),
        (WasmBinOp::Div(_), BinOpCase::Div) | (WasmBinOp::Rem(_), BinOpCase::Rem)
    )
}

fn binop_sign(v: AlValue, case: BinOpCase) -> Result<Sign, EvalError> {
    let op = as_binop(v)?;
    match (op, case) {
        (WasmBinOp::Div(sx), BinOpCase::Div) => Ok(sx),
        (WasmBinOp::Rem(sx), BinOpCase::Rem) => Ok(sx),
        other => panic!("LetBinOpCase mismatch: {other:?}"),
    }
}

fn binop_sign_value(op: WasmBinOp) -> Sign {
    match op {
        WasmBinOp::Div(sx) | WasmBinOp::Rem(sx) => sx,
        _ => panic!("BinOpSignOf on non-case binop: {op:?}"),
    }
}

pub fn size(valtype: ValType) -> Option<u32> {
    eval_size(valtype)
}

pub fn sizenn(nt: NumType) -> u32 {
    eval_sizenn(nt)
}

pub fn idiv_is_empty(n: u32, sx: Sign, i_1: u32, i_2: u32) -> bool {
    eval_idiv_is_empty(n, sx, i_1, i_2)
}

pub fn binop_concrete(nt: NumType, binop: WasmBinOp, i_1: u32, i_2: u32) -> Option<u32> {
    eval_binop_(nt, binop, i_1, i_2)
}
