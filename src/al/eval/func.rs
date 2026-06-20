//! Concrete evaluator for [`FuncA`](super::super::ast::FuncA) bodies (OCaml `FuncA`).

use super::super::ast::{Arg, Expr, FuncA, Instr, InstrCond, LetLhs, Param, ParamType, Pred};
use super::super::defs::{BinOpCase, NumType, Sign, ValType, WasmBinOp, lookup_func};

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

pub fn eval_fn(def: &FuncA, args: &[(&str, AlValue)]) -> EvalResult {
    let mut env = AlEnv::with_args(def.params, args);
    eval_fn_steps(&def.body, &mut env)
}

/// Variable environment for `$fn` bodies and `Instr` templates.
pub struct AlEnv {
    vars: Vec<(&'static str, AlValue)>,
}

impl AlEnv {
    pub fn new() -> Self {
        Self { vars: Vec::new() }
    }

    fn with_args(params: &[Param], args: &[(&str, AlValue)]) -> Self {
        let mut env = Self::new();
        for param in params {
            let val = args
                .iter()
                .find(|(n, _)| *n == param.name)
                .map(|(_, v)| v.clone())
                .unwrap_or_else(|| panic!("missing arg {} for AL fn", param.name));
            env.bind(param.name, val);
        }
        env
    }

    pub fn bind(&mut self, name: &'static str, val: AlValue) {
        if let Some(slot) = self.vars.iter_mut().find(|(n, _)| *n == name) {
            slot.1 = val;
        } else {
            self.vars.push((name, val));
        }
    }

    pub fn get(&self, name: &str) -> &AlValue {
        self.vars
            .iter()
            .find(|(n, _)| *n == name)
            .map(|(_, v)| v)
            .unwrap_or_else(|| panic!("unbound AL variable: {name}"))
    }
}

/// Evaluate an [`Expr`] (rule bodies and [`FuncA`] bodies).
pub fn eval_expr(expr: &Expr, env: &AlEnv) -> EvalResult {
    eval_expr_inner(expr, env)
}

fn eval_fn_steps(steps: &[Instr], env: &mut AlEnv) -> EvalResult {
    for step in steps {
        if let Some(val) = eval_fn_step(step, env)? {
            return Ok(val);
        }
    }
    Err(EvalError::Fail)
}

fn eval_fn_step(step: &Instr, env: &mut AlEnv) -> Result<Option<AlValue>, EvalError> {
    match step {
        Instr::ReturnI(expr) => Ok(Some(eval_expr_inner(expr, env)?)),
        Instr::FailI => Err(EvalError::Fail),
        Instr::AssertI(InstrCond::Pred(pred)) => {
            if !eval_pred(pred, env)? {
                return Err(EvalError::Assert);
            }
            Ok(None)
        }
        Instr::AssertI(InstrCond::Expr(_)) => panic!("expr assert in func body"),
        Instr::LetI {
            lhs: LetLhs::Var(name),
            expr,
        } => {
            env.bind(name, eval_expr_inner(expr, env)?);
            Ok(None)
        }
        Instr::LetI {
            lhs: LetLhs::BinOpCase(case, sx_name),
            expr: binop,
        } => {
            let sx = binop_sign(eval_expr_inner(binop, env)?, *case)?;
            env.bind(sx_name, AlValue::Sign(sx));
            Ok(None)
        }
        Instr::IfI {
            cond: InstrCond::Pred(pred),
            then_steps,
            else_steps,
        } => {
            if eval_pred(pred, env)? {
                eval_fn_steps(then_steps, env).map(Some)
            } else if else_steps.is_empty() {
                Ok(None)
            } else {
                eval_fn_steps(else_steps, env).map(Some)
            }
        }
        Instr::IfI {
            cond: InstrCond::Expr(_),
            ..
        } => panic!("expr if in func body"),
        Instr::PopI(_)
        | Instr::PushI(_)
        | Instr::TrapI
        | Instr::ExecuteI(_)
        | Instr::PerformI(_, _)
        | Instr::ReplaceI { .. } => {
            panic!("rule instr in func body")
        }
    }
}

fn eval_expr_inner(expr: &Expr, env: &AlEnv) -> EvalResult {
    match expr {
        Expr::VarE(name) => Ok(env.get(name).clone()),
        Expr::NatLit(n) => Ok(AlValue::Nat(*n)),
        Expr::IntLit(n) => Ok(AlValue::Int(*n)),
        Expr::ValTypeLit(vt) => Ok(AlValue::ValType(*vt)),
        Expr::SignLit(sx) => Ok(AlValue::Sign(*sx)),
        Expr::BinOpLit(op) => Ok(AlValue::BinOp(*op)),
        Expr::EmptyOpt => Ok(AlValue::Opt(None)),
        Expr::SomeOpt(inner) => Ok(AlValue::Opt(Some(Box::new(eval_expr(inner, env)?)))),
        Expr::EmptyList => Ok(AlValue::List(vec![])),
        Expr::SingletonList(inner) => Ok(AlValue::List(vec![eval_expr(inner, env)?])),
        Expr::IntCoerce(inner) => Ok(AlValue::Int(as_int(eval_expr(inner, env)?)?)),
        Expr::NatCoerce(inner) => match eval_expr(inner, env)? {
            AlValue::Nat(n) => Ok(AlValue::Nat(n)),
            // `$nat$` reinterprets i32 bit patterns (e.g. `$truncz` of 2^31).
            AlValue::Int(n) => Ok(AlValue::Nat(n as u32)),
            AlValue::Rat(n, d) => Ok(AlValue::Nat((n / d) as u32)),
            other => panic!("nat coerce on {other:?}"),
        },
        Expr::RatCoerce(inner) => as_rat(eval_expr(inner, env)?),
        Expr::TruncZ(inner) => {
            let r = as_rat_pair(eval_expr(inner, env)?)?;
            Ok(AlValue::Int(trunc_rat(r)))
        }
        Expr::Add(a, b) => eval_add(eval_expr(a, env)?, eval_expr(b, env)?),
        Expr::Sub(a, b) => eval_sub(eval_expr(a, env)?, eval_expr(b, env)?),
        Expr::Mul(a, b) => eval_mul(eval_expr(a, env)?, eval_expr(b, env)?),
        Expr::Div(a, b) => eval_div(eval_expr(a, env)?, eval_expr(b, env)?),
        Expr::Mod(a, b) => eval_mod(eval_expr(a, env)?, eval_expr(b, env)?),
        Expr::Rem(a, b) => eval_rem(eval_expr(a, env)?, eval_expr(b, env)?),
        Expr::Shl(a, b) => eval_shl(eval_expr(a, env)?, eval_expr(b, env)?),
        Expr::BitAnd(a, b) => eval_bitand(eval_expr(a, env)?, eval_expr(b, env)?),
        Expr::BitOr(a, b) => eval_bitor(eval_expr(a, env)?, eval_expr(b, env)?),
        Expr::BitXor(a, b) => eval_bitxor(eval_expr(a, env)?, eval_expr(b, env)?),
        Expr::Pow(a, b) => eval_pow(eval_expr(a, env)?, eval_expr(b, env)?),
        Expr::Neg(inner) => Ok(AlValue::Int(-as_int(eval_expr(inner, env)?)?)),
        Expr::Choose(inner) => eval_choose(eval_expr(inner, env)?),
        Expr::BinOpSignOf(inner) => Ok(AlValue::Sign(binop_sign_value(as_binop(eval_expr(
            inner, env,
        )?)?))),
        Expr::Call(name, args) => eval_call(name, args, env),
        Expr::OptionalLen(inner) => Ok(AlValue::Nat(match eval_expr(inner, env)? {
            AlValue::List(items) if items.is_empty() => 0,
            AlValue::Opt(None) => 0,
            _ => 1,
        })),
        Expr::TopValue(nt) => Ok(AlValue::NumType(*nt)),
        Expr::TopValueAny => Ok(AlValue::Nat(0)),
        Expr::CaseE(..) => panic!("CaseE in fn eval"),
        Expr::AccE(..) => panic!("AccE in fn eval"),
    }
}

fn eval_call(name: &str, args: &[Arg], env: &AlEnv) -> EvalResult {
    let mut bound = Vec::new();
    for arg in args {
        bound.push(match arg {
            Arg::Var(name) => env.get(name).clone(),
            Arg::Nat(n) => AlValue::Nat(*n),
            Arg::NumType(nt) => AlValue::NumType(*nt),
            Arg::ValType(vt) => AlValue::ValType(*vt),
            Arg::Sign(sx) => AlValue::Sign(*sx),
            Arg::BinOp(op) => AlValue::BinOp(*op),
            Arg::ExpA(expr) => eval_expr(expr, env)?,
        });
    }

    if name == "const" {
        let _nt = as_numtype(bound[0].clone())?;
        return Ok(AlValue::Nat(as_nat(bound[1].clone())?));
    }

    let def = lookup_func(name).unwrap_or_else(|| panic!("unsupported AL call in fn eval: {name}"));
    let fn_args = bind_eval_fn_args(&def, bound)?;
    eval_fn(&def, &fn_args)
}

fn eval_pred(pred: &Pred, env: &AlEnv) -> Result<bool, EvalError> {
    match pred {
        Pred::Eq(a, b) => Ok(eval_eq(eval_expr(a, env)?, eval_expr(b, env)?)),
        Pred::Lt(a, b) => cmp_lt(eval_expr(a, env)?, eval_expr(b, env)?),
        Pred::Le(a, b) => {
            let av = eval_expr(a, env)?;
            let bv = eval_expr(b, env)?;
            Ok(cmp_lt(av.clone(), bv.clone())? || cmp_eq(av, bv))
        }
        Pred::And(a, b) => {
            let left = eval_pred(a, env)?;
            let right = eval_pred(b, env)?;
            Ok(left && right)
        }
        Pred::OptIsNone(expr) => Ok(matches!(eval_expr(expr, env)?, AlValue::Opt(None))),
        Pred::TypeIsInn(expr) => Ok(matches!(eval_expr(expr, env)?, AlValue::NumType(_))),
        Pred::TypeIsFnn(_) => Ok(false),
        Pred::BinOpEq(expr, op) => Ok(as_binop(eval_expr(expr, env)?)? == *op),
        Pred::BinOpCaseIs(expr, case) => Ok(binop_case(as_binop(eval_expr(expr, env)?)?, *case)),
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
    /// `eval_pow(2, N)` for `N >= 32` uses `Nat(0)` as a `2^32` sentinel (u32 wrap).
    fn wrap_u32_mod_2p32(v: AlValue) -> EvalResult {
        Ok(AlValue::Nat(match v {
            AlValue::Nat(n) => n,
            AlValue::Int(n) => n as u32,
            other => panic!("mod 2^32 expected numeric, got {other:?}"),
        }))
    }
    match (a, b) {
        (a, AlValue::Nat(0)) | (a, AlValue::Int(0)) => wrap_u32_mod_2p32(a),
        (AlValue::Nat(x), AlValue::Nat(y)) => Ok(AlValue::Nat(x % y.max(1))),
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

fn bind_eval_fn_args(
    def: &FuncA,
    bound: Vec<AlValue>,
) -> Result<Vec<(&'static str, AlValue)>, EvalError> {
    assert_eq!(
        def.params.len(),
        bound.len(),
        "arg count mismatch for ${}",
        def.id
    );
    def.params
        .iter()
        .zip(bound)
        .map(|(param, val)| Ok((param.name, coerce_al(param.ty, val)?)))
        .collect::<Result<Vec<_>, _>>()
}

fn coerce_al(ty: ParamType, val: AlValue) -> Result<AlValue, EvalError> {
    Ok(match ty {
        ParamType::Nat => AlValue::Nat(as_nat(val)?),
        ParamType::Int => AlValue::Int(as_int(val)?),
        ParamType::ValType => AlValue::ValType(as_valtype(val)?),
        ParamType::NumType => AlValue::NumType(as_numtype(val)?),
        ParamType::Sign => AlValue::Sign(as_sign(val)?),
        ParamType::BinOp => AlValue::BinOp(as_binop(val)?),
        ParamType::Any => val,
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
