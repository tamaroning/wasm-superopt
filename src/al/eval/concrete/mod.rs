//! Concrete AL interpreter.

mod value_ast;

#[cfg(test)]
pub use value_ast::eval_value_ast_concrete;
pub use value_ast::eval_value_ast_concrete_sig;

use super::env::Env;
use super::error::EvalError;
use super::value::{AlValue, Rat};
use crate::al::ast::{
    Arg, BinOpCase, Expr, FuncA, Instr, InstrCond, LetLhs, Pred, RelOpCase, UnOpCase, WasmBinOp,
    WasmRelOp, WasmUnOp,
};
use crate::al::defs::lookup_func;

pub type EvalResult<T> = Result<T, EvalError>;

pub fn call_func(name: &str, args: Vec<AlValue>) -> EvalResult<AlValue> {
    if let Some(v) = eval_builtin(name, &args) {
        return Ok(v);
    }
    let func = lookup_func(name).ok_or_else(|| EvalError::UnknownFunc(name.to_string()))?;
    let mut env = Env::new();
    for (param, arg) in func.params.iter().zip(args) {
        env.bind(param.name, arg);
    }
    eval_func_body(&func, &mut env)
}

fn eval_builtin(name: &str, args: &[AlValue]) -> Option<AlValue> {
    match name {
        "sizenn" => {
            let nt = match args.first()? {
                AlValue::NumType(nt) => *nt,
                _ => return None,
            };
            Some(AlValue::Nat(nt.bit_width() as u64))
        }
        "truncz" => {
            let r = args.first()?.clone();
            let rat = match r {
                AlValue::Rat(r) => r,
                _ => return None,
            };
            Some(AlValue::Int(rat.trunc_toward_zero()))
        }
        "iclz_" => {
            let n = args.get(0)?.as_nat()? as u32;
            let i = args.get(1)?.as_nat()? as u64;
            let mask = if n == 64 { u64::MAX } else { (1u64 << n) - 1 };
            let i = i & mask;
            let clz = if i == 0 {
                n
            } else {
                i.leading_zeros() - (64 - n)
            };
            Some(AlValue::Nat(clz as u64))
        }
        "ictz_" => {
            let n = args.get(0)?.as_nat()? as u32;
            let i = args.get(1)?.as_nat()? as u64;
            let mask = if n == 64 { u64::MAX } else { (1u64 << n) - 1 };
            let i = i & mask;
            let ctz = if i == 0 { n } else { i.trailing_zeros().min(n) };
            Some(AlValue::Nat(ctz as u64))
        }
        "ipopcnt_" => {
            let n = args.get(0)?.as_nat()? as u32;
            let i = args.get(1)?.as_nat()? as u64;
            let mask = if n == 64 { u64::MAX } else { (1u64 << n) - 1 };
            Some(AlValue::Nat((i & mask).count_ones() as u64))
        }
        "fadd_" | "fsub_" | "fmul_" | "fdiv_" | "fmin_" | "fmax_" | "fcopysign_" => {
            float_binop_builtin(name, args)
        }
        "fabs_" | "fneg_" | "fsqrt_" | "fceil_" | "ffloor_" | "ftrunc_" | "fnearest_" => {
            float_unop_builtin(name, args)
        }
        "feq_" | "fne_" | "flt_" | "fgt_" | "fle_" | "fge_" => float_relop_builtin(name, args),
        _ => None,
    }
}

fn nat_bits(args: &[AlValue], idx: usize) -> Option<u64> {
    args.get(idx)?.as_nat()
}

fn float_width(args: &[AlValue]) -> Option<u32> {
    Some(args.first()?.as_nat()? as u32)
}

fn float_binop_builtin(name: &str, args: &[AlValue]) -> Option<AlValue> {
    let bits = float_width(args)?;
    let a = nat_bits(args, 1)?;
    let b = nat_bits(args, 2)?;
    let out = match (bits, name) {
        (32, "fadd_") => (f32::from_bits(a as u32) + f32::from_bits(b as u32)).to_bits() as u64,
        (32, "fsub_") => (f32::from_bits(a as u32) - f32::from_bits(b as u32)).to_bits() as u64,
        (32, "fmul_") => (f32::from_bits(a as u32) * f32::from_bits(b as u32)).to_bits() as u64,
        (32, "fdiv_") => (f32::from_bits(a as u32) / f32::from_bits(b as u32)).to_bits() as u64,
        (32, "fmin_") => f32::from_bits(a as u32)
            .min(f32::from_bits(b as u32))
            .to_bits() as u64,
        (32, "fmax_") => f32::from_bits(a as u32)
            .max(f32::from_bits(b as u32))
            .to_bits() as u64,
        (32, "fcopysign_") => f32::from_bits(a as u32)
            .copysign(f32::from_bits(b as u32))
            .to_bits() as u64,
        (64, "fadd_") => (f64::from_bits(a) + f64::from_bits(b)).to_bits(),
        (64, "fsub_") => (f64::from_bits(a) - f64::from_bits(b)).to_bits(),
        (64, "fmul_") => (f64::from_bits(a) * f64::from_bits(b)).to_bits(),
        (64, "fdiv_") => (f64::from_bits(a) / f64::from_bits(b)).to_bits(),
        (64, "fmin_") => f64::from_bits(a).min(f64::from_bits(b)).to_bits(),
        (64, "fmax_") => f64::from_bits(a).max(f64::from_bits(b)).to_bits(),
        (64, "fcopysign_") => f64::from_bits(a).copysign(f64::from_bits(b)).to_bits(),
        _ => return None,
    };
    Some(AlValue::List(vec![AlValue::Nat(out)]))
}

fn float_unop_builtin(name: &str, args: &[AlValue]) -> Option<AlValue> {
    let bits = float_width(args)?;
    let a = nat_bits(args, 1)?;
    let out = match (bits, name) {
        (32, "fabs_") => f32::from_bits(a as u32).abs().to_bits() as u64,
        (32, "fneg_") => (-f32::from_bits(a as u32)).to_bits() as u64,
        (32, "fsqrt_") => f32::from_bits(a as u32).sqrt().to_bits() as u64,
        (32, "fceil_") => f32::from_bits(a as u32).ceil().to_bits() as u64,
        (32, "ffloor_") => f32::from_bits(a as u32).floor().to_bits() as u64,
        (32, "ftrunc_") => f32::from_bits(a as u32).trunc().to_bits() as u64,
        (32, "fnearest_") => f32::from_bits(a as u32).round().to_bits() as u64,
        (64, "fabs_") => f64::from_bits(a).abs().to_bits(),
        (64, "fneg_") => (-f64::from_bits(a)).to_bits(),
        (64, "fsqrt_") => f64::from_bits(a).sqrt().to_bits(),
        (64, "fceil_") => f64::from_bits(a).ceil().to_bits(),
        (64, "ffloor_") => f64::from_bits(a).floor().to_bits(),
        (64, "ftrunc_") => f64::from_bits(a).trunc().to_bits(),
        (64, "fnearest_") => f64::from_bits(a).round().to_bits(),
        _ => return None,
    };
    Some(AlValue::List(vec![AlValue::Nat(out)]))
}

fn float_relop_builtin(name: &str, args: &[AlValue]) -> Option<AlValue> {
    let bits = float_width(args)?;
    let a = nat_bits(args, 1)?;
    let b = nat_bits(args, 2)?;
    let cmp = match (bits, name) {
        (32, "feq_") => f32::from_bits(a as u32) == f32::from_bits(b as u32),
        (32, "fne_") => f32::from_bits(a as u32) != f32::from_bits(b as u32),
        (32, "flt_") => f32::from_bits(a as u32) < f32::from_bits(b as u32),
        (32, "fgt_") => f32::from_bits(a as u32) > f32::from_bits(b as u32),
        (32, "fle_") => f32::from_bits(a as u32) <= f32::from_bits(b as u32),
        (32, "fge_") => f32::from_bits(a as u32) >= f32::from_bits(b as u32),
        (64, "feq_") => f64::from_bits(a) == f64::from_bits(b),
        (64, "fne_") => f64::from_bits(a) != f64::from_bits(b),
        (64, "flt_") => f64::from_bits(a) < f64::from_bits(b),
        (64, "fgt_") => f64::from_bits(a) > f64::from_bits(b),
        (64, "fle_") => f64::from_bits(a) <= f64::from_bits(b),
        (64, "fge_") => f64::from_bits(a) >= f64::from_bits(b),
        _ => return None,
    };
    Some(AlValue::Nat(u64::from(cmp)))
}

fn eval_func_body(func: &FuncA, env: &mut Env) -> EvalResult<AlValue> {
    eval_instrs(&func.body, env)
}

fn eval_instrs(instrs: &[Instr], env: &mut Env) -> EvalResult<AlValue> {
    let mut pc = 0usize;
    while pc < instrs.len() {
        match eval_instr(&instrs[pc], env)? {
            InstrOutcome::Continue => pc += 1,
            InstrOutcome::Return(v) => return Ok(v),
            InstrOutcome::Fail => return Err(EvalError::Fail),
        }
    }
    Err(EvalError::Fail)
}

enum InstrOutcome {
    Continue,
    Return(AlValue),
    Fail,
}

fn eval_instr(instr: &Instr, env: &mut Env) -> EvalResult<InstrOutcome> {
    match instr {
        Instr::IfI {
            cond,
            then_steps,
            else_steps,
        } => {
            let take_then = eval_cond(cond, env)?;
            let branch = if take_then {
                then_steps.as_slice()
            } else {
                else_steps.as_slice()
            };
            if branch.is_empty() {
                return Ok(InstrOutcome::Continue);
            }
            eval_instrs(branch, env).map(InstrOutcome::Return)
        }
        Instr::AssertI(cond) => {
            if !eval_cond(cond, env)? {
                return Err(EvalError::AssertFailed);
            }
            Ok(InstrOutcome::Continue)
        }
        Instr::LetI { lhs, expr } => {
            let v = eval_expr(expr, env)?;
            bind_lhs(lhs, v, env)?;
            Ok(InstrOutcome::Continue)
        }
        Instr::ReturnI(expr) => Ok(InstrOutcome::Return(eval_expr(expr, env)?)),
        Instr::FailI => Ok(InstrOutcome::Fail),
        Instr::PopI(_)
        | Instr::PushI(_)
        | Instr::ExecuteI(_)
        | Instr::PerformI(_, _)
        | Instr::ReplaceI { .. }
        | Instr::TrapI => Err(EvalError::Unimplemented("stack machine instr")),
    }
}

fn bind_lhs(lhs: &LetLhs, value: AlValue, env: &mut Env) -> EvalResult<()> {
    match lhs {
        LetLhs::Var(name) => {
            env.bind(name, value);
            Ok(())
        }
        LetLhs::BinOpCase(case, name) => {
            let binop = match value {
                AlValue::BinOp(b) => b,
                _ => return Err(EvalError::TypeMismatch("expected binop")),
            };
            let sx = match (case, binop) {
                (BinOpCase::Div, WasmBinOp::Div(s)) => s,
                (BinOpCase::Div, _) => return Err(EvalError::TypeMismatch("expected DIV")),
                (BinOpCase::Rem, WasmBinOp::Rem(s)) => s,
                (BinOpCase::Rem, _) => return Err(EvalError::TypeMismatch("expected REM")),
                (BinOpCase::Shr, WasmBinOp::Shr(s)) => s,
                (BinOpCase::Shr, _) => return Err(EvalError::TypeMismatch("expected SHR")),
            };
            env.bind(name, AlValue::Sign(sx));
            Ok(())
        }
        LetLhs::RelOpCase(case, name) => {
            let relop = match value {
                AlValue::RelOp(r) => r,
                _ => return Err(EvalError::TypeMismatch("expected relop")),
            };
            let sx = match (case, relop) {
                (RelOpCase::Lt, WasmRelOp::Lt(s)) => s,
                (RelOpCase::Lt, _) => return Err(EvalError::TypeMismatch("expected LT")),
                (RelOpCase::Gt, WasmRelOp::Gt(s)) => s,
                (RelOpCase::Gt, _) => return Err(EvalError::TypeMismatch("expected GT")),
                (RelOpCase::Le, WasmRelOp::Le(s)) => s,
                (RelOpCase::Le, _) => return Err(EvalError::TypeMismatch("expected LE")),
                (RelOpCase::Ge, WasmRelOp::Ge(s)) => s,
                (RelOpCase::Ge, _) => return Err(EvalError::TypeMismatch("expected GE")),
            };
            env.bind(name, AlValue::Sign(sx));
            Ok(())
        }
        LetLhs::UnOpCase(UnOpCase::Extend, name) => {
            let _unop = match value {
                AlValue::UnOp(u) => u,
                _ => return Err(EvalError::TypeMismatch("expected unop")),
            };
            // Extend width M is embedded in unop case; not needed for ValueAst path.
            env.bind(name, AlValue::Nat(0));
            Ok(())
        }
    }
}

fn eval_cond(cond: &InstrCond, env: &mut Env) -> EvalResult<bool> {
    match cond {
        InstrCond::Expr(expr) => eval_expr_as_bool(expr, env),
        InstrCond::Pred(pred) => eval_pred(pred, env),
    }
}

fn eval_expr_as_bool(expr: &Expr, env: &mut Env) -> EvalResult<bool> {
    match eval_expr(expr, env)? {
        AlValue::Bool(b) => Ok(b),
        AlValue::Nat(0) => Ok(false),
        AlValue::Nat(_) => Ok(true),
        AlValue::Int(0) => Ok(false),
        AlValue::Int(_) => Ok(true),
        _ => Err(EvalError::TypeMismatch("expected bool in condition")),
    }
}

pub fn eval_pred(pred: &Pred, env: &mut Env) -> EvalResult<bool> {
    match pred {
        Pred::Eq(a, b) => Ok(values_equal(&eval_expr(a, env)?, &eval_expr(b, env)?)),
        Pred::Lt(a, b) => cmp_nat(&eval_expr(a, env)?, &eval_expr(b, env)?, |x, y| x < y),
        Pred::Le(a, b) => cmp_nat(&eval_expr(a, env)?, &eval_expr(b, env)?, |x, y| x <= y),
        Pred::Gt(a, b) => cmp_nat(&eval_expr(a, env)?, &eval_expr(b, env)?, |x, y| x > y),
        Pred::Ge(a, b) => cmp_nat(&eval_expr(a, env)?, &eval_expr(b, env)?, |x, y| x >= y),
        Pred::Ne(a, b) => Ok(!values_equal(&eval_expr(a, env)?, &eval_expr(b, env)?)),
        Pred::And(a, b) => Ok(eval_pred(a, env)? && eval_pred(b, env)?),
        Pred::OptIsNone(expr) => {
            let v = eval_expr(expr, env)?;
            Ok(v.is_empty_list_or_opt())
        }
        Pred::TypeIsInn(expr) => Ok(matches!(
            eval_expr(expr, env)?,
            AlValue::NumType(nt) if nt.is_inn()
        )),
        Pred::TypeIsFnn(expr) => Ok(matches!(
            eval_expr(expr, env)?,
            AlValue::NumType(nt) if nt.is_fnn()
        )),
        Pred::NumTypeEq(expr, expected) => Ok(matches!(
            eval_expr(expr, env)?,
            AlValue::NumType(nt) if nt == *expected
        )),
        Pred::BinOpEq(expr, expected) => Ok(matches!(
            &eval_expr(expr, env)?,
            AlValue::BinOp(b) if *b == *expected
        )),
        Pred::BinOpCaseIs(expr, case) => {
            let b = match eval_expr(expr, env)? {
                AlValue::BinOp(b) => b,
                _ => return Err(EvalError::TypeMismatch("expected binop")),
            };
            Ok(matches!(
                (case, b),
                (BinOpCase::Div, WasmBinOp::Div(_))
                    | (BinOpCase::Rem, WasmBinOp::Rem(_))
                    | (BinOpCase::Shr, WasmBinOp::Shr(_))
            ))
        }
        Pred::RelOpEq(expr, expected) => Ok(matches!(
            &eval_expr(expr, env)?,
            AlValue::RelOp(r) if *r == *expected
        )),
        Pred::RelOpCaseIs(expr, case) => {
            let r = match eval_expr(expr, env)? {
                AlValue::RelOp(r) => r,
                _ => return Err(EvalError::TypeMismatch("expected relop")),
            };
            Ok(matches!(
                (case, r),
                (RelOpCase::Lt, WasmRelOp::Lt(_))
                    | (RelOpCase::Gt, WasmRelOp::Gt(_))
                    | (RelOpCase::Le, WasmRelOp::Le(_))
                    | (RelOpCase::Ge, WasmRelOp::Ge(_))
            ))
        }
        Pred::TestOpEq(expr, expected) => Ok(matches!(
            &eval_expr(expr, env)?,
            AlValue::TestOp(t) if *t == *expected
        )),
        Pred::UnOpEq(expr, expected) => Ok(matches!(
            &eval_expr(expr, env)?,
            AlValue::UnOp(u) if *u == *expected
        )),
        Pred::UnOpCaseIs(expr, case) => {
            let u = match eval_expr(expr, env)? {
                AlValue::UnOp(u) => u,
                _ => return Err(EvalError::TypeMismatch("expected unop")),
            };
            Ok(matches!((case, u), (UnOpCase::Extend, WasmUnOp::Extend)))
        }
    }
}

fn cmp_nat<F>(a: &AlValue, b: &AlValue, f: F) -> EvalResult<bool>
where
    F: FnOnce(u64, u64) -> bool,
{
    let a = nat_of(a)?;
    let b = nat_of(b)?;
    Ok(f(a, b))
}

fn nat_of(v: &AlValue) -> EvalResult<u64> {
    v.as_nat()
        .or_else(|| v.as_int().map(|i| i as u64))
        .ok_or(EvalError::TypeMismatch("expected nat"))
}

fn values_equal(a: &AlValue, b: &AlValue) -> bool {
    match (a, b) {
        (AlValue::Nat(x), AlValue::Nat(y)) => x == y,
        (AlValue::Int(x), AlValue::Int(y)) => x == y,
        (AlValue::Bool(x), AlValue::Bool(y)) => x == y,
        (AlValue::Sign(x), AlValue::Sign(y)) => x == y,
        (AlValue::NumType(x), AlValue::NumType(y)) => x == y,
        (AlValue::ValType(x), AlValue::ValType(y)) => x == y,
        (AlValue::BinOp(x), AlValue::BinOp(y)) => x == y,
        (AlValue::RelOp(x), AlValue::RelOp(y)) => x == y,
        (AlValue::TestOp(x), AlValue::TestOp(y)) => x == y,
        (AlValue::UnOp(x), AlValue::UnOp(y)) => x == y,
        (AlValue::Rat(x), AlValue::Rat(y)) => x == y,
        (AlValue::Opt(x), AlValue::Opt(y)) => match (x, y) {
            (None, None) => true,
            (Some(a), Some(b)) => values_equal(a, b),
            _ => false,
        },
        (AlValue::List(x), AlValue::List(y)) => {
            x.len() == y.len() && x.iter().zip(y).all(|(a, b)| values_equal(a, b))
        }
        _ => false,
    }
}

pub fn eval_expr(expr: &Expr, env: &mut Env) -> EvalResult<AlValue> {
    match expr {
        Expr::VarE(name) => env.get(name).cloned().ok_or(EvalError::UnknownVar(name)),
        Expr::NatLit(n) => Ok(AlValue::Nat(*n as u64)),
        Expr::IntLit(n) => Ok(AlValue::Int(*n as i64)),
        Expr::BoolLit(b) => Ok(AlValue::Bool(*b)),
        Expr::ValTypeLit(vt) => Ok(AlValue::ValType(*vt)),
        Expr::SignLit(s) => Ok(AlValue::Sign(*s)),
        Expr::BinOpLit(b) => Ok(AlValue::BinOp(*b)),
        Expr::RelOpLit(r) => Ok(AlValue::RelOp(*r)),
        Expr::TestOpLit(t) => Ok(AlValue::TestOp(*t)),
        Expr::UnOpLit(u) => Ok(AlValue::UnOp(*u)),
        Expr::EmptyOpt => Ok(AlValue::Opt(None)),
        Expr::SomeOpt(v) => Ok(AlValue::Opt(Some(Box::new(eval_expr(v, env)?)))),
        Expr::EmptyList => Ok(AlValue::List(vec![])),
        Expr::SingletonList(v) => Ok(AlValue::List(vec![eval_expr(v, env)?])),
        Expr::OptionalLen(v) => Ok(AlValue::Nat(eval_expr(v, env)?.list_len() as u64)),
        Expr::Choose(v) => eval_expr(v, env)?
            .choose_singleton()
            .ok_or(EvalError::TypeMismatch("choose: not singleton")),
        Expr::IntCoerce(v) => Ok(AlValue::Int(int_of(&eval_expr(v, env)?)?)),
        Expr::NatCoerce(v) => Ok(AlValue::Nat(nat_of(&eval_expr(v, env)?)?)),
        Expr::RatCoerce(v) => rat_coerce_value(&eval_expr(v, env)?),
        Expr::TruncZ(v) => {
            let r = rat_coerce_value(&eval_expr(v, env)?)?;
            Ok(AlValue::Int(match r {
                AlValue::Rat(r) => r.trunc_toward_zero(),
                _ => unreachable!(),
            }))
        }
        Expr::Call(name, args) => {
            let evaluated: EvalResult<Vec<AlValue>> =
                args.iter().map(|a| eval_arg(a, env)).collect();
            call_func(name, evaluated?)
        }
        Expr::Eq(a, b) => cmp_expr_bool(a, b, env, |x, y| Ok(x == y)),
        Expr::Ne(a, b) => cmp_expr_bool(a, b, env, |x, y| Ok(x != y)),
        Expr::LtCmp(a, b) => cmp_expr_bool(a, b, env, |x, y| Ok(x < y)),
        Expr::LeCmp(a, b) => cmp_expr_bool(a, b, env, |x, y| Ok(x <= y)),
        Expr::GtCmp(a, b) => cmp_expr_bool(a, b, env, |x, y| Ok(x > y)),
        Expr::GeCmp(a, b) => cmp_expr_bool(a, b, env, |x, y| Ok(x >= y)),
        Expr::Add(a, b) => nat_binop(a, b, env, |x, y| x.wrapping_add(y)),
        Expr::Sub(a, b) => {
            let ai = int_of(&eval_expr(a, env)?)?;
            let bi = int_of(&eval_expr(b, env)?)?;
            Ok(AlValue::Int(ai.wrapping_sub(bi)))
        }
        Expr::Mul(a, b) => nat_binop(a, b, env, |x, y| x.wrapping_mul(y)),
        Expr::Div(a, b) => {
            let ar = rat_of(&eval_expr(a, env)?)?;
            let br = rat_of(&eval_expr(b, env)?)?;
            Ok(AlValue::Rat(Rat::new(ar.num * br.den, ar.den * br.num)))
        }
        Expr::Mod(a, b) => {
            let an = nat_of(&eval_expr(a, env)?)?;
            let bn = nat_of(&eval_expr(b, env)?)?;
            // `full_modulus` for i64 is 2^64, which overflows u64 `Nat` to 0.
            // Wasm wrap semantics: reduce mod 2^N on N-bit values ≡ identity in u64.
            Ok(AlValue::Nat(if bn == 0 { an } else { an % bn }))
        }
        Expr::Rem(a, b) => {
            let an = nat_of(&eval_expr(a, env)?)?;
            let bn = nat_of(&eval_expr(b, env)?)?;
            Ok(AlValue::Nat(if bn == 0 { an } else { an % bn }))
        }
        Expr::Pow(a, b) => {
            let base = nat_of(&eval_expr(a, env)?)?;
            let exp = nat_of(&eval_expr(b, env)?)?;
            // Spectec `2^N` for N=64 exceeds u64; carrier 0 means mod 2^64 (see Mod).
            let out = if base == 2 && exp == 64 {
                0
            } else {
                base.saturating_pow(exp as u32)
            };
            Ok(AlValue::Nat(out))
        }
        Expr::Shl(a, b) => {
            let an = nat_of(&eval_expr(a, env)?)?;
            let bn = nat_of(&eval_expr(b, env)?)?;
            Ok(AlValue::Nat(an << bn))
        }
        Expr::BitAnd(a, b) => nat_binop(a, b, env, |x, y| x & y),
        Expr::BitOr(a, b) => nat_binop(a, b, env, |x, y| x | y),
        Expr::BitXor(a, b) => nat_binop(a, b, env, |x, y| x ^ y),
        Expr::LShr(a, b) => {
            let an = nat_of(&eval_expr(a, env)?)?;
            let bn = nat_of(&eval_expr(b, env)?)?;
            Ok(AlValue::Nat(an.wrapping_shr((bn % 64) as u32)))
        }
        Expr::AShr(a, b) => {
            let an = nat_of(&eval_expr(a, env)?)?;
            let bn = nat_of(&eval_expr(b, env)?)?;
            let shift = (bn % 64) as u32;
            Ok(AlValue::Nat((an as i64).wrapping_shr(shift) as u64))
        }
        Expr::Rotl(a, b) => {
            let an = nat_of(&eval_expr(a, env)?)? as u32;
            let bn = (nat_of(&eval_expr(b, env)?)? % 32) as u32;
            Ok(AlValue::Nat(an.rotate_left(bn) as u64))
        }
        Expr::Rotr(a, b) => {
            let an = nat_of(&eval_expr(a, env)?)? as u32;
            let bn = (nat_of(&eval_expr(b, env)?)? % 32) as u32;
            Ok(AlValue::Nat(an.rotate_right(bn) as u64))
        }
        Expr::Neg(v) => {
            let i = int_of(&eval_expr(v, env)?)?;
            Ok(AlValue::Int(-i))
        }
        Expr::BinOpSignOf(v) => {
            let b = match eval_expr(v, env)? {
                AlValue::BinOp(b) => b,
                _ => return Err(EvalError::TypeMismatch("BinOpSignOf")),
            };
            let s = match b {
                WasmBinOp::Div(s) | WasmBinOp::Rem(s) | WasmBinOp::Shr(s) => s,
                _ => return Err(EvalError::TypeMismatch("BinOpSignOf: not signed case")),
            };
            Ok(AlValue::Sign(s))
        }
        Expr::TopValue(_) | Expr::TopValueAny | Expr::CaseE(_, _) | Expr::AccE(_, _) => {
            Err(EvalError::Unimplemented("stack expr"))
        }
    }
}

fn eval_arg(arg: &Arg, env: &mut Env) -> EvalResult<AlValue> {
    match arg {
        Arg::NumType(nt) => Ok(AlValue::NumType(*nt)),
        Arg::ValType(vt) => Ok(AlValue::ValType(*vt)),
        Arg::BinOp(b) => Ok(AlValue::BinOp(*b)),
        Arg::RelOp(r) => Ok(AlValue::RelOp(*r)),
        Arg::TestOp(t) => Ok(AlValue::TestOp(*t)),
        Arg::UnOp(u) => Ok(AlValue::UnOp(*u)),
        Arg::Var(name) => env.get(name).cloned().ok_or(EvalError::UnknownVar(name)),
        Arg::Nat(n) => Ok(AlValue::Nat(*n as u64)),
        Arg::Sign(s) => Ok(AlValue::Sign(*s)),
        Arg::ExpA(expr) => eval_expr(expr, env),
    }
}

fn cmp_expr_bool<F>(a: &Expr, b: &Expr, env: &mut Env, f: F) -> EvalResult<AlValue>
where
    F: FnOnce(u64, u64) -> EvalResult<bool>,
{
    let av = nat_of(&eval_expr(a, env)?)?;
    let bv = nat_of(&eval_expr(b, env)?)?;
    Ok(AlValue::Bool(f(av, bv)?))
}

fn nat_binop<F>(a: &Expr, b: &Expr, env: &mut Env, f: F) -> EvalResult<AlValue>
where
    F: FnOnce(u64, u64) -> u64,
{
    let av = nat_of(&eval_expr(a, env)?)?;
    let bv = nat_of(&eval_expr(b, env)?)?;
    Ok(AlValue::Nat(f(av, bv)))
}

fn int_of(v: &AlValue) -> EvalResult<i64> {
    match v {
        AlValue::Int(i) => Ok(*i),
        AlValue::Nat(n) => Ok(*n as i64),
        _ => Err(EvalError::TypeMismatch("expected int")),
    }
}

fn rat_of(v: &AlValue) -> EvalResult<Rat> {
    match v {
        AlValue::Rat(r) => Ok(*r),
        AlValue::Int(i) => Ok(Rat::from_int(*i)),
        AlValue::Nat(n) => Ok(Rat::from_int(*n as i64)),
        _ => Err(EvalError::TypeMismatch("expected rat")),
    }
}

fn rat_coerce_value(v: &AlValue) -> EvalResult<AlValue> {
    Ok(AlValue::Rat(rat_of(v)?))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::al::ast::WasmBinOp;
    use crate::al::{NumType, Sign};

    #[test]
    fn signed_min_div_neg_one_is_empty() {
        let args = vec![
            AlValue::NumType(NumType::I32),
            AlValue::BinOp(WasmBinOp::Div(Sign::S)),
            AlValue::Nat(i32::MIN as u32 as u64),
            AlValue::Nat((-1i32) as u32 as u64),
        ];
        let list = call_func("binop_", args).unwrap();
        assert!(list.is_empty_list_or_opt());
    }

    #[test]
    fn i64_add_neg_one_plus_zero() {
        let args = vec![
            AlValue::NumType(NumType::I64),
            AlValue::BinOp(WasmBinOp::Add),
            AlValue::Nat((-1i64) as u64),
            AlValue::Nat(0),
        ];
        let list = call_func("binop_", args).unwrap();
        assert!(!list.is_empty_list_or_opt());
        let v = list.choose_singleton().unwrap();
        assert_eq!(
            v.as_nat().map(|n| n as i64),
            Some(-1i64),
            "i64.add (-1) 0 should be -1"
        );
    }

    #[test]
    fn add_wraps() {
        let args = vec![
            AlValue::NumType(NumType::I32),
            AlValue::BinOp(WasmBinOp::Add),
            AlValue::Nat(i32::MAX as u32 as u64),
            AlValue::Nat(1),
        ];
        let list = call_func("binop_", args).unwrap();
        let v = list.choose_singleton().unwrap();
        assert_eq!(v.as_nat(), Some(i32::MIN as u32 as u64));
    }
}
