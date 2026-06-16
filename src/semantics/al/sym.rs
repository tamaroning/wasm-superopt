//! Symbolic encoder for meta-level AL `$fn` definitions (Z3).

use std::ops::{Add, Mul, Sub};

use super::al_defs::lookup_fn;
use super::ir::{NumType, Sign, WasmBinOp};
use super::super::I32_BITS;
use super::meta::{
    AlMetaArg, AlMetaExpr, AlMetaFnDef, AlMetaFnStep, AlMetaParam, AlMetaParamType, AlMetaPred,
    BinOpCase, ValType,
};
use z3::Context;
use z3::ast::{Ast, BV, Bool, Int};

#[derive(Clone, Debug)]
pub enum SymValue<'ctx> {
    Nat(BV<'ctx>),
    Int(BV<'ctx>),
    Rat(Int<'ctx>, Int<'ctx>),
    NumType(NumType),
    ValType(ValType),
    Sign(Sign),
    BinOp(WasmBinOp),
    Opt(Option<Box<SymValue<'ctx>>>),
    List(Vec<SymValue<'ctx>>),
    /// Symbolic optional with explicit emptiness (ε vs defined).
    Partial {
        empty: Bool<'ctx>,
        value: Box<SymValue<'ctx>>,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EncodeError {
    Fail,
    Assert,
}

type EncodeResult<'ctx> = Result<SymValue<'ctx>, EncodeError>;

pub fn encode_fn<'ctx>(
    ctx: &'ctx Context,
    def: &AlMetaFnDef,
    args: &[(&str, SymValue<'ctx>)],
) -> EncodeResult<'ctx> {
    let mut env = SymEnv::new(def.params, args);
    encode_fn_steps(ctx, &def.body, &mut env)
}

pub fn encode_call<'ctx>(
    ctx: &'ctx Context,
    name: &str,
    args: &[AlMetaArg],
    env: &SymEnv<'ctx>,
) -> EncodeResult<'ctx> {
    let mut bound = Vec::new();
    for arg in args {
        bound.push(match arg {
            AlMetaArg::Var(name) => env.get(name).clone(),
            AlMetaArg::Nat(n) => SymValue::nat_const(ctx, *n),
            AlMetaArg::NumType(nt) => SymValue::NumType(*nt),
            AlMetaArg::ValType(vt) => SymValue::ValType(*vt),
            AlMetaArg::Sign(sx) => SymValue::Sign(*sx),
            AlMetaArg::BinOp(op) => SymValue::BinOp(*op),
            AlMetaArg::Expr(expr) => encode_expr(ctx, expr, env)?,
        });
    }

    let def = lookup_fn(name).unwrap_or_else(|| panic!("unsupported AL call in sym encode: {name}"));
    let fn_args = bind_sym_fn_args(&def, bound)?;
    encode_fn(ctx, &def, &fn_args)
}

/// Whether `|$expr| <= 0` (list/opt empty) as a Z3 boolean.
pub fn sym_is_empty<'ctx>(ctx: &'ctx Context, v: &SymValue<'ctx>) -> Bool<'ctx> {
    match v {
        SymValue::List(items) if items.is_empty() => Bool::from_bool(ctx, true),
        SymValue::Opt(None) => Bool::from_bool(ctx, true),
        SymValue::List(items) if items.len() == 1 => Bool::from_bool(ctx, false),
        SymValue::Opt(Some(_)) => Bool::from_bool(ctx, false),
        SymValue::Partial { empty, .. } => empty.clone(),
        other => panic!("sym_is_empty on {other:?}"),
    }
}

/// Spectec `choose` — extract singleton nat BV from list/opt.
///
/// Empty list/opt return a dummy zero; callers that branch on `sym_is_empty`
/// must use `is_empty.ite(&zero, &sym_choose_nat(...))` (see `meta_z3`).
pub fn sym_choose_nat<'ctx>(ctx: &'ctx Context, v: SymValue<'ctx>) -> BV<'ctx> {
    let zero = BV::from_u64(ctx, 0, I32_BITS);
    match v {
        SymValue::Opt(None) => zero,
        SymValue::List(items) if items.is_empty() => zero,
        SymValue::Opt(Some(inner)) => as_nat_bv_direct(ctx, *inner),
        SymValue::List(items) if items.len() == 1 => as_nat_bv_direct(ctx, items[0].clone()),
        SymValue::Partial { empty, value } => {
            empty.ite(&zero, &as_nat_bv_direct(ctx, *value))
        }
        other => panic!("sym_choose_nat on {other:?}"),
    }
}

/// Extract singleton value from optional/list (Spectec `choose`).
pub fn encode_choose<'ctx>(
    ctx: &'ctx Context,
    expr: &AlMetaExpr,
    env: &SymEnv<'ctx>,
) -> EncodeResult<'ctx> {
    encode_choose_value(ctx, encode_expr(ctx, expr, env)?)
}

pub fn encode_expr<'ctx>(
    ctx: &'ctx Context,
    expr: &AlMetaExpr,
    env: &SymEnv<'ctx>,
) -> EncodeResult<'ctx> {
    match expr {
        AlMetaExpr::Param(name) => Ok(env.get(name).clone()),
        AlMetaExpr::NatLit(n) => Ok(SymValue::nat_const(ctx, *n)),
        AlMetaExpr::IntLit(n) => Ok(SymValue::int_const(ctx, *n)),
        AlMetaExpr::ValTypeLit(vt) => Ok(SymValue::ValType(*vt)),
        AlMetaExpr::SignLit(sx) => Ok(SymValue::Sign(*sx)),
        AlMetaExpr::BinOpLit(op) => Ok(SymValue::BinOp(*op)),
        AlMetaExpr::EmptyOpt => Ok(SymValue::Opt(None)),
        AlMetaExpr::SomeOpt(inner) => Ok(SymValue::Opt(Some(Box::new(encode_expr(
            ctx, inner, env,
        )?)))),
        AlMetaExpr::EmptyList => Ok(SymValue::List(vec![])),
        AlMetaExpr::SingletonList(inner) => {
            Ok(SymValue::List(vec![encode_expr(ctx, inner, env)?]))
        }
        AlMetaExpr::IntCoerce(inner) => {
            Ok(SymValue::Int(int_coerce(ctx, encode_expr(ctx, inner, env)?)?))
        }
        AlMetaExpr::NatCoerce(inner) => nat_coerce(ctx, encode_expr(ctx, inner, env)?),
        AlMetaExpr::RatCoerce(inner) => as_rat(ctx, encode_expr(ctx, inner, env)?),
        AlMetaExpr::TruncZ(inner) => {
            let r = as_rat_pair(encode_expr(ctx, inner, env)?)?;
            Ok(SymValue::Int(trunc_rat(ctx, r)))
        }
        AlMetaExpr::Add(a, b) => sym_add(ctx, encode_expr(ctx, a, env)?, encode_expr(ctx, b, env)?),
        AlMetaExpr::Sub(a, b) => sym_sub(ctx, encode_expr(ctx, a, env)?, encode_expr(ctx, b, env)?),
        AlMetaExpr::Mul(a, b) => sym_mul(ctx, encode_expr(ctx, a, env)?, encode_expr(ctx, b, env)?),
        AlMetaExpr::Div(a, b) => sym_div(ctx, encode_expr(ctx, a, env)?, encode_expr(ctx, b, env)?),
        AlMetaExpr::Mod(a, b) => sym_mod(ctx, encode_expr(ctx, a, env)?, encode_expr(ctx, b, env)?),
        AlMetaExpr::Rem(a, b) => sym_rem(ctx, encode_expr(ctx, a, env)?, encode_expr(ctx, b, env)?),
        AlMetaExpr::Shl(a, b) => sym_shl(ctx, encode_expr(ctx, a, env)?, encode_expr(ctx, b, env)?),
        AlMetaExpr::BitAnd(a, b) => {
            sym_bitand(ctx, encode_expr(ctx, a, env)?, encode_expr(ctx, b, env)?)
        }
        AlMetaExpr::BitOr(a, b) => {
            sym_bitor(ctx, encode_expr(ctx, a, env)?, encode_expr(ctx, b, env)?)
        }
        AlMetaExpr::BitXor(a, b) => {
            sym_bitxor(ctx, encode_expr(ctx, a, env)?, encode_expr(ctx, b, env)?)
        }
        AlMetaExpr::Pow(a, b) => sym_pow(ctx, encode_expr(ctx, a, env)?, encode_expr(ctx, b, env)?),
        AlMetaExpr::Neg(inner) => Ok(SymValue::Int(
            int_coerce(ctx, encode_expr(ctx, inner, env)?)?.bvneg(),
        )),
        AlMetaExpr::Choose(inner) => encode_choose(ctx, inner, env),
        AlMetaExpr::BinOpSignOf(inner) => Ok(SymValue::Sign(binop_sign_value(as_binop(
            encode_expr(ctx, inner, env)?,
        )?))),
        AlMetaExpr::Call(name, args) => encode_call(ctx, name, args, env),
        AlMetaExpr::OptionalLen(inner) => Ok(SymValue::nat_const(
            ctx,
            match encode_expr(ctx, inner, env)? {
                SymValue::List(items) if items.is_empty() => 0,
                SymValue::Opt(None) => 0,
                _ => 1,
            },
        )),
        AlMetaExpr::TopValue(_) => panic!("step-only TopValue in sym encode: {expr:?}"),
    }
}

pub struct SymEnv<'ctx> {
    vars: Vec<(&'static str, SymValue<'ctx>)>,
}

impl<'ctx> SymEnv<'ctx> {
    pub fn new(params: &[AlMetaParam], args: &[(&str, SymValue<'ctx>)]) -> Self {
        let mut vars = Vec::new();
        for param in params {
            let val = args
                .iter()
                .find(|(n, _)| *n == param.name)
                .map(|(_, v)| v.clone())
                .unwrap_or_else(|| panic!("missing arg {} for AL fn", param.name));
            vars.push((param.name, val));
        }
        Self { vars }
    }

    pub fn bind(&mut self, name: &'static str, val: SymValue<'ctx>) {
        if let Some(slot) = self.vars.iter_mut().find(|(n, _)| *n == name) {
            slot.1 = val;
        } else {
            self.vars.push((name, val));
        }
    }

    pub fn get(&self, name: &str) -> &SymValue<'ctx> {
        self.vars
            .iter()
            .find(|(n, _)| *n == name)
            .map(|(_, v)| v)
            .unwrap_or_else(|| panic!("unbound AL variable: {name}"))
    }
}

impl<'ctx> SymValue<'ctx> {
    pub fn nat_const(ctx: &'ctx Context, n: u32) -> Self {
        SymValue::Nat(BV::from_u64(ctx, n as u64, I32_BITS))
    }

    pub fn int_const(ctx: &'ctx Context, n: i32) -> Self {
        SymValue::Int(BV::from_i64(ctx, n as i64, I32_BITS))
    }

    pub fn nat_from_bv(bv: BV<'ctx>) -> Self {
        SymValue::Nat(bv)
    }

    /// Push an i32 stack value as a Spectec nat bit-pattern.
    pub fn nat_from_stack(bv: BV<'ctx>) -> Self {
        SymValue::Nat(bv)
    }
}

fn encode_fn_steps<'ctx>(
    ctx: &'ctx Context,
    steps: &[AlMetaFnStep],
    env: &mut SymEnv<'ctx>,
) -> EncodeResult<'ctx> {
    encode_fn_steps_from(ctx, steps, env, 0)
}

fn encode_fn_steps_from<'ctx>(
    ctx: &'ctx Context,
    steps: &[AlMetaFnStep],
    env: &mut SymEnv<'ctx>,
    idx: usize,
) -> EncodeResult<'ctx> {
    if idx >= steps.len() {
        return Err(EncodeError::Fail);
    }
    match encode_fn_step(ctx, &steps[idx], env, steps, idx)? {
        Some(v) => Ok(v),
        None => encode_fn_steps_from(ctx, steps, env, idx + 1),
    }
}

fn encode_fn_step<'ctx>(
    ctx: &'ctx Context,
    step: &AlMetaFnStep,
    env: &mut SymEnv<'ctx>,
    steps: &[AlMetaFnStep],
    idx: usize,
) -> Result<Option<SymValue<'ctx>>, EncodeError> {
    match step {
        AlMetaFnStep::Return(expr) => Ok(Some(encode_expr(ctx, expr, env)?)),
        AlMetaFnStep::Fail => Err(EncodeError::Fail),
        AlMetaFnStep::Assert(pred) => {
            match encode_pred_concrete(ctx, pred, env)? {
                Some(false) => return Err(EncodeError::Assert),
                Some(true) | None => {}
            }
            Ok(None)
        }
        AlMetaFnStep::Let { name, expr } => {
            env.bind(name, encode_expr(ctx, expr, env)?);
            Ok(None)
        }
        AlMetaFnStep::LetBinOpCase {
            case,
            sx_name,
            binop,
        } => {
            let sx = binop_sign(encode_expr(ctx, binop, env)?, *case)?;
            env.bind(sx_name, SymValue::Sign(sx));
            Ok(None)
        }
        AlMetaFnStep::If {
            cond,
            then_steps,
            else_steps,
        } => {
            if let Some(b) = encode_pred_concrete(ctx, cond, env)? {
                if b {
                    return encode_fn_steps(ctx, then_steps, env).map(Some);
                }
                if else_steps.is_empty() {
                    return Ok(None);
                }
                return encode_fn_steps(ctx, else_steps, env).map(Some);
            }
            let c = encode_pred_z3(ctx, cond, env)?;
            if let Some(b) = z3_bool_definite(&c) {
                if b {
                    return encode_fn_steps(ctx, then_steps, env).map(Some);
                }
                if else_steps.is_empty() {
                    return Ok(None);
                }
                return encode_fn_steps(ctx, else_steps, env).map(Some);
            }
            if else_steps.is_empty() {
                let then_v = encode_fn_steps(ctx, then_steps, env)?;
                match encode_fn_steps_from(ctx, steps, env, idx + 1) {
                    Ok(rest) => Ok(Some(sym_if_else(ctx, c, then_v, rest))),
                    Err(EncodeError::Fail) => Ok(Some(then_v)),
                    Err(e) => Err(e),
                }
            } else {
                let then_v = encode_fn_steps(ctx, then_steps, env)?;
                let else_v = encode_fn_steps(ctx, else_steps, env)?;
                Ok(Some(sym_if_else(ctx, c, then_v, else_v)))
            }
        }
    }
}

fn encode_pred_concrete<'ctx>(
    ctx: &'ctx Context,
    pred: &AlMetaPred,
    env: &SymEnv<'ctx>,
) -> Result<Option<bool>, EncodeError> {
    match pred {
        AlMetaPred::Eq(a, b) => {
            let av = encode_expr(ctx, a, env)?;
            let bv = encode_expr(ctx, b, env)?;
            Ok(sym_eq_concrete(av, bv))
        }
        AlMetaPred::Lt(a, b) => {
            let av = encode_expr(ctx, a, env)?;
            let bv = encode_expr(ctx, b, env)?;
            Ok(sym_cmp_lt_concrete(&av, &bv))
        }
        AlMetaPred::Le(a, b) => {
            let av = encode_expr(ctx, a, env)?;
            let bv = encode_expr(ctx, b, env)?;
            match (sym_cmp_lt_concrete(&av, &bv), sym_eq_concrete(av, bv)) {
                (Some(lt), Some(eq)) => Ok(Some(lt || eq)),
                _ => Ok(None),
            }
        }
        AlMetaPred::And(a, b) => match (
            encode_pred_concrete(ctx, a, env)?,
            encode_pred_concrete(ctx, b, env)?,
        ) {
            (Some(x), Some(y)) => Ok(Some(x && y)),
            _ => Ok(None),
        },
        AlMetaPred::OptIsNone(expr) => Ok(sym_opt_is_none_concrete(
            &encode_expr(ctx, expr, env)?,
        )),
        AlMetaPred::TypeIsInn(expr) => Ok(Some(matches!(
            encode_expr(ctx, expr, env)?,
            SymValue::NumType(_)
        ))),
        AlMetaPred::TypeIsFnn(_) => Ok(Some(false)),
        AlMetaPred::BinOpEq(expr, op) => Ok(Some(
            as_binop(encode_expr(ctx, expr, env)?)? == *op,
        )),
        AlMetaPred::BinOpCaseIs(expr, case) => Ok(Some(binop_case(
            as_binop(encode_expr(ctx, expr, env)?)?,
            *case,
        ))),
    }
}

fn sym_eq_concrete<'ctx>(a: SymValue<'ctx>, b: SymValue<'ctx>) -> Option<bool> {
    match (a, b) {
        (SymValue::Nat(x), SymValue::Nat(y)) => {
            match (bv_const_u64(&x), bv_const_u64(&y)) {
                (Some(xu), Some(yu)) => Some(xu == yu),
                _ => None,
            }
        }
        (SymValue::Int(x), SymValue::Int(y)) => match (x.as_i64(), y.as_i64()) {
            (Some(xi), Some(yi)) => Some(xi == yi),
            _ => None,
        },
        (SymValue::Sign(x), SymValue::Sign(y)) => Some(x == y),
        (SymValue::BinOp(x), SymValue::BinOp(y)) => Some(x == y),
        (SymValue::NumType(x), SymValue::NumType(y)) => Some(x == y),
        (SymValue::ValType(x), SymValue::ValType(y)) => Some(x == y),
        (SymValue::Rat(xn, xd), SymValue::Rat(yn, yd)) => match (
            int_concrete(&xn),
            int_concrete(&xd),
            int_concrete(&yn),
            int_concrete(&yd),
        ) {
            (Some(xni), Some(xdi), Some(yni), Some(ydi)) => Some(xni * ydi == yni * xdi),
            _ => None,
        },
        _ => Some(false),
    }
}

fn sym_cmp_lt_concrete<'ctx>(a: &SymValue<'ctx>, b: &SymValue<'ctx>) -> Option<bool> {
    if matches!((a, b), (SymValue::Nat(_), SymValue::Nat(y)) if is_zero_bv(y)) {
        return Some(true);
    }
    let ai = sym_to_i64(a)?;
    let bi = sym_to_i64(b)?;
    Some(ai < bi)
}

fn sym_to_i64<'ctx>(v: &SymValue<'ctx>) -> Option<i64> {
    match v {
        SymValue::Nat(bv) => bv.as_u64().map(|n| n as i64),
        SymValue::Int(bv) => bv.as_i64(),
        SymValue::Rat(n, d) => {
            let nn = int_concrete(&n)?;
            let dd = int_concrete(&d)?;
            Some(nn / dd)
        }
        _ => None,
    }
}

fn sym_opt_is_none_concrete<'ctx>(v: &SymValue<'ctx>) -> Option<bool> {
    match v {
        SymValue::List(items) if items.is_empty() => Some(true),
        SymValue::Opt(None) => Some(true),
        SymValue::List(items) if items.len() == 1 => Some(false),
        SymValue::Opt(Some(_)) => Some(false),
        SymValue::Partial { empty, .. } => empty.as_bool(),
        _ => None,
    }
}

fn encode_pred_z3<'ctx>(
    ctx: &'ctx Context,
    pred: &AlMetaPred,
    env: &SymEnv<'ctx>,
) -> Result<Bool<'ctx>, EncodeError> {
    match pred {
        AlMetaPred::Eq(a, b) => sym_eq_z3(ctx, encode_expr(ctx, a, env)?, encode_expr(ctx, b, env)?),
        AlMetaPred::Lt(a, b) => sym_lt_z3(ctx, encode_expr(ctx, a, env)?, encode_expr(ctx, b, env)?),
        AlMetaPred::Le(a, b) => {
            let av = encode_expr(ctx, a, env)?;
            let bv = encode_expr(ctx, b, env)?;
            Ok(Bool::or(
                ctx,
                &[&sym_lt_z3(ctx, av.clone(), bv.clone())?, &sym_eq_z3(ctx, av, bv)?],
            ))
        }
        AlMetaPred::And(a, b) => Ok(Bool::and(
            ctx,
            &[
                &encode_pred_z3(ctx, a, env)?,
                &encode_pred_z3(ctx, b, env)?,
            ],
        )),
        AlMetaPred::OptIsNone(expr) => Ok(sym_is_empty(ctx, &encode_expr(ctx, expr, env)?)),
        AlMetaPred::TypeIsInn(expr) => Ok(Bool::from_bool(
            ctx,
            matches!(encode_expr(ctx, expr, env)?, SymValue::NumType(_)),
        )),
        AlMetaPred::TypeIsFnn(_) => Ok(Bool::from_bool(ctx, false)),
        AlMetaPred::BinOpEq(expr, op) => Ok(Bool::from_bool(
            ctx,
            as_binop(encode_expr(ctx, expr, env)?)? == *op,
        )),
        AlMetaPred::BinOpCaseIs(expr, case) => Ok(Bool::from_bool(
            ctx,
            binop_case(as_binop(encode_expr(ctx, expr, env)?)?, *case),
        )),
    }
}

fn sym_as_z3_int<'ctx>(v: &SymValue<'ctx>) -> Int<'ctx> {
    match v {
        SymValue::Nat(bv) => bv.to_int(false),
        SymValue::Int(bv) => bv.to_int(true),
        SymValue::Rat(n, d) => n.div(d),
        other => panic!("sym_as_z3_int on {other:?}"),
    }
}

fn sym_is_numeric(v: &SymValue<'_>) -> bool {
    matches!(v, SymValue::Nat(_) | SymValue::Int(_) | SymValue::Rat(_, _))
}

fn sym_eq_z3<'ctx>(
    ctx: &'ctx Context,
    a: SymValue<'ctx>,
    b: SymValue<'ctx>,
) -> Result<Bool<'ctx>, EncodeError> {
    Ok(match (a, b) {
        (SymValue::Nat(x), SymValue::Nat(y)) => x._eq(&y),
        (SymValue::Int(x), SymValue::Int(y)) => x._eq(&y),
        (SymValue::Sign(x), SymValue::Sign(y)) => Bool::from_bool(ctx, x == y),
        (SymValue::BinOp(x), SymValue::BinOp(y)) => Bool::from_bool(ctx, x == y),
        (SymValue::NumType(x), SymValue::NumType(y)) => Bool::from_bool(ctx, x == y),
        (SymValue::ValType(x), SymValue::ValType(y)) => Bool::from_bool(ctx, x == y),
        (SymValue::Rat(xn, xd), SymValue::Rat(yn, yd)) => xn.mul(&yd)._eq(&yn.mul(&xd)),
        _ => Bool::from_bool(ctx, false),
    })
}

fn sym_lt_z3<'ctx>(
    ctx: &'ctx Context,
    a: SymValue<'ctx>,
    b: SymValue<'ctx>,
) -> Result<Bool<'ctx>, EncodeError> {
    if matches!((&a, &b), (SymValue::Nat(_), SymValue::Nat(y)) if is_zero_bv(y)) {
        return Ok(Bool::from_bool(ctx, true));
    }
    Ok(match (&a, &b) {
        (SymValue::Nat(x), SymValue::Nat(y)) => x.bvult(y),
        (SymValue::Int(x), SymValue::Int(y)) => x.bvslt(y),
        (SymValue::Rat(xn, xd), SymValue::Rat(yn, yd)) => xn.mul(yd).lt(&yn.mul(xd)),
        (a, b) if sym_is_numeric(a) && sym_is_numeric(b) => {
            sym_as_z3_int(a).lt(&sym_as_z3_int(b))
        }
        (a, b) => panic!("sym_lt_z3 on incompatible {a:?} {b:?}"),
    })
}

fn z3_bool_definite<'ctx>(b: &Bool<'ctx>) -> Option<bool> {
    if let Some(v) = b.as_bool() {
        return Some(v);
    }
    b.simplify().as_bool()
}

fn sym_if_else<'ctx>(
    ctx: &'ctx Context,
    cond: Bool<'ctx>,
    then_v: SymValue<'ctx>,
    else_v: SymValue<'ctx>,
) -> SymValue<'ctx> {
    if is_optional_form(&then_v) || is_optional_form(&else_v) {
        let (t_empty, t_val) = sym_as_partial(ctx, then_v);
        let (e_empty, e_val) = sym_as_partial(ctx, else_v);
        return SymValue::Partial {
            empty: Bool::or(
                ctx,
                &[
                    &Bool::and(ctx, &[&cond, &t_empty]),
                    &Bool::and(ctx, &[&cond.not(), &e_empty]),
                ],
            ),
            value: Box::new(merge_cond_values(ctx, &cond, *t_val, *e_val)),
        };
    }
    match (then_v, else_v) {
        (SymValue::Int(t), SymValue::Int(e)) => SymValue::Int(cond.ite(&t, &e)),
        (SymValue::Nat(t), SymValue::Nat(e)) => SymValue::Nat(cond.ite(&t, &e)),
        (a, b) => panic!("sym_if_else on incompatible {a:?} {b:?}"),
    }
}

fn is_optional_form<'ctx>(v: &SymValue<'ctx>) -> bool {
    matches!(
        v,
        SymValue::Opt(_) | SymValue::List(_) | SymValue::Partial { .. }
    )
}

fn merge_cond_values<'ctx>(
    ctx: &'ctx Context,
    cond: &Bool<'ctx>,
    then_v: SymValue<'ctx>,
    else_v: SymValue<'ctx>,
) -> SymValue<'ctx> {
    match (then_v, else_v) {
        (SymValue::Nat(t), SymValue::Nat(e)) => SymValue::Nat(cond.ite(&t, &e)),
        (SymValue::Int(t), SymValue::Int(e)) => SymValue::Int(cond.ite(&t, &e)),
        (t, e) => SymValue::Nat(cond.ite(
            &as_nat_bv_direct(ctx, t),
            &as_nat_bv_direct(ctx, e),
        )),
    }
}

fn sym_as_partial<'ctx>(
    ctx: &'ctx Context,
    v: SymValue<'ctx>,
) -> (Bool<'ctx>, Box<SymValue<'ctx>>) {
    match v {
        SymValue::Partial { empty, value } => (empty, value),
        SymValue::Opt(None) => (
            Bool::from_bool(ctx, true),
            Box::new(SymValue::Nat(BV::from_u64(ctx, 0, I32_BITS))),
        ),
        SymValue::Opt(Some(inner)) => (Bool::from_bool(ctx, false), inner),
        SymValue::List(items) if items.is_empty() => (
            Bool::from_bool(ctx, true),
            Box::new(SymValue::Nat(BV::from_u64(ctx, 0, I32_BITS))),
        ),
        SymValue::List(items) if items.len() == 1 => (Bool::from_bool(ctx, false), Box::new(items[0].clone())),
        other => (Bool::from_bool(ctx, false), Box::new(other)),
    }
}

fn as_nat_bv_direct<'ctx>(_ctx: &'ctx Context, v: SymValue<'ctx>) -> BV<'ctx> {
    match v {
        SymValue::Nat(bv) => bv,
        SymValue::Int(bv) => bv,
        other => panic!("expected nat bv, got {other:?}"),
    }
}

fn encode_choose_value<'ctx>(
    _ctx: &'ctx Context,
    v: SymValue<'ctx>,
) -> EncodeResult<'ctx> {
    match v {
        SymValue::Opt(Some(inner)) => Ok(*inner),
        SymValue::List(items) if items.len() == 1 => Ok(items[0].clone()),
        SymValue::Partial { value, .. } => Ok(*value),
        other => panic!("choose on {other:?}"),
    }
}

fn bv_const_u64<'ctx>(bv: &BV<'ctx>) -> Option<u64> {
    bv.as_u64()
}

fn is_zero_bv<'ctx>(bv: &BV<'ctx>) -> bool {
    bv_const_u64(bv) == Some(0)
}

// ---------------------------------------------------------------------------
// SpecTec numerics builtins (wasm-2.0/3-numerics.spectec, numerics.ml)
// ---------------------------------------------------------------------------

/// `maskN z = 2^z - 1` (`numerics.ml`).
fn mask_n_bv<'ctx>(ctx: &'ctx Context, z: u32) -> BV<'ctx> {
    let bits = z.min(I32_BITS);
    if bits == I32_BITS {
        BV::from_u64(ctx, u32::MAX as u64, I32_BITS)
    } else {
        BV::from_u64(ctx, (1u64 << bits) - 1, I32_BITS)
    }
}

/// `$truncz(rat)` — 0 方向切り捨て; see `truncz_rat`.
fn truncz_rat<'ctx>(_ctx: &'ctx Context, (n, d): (Int<'ctx>, Int<'ctx>)) -> BV<'ctx> {
    let q = n.div(&d);
    BV::from_int(&q, I32_BITS)
}

/// `\ 2^N` for Inn types: modulus `0` is the `2^32` sentinel (identity on u32 bits).
fn sym_mod_inn<'ctx>(ctx: &'ctx Context, x: BV<'ctx>, modulus: &BV<'ctx>, signed: bool) -> BV<'ctx> {
    let zero = BV::from_u64(ctx, 0, I32_BITS);
    let one = BV::from_u64(ctx, 1, I32_BITS);
    let is_mod_2p32 = modulus._eq(&zero);
    if signed {
        let m = modulus.bvsgt(&one).ite(modulus, &one);
        is_mod_2p32.ite(&x, &x.bvsrem(&m))
    } else {
        is_mod_2p32.ite(&x, &x.bvurem(&modulus.bvugt(&one).ite(modulus, &one)))
    }
}

/// `$iand_(N, m, n) = (m & n) & mask(N)`.
fn sym_iand_<'ctx>(ctx: &'ctx Context, z: u32, m: &BV<'ctx>, n: &BV<'ctx>) -> BV<'ctx> {
    m.bvand(n).bvand(&mask_n_bv(ctx, z))
}

/// `$ior_(N, m, n) = (m | n) & mask(N)`.
fn sym_ior_<'ctx>(ctx: &'ctx Context, z: u32, m: &BV<'ctx>, n: &BV<'ctx>) -> BV<'ctx> {
    m.bvor(n).bvand(&mask_n_bv(ctx, z))
}

/// `$ixor_(N, m, n) = (m xor n) & mask(N)`.
fn sym_ixor_<'ctx>(ctx: &'ctx Context, z: u32, m: &BV<'ctx>, n: &BV<'ctx>) -> BV<'ctx> {
    m.bvxor(n).bvand(&mask_n_bv(ctx, z))
}

/// `$ishl_(N, m, n) = (m << (n rem N)) & mask(N)` — amount `rem` is done in AL (`inn_ishl`).
fn sym_ishl_<'ctx>(ctx: &'ctx Context, z: u32, m: &BV<'ctx>, amount: &BV<'ctx>) -> BV<'ctx> {
    m.bvshl(amount).bvand(&mask_n_bv(ctx, z))
}

// ---------------------------------------------------------------------------
// Symbolic expression helpers
// ---------------------------------------------------------------------------

fn int_coerce<'ctx>(ctx: &'ctx Context, v: SymValue<'ctx>) -> Result<BV<'ctx>, EncodeError> {
    Ok(match v {
        SymValue::Int(bv) => bv,
        SymValue::Nat(bv) => bv,
        SymValue::Rat(n, d) => {
            let q = n.div(&d);
            BV::from_int(&q, I32_BITS)
        }
        other => panic!("int coerce on {other:?}"),
    })
}

fn nat_coerce<'ctx>(_ctx: &'ctx Context, v: SymValue<'ctx>) -> EncodeResult<'ctx> {
    Ok(match v {
        SymValue::Nat(bv) => SymValue::Nat(bv),
        SymValue::Int(bv) => SymValue::Nat(bv),
        SymValue::Rat(n, d) => {
            let q = n.div(&d);
            SymValue::Nat(BV::from_int(&q, I32_BITS))
        }
        other => panic!("nat coerce on {other:?}"),
    })
}

fn as_rat<'ctx>(ctx: &'ctx Context, v: SymValue<'ctx>) -> EncodeResult<'ctx> {
    Ok(match v {
        SymValue::Rat(n, d) => SymValue::Rat(n, d),
        SymValue::Nat(bv) => {
            let i = bv.to_int(false);
            SymValue::Rat(i, Int::from_i64(ctx, 1))
        }
        SymValue::Int(bv) => {
            let i = bv.to_int(true);
            SymValue::Rat(i, Int::from_i64(ctx, 1))
        }
        other => panic!("expected rat, got {other:?}"),
    })
}

fn as_rat_pair<'ctx>(v: SymValue<'ctx>) -> Result<(Int<'ctx>, Int<'ctx>), EncodeError> {
    match v {
        SymValue::Rat(n, d) => Ok((n, d)),
        other => panic!("expected rat, got {other:?}"),
    }
}

fn int_concrete<'ctx>(i: &Int<'ctx>) -> Option<i64> {
    i.as_i64().or_else(|| i.simplify().as_i64())
}

fn trunc_rat<'ctx>(ctx: &'ctx Context, (n, d): (Int<'ctx>, Int<'ctx>)) -> BV<'ctx> {
    truncz_rat(ctx, (n, d))
}

fn sym_add<'ctx>(
    ctx: &'ctx Context,
    a: SymValue<'ctx>,
    b: SymValue<'ctx>,
) -> EncodeResult<'ctx> {
    Ok(match (a, b) {
        (SymValue::Nat(x), SymValue::Nat(y)) => SymValue::Nat(x.bvadd(&y)),
        (SymValue::Int(x), SymValue::Int(y)) => SymValue::Int(x.bvadd(&y)),
        (SymValue::Rat(x, xd), SymValue::Rat(y, yd)) => SymValue::Rat(
            x.mul(&yd).add(&y.mul(&xd)),
            xd.mul(&yd),
        ),
        (SymValue::Int(x), SymValue::Nat(y)) => {
            let ybv = int_coerce(ctx, SymValue::Nat(y))?;
            SymValue::Nat(int_coerce(ctx, SymValue::Int(x))?.bvadd(&ybv))
        }
        _ => panic!("add on incompatible values"),
    })
}

fn sym_sub<'ctx>(
    ctx: &'ctx Context,
    a: SymValue<'ctx>,
    b: SymValue<'ctx>,
) -> EncodeResult<'ctx> {
    Ok(match (a, b) {
        (SymValue::Nat(x), SymValue::Nat(y)) => SymValue::Nat(x.bvsub(&y)),
        (SymValue::Int(x), SymValue::Int(y)) => SymValue::Int(x.bvsub(&y)),
        (SymValue::Rat(x, xd), SymValue::Rat(y, yd)) => SymValue::Rat(
            x.mul(&yd).sub(&y.mul(&xd)),
            xd.mul(&yd),
        ),
        (SymValue::Int(x), SymValue::Nat(y)) => SymValue::Int(x.bvsub(&int_coerce(ctx, SymValue::Nat(y))?)),
        (SymValue::Nat(x), SymValue::Int(y)) => {
            SymValue::Int(int_coerce(ctx, SymValue::Nat(x))?.bvsub(&y))
        }
        _ => panic!("sub on incompatible values"),
    })
}

fn sym_mul<'ctx>(
    _ctx: &'ctx Context,
    a: SymValue<'ctx>,
    b: SymValue<'ctx>,
) -> EncodeResult<'ctx> {
    Ok(match (a, b) {
        (SymValue::Nat(x), SymValue::Nat(y)) => SymValue::Nat(x.bvmul(&y)),
        (SymValue::Int(x), SymValue::Int(y)) => SymValue::Int(x.bvmul(&y)),
        (SymValue::Rat(x, xd), SymValue::Rat(y, yd)) => {
            SymValue::Rat(x.mul(&y), xd.mul(&yd))
        }
        _ => panic!("mul on incompatible values"),
    })
}

fn sym_div<'ctx>(
    _ctx: &'ctx Context,
    a: SymValue<'ctx>,
    b: SymValue<'ctx>,
) -> EncodeResult<'ctx> {
    match (a, b) {
        (SymValue::Rat(x, xd), SymValue::Rat(y, yd)) => Ok(SymValue::Rat(x.mul(&yd), xd.mul(&y))),
        _ => panic!("div on incompatible values"),
    }
}

fn sym_mod<'ctx>(
    ctx: &'ctx Context,
    a: SymValue<'ctx>,
    b: SymValue<'ctx>,
) -> EncodeResult<'ctx> {
    Ok(match (a, b) {
        (SymValue::Nat(x), SymValue::Nat(y)) => {
            if let (Some(xu), Some(yu)) = (bv_const_u64(&x), bv_const_u64(&y)) {
                if yu == 0 {
                    SymValue::Nat(x)
                } else {
                    SymValue::Nat(BV::from_u64(ctx, xu % yu, I32_BITS))
                }
            } else {
                SymValue::Nat(sym_mod_inn(ctx, x, &y, false))
            }
        }
        (SymValue::Int(x), SymValue::Int(y)) => SymValue::Int(sym_mod_inn(ctx, x, &y, true)),
        _ => panic!("mod on incompatible values"),
    })
}

fn sym_rem<'ctx>(
    ctx: &'ctx Context,
    a: SymValue<'ctx>,
    b: SymValue<'ctx>,
) -> EncodeResult<'ctx> {
    let x = as_nat_bv(ctx, a)?;
    let y = as_nat_bv(ctx, b)?;
    let one = BV::from_u64(ctx, 1, I32_BITS);
    Ok(SymValue::Nat(x.bvurem(&y.bvugt(&one).ite(&y, &one))))
}

fn sym_shl<'ctx>(
    ctx: &'ctx Context,
    a: SymValue<'ctx>,
    b: SymValue<'ctx>,
) -> EncodeResult<'ctx> {
    let x = as_nat_bv(ctx, a)?;
    let y = as_nat_bv(ctx, b)?;
    Ok(SymValue::Nat(sym_ishl_(ctx, I32_BITS, &x, &y)))
}

fn sym_bitand<'ctx>(
    ctx: &'ctx Context,
    a: SymValue<'ctx>,
    b: SymValue<'ctx>,
) -> EncodeResult<'ctx> {
    let x = as_nat_bv(ctx, a)?;
    let y = as_nat_bv(ctx, b)?;
    Ok(SymValue::Nat(sym_iand_(ctx, I32_BITS, &x, &y)))
}

fn sym_bitor<'ctx>(
    ctx: &'ctx Context,
    a: SymValue<'ctx>,
    b: SymValue<'ctx>,
) -> EncodeResult<'ctx> {
    let x = as_nat_bv(ctx, a)?;
    let y = as_nat_bv(ctx, b)?;
    Ok(SymValue::Nat(sym_ior_(ctx, I32_BITS, &x, &y)))
}

fn sym_bitxor<'ctx>(
    ctx: &'ctx Context,
    a: SymValue<'ctx>,
    b: SymValue<'ctx>,
) -> EncodeResult<'ctx> {
    let x = as_nat_bv(ctx, a)?;
    let y = as_nat_bv(ctx, b)?;
    Ok(SymValue::Nat(sym_ixor_(ctx, I32_BITS, &x, &y)))
}

fn sym_pow<'ctx>(
    ctx: &'ctx Context,
    a: SymValue<'ctx>,
    b: SymValue<'ctx>,
) -> EncodeResult<'ctx> {
    let base = as_nat_u32_concrete(&a)?;
    let exp = as_nat_u32_concrete(&b)?;
    let result = match (base, exp) {
        (2, e) if e >= 32 => 0,
        (2, e) => 1u32.checked_shl(e).unwrap_or(0),
        _ => panic!("unsupported pow({base}, {exp})"),
    };
    Ok(SymValue::nat_const(ctx, result))
}

fn as_nat_bv<'ctx>(_ctx: &'ctx Context, v: SymValue<'ctx>) -> Result<BV<'ctx>, EncodeError> {
    Ok(match v {
        SymValue::Nat(bv) => bv,
        SymValue::Int(bv) => bv,
        other => panic!("expected nat bv, got {other:?}"),
    })
}

fn as_nat_u32<'ctx>(v: &SymValue<'ctx>) -> Result<u32, EncodeError> {
    match v {
        SymValue::Nat(bv) => Ok(bv_concrete_u32(bv).unwrap_or(0)),
        _ => panic!("expected nat, got {v:?}"),
    }
}

fn as_nat_u32_concrete<'ctx>(v: &SymValue<'ctx>) -> Result<u32, EncodeError> {
    as_nat_u32(v)
}

fn bind_sym_fn_args<'ctx>(
    def: &AlMetaFnDef,
    bound: Vec<SymValue<'ctx>>,
) -> Result<Vec<(&'static str, SymValue<'ctx>)>, EncodeError> {
    assert_eq!(
        def.params.len(),
        bound.len(),
        "arg count mismatch for ${}",
        def.name
    );
    def.params
        .iter()
        .zip(bound)
        .map(|(param, val)| Ok((param.name, coerce_sym(param.ty, val)?)))
        .collect::<Result<Vec<_>, _>>()
}

fn coerce_sym<'ctx>(ty: AlMetaParamType, val: SymValue<'ctx>) -> EncodeResult<'ctx> {
    Ok(match ty {
        AlMetaParamType::Nat | AlMetaParamType::Int | AlMetaParamType::Any => val,
        AlMetaParamType::ValType => SymValue::ValType(as_valtype(val)?),
        AlMetaParamType::NumType => SymValue::NumType(as_numtype(val)?),
        AlMetaParamType::Sign => SymValue::Sign(as_sign(val)?),
        AlMetaParamType::BinOp => SymValue::BinOp(as_binop(val)?),
    })
}

fn as_valtype(v: SymValue<'_>) -> Result<ValType, EncodeError> {
    match v {
        SymValue::ValType(vt) => Ok(vt),
        SymValue::NumType(NumType::I32) => Ok(ValType::I32),
        other => panic!("expected valtype, got {other:?}"),
    }
}

fn as_numtype(v: SymValue<'_>) -> Result<NumType, EncodeError> {
    match v {
        SymValue::NumType(nt) => Ok(nt),
        other => panic!("expected numtype, got {other:?}"),
    }
}

fn as_sign(v: SymValue<'_>) -> Result<Sign, EncodeError> {
    match v {
        SymValue::Sign(sx) => Ok(sx),
        other => panic!("expected sign, got {other:?}"),
    }
}

fn as_binop(v: SymValue<'_>) -> Result<WasmBinOp, EncodeError> {
    match v {
        SymValue::BinOp(op) => Ok(op),
        other => panic!("expected binop, got {other:?}"),
    }
}

fn binop_case(op: WasmBinOp, case: BinOpCase) -> bool {
    matches!(
        (op, case),
        (WasmBinOp::Div(_), BinOpCase::Div) | (WasmBinOp::Rem(_), BinOpCase::Rem)
    )
}

fn binop_sign(v: SymValue<'_>, case: BinOpCase) -> Result<Sign, EncodeError> {
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

// ---------------------------------------------------------------------------
// Concretization (tests): evaluate encoded result with constant inputs
// ---------------------------------------------------------------------------

pub fn encode_binop_stack<'ctx>(
    ctx: &'ctx Context,
    nt: NumType,
    binop: WasmBinOp,
    i_1: BV<'ctx>,
    i_2: BV<'ctx>,
) -> Result<SymValue<'ctx>, EncodeError> {
    use super::al_defs::binop_def;
    encode_fn(
        ctx,
        &binop_def(),
        &[
            ("numtype", SymValue::NumType(nt)),
            ("binop_", SymValue::BinOp(binop)),
            ("iN_1", SymValue::nat_from_stack(i_1)),
            ("iN_2", SymValue::nat_from_stack(i_2)),
        ],
    )
}

fn bv_concrete_u32<'ctx>(bv: &BV<'ctx>) -> Option<u32> {
    bv.as_u64()
        .map(|n| n as u32)
        .or_else(|| bv.simplify().as_u64().map(|n| n as u32))
}

fn concretize_binop_list<'ctx>(v: SymValue<'ctx>) -> Result<Option<u32>, EncodeError> {
    match v {
        SymValue::List(items) if items.is_empty() => Ok(None),
        SymValue::List(items) => match items.as_slice() {
            [SymValue::Nat(bv)] => Ok(Some(bv_concrete_u32(&bv).unwrap_or(0) as u32)),
            other => panic!("binop_ singleton list expected Nat, got {other:?}"),
        },
        SymValue::Opt(None) => Ok(None),
        SymValue::Opt(Some(inner)) => match *inner {
            SymValue::Nat(bv) => Ok(Some(bv_concrete_u32(&bv).unwrap_or(0) as u32)),
            other => panic!("binop_ optional expected Nat, got {other:?}"),
        },
        SymValue::Partial { empty, value } => {
            if empty.as_bool() != Some(false) {
                return Ok(None);
            }
            match *value {
                SymValue::Nat(bv) => Ok(Some(bv_concrete_u32(&bv).unwrap_or(0) as u32)),
                other => panic!("binop_ partial expected Nat, got {other:?}"),
            }
        }
        other => panic!("binop_ returned unexpected {other:?}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::semantics::al::eval::eval_binop_;
    use crate::semantics::al::ir::{NumType, Sign, WasmBinOp};
    use crate::semantics::z3_context;

    fn encode_binop_concrete(
        ctx: &z3::Context,
        nt: NumType,
        binop: WasmBinOp,
        i_1: u32,
        i_2: u32,
    ) -> Result<Option<u32>, EncodeError> {
        concretize_binop_list(encode_binop_stack(
            ctx,
            nt,
            binop,
            BV::from_u64(ctx, i_1 as u64, I32_BITS),
            BV::from_u64(ctx, i_2 as u64, I32_BITS),
        )?)
    }

    #[test]
    fn encode_binop_matches_eval_add() {
        let ctx = z3_context();
        assert_eq!(
            encode_binop_concrete(&ctx, NumType::I32, WasmBinOp::Add, 3, 5).unwrap(),
            eval_binop_(NumType::I32, WasmBinOp::Add, 3, 5)
        );
    }

    #[test]
    fn encode_binop_matches_eval_div_s_trap() {
        let ctx = z3_context();
        assert_eq!(
            encode_binop_concrete(&ctx, NumType::I32, WasmBinOp::Div(Sign::S), 0, 0).unwrap(),
            None
        );
        assert_eq!(
            encode_binop_concrete(
                &ctx,
                NumType::I32,
                WasmBinOp::Div(Sign::S),
                i32::MIN as u32,
                (-1i32) as u32,
            )
            .unwrap(),
            None
        );
    }

    #[test]
    fn encode_binop_matches_eval_div_s_defined() {
        let ctx = z3_context();
        assert_eq!(
            encode_binop_concrete(&ctx, NumType::I32, WasmBinOp::Div(Sign::S), 8, 2).unwrap(),
            eval_binop_(NumType::I32, WasmBinOp::Div(Sign::S), 8, 2)
        );
    }

    #[test]
    fn encode_binop_div_u_max_u32_by_one() {
        let ctx = z3_context();
        assert_eq!(
            encode_binop_concrete(&ctx, NumType::I32, WasmBinOp::Div(Sign::U), u32::MAX, 1)
                .unwrap(),
            eval_binop_(NumType::I32, WasmBinOp::Div(Sign::U), u32::MAX, 1)
        );
    }

    #[test]
    fn encode_binop_and_matches_eval_with_high_bits() {
        let ctx = z3_context();
        assert_eq!(
            encode_binop_concrete(&ctx, NumType::I32, WasmBinOp::And, u32::MAX, u32::MAX).unwrap(),
            eval_binop_(NumType::I32, WasmBinOp::And, u32::MAX, u32::MAX)
        );
    }
}
