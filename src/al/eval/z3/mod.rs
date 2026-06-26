//! Z3 AL interpreter — same AL AST as [`super::concrete`].

mod context;
mod value_ast;

pub use context::z3_context;
pub use value_ast::{asts_valid_rewrite_z3, eval_value_ast_z3};

use super::env::Env;
use super::error::EvalError;
use super::value::AlValue;
use crate::al::ast::{
    Arg, BinOpCase, Expr, FuncA, Instr, InstrCond, LetLhs, NumType, Pred, RelOpCase, Sign,
    UnOpCase, WasmBinOp, WasmRelOp, WasmTestOp, WasmUnOp,
};
use crate::al::defs::lookup_func;
use crate::al::I32_BITS;
use crate::value::{RuleSignature, StackTy};
use z3::ast::{Ast, BV, Bool, Int};
use z3::Context;

const I32_WIDTH: u32 = I32_BITS;

fn nat_width<'ctx>(v: &SymValue<'ctx>) -> Option<u32> {
    match v {
        SymValue::Meta(AlValue::Nat(n)) => Some(*n as u32),
        _ => None,
    }
}

/// Symbolic AL value during Z3 evaluation.
#[derive(Clone)]
pub enum SymValue<'ctx> {
    Bv(BV<'ctx>),
    Int(Int<'ctx>),
    Bool(Bool<'ctx>),
    Opt(Option<Box<SymValue<'ctx>>>),
    List(Vec<SymValue<'ctx>>),
    Meta(AlValue),
}

impl<'ctx> SymValue<'ctx> {
    fn list_len(&self) -> usize {
        match self {
            Self::List(v) => v.len(),
            Self::Opt(None) => 0,
            Self::Opt(Some(_)) => 1,
            _ => 0,
        }
    }

    fn is_empty_list_or_opt(&self) -> bool {
        self.list_len() == 0
    }

    fn choose_singleton(self) -> Option<SymValue<'ctx>> {
        match self {
            Self::List(mut v) if v.len() == 1 => Some(v.remove(0)),
            Self::Opt(Some(v)) => Some(*v),
            _ => None,
        }
    }
}

pub struct SymEval<'ctx> {
    ctx: &'ctx Context,
    sig: RuleSignature,
}

impl<'ctx> SymEval<'ctx> {
    pub fn new(ctx: &'ctx Context, sig: RuleSignature) -> Self {
        Self { ctx, sig }
    }

    fn bitwidth_of(&self, ty: StackTy) -> u32 {
        ty.bit_width()
    }

    fn al_num_type(&self, ty: StackTy) -> NumType {
        ty.al_num_type()
    }

    pub fn call_func(
        &self,
        name: &str,
        args: Vec<SymValue<'ctx>>,
    ) -> Result<SymValue<'ctx>, EvalError> {
        if let Some(v) = self.eval_builtin(name, &args) {
            return Ok(v);
        }
        let func = lookup_func(name).ok_or_else(|| EvalError::UnknownFunc(name.to_string()))?;
        let mut env = SymEnv::new();
        for (param, arg) in func.params.iter().zip(args) {
            env.bind(param.name, arg);
        }
        self.eval_func_body(&func, &mut env)
    }

    fn eval_builtin(&self, name: &str, args: &[SymValue<'ctx>]) -> Option<SymValue<'ctx>> {
        match name {
            "truncz" => {
                let i = match args.first()? {
                    SymValue::Int(x) => x,
                    SymValue::Bv(b) => return Some(SymValue::Int(b.to_int(true))),
                    _ => return None,
                };
                Some(SymValue::Int(i.clone()))
            }
            "iclz_" => {
                let n = nat_width(args.get(0)?)?;
                let v = match args.get(1)? {
                    SymValue::Bv(b) => b.clone(),
                    _ => return None,
                };
                Some(SymValue::Bv(self.inn_clz(n, &v)))
            }
            "ictz_" => {
                let n = nat_width(args.get(0)?)?;
                let v = match args.get(1)? {
                    SymValue::Bv(b) => b.clone(),
                    _ => return None,
                };
                Some(SymValue::Bv(self.inn_ctz(n, &v)))
            }
            "ipopcnt_" => {
                let n = nat_width(args.get(0)?)?;
                let v = match args.get(1)? {
                    SymValue::Bv(b) => b.clone(),
                    _ => return None,
                };
                Some(SymValue::Bv(self.inn_popcnt(n, &v)))
            }
            _ => None,
        }
    }

    fn default_width(&self) -> u32 {
        let mut w = self.sig.output.bit_width();
        for &ty in &self.sig.inputs {
            w = w.max(ty.bit_width());
        }
        w
    }

    fn inn_clz(&self, width: u32, v: &BV<'ctx>) -> BV<'ctx> {
        let bw = width;
        let mut out = BV::from_u64(self.ctx, width as u64, bw);
        for i in (0..width).rev() {
            let bit = v.extract(i, i)._eq(&BV::from_u64(self.ctx, 1, 1));
            let val = BV::from_u64(self.ctx, (width - 1 - i) as u64, bw);
            out = bit.ite(&val, &out);
        }
        out
    }

    fn inn_ctz(&self, width: u32, v: &BV<'ctx>) -> BV<'ctx> {
        let bw = width;
        let mut out = BV::from_u64(self.ctx, width as u64, bw);
        for i in 0..width {
            let bit = v.extract(i, i)._eq(&BV::from_u64(self.ctx, 1, 1));
            let val = BV::from_u64(self.ctx, i as u64, bw);
            out = bit.ite(&val, &out);
        }
        out
    }

    fn inn_popcnt(&self, width: u32, v: &BV<'ctx>) -> BV<'ctx> {
        let bw = self.default_width();
        let mut sum = BV::from_u64(self.ctx, 0, bw);
        for i in 0..width {
            let bit = v.extract(i, i)._eq(&BV::from_u64(self.ctx, 1, 1));
            let one = bit.ite(
                &BV::from_u64(self.ctx, 1, bw),
                &BV::from_u64(self.ctx, 0, bw),
            );
            sum = sum.bvadd(&one);
        }
        sum
    }

    #[allow(dead_code)]
    fn i32_clz(&self, v: &BV<'ctx>) -> BV<'ctx> {
        self.inn_clz(32, v)
    }

    #[allow(dead_code)]
    fn i32_ctz(&self, v: &BV<'ctx>) -> BV<'ctx> {
        self.inn_ctz(32, v)
    }

    #[allow(dead_code)]
    fn i32_popcnt(&self, v: &BV<'ctx>) -> BV<'ctx> {
        self.inn_popcnt(32, v)
    }

    fn eval_func_body(
        &self,
        func: &FuncA,
        env: &mut SymEnv<'ctx>,
    ) -> Result<SymValue<'ctx>, EvalError> {
        self.eval_instrs(&func.body, env)
    }

    fn eval_instrs(
        &self,
        instrs: &[Instr],
        env: &mut SymEnv<'ctx>,
    ) -> Result<SymValue<'ctx>, EvalError> {
        let mut pc = 0usize;
        while pc < instrs.len() {
            match self.eval_instr(&instrs[pc], env)? {
                InstrOutcome::Continue => pc += 1,
                InstrOutcome::Return(v) => return Ok(v),
                InstrOutcome::Fail => return Err(EvalError::Fail),
            }
        }
        Err(EvalError::Fail)
    }

    fn eval_instr(
        &self,
        instr: &Instr,
        env: &mut SymEnv<'ctx>,
    ) -> Result<InstrOutcome<'ctx>, EvalError> {
        match instr {
            Instr::IfI {
                cond,
                then_steps,
                else_steps,
            } => {
                let take_then = self.eval_cond(cond, env)?;
                let branch = if take_then {
                    then_steps.as_slice()
                } else {
                    else_steps.as_slice()
                };
                if branch.is_empty() {
                    return Ok(InstrOutcome::Continue);
                }
                self.eval_instrs(branch, env).map(InstrOutcome::Return)
            }
            Instr::AssertI(cond) => {
                if !self.eval_cond(cond, env)? {
                    return Err(EvalError::AssertFailed);
                }
                Ok(InstrOutcome::Continue)
            }
            Instr::LetI { lhs, expr } => {
                let v = self.eval_expr(expr, env)?;
                self.bind_lhs(lhs, v, env)?;
                Ok(InstrOutcome::Continue)
            }
            Instr::ReturnI(expr) => Ok(InstrOutcome::Return(self.eval_expr(expr, env)?)),
            Instr::FailI => Ok(InstrOutcome::Fail),
            _ => Err(EvalError::Unimplemented("stack machine instr")),
        }
    }

    fn bind_lhs(
        &self,
        lhs: &LetLhs,
        value: SymValue<'ctx>,
        env: &mut SymEnv<'ctx>,
    ) -> Result<(), EvalError> {
        match lhs {
            LetLhs::Var(name) => {
                env.bind(name, value);
                Ok(())
            }
            LetLhs::BinOpCase(case, name) => {
                let binop = match value {
                    SymValue::Meta(AlValue::BinOp(b)) => b,
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
                env.bind(name, SymValue::Meta(AlValue::Sign(sx)));
                Ok(())
            }
            LetLhs::RelOpCase(case, name) => {
                let relop = match value {
                    SymValue::Meta(AlValue::RelOp(r)) => r,
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
                env.bind(name, SymValue::Meta(AlValue::Sign(sx)));
                Ok(())
            }
            LetLhs::UnOpCase(UnOpCase::Extend, name) => {
                env.bind(name, SymValue::Meta(AlValue::Nat(0)));
                Ok(())
            }
        }
    }

    fn eval_cond(&self, cond: &InstrCond, env: &mut SymEnv<'ctx>) -> Result<bool, EvalError> {
        match cond {
            InstrCond::Expr(expr) => {
                let mut cenv = Env::new();
                let v = super::concrete::eval_expr(expr, &mut cenv)?;
                match v {
                    AlValue::Bool(b) => Ok(b),
                    AlValue::Nat(0) => Ok(false),
                    AlValue::Nat(_) => Ok(true),
                    _ => Err(EvalError::TypeMismatch("bool cond expr")),
                }
            }
            InstrCond::Pred(pred) => self.eval_pred(pred, env),
        }
    }

    fn eval_pred(&self, pred: &Pred, env: &mut SymEnv<'ctx>) -> Result<bool, EvalError> {
        match pred {
            Pred::Eq(a, b) => Ok(self.values_equal(
                &self.eval_expr(a, env)?,
                &self.eval_expr(b, env)?,
            )),
            Pred::Lt(_, _)
            | Pred::Le(_, _)
            | Pred::Gt(_, _)
            | Pred::Ge(_, _)
            | Pred::Ne(_, _) => {
                let mut cenv = Env::new();
                Ok(super::concrete::eval_pred(pred, &mut cenv)?)
            }
            Pred::And(a, b) => Ok(self.eval_pred(a, env)? && self.eval_pred(b, env)?),
            Pred::OptIsNone(expr) => Ok(self.eval_expr(expr, env)?.is_empty_list_or_opt()),
            Pred::TypeIsInn(expr) => Ok(matches!(
                self.eval_expr(expr, env)?,
                SymValue::Meta(AlValue::NumType(nt)) if nt.is_inn()
            )),
            Pred::TypeIsFnn(expr) => Ok(matches!(
                self.eval_expr(expr, env)?,
                SymValue::Meta(AlValue::NumType(nt)) if nt.is_fnn()
            )),
            Pred::NumTypeEq(expr, expected) => Ok(matches!(
                self.eval_expr(expr, env)?,
                SymValue::Meta(AlValue::NumType(nt)) if nt == *expected
            )),
            Pred::BinOpEq(expr, expected) => Ok(matches!(
                self.eval_expr(expr, env)?,
                SymValue::Meta(AlValue::BinOp(b)) if b == *expected
            )),
            Pred::BinOpCaseIs(expr, case) => {
                let b = match self.eval_expr(expr, env)? {
                    SymValue::Meta(AlValue::BinOp(b)) => b,
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
                self.eval_expr(expr, env)?,
                SymValue::Meta(AlValue::RelOp(r)) if r == *expected
            )),
            Pred::RelOpCaseIs(expr, case) => {
                let r = match self.eval_expr(expr, env)? {
                    SymValue::Meta(AlValue::RelOp(r)) => r,
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
                self.eval_expr(expr, env)?,
                SymValue::Meta(AlValue::TestOp(t)) if t == *expected
            )),
            Pred::UnOpEq(expr, expected) => Ok(matches!(
                self.eval_expr(expr, env)?,
                SymValue::Meta(AlValue::UnOp(u)) if u == *expected
            )),
            Pred::UnOpCaseIs(expr, case) => {
                let u = match self.eval_expr(expr, env)? {
                    SymValue::Meta(AlValue::UnOp(u)) => u,
                    _ => return Err(EvalError::TypeMismatch("expected unop")),
                };
                Ok(matches!((case, u), (UnOpCase::Extend, WasmUnOp::Extend)))
            }
        }
    }

    fn values_equal(&self, a: &SymValue<'ctx>, b: &SymValue<'ctx>) -> bool {
        match (a, b) {
            (SymValue::Meta(x), SymValue::Meta(y)) => x == y,
            (SymValue::Bv(x), SymValue::Bv(y)) => x
                .simplify()
                ._eq(&y.simplify())
                .as_bool()
                .unwrap_or(false),
            _ => false,
        }
    }

    fn eval_expr(
        &self,
        expr: &Expr,
        env: &mut SymEnv<'ctx>,
    ) -> Result<SymValue<'ctx>, EvalError> {
        match expr {
            Expr::VarE(name) => env
                .get(name)
                .cloned()
                .ok_or(EvalError::UnknownVar(name)),
            Expr::NatLit(n) => Ok(SymValue::Bv(BV::from_u64(
                self.ctx,
                *n as u64,
                self.default_width(),
            ))),
            Expr::IntLit(n) => Ok(SymValue::Int(Int::from_i64(self.ctx, *n as i64))),
            Expr::BoolLit(b) => Ok(SymValue::Bool(Bool::from_bool(self.ctx, *b))),
            Expr::ValTypeLit(vt) => Ok(SymValue::Meta(AlValue::ValType(*vt))),
            Expr::SignLit(s) => Ok(SymValue::Meta(AlValue::Sign(*s))),
            Expr::BinOpLit(b) => Ok(SymValue::Meta(AlValue::BinOp(*b))),
            Expr::RelOpLit(r) => Ok(SymValue::Meta(AlValue::RelOp(*r))),
            Expr::TestOpLit(t) => Ok(SymValue::Meta(AlValue::TestOp(*t))),
            Expr::UnOpLit(u) => Ok(SymValue::Meta(AlValue::UnOp(*u))),
            Expr::EmptyOpt => Ok(SymValue::Opt(None)),
            Expr::SomeOpt(v) => Ok(SymValue::Opt(Some(Box::new(self.eval_expr(v, env)?)))),
            Expr::EmptyList => Ok(SymValue::List(vec![])),
            Expr::SingletonList(v) => Ok(SymValue::List(vec![self.eval_expr(v, env)?])),
            Expr::OptionalLen(v) => {
                let len = self.eval_expr(v, env)?.list_len();
                Ok(SymValue::Bv(BV::from_u64(self.ctx, len as u64, self.default_width())))
            }
            Expr::Choose(v) => self
                .eval_expr(v, env)?
                .choose_singleton()
                .ok_or(EvalError::TypeMismatch("choose")),
            Expr::IntCoerce(v) => {
                let bv = self.bv_of(&self.eval_expr(v, env)?)?;
                Ok(SymValue::Int(bv.to_int(true)))
            }
            Expr::NatCoerce(v) => Ok(SymValue::Bv(self.bv_of(&self.eval_expr(v, env)?)?)),
            Expr::RatCoerce(v) => {
                let i = match self.eval_expr(v, env)? {
                    SymValue::Int(x) => x,
                    SymValue::Bv(b) => b.to_int(true),
                    _ => return Err(EvalError::TypeMismatch("rat coerce")),
                };
                Ok(SymValue::Int(i))
            }
            Expr::TruncZ(v) => {
                let i = match self.eval_expr(v, env)? {
                    SymValue::Int(x) => x,
                    _ => return Err(EvalError::TypeMismatch("truncz")),
                };
                Ok(SymValue::Int(i))
            }
            Expr::Call(name, args) => {
                let evaluated: Result<Vec<SymValue<'ctx>>, EvalError> =
                    args.iter().map(|a| self.eval_arg(a, env)).collect();
                self.call_func(name, evaluated?)
            }
            Expr::Eq(a, b) => self.cmp_bv_bool(a, b, env, |x, y| x._eq(&y)),
            Expr::Ne(a, b) => self.cmp_bv_bool(a, b, env, |x, y| x._eq(&y).not()),
            Expr::LtCmp(a, b) => self.cmp_bv_bool(a, b, env, |x, y| x.bvult(&y)),
            Expr::LeCmp(a, b) => self.cmp_bv_bool(a, b, env, |x, y| x.bvule(&y)),
            Expr::GtCmp(a, b) => self.cmp_bv_bool(a, b, env, |x, y| x.bvugt(&y)),
            Expr::GeCmp(a, b) => self.cmp_bv_bool(a, b, env, |x, y| x.bvuge(&y)),
            Expr::Add(a, b) => self.bv_binop(a, b, env, |x, y| x.bvadd(&y)),
            Expr::Sub(a, b) => self.bv_binop(a, b, env, |x, y| x.bvsub(&y)),
            Expr::Mul(a, b) => self.bv_binop(a, b, env, |x, y| x.bvmul(&y)),
            Expr::Div(a, b) => {
                let ai = self.int_of_expr(a, env)?;
                let bi = self.int_of_expr(b, env)?;
                Ok(SymValue::Int(ai.div(&bi)))
            }
            Expr::Mod(a, b) | Expr::Rem(a, b) => self.bv_binop(a, b, env, |x, y| x.bvurem(&y)),
            Expr::Pow(a, b) => {
                let base = self.nat_u64(&self.eval_expr(a, env)?)?;
                let exp = self.nat_u64(&self.eval_expr(b, env)?)?;
                Ok(SymValue::Bv(BV::from_u64(
                    self.ctx,
                    base.saturating_pow(exp as u32),
                    self.default_width(),
                )))
            }
            Expr::Shl(a, b) => self.bv_binop(a, b, env, |x, y| x.bvshl(&y)),
            Expr::BitAnd(a, b) => self.bv_binop(a, b, env, |x, y| x.bvand(&y)),
            Expr::BitOr(a, b) => self.bv_binop(a, b, env, |x, y| x.bvor(&y)),
            Expr::BitXor(a, b) => self.bv_binop(a, b, env, |x, y| x.bvxor(&y)),
            Expr::LShr(a, b) => self.bv_binop(a, b, env, |x, y| x.bvlshr(&y)),
            Expr::AShr(a, b) => self.bv_binop(a, b, env, |x, y| x.bvashr(&y)),
            Expr::Rotl(a, b) => {
                let mask = self.default_width() - 1;
                self.bv_binop(a, b, env, |x, y| {
                    x.bvrotl(&y.bvand(&BV::from_u64(self.ctx, mask as u64, self.default_width())))
                })
            }
            Expr::Rotr(a, b) => {
                let mask = self.default_width() - 1;
                self.bv_binop(a, b, env, |x, y| {
                    x.bvrotr(&y.bvand(&BV::from_u64(self.ctx, mask as u64, self.default_width())))
                })
            }
            Expr::Neg(_) => Err(EvalError::Unimplemented("Neg")),
            Expr::BinOpSignOf(_)
            | Expr::TopValue(_)
            | Expr::TopValueAny
            | Expr::CaseE(_, _)
            | Expr::AccE(_, _) => Err(EvalError::Unimplemented("sym expr")),
        }
    }

    fn eval_arg(&self, arg: &Arg, env: &mut SymEnv<'ctx>) -> Result<SymValue<'ctx>, EvalError> {
        match arg {
            Arg::NumType(nt) => Ok(SymValue::Meta(AlValue::NumType(*nt))),
            Arg::ValType(vt) => Ok(SymValue::Meta(AlValue::ValType(*vt))),
            Arg::BinOp(b) => Ok(SymValue::Meta(AlValue::BinOp(*b))),
            Arg::RelOp(r) => Ok(SymValue::Meta(AlValue::RelOp(*r))),
            Arg::TestOp(t) => Ok(SymValue::Meta(AlValue::TestOp(*t))),
            Arg::UnOp(u) => Ok(SymValue::Meta(AlValue::UnOp(*u))),
            Arg::Var(name) => env
                .get(name)
                .cloned()
                .ok_or(EvalError::UnknownVar(name)),
            Arg::Nat(n) => Ok(SymValue::Bv(BV::from_u64(self.ctx, *n as u64, self.default_width()))),
            Arg::Sign(s) => Ok(SymValue::Meta(AlValue::Sign(*s))),
            Arg::ExpA(expr) => self.eval_expr(expr, env),
        }
    }

    fn bv_of(&self, v: &SymValue<'ctx>) -> Result<BV<'ctx>, EvalError> {
        match v {
            SymValue::Bv(b) => Ok(b.clone()),
            SymValue::Meta(AlValue::Nat(n)) => Ok(BV::from_u64(self.ctx, *n, self.default_width())),
            _ => Err(EvalError::TypeMismatch("expected bv")),
        }
    }

    fn nat_u64(&self, v: &SymValue<'ctx>) -> Result<u64, EvalError> {
        match v {
            SymValue::Meta(AlValue::Nat(n)) => Ok(*n),
            SymValue::Bv(b) => b
                .as_u64()
                .ok_or(EvalError::TypeMismatch("pow needs concrete nat")),
            _ => Err(EvalError::TypeMismatch("expected nat")),
        }
    }

    fn int_of_expr(
        &self,
        expr: &Expr,
        env: &mut SymEnv<'ctx>,
    ) -> Result<Int<'ctx>, EvalError> {
        match self.eval_expr(expr, env)? {
            SymValue::Int(i) => Ok(i),
            SymValue::Bv(b) => Ok(b.to_int(true)),
            _ => Err(EvalError::TypeMismatch("expected int")),
        }
    }

    fn align_bv_pair(&self, a: BV<'ctx>, b: BV<'ctx>) -> (BV<'ctx>, BV<'ctx>) {
        let w = a.get_size().max(b.get_size());
        (
            self.coerce_bv_width(a, w),
            self.coerce_bv_width(b, w),
        )
    }

    fn coerce_bv_width(&self, v: BV<'ctx>, w: u32) -> BV<'ctx> {
        let cur = v.get_size();
        if cur > w {
            v.extract(w - 1, 0)
        } else if cur < w {
            v.zero_ext(w - cur)
        } else {
            v
        }
    }

    fn bv_binop<F>(
        &self,
        a: &Expr,
        b: &Expr,
        env: &mut SymEnv<'ctx>,
        f: F,
    ) -> Result<SymValue<'ctx>, EvalError>
    where
        F: FnOnce(BV<'ctx>, BV<'ctx>) -> BV<'ctx>,
    {
        let av = self.bv_of(&self.eval_expr(a, env)?)?;
        let bv = self.bv_of(&self.eval_expr(b, env)?)?;
        let (av, bv) = self.align_bv_pair(av, bv);
        Ok(SymValue::Bv(f(av, bv)))
    }

    fn cmp_bv_bool<F>(
        &self,
        a: &Expr,
        b: &Expr,
        env: &mut SymEnv<'ctx>,
        f: F,
    ) -> Result<SymValue<'ctx>, EvalError>
    where
        F: FnOnce(BV<'ctx>, BV<'ctx>) -> Bool<'ctx>,
    {
        let av = self.bv_of(&self.eval_expr(a, env)?)?;
        let bv = self.bv_of(&self.eval_expr(b, env)?)?;
        let (av, bv) = self.align_bv_pair(av, bv);
        Ok(SymValue::Bool(f(av, bv)))
    }
}

enum InstrOutcome<'ctx> {
    Continue,
    Return(SymValue<'ctx>),
    Fail,
}

struct SymEnv<'ctx> {
    bindings: std::collections::HashMap<String, SymValue<'ctx>>,
}

impl<'ctx> SymEnv<'ctx> {
    fn new() -> Self {
        Self {
            bindings: std::collections::HashMap::new(),
        }
    }

    fn bind(&mut self, name: &str, value: SymValue<'ctx>) {
        self.bindings.insert(name.to_string(), value);
    }

    fn get(&self, name: &str) -> Option<&SymValue<'ctx>> {
        self.bindings.get(name)
    }
}
