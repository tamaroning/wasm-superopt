//! Z3 AL interpreter — same AL AST as [`super::concrete`].

mod context;

pub use context::z3_context;

use super::env::Env;
use super::error::EvalError;
use super::value::AlValue;
use crate::al::ast::{
    Arg, BinOpCase, Expr, FuncA, Instr, InstrCond, LetLhs, NumType, Pred, RelOpCase, Sign,
    UnOpCase, WasmBinOp, WasmRelOp, WasmTestOp, WasmUnOp,
};
use crate::al::defs::lookup_func;
use crate::al::I32_BITS;
use crate::value::ValueAst;
use z3::ast::{Ast, BV, Bool, Int};
use z3::Context;

const I32_WIDTH: u32 = I32_BITS;

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
}

impl<'ctx> SymEval<'ctx> {
    pub fn new(ctx: &'ctx Context) -> Self {
        Self { ctx }
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
                let v = match args.get(1)? {
                    SymValue::Bv(b) => b.clone(),
                    _ => return None,
                };
                Some(SymValue::Bv(self.i32_clz(&v)))
            }
            "ictz_" => {
                let v = match args.get(1)? {
                    SymValue::Bv(b) => b.clone(),
                    _ => return None,
                };
                Some(SymValue::Bv(self.i32_ctz(&v)))
            }
            "ipopcnt_" => {
                let v = match args.get(1)? {
                    SymValue::Bv(b) => b.clone(),
                    _ => return None,
                };
                Some(SymValue::Bv(self.i32_popcnt(&v)))
            }
            _ => None,
        }
    }

    fn i32_clz(&self, v: &BV<'ctx>) -> BV<'ctx> {
        let mut out = BV::from_u64(self.ctx, 32, I32_WIDTH);
        for i in (0..32).rev() {
            let bit = v.extract(i, i)._eq(&BV::from_u64(self.ctx, 1, 1));
            let val = BV::from_u64(self.ctx, (31 - i) as u64, I32_WIDTH);
            out = bit.ite(&val, &out);
        }
        out
    }

    fn i32_ctz(&self, v: &BV<'ctx>) -> BV<'ctx> {
        let mut out = BV::from_u64(self.ctx, 32, I32_WIDTH);
        for i in 0..32 {
            let bit = v.extract(i, i)._eq(&BV::from_u64(self.ctx, 1, 1));
            let val = BV::from_u64(self.ctx, i as u64, I32_WIDTH);
            out = bit.ite(&val, &out);
        }
        out
    }

    fn i32_popcnt(&self, v: &BV<'ctx>) -> BV<'ctx> {
        let mut sum = BV::from_u64(self.ctx, 0, I32_WIDTH);
        for i in 0..32 {
            let bit = v.extract(i, i)._eq(&BV::from_u64(self.ctx, 1, 1));
            let one = bit.ite(
                &BV::from_u64(self.ctx, 1, I32_WIDTH),
                &BV::from_u64(self.ctx, 0, I32_WIDTH),
            );
            sum = sum.bvadd(&one);
        }
        sum
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
                SymValue::Meta(AlValue::NumType(NumType::I32))
            )),
            Pred::TypeIsFnn(_) => Ok(false),
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
                I32_WIDTH,
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
                Ok(SymValue::Bv(BV::from_u64(self.ctx, len as u64, I32_WIDTH)))
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
                    I32_WIDTH,
                )))
            }
            Expr::Shl(a, b) => self.bv_binop(a, b, env, |x, y| x.bvshl(&y)),
            Expr::BitAnd(a, b) => self.bv_binop(a, b, env, |x, y| x.bvand(&y)),
            Expr::BitOr(a, b) => self.bv_binop(a, b, env, |x, y| x.bvor(&y)),
            Expr::BitXor(a, b) => self.bv_binop(a, b, env, |x, y| x.bvxor(&y)),
            Expr::LShr(a, b) => self.bv_binop(a, b, env, |x, y| x.bvlshr(&y)),
            Expr::AShr(a, b) => self.bv_binop(a, b, env, |x, y| x.bvashr(&y)),
            Expr::Rotl(a, b) => self.bv_binop(a, b, env, |x, y| {
                x.bvrotl(&y.bvand(&BV::from_u64(self.ctx, 31, I32_WIDTH)))
            }),
            Expr::Rotr(a, b) => self.bv_binop(a, b, env, |x, y| {
                x.bvrotr(&y.bvand(&BV::from_u64(self.ctx, 31, I32_WIDTH)))
            }),
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
            Arg::Nat(n) => Ok(SymValue::Bv(BV::from_u64(self.ctx, *n as u64, I32_WIDTH))),
            Arg::Sign(s) => Ok(SymValue::Meta(AlValue::Sign(*s))),
            Arg::ExpA(expr) => self.eval_expr(expr, env),
        }
    }

    fn bv_of(&self, v: &SymValue<'ctx>) -> Result<BV<'ctx>, EvalError> {
        match v {
            SymValue::Bv(b) => Ok(b.clone()),
            SymValue::Meta(AlValue::Nat(n)) => Ok(BV::from_u64(self.ctx, *n, I32_WIDTH)),
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
        Ok(SymValue::Bool(f(av, bv)))
    }

    pub fn eval_value_ast(
        &self,
        ast: &ValueAst,
        vars: &[BV<'ctx>],
    ) -> Result<(BV<'ctx>, Bool<'ctx>), EvalError> {
        match ast {
            ValueAst::Symbol(i) => Ok((vars[*i].clone(), Bool::from_bool(self.ctx, false))),
            ValueAst::Const(n) => Ok((
                BV::from_i64(self.ctx, *n as i64, I32_WIDTH),
                Bool::from_bool(self.ctx, false),
            )),
            ValueAst::Add(l, r) => self.eval_binop_partial(l, r, vars, WasmBinOp::Add),
            ValueAst::Sub(l, r) => self.eval_binop_partial(l, r, vars, WasmBinOp::Sub),
            ValueAst::Mul(l, r) => self.eval_binop_partial(l, r, vars, WasmBinOp::Mul),
            ValueAst::DivU(l, r) => {
                self.eval_binop_partial(l, r, vars, WasmBinOp::Div(Sign::U))
            }
            ValueAst::DivS(l, r) => {
                self.eval_binop_partial(l, r, vars, WasmBinOp::Div(Sign::S))
            }
            ValueAst::RemU(l, r) => {
                self.eval_binop_partial(l, r, vars, WasmBinOp::Rem(Sign::U))
            }
            ValueAst::RemS(l, r) => {
                self.eval_binop_partial(l, r, vars, WasmBinOp::Rem(Sign::S))
            }
            ValueAst::Shl(l, r) => self.eval_binop_partial(l, r, vars, WasmBinOp::Shl),
            ValueAst::And(l, r) => self.eval_binop_partial(l, r, vars, WasmBinOp::And),
            ValueAst::Or(l, r) => self.eval_binop_partial(l, r, vars, WasmBinOp::Or),
            ValueAst::Xor(l, r) => self.eval_binop_partial(l, r, vars, WasmBinOp::Xor),
            ValueAst::ShrU(l, r) => {
                self.eval_binop_partial(l, r, vars, WasmBinOp::Shr(Sign::U))
            }
            ValueAst::ShrS(l, r) => {
                self.eval_binop_partial(l, r, vars, WasmBinOp::Shr(Sign::S))
            }
            ValueAst::Rotl(l, r) => self.eval_binop_partial(l, r, vars, WasmBinOp::Rotl),
            ValueAst::Rotr(l, r) => self.eval_binop_partial(l, r, vars, WasmBinOp::Rotr),
            ValueAst::Eq(l, r) => self.eval_relop(l, r, vars, WasmRelOp::Eq),
            ValueAst::Ne(l, r) => self.eval_relop(l, r, vars, WasmRelOp::Ne),
            ValueAst::LtS(l, r) => self.eval_relop(l, r, vars, WasmRelOp::Lt(Sign::S)),
            ValueAst::LeS(l, r) => self.eval_relop(l, r, vars, WasmRelOp::Le(Sign::S)),
            ValueAst::GtS(l, r) => self.eval_relop(l, r, vars, WasmRelOp::Gt(Sign::S)),
            ValueAst::Eqz(c) => self.eval_testop(c, vars, WasmTestOp::Eqz),
            ValueAst::Clz(c) => self.eval_unop(c, vars, WasmUnOp::Clz),
            ValueAst::Ctz(c) => self.eval_unop(c, vars, WasmUnOp::Ctz),
            ValueAst::Popcnt(c) => self.eval_unop(c, vars, WasmUnOp::Popcnt),
        }
    }

    fn eval_binop_partial(
        &self,
        l: &ValueAst,
        r: &ValueAst,
        vars: &[BV<'ctx>],
        binop: WasmBinOp,
    ) -> Result<(BV<'ctx>, Bool<'ctx>), EvalError> {
        let (l_val, l_trap) = self.eval_value_ast(l, vars)?;
        if l_trap.as_bool().unwrap_or(false) {
            return Ok((l_val, l_trap));
        }
        let (r_val, r_trap) = self.eval_value_ast(r, vars)?;
        let trap = Bool::or(self.ctx, &[&l_trap, &r_trap]);
        let args = vec![
            SymValue::Meta(AlValue::NumType(NumType::I32)),
            SymValue::Meta(AlValue::BinOp(binop)),
            SymValue::Bv(l_val),
            SymValue::Bv(r_val),
        ];
        let list = self.call_func("binop_", args)?;
        if list.is_empty_list_or_opt() {
            Ok((
                BV::from_u64(self.ctx, 0, I32_WIDTH),
                Bool::from_bool(self.ctx, true),
            ))
        } else if let Some(SymValue::Bv(v)) = list.choose_singleton() {
            Ok((v, trap))
        } else {
            Ok((
                BV::from_u64(self.ctx, 0, I32_WIDTH),
                Bool::from_bool(self.ctx, true),
            ))
        }
    }

    fn eval_relop(
        &self,
        l: &ValueAst,
        r: &ValueAst,
        vars: &[BV<'ctx>],
        relop: WasmRelOp,
    ) -> Result<(BV<'ctx>, Bool<'ctx>), EvalError> {
        let (l_val, l_trap) = self.eval_value_ast(l, vars)?;
        if l_trap.as_bool().unwrap_or(false) {
            return Ok((l_val, l_trap));
        }
        let (r_val, r_trap) = self.eval_value_ast(r, vars)?;
        let trap = Bool::or(self.ctx, &[&l_trap, &r_trap]);
        let args = vec![
            SymValue::Meta(AlValue::NumType(NumType::I32)),
            SymValue::Meta(AlValue::RelOp(relop)),
            SymValue::Bv(l_val),
            SymValue::Bv(r_val),
        ];
        let v = self.call_func("relop_", args)?;
        let bv = match v {
            SymValue::Bv(b) => b,
            SymValue::Meta(AlValue::Nat(n)) => BV::from_u64(self.ctx, n, I32_WIDTH),
            _ => BV::from_u64(self.ctx, 0, I32_WIDTH),
        };
        Ok((bv, trap))
    }

    fn eval_testop(
        &self,
        c: &ValueAst,
        vars: &[BV<'ctx>],
        testop: WasmTestOp,
    ) -> Result<(BV<'ctx>, Bool<'ctx>), EvalError> {
        let (c_val, c_trap) = self.eval_value_ast(c, vars)?;
        if c_trap.as_bool().unwrap_or(false) {
            return Ok((c_val, c_trap));
        }
        let args = vec![
            SymValue::Meta(AlValue::NumType(NumType::I32)),
            SymValue::Meta(AlValue::TestOp(testop)),
            SymValue::Bv(c_val),
        ];
        let v = self.call_func("testop_", args)?;
        let bv = match v {
            SymValue::Bv(b) => b,
            SymValue::Meta(AlValue::Nat(n)) => BV::from_u64(self.ctx, n, I32_WIDTH),
            _ => BV::from_u64(self.ctx, 0, I32_WIDTH),
        };
        Ok((bv, c_trap))
    }

    fn eval_unop(
        &self,
        c: &ValueAst,
        vars: &[BV<'ctx>],
        unop: WasmUnOp,
    ) -> Result<(BV<'ctx>, Bool<'ctx>), EvalError> {
        let (c_val, c_trap) = self.eval_value_ast(c, vars)?;
        if c_trap.as_bool().unwrap_or(false) {
            return Ok((c_val, c_trap));
        }
        let args = vec![
            SymValue::Meta(AlValue::NumType(NumType::I32)),
            SymValue::Meta(AlValue::UnOp(unop)),
            SymValue::Bv(c_val),
        ];
        let list = self.call_func("unop_", args)?;
        if list.is_empty_list_or_opt() {
            Ok((
                BV::from_u64(self.ctx, 0, I32_WIDTH),
                Bool::from_bool(self.ctx, true),
            ))
        } else if let Some(SymValue::Bv(v)) = list.choose_singleton() {
            Ok((v, c_trap))
        } else {
            Ok((
                BV::from_u64(self.ctx, 0, I32_WIDTH),
                Bool::from_bool(self.ctx, true),
            ))
        }
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

pub fn eval_value_ast_z3<'ctx>(
    ctx: &'ctx Context,
    ast: &ValueAst,
    vars: &[BV<'ctx>],
) -> Option<(BV<'ctx>, Bool<'ctx>)> {
    let eval = SymEval::new(ctx);
    eval.eval_value_ast(ast, vars).ok()
}

pub fn asts_valid_rewrite_z3<'ctx>(
    ctx: &'ctx Context,
    num_inputs: usize,
    lhs: &ValueAst,
    rhs: &ValueAst,
) -> bool {
    use z3::SatResult;
    let vars: Vec<BV<'_>> = (0..num_inputs)
        .map(|i| BV::new_const(ctx, format!("in_{i}"), I32_WIDTH))
        .collect();
    let eval = SymEval::new(ctx);
    let (lv, lt) = match eval.eval_value_ast(lhs, &vars) {
        Ok(pair) => pair,
        Err(_) => return false,
    };
    let (rv, rt) = match eval.eval_value_ast(rhs, &vars) {
        Ok(pair) => pair,
        Err(_) => return false,
    };
    let solver = z3::Solver::new(ctx);
    let trap_violation = lt.xor(&rt);
    let defined_both = Bool::and(ctx, &[&lt.not(), &rt.not()]);
    let value_violation = Bool::and(ctx, &[&defined_both, &lv._eq(&rv).not()]);
    solver.assert(&Bool::or(ctx, &[&trap_violation, &value_violation]));
    matches!(solver.check(), SatResult::Unsat)
}
