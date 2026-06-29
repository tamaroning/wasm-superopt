//! Z3 evaluation of typed [`ValueAst`] under a [`RuleSignature`].

use super::{EvalError, SymEval, SymValue};
use crate::al::ast::{NumType, Sign, WasmBinOp, WasmRelOp, WasmTestOp, WasmUnOp};
use crate::al::eval::value::AlValue;
use crate::value::{RuleSignature, StackTy, ValueAst, ValueOp};
use z3::ast::{Ast, BV, Bool};

fn normalize_bv_width<'ctx>(ctx: &'ctx z3::Context, v: BV<'ctx>, out_w: u32) -> BV<'ctx> {
    let w = v.get_size();
    if w > out_w {
        v.extract(out_w - 1, 0)
    } else if w < out_w {
        v.zero_ext(out_w - w)
    } else {
        v
    }
}

impl<'ctx> SymEval<'ctx> {
    pub fn eval_value_ast(
        &self,
        ast: &ValueAst,
        vars: &[BV<'ctx>],
    ) -> Result<(BV<'ctx>, Bool<'ctx>), EvalError> {
        match ast {
            ValueAst::Symbol(i) => Ok((vars[*i].clone(), Bool::from_bool(self.ctx, false))),
            ValueAst::Const { ty, value } => Ok((
                BV::from_i64(self.ctx, *value, ty.bit_width()),
                Bool::from_bool(self.ctx, false),
            )),
            ValueAst::App { op, args } => self.eval_value_op(*op, args, vars),
        }
    }

    fn eval_value_op(
        &self,
        op: ValueOp,
        args: &[ValueAst],
        vars: &[BV<'ctx>],
    ) -> Result<(BV<'ctx>, Bool<'ctx>), EvalError> {
        use ValueOp::*;
        let out_w = op.push().bit_width();
        let refs: Vec<&ValueAst> = args.iter().collect();
        match op {
            I32Add => self.eval_binop(&refs, vars, NumType::I32, WasmBinOp::Add, out_w),
            I32Sub => self.eval_binop(&refs, vars, NumType::I32, WasmBinOp::Sub, out_w),
            I32Mul => self.eval_binop(&refs, vars, NumType::I32, WasmBinOp::Mul, out_w),
            I32DivU => self.eval_binop(&refs, vars, NumType::I32, WasmBinOp::Div(Sign::U), out_w),
            I32DivS => self.eval_binop(&refs, vars, NumType::I32, WasmBinOp::Div(Sign::S), out_w),
            I32RemU => self.eval_binop(&refs, vars, NumType::I32, WasmBinOp::Rem(Sign::U), out_w),
            I32RemS => self.eval_binop(&refs, vars, NumType::I32, WasmBinOp::Rem(Sign::S), out_w),
            I32Shl => self.eval_binop(&refs, vars, NumType::I32, WasmBinOp::Shl, out_w),
            I32And => self.eval_binop(&refs, vars, NumType::I32, WasmBinOp::And, out_w),
            I32Or => self.eval_binop(&refs, vars, NumType::I32, WasmBinOp::Or, out_w),
            I32Xor => self.eval_binop(&refs, vars, NumType::I32, WasmBinOp::Xor, out_w),
            I32ShrU => self.eval_binop(&refs, vars, NumType::I32, WasmBinOp::Shr(Sign::U), out_w),
            I32ShrS => self.eval_binop(&refs, vars, NumType::I32, WasmBinOp::Shr(Sign::S), out_w),
            I32Rotl => self.eval_binop(&refs, vars, NumType::I32, WasmBinOp::Rotl, out_w),
            I32Rotr => self.eval_binop(&refs, vars, NumType::I32, WasmBinOp::Rotr, out_w),
            I64Add => self.eval_binop(&refs, vars, NumType::I64, WasmBinOp::Add, out_w),
            I64Sub => self.eval_binop(&refs, vars, NumType::I64, WasmBinOp::Sub, out_w),
            I64Mul => self.eval_binop(&refs, vars, NumType::I64, WasmBinOp::Mul, out_w),
            I64DivU => self.eval_binop(&refs, vars, NumType::I64, WasmBinOp::Div(Sign::U), out_w),
            I64DivS => self.eval_binop(&refs, vars, NumType::I64, WasmBinOp::Div(Sign::S), out_w),
            I64RemU => self.eval_binop(&refs, vars, NumType::I64, WasmBinOp::Rem(Sign::U), out_w),
            I64RemS => self.eval_binop(&refs, vars, NumType::I64, WasmBinOp::Rem(Sign::S), out_w),
            I64Shl => self.eval_binop(&refs, vars, NumType::I64, WasmBinOp::Shl, out_w),
            I64And => self.eval_binop(&refs, vars, NumType::I64, WasmBinOp::And, out_w),
            I64Or => self.eval_binop(&refs, vars, NumType::I64, WasmBinOp::Or, out_w),
            I64Xor => self.eval_binop(&refs, vars, NumType::I64, WasmBinOp::Xor, out_w),
            I64ShrU => self.eval_binop(&refs, vars, NumType::I64, WasmBinOp::Shr(Sign::U), out_w),
            I64ShrS => self.eval_binop(&refs, vars, NumType::I64, WasmBinOp::Shr(Sign::S), out_w),
            I64Rotl => self.eval_binop(&refs, vars, NumType::I64, WasmBinOp::Rotl, out_w),
            I64Rotr => self.eval_binop(&refs, vars, NumType::I64, WasmBinOp::Rotr, out_w),
            I32Eq => self.eval_relop(&refs, vars, NumType::I32, WasmRelOp::Eq),
            I32Ne => self.eval_relop(&refs, vars, NumType::I32, WasmRelOp::Ne),
            I32LtS => self.eval_relop(&refs, vars, NumType::I32, WasmRelOp::Lt(Sign::S)),
            I32LeS => self.eval_relop(&refs, vars, NumType::I32, WasmRelOp::Le(Sign::S)),
            I32GtS => self.eval_relop(&refs, vars, NumType::I32, WasmRelOp::Gt(Sign::S)),
            I64Eq => self.eval_relop(&refs, vars, NumType::I64, WasmRelOp::Eq),
            I64Ne => self.eval_relop(&refs, vars, NumType::I64, WasmRelOp::Ne),
            I64LtS => self.eval_relop(&refs, vars, NumType::I64, WasmRelOp::Lt(Sign::S)),
            I64LeS => self.eval_relop(&refs, vars, NumType::I64, WasmRelOp::Le(Sign::S)),
            I64GtS => self.eval_relop(&refs, vars, NumType::I64, WasmRelOp::Gt(Sign::S)),
            I32Eqz => self.eval_testop(&refs, vars, NumType::I32, WasmTestOp::Eqz),
            I64Eqz => self.eval_testop(&refs, vars, NumType::I64, WasmTestOp::Eqz),
            I32Clz => self.eval_unop(&refs, vars, NumType::I32, WasmUnOp::Clz, out_w),
            I32Ctz => self.eval_unop(&refs, vars, NumType::I32, WasmUnOp::Ctz, out_w),
            I32Popcnt => self.eval_unop(&refs, vars, NumType::I32, WasmUnOp::Popcnt, out_w),
            I64Clz => self.eval_unop(&refs, vars, NumType::I64, WasmUnOp::Clz, out_w),
            I64Ctz => self.eval_unop(&refs, vars, NumType::I64, WasmUnOp::Ctz, out_w),
            I64Popcnt => self.eval_unop(&refs, vars, NumType::I64, WasmUnOp::Popcnt, out_w),
            I64ExtendI32S => self.eval_extend(&refs, vars, true, out_w),
            I64ExtendI32U => self.eval_extend(&refs, vars, false, out_w),
            I32WrapI64 => self.eval_wrap(&refs, vars, out_w),
            F32Add => self.eval_binop(&refs, vars, NumType::F32, WasmBinOp::Add, out_w),
            F32Sub => self.eval_binop(&refs, vars, NumType::F32, WasmBinOp::Sub, out_w),
            F32Mul => self.eval_binop(&refs, vars, NumType::F32, WasmBinOp::Mul, out_w),
            F32Div => self.eval_binop(&refs, vars, NumType::F32, WasmBinOp::FloatDiv, out_w),
            F32Min => self.eval_binop(&refs, vars, NumType::F32, WasmBinOp::Min, out_w),
            F32Max => self.eval_binop(&refs, vars, NumType::F32, WasmBinOp::Max, out_w),
            F32Copysign => self.eval_binop(&refs, vars, NumType::F32, WasmBinOp::Copysign, out_w),
            F64Add => self.eval_binop(&refs, vars, NumType::F64, WasmBinOp::Add, out_w),
            F64Sub => self.eval_binop(&refs, vars, NumType::F64, WasmBinOp::Sub, out_w),
            F64Mul => self.eval_binop(&refs, vars, NumType::F64, WasmBinOp::Mul, out_w),
            F64Div => self.eval_binop(&refs, vars, NumType::F64, WasmBinOp::FloatDiv, out_w),
            F64Min => self.eval_binop(&refs, vars, NumType::F64, WasmBinOp::Min, out_w),
            F64Max => self.eval_binop(&refs, vars, NumType::F64, WasmBinOp::Max, out_w),
            F64Copysign => self.eval_binop(&refs, vars, NumType::F64, WasmBinOp::Copysign, out_w),
            F32Eq => self.eval_relop(&refs, vars, NumType::F32, WasmRelOp::Eq),
            F32Ne => self.eval_relop(&refs, vars, NumType::F32, WasmRelOp::Ne),
            F32Lt => self.eval_relop(&refs, vars, NumType::F32, WasmRelOp::Flt),
            F32Le => self.eval_relop(&refs, vars, NumType::F32, WasmRelOp::Fle),
            F32Gt => self.eval_relop(&refs, vars, NumType::F32, WasmRelOp::Fgt),
            F32Ge => self.eval_relop(&refs, vars, NumType::F32, WasmRelOp::Fge),
            F64Eq => self.eval_relop(&refs, vars, NumType::F64, WasmRelOp::Eq),
            F64Ne => self.eval_relop(&refs, vars, NumType::F64, WasmRelOp::Ne),
            F64Lt => self.eval_relop(&refs, vars, NumType::F64, WasmRelOp::Flt),
            F64Le => self.eval_relop(&refs, vars, NumType::F64, WasmRelOp::Fle),
            F64Gt => self.eval_relop(&refs, vars, NumType::F64, WasmRelOp::Fgt),
            F64Ge => self.eval_relop(&refs, vars, NumType::F64, WasmRelOp::Fge),
            F32Abs => self.eval_unop(&refs, vars, NumType::F32, WasmUnOp::Abs, out_w),
            F32Neg => self.eval_unop(&refs, vars, NumType::F32, WasmUnOp::Neg, out_w),
            F32Sqrt => self.eval_unop(&refs, vars, NumType::F32, WasmUnOp::Sqrt, out_w),
            F32Ceil => self.eval_unop(&refs, vars, NumType::F32, WasmUnOp::Ceil, out_w),
            F32Floor => self.eval_unop(&refs, vars, NumType::F32, WasmUnOp::Floor, out_w),
            F32Trunc => self.eval_unop(&refs, vars, NumType::F32, WasmUnOp::Trunc, out_w),
            F32Nearest => self.eval_unop(&refs, vars, NumType::F32, WasmUnOp::Nearest, out_w),
            F64Abs => self.eval_unop(&refs, vars, NumType::F64, WasmUnOp::Abs, out_w),
            F64Neg => self.eval_unop(&refs, vars, NumType::F64, WasmUnOp::Neg, out_w),
            F64Sqrt => self.eval_unop(&refs, vars, NumType::F64, WasmUnOp::Sqrt, out_w),
            F64Ceil => self.eval_unop(&refs, vars, NumType::F64, WasmUnOp::Ceil, out_w),
            F64Floor => self.eval_unop(&refs, vars, NumType::F64, WasmUnOp::Floor, out_w),
            F64Trunc => self.eval_unop(&refs, vars, NumType::F64, WasmUnOp::Trunc, out_w),
            F64Nearest => self.eval_unop(&refs, vars, NumType::F64, WasmUnOp::Nearest, out_w),
        }
    }

    fn eval_binop(
        &self,
        args: &[&ValueAst],
        vars: &[BV<'ctx>],
        nt: NumType,
        binop: WasmBinOp,
        out_w: u32,
    ) -> Result<(BV<'ctx>, Bool<'ctx>), EvalError> {
        let (l_val, l_trap) = self.eval_value_ast(args[0], vars)?;
        if l_trap.as_bool().unwrap_or(false) {
            return Ok((l_val, l_trap));
        }
        let (r_val, r_trap) = self.eval_value_ast(args[1], vars)?;
        let trap = Bool::or(self.ctx, &[&l_trap, &r_trap]);
        let al_args = vec![
            SymValue::Meta(AlValue::NumType(nt)),
            SymValue::Meta(AlValue::BinOp(binop)),
            SymValue::Bv(l_val),
            SymValue::Bv(r_val),
        ];
        let list = self.call_func("binop_", al_args)?;
        if list.is_empty_list_or_opt() {
            Ok((
                BV::from_u64(self.ctx, 0, out_w),
                Bool::from_bool(self.ctx, true),
            ))
        } else if let Some(SymValue::Bv(v)) = list.choose_singleton() {
            Ok((v, trap))
        } else {
            Ok((
                BV::from_u64(self.ctx, 0, out_w),
                Bool::from_bool(self.ctx, true),
            ))
        }
    }

    fn eval_relop(
        &self,
        args: &[&ValueAst],
        vars: &[BV<'ctx>],
        nt: NumType,
        relop: WasmRelOp,
    ) -> Result<(BV<'ctx>, Bool<'ctx>), EvalError> {
        let (l_val, l_trap) = self.eval_value_ast(args[0], vars)?;
        if l_trap.as_bool().unwrap_or(false) {
            return Ok((l_val, l_trap));
        }
        let (r_val, r_trap) = self.eval_value_ast(args[1], vars)?;
        let trap = Bool::or(self.ctx, &[&l_trap, &r_trap]);
        let al_args = vec![
            SymValue::Meta(AlValue::NumType(nt)),
            SymValue::Meta(AlValue::RelOp(relop)),
            SymValue::Bv(l_val),
            SymValue::Bv(r_val),
        ];
        let v = self.call_func("relop_", al_args)?;
        let bv = match v {
            SymValue::Bv(b) => b,
            SymValue::Meta(AlValue::Nat(n)) => BV::from_u64(self.ctx, n, 32),
            _ => BV::from_u64(self.ctx, 0, 32),
        };
        Ok((bv, trap))
    }

    fn eval_testop(
        &self,
        args: &[&ValueAst],
        vars: &[BV<'ctx>],
        nt: NumType,
        testop: WasmTestOp,
    ) -> Result<(BV<'ctx>, Bool<'ctx>), EvalError> {
        let (c_val, c_trap) = self.eval_value_ast(args[0], vars)?;
        if c_trap.as_bool().unwrap_or(false) {
            return Ok((c_val, c_trap));
        }
        let al_args = vec![
            SymValue::Meta(AlValue::NumType(nt)),
            SymValue::Meta(AlValue::TestOp(testop)),
            SymValue::Bv(c_val),
        ];
        let v = self.call_func("testop_", al_args)?;
        let bv = match v {
            SymValue::Bv(b) => b,
            SymValue::Meta(AlValue::Nat(n)) => BV::from_u64(self.ctx, n, 32),
            _ => BV::from_u64(self.ctx, 0, 32),
        };
        Ok((bv, c_trap))
    }

    fn eval_unop(
        &self,
        args: &[&ValueAst],
        vars: &[BV<'ctx>],
        nt: NumType,
        unop: WasmUnOp,
        out_w: u32,
    ) -> Result<(BV<'ctx>, Bool<'ctx>), EvalError> {
        let (c_val, c_trap) = self.eval_value_ast(args[0], vars)?;
        if c_trap.as_bool().unwrap_or(false) {
            return Ok((c_val, c_trap));
        }
        let al_args = vec![
            SymValue::Meta(AlValue::NumType(nt)),
            SymValue::Meta(AlValue::UnOp(unop)),
            SymValue::Bv(c_val),
        ];
        let list = self.call_func("unop_", al_args)?;
        if list.is_empty_list_or_opt() {
            Ok((
                BV::from_u64(self.ctx, 0, out_w),
                Bool::from_bool(self.ctx, true),
            ))
        } else if let Some(SymValue::Bv(v)) = list.choose_singleton() {
            Ok((v, c_trap))
        } else {
            Ok((
                BV::from_u64(self.ctx, 0, out_w),
                Bool::from_bool(self.ctx, true),
            ))
        }
    }

    fn eval_extend(
        &self,
        args: &[&ValueAst],
        vars: &[BV<'ctx>],
        signed: bool,
        out_w: u32,
    ) -> Result<(BV<'ctx>, Bool<'ctx>), EvalError> {
        let (c_val, c_trap) = self.eval_value_ast(args[0], vars)?;
        if c_trap.as_bool().unwrap_or(false) {
            return Ok((c_val, c_trap));
        }
        let extended = if signed {
            c_val.sign_ext(out_w - 32)
        } else {
            c_val.zero_ext(out_w - 32)
        };
        Ok((extended, c_trap))
    }

    fn eval_wrap(
        &self,
        args: &[&ValueAst],
        vars: &[BV<'ctx>],
        out_w: u32,
    ) -> Result<(BV<'ctx>, Bool<'ctx>), EvalError> {
        let (c_val, c_trap) = self.eval_value_ast(args[0], vars)?;
        if c_trap.as_bool().unwrap_or(false) {
            return Ok((c_val, c_trap));
        }
        Ok((c_val.extract(out_w - 1, 0), c_trap))
    }
}

pub fn eval_value_ast_z3<'ctx>(
    ctx: &'ctx z3::Context,
    sig: &RuleSignature,
    ast: &ValueAst,
    vars: &[BV<'ctx>],
) -> Option<(BV<'ctx>, Bool<'ctx>)> {
    let eval = SymEval::new(ctx, sig.clone());
    eval.eval_value_ast(ast, vars).ok()
}

pub fn asts_valid_rewrite_z3<'ctx>(
    ctx: &'ctx z3::Context,
    sig: &RuleSignature,
    lhs: &ValueAst,
    rhs: &ValueAst,
) -> bool {
    use z3::SatResult;
    let vars: Vec<BV<'_>> = sig
        .inputs
        .iter()
        .enumerate()
        .map(|(i, ty)| BV::new_const(ctx, format!("in_{i}"), ty.bit_width()))
        .collect();
    let eval = SymEval::new(ctx, sig.clone());
    let (lv, lt) = match eval.eval_value_ast(lhs, &vars) {
        Ok(pair) => pair,
        Err(_) => return false,
    };
    let (rv, rt) = match eval.eval_value_ast(rhs, &vars) {
        Ok(pair) => pair,
        Err(_) => return false,
    };
    let out_w = sig.output.bit_width();
    let lv = normalize_bv_width(ctx, lv, out_w);
    let rv = normalize_bv_width(ctx, rv, out_w);
    let solver = z3::Solver::new(ctx);
    let trap_violation = lt.xor(&rt);
    let defined_both = Bool::and(ctx, &[&lt.not(), &rt.not()]);
    let value_violation = Bool::and(ctx, &[&defined_both, &lv._eq(&rv).not()]);
    solver.assert(&Bool::or(ctx, &[&trap_violation, &value_violation]));
    matches!(solver.check(), SatResult::Unsat)
}
