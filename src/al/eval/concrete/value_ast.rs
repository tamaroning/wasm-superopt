//! Evaluate [`ValueAst`](crate::value::ValueAst) via AL `$fn` helpers.

use super::super::value::{AlValue, ValueAstResult, nat_to_value, value_to_nat};
use super::call_func;
use crate::al::ast::{NumType, Sign, WasmBinOp, WasmRelOp, WasmTestOp, WasmUnOp};
use crate::value::{RuleSignature, ValueAst, ValueOp};

fn eval_partial_list(
    left: &ValueAst,
    right: &ValueAst,
    sig: &RuleSignature,
    inputs: &[i64],
    nt: NumType,
    binop: WasmBinOp,
) -> ValueAstResult {
    let l = eval_value_ast_concrete_sig(sig, left, inputs);
    if l.trap {
        return l;
    }
    let r = eval_value_ast_concrete_sig(sig, right, inputs);
    if r.trap {
        return r;
    }
    eval_binop_list(l.value, r.value, nt, binop)
}

fn eval_binop_list(a: i64, b: i64, nt: NumType, binop: WasmBinOp) -> ValueAstResult {
    let bits = nt.bit_width();
    let args = vec![
        AlValue::NumType(nt),
        AlValue::BinOp(binop),
        AlValue::Nat(value_to_nat(a, bits)),
        AlValue::Nat(value_to_nat(b, bits)),
    ];
    match call_func("binop_", args) {
        Ok(list) if list.is_empty_list_or_opt() => ValueAstResult {
            value: 0,
            trap: true,
        },
        Ok(list) => match list.choose_singleton() {
            Some(v) => ValueAstResult {
                value: nat_to_value(v.as_nat().unwrap_or(0), bits),
                trap: false,
            },
            None => ValueAstResult {
                value: 0,
                trap: true,
            },
        },
        Err(_) => ValueAstResult {
            value: 0,
            trap: true,
        },
    }
}

fn eval_unop_list(a: i64, nt: NumType, unop: WasmUnOp) -> ValueAstResult {
    let bits = nt.bit_width();
    let args = vec![
        AlValue::NumType(nt),
        AlValue::UnOp(unop),
        AlValue::Nat(value_to_nat(a, bits)),
    ];
    match call_func("unop_", args) {
        Ok(list) if list.is_empty_list_or_opt() => ValueAstResult {
            value: 0,
            trap: true,
        },
        Ok(list) => match list.choose_singleton() {
            Some(v) => ValueAstResult {
                value: nat_to_value(v.as_nat().unwrap_or(0), bits),
                trap: false,
            },
            None => ValueAstResult {
                value: 0,
                trap: true,
            },
        },
        Err(_) => ValueAstResult {
            value: 0,
            trap: true,
        },
    }
}

fn eval_relop(a: i64, b: i64, nt: NumType, relop: WasmRelOp) -> ValueAstResult {
    let bits = nt.bit_width();
    let args = vec![
        AlValue::NumType(nt),
        AlValue::RelOp(relop),
        AlValue::Nat(value_to_nat(a, bits)),
        AlValue::Nat(value_to_nat(b, bits)),
    ];
    match call_func("relop_", args) {
        Ok(v) => ValueAstResult {
            value: nat_to_value(v.as_nat().unwrap_or(0), 32),
            trap: false,
        },
        Err(_) => ValueAstResult {
            value: 0,
            trap: true,
        },
    }
}

fn eval_testop(a: i64, nt: NumType, testop: WasmTestOp) -> ValueAstResult {
    let bits = nt.bit_width();
    let args = vec![
        AlValue::NumType(nt),
        AlValue::TestOp(testop),
        AlValue::Nat(value_to_nat(a, bits)),
    ];
    match call_func("testop_", args) {
        Ok(v) => ValueAstResult {
            value: nat_to_value(v.as_nat().unwrap_or(0), 32),
            trap: false,
        },
        Err(_) => ValueAstResult {
            value: 0,
            trap: true,
        },
    }
}

fn extend_i32_to_i64(v: i64, signed: bool) -> i64 {
    if signed {
        v as i32 as i64
    } else {
        (v as u32) as u64 as i64
    }
}

fn wrap_i64_to_i32(v: i64) -> i64 {
    v as i32 as i64
}

fn eval_op(sig: &RuleSignature, op: ValueOp, args: &[&ValueAst], inputs: &[i64]) -> ValueAstResult {
    use ValueOp::*;
    match op {
        I32Add => eval_partial_list(args[0], args[1], sig, inputs, NumType::I32, WasmBinOp::Add),
        I32Sub => eval_partial_list(args[0], args[1], sig, inputs, NumType::I32, WasmBinOp::Sub),
        I32Mul => eval_partial_list(args[0], args[1], sig, inputs, NumType::I32, WasmBinOp::Mul),
        I32DivU => eval_partial_list(
            args[0],
            args[1],
            sig,
            inputs,
            NumType::I32,
            WasmBinOp::Div(Sign::U),
        ),
        I32DivS => eval_partial_list(
            args[0],
            args[1],
            sig,
            inputs,
            NumType::I32,
            WasmBinOp::Div(Sign::S),
        ),
        I32RemU => eval_partial_list(
            args[0],
            args[1],
            sig,
            inputs,
            NumType::I32,
            WasmBinOp::Rem(Sign::U),
        ),
        I32RemS => eval_partial_list(
            args[0],
            args[1],
            sig,
            inputs,
            NumType::I32,
            WasmBinOp::Rem(Sign::S),
        ),
        I32Shl => eval_partial_list(args[0], args[1], sig, inputs, NumType::I32, WasmBinOp::Shl),
        I32And => eval_partial_list(args[0], args[1], sig, inputs, NumType::I32, WasmBinOp::And),
        I32Or => eval_partial_list(args[0], args[1], sig, inputs, NumType::I32, WasmBinOp::Or),
        I32Xor => eval_partial_list(args[0], args[1], sig, inputs, NumType::I32, WasmBinOp::Xor),
        I32ShrU => eval_partial_list(
            args[0],
            args[1],
            sig,
            inputs,
            NumType::I32,
            WasmBinOp::Shr(Sign::U),
        ),
        I32ShrS => eval_partial_list(
            args[0],
            args[1],
            sig,
            inputs,
            NumType::I32,
            WasmBinOp::Shr(Sign::S),
        ),
        I32Rotl => eval_partial_list(args[0], args[1], sig, inputs, NumType::I32, WasmBinOp::Rotl),
        I32Rotr => eval_partial_list(args[0], args[1], sig, inputs, NumType::I32, WasmBinOp::Rotr),
        I64Add => eval_partial_list(args[0], args[1], sig, inputs, NumType::I64, WasmBinOp::Add),
        I64Sub => eval_partial_list(args[0], args[1], sig, inputs, NumType::I64, WasmBinOp::Sub),
        I64Mul => eval_partial_list(args[0], args[1], sig, inputs, NumType::I64, WasmBinOp::Mul),
        I64DivU => eval_partial_list(
            args[0],
            args[1],
            sig,
            inputs,
            NumType::I64,
            WasmBinOp::Div(Sign::U),
        ),
        I64DivS => eval_partial_list(
            args[0],
            args[1],
            sig,
            inputs,
            NumType::I64,
            WasmBinOp::Div(Sign::S),
        ),
        I64RemU => eval_partial_list(
            args[0],
            args[1],
            sig,
            inputs,
            NumType::I64,
            WasmBinOp::Rem(Sign::U),
        ),
        I64RemS => eval_partial_list(
            args[0],
            args[1],
            sig,
            inputs,
            NumType::I64,
            WasmBinOp::Rem(Sign::S),
        ),
        I64Shl => eval_partial_list(args[0], args[1], sig, inputs, NumType::I64, WasmBinOp::Shl),
        I64And => eval_partial_list(args[0], args[1], sig, inputs, NumType::I64, WasmBinOp::And),
        I64Or => eval_partial_list(args[0], args[1], sig, inputs, NumType::I64, WasmBinOp::Or),
        I64Xor => eval_partial_list(args[0], args[1], sig, inputs, NumType::I64, WasmBinOp::Xor),
        I64ShrU => eval_partial_list(
            args[0],
            args[1],
            sig,
            inputs,
            NumType::I64,
            WasmBinOp::Shr(Sign::U),
        ),
        I64ShrS => eval_partial_list(
            args[0],
            args[1],
            sig,
            inputs,
            NumType::I64,
            WasmBinOp::Shr(Sign::S),
        ),
        I64Rotl => eval_partial_list(args[0], args[1], sig, inputs, NumType::I64, WasmBinOp::Rotl),
        I64Rotr => eval_partial_list(args[0], args[1], sig, inputs, NumType::I64, WasmBinOp::Rotr),
        I32Eq => {
            let l = eval_value_ast_concrete_sig(sig, args[0], inputs);
            if l.trap {
                return l;
            }
            let r = eval_value_ast_concrete_sig(sig, args[1], inputs);
            if r.trap {
                return r;
            }
            eval_relop(l.value, r.value, NumType::I32, WasmRelOp::Eq)
        }
        I32Ne => {
            let l = eval_value_ast_concrete_sig(sig, args[0], inputs);
            if l.trap {
                return l;
            }
            let r = eval_value_ast_concrete_sig(sig, args[1], inputs);
            if r.trap {
                return r;
            }
            eval_relop(l.value, r.value, NumType::I32, WasmRelOp::Ne)
        }
        I32LtS => {
            let l = eval_value_ast_concrete_sig(sig, args[0], inputs);
            if l.trap {
                return l;
            }
            let r = eval_value_ast_concrete_sig(sig, args[1], inputs);
            if r.trap {
                return r;
            }
            eval_relop(l.value, r.value, NumType::I32, WasmRelOp::Lt(Sign::S))
        }
        I32LeS => {
            let l = eval_value_ast_concrete_sig(sig, args[0], inputs);
            if l.trap {
                return l;
            }
            let r = eval_value_ast_concrete_sig(sig, args[1], inputs);
            if r.trap {
                return r;
            }
            eval_relop(l.value, r.value, NumType::I32, WasmRelOp::Le(Sign::S))
        }
        I32GtS => {
            let l = eval_value_ast_concrete_sig(sig, args[0], inputs);
            if l.trap {
                return l;
            }
            let r = eval_value_ast_concrete_sig(sig, args[1], inputs);
            if r.trap {
                return r;
            }
            eval_relop(l.value, r.value, NumType::I32, WasmRelOp::Gt(Sign::S))
        }
        I64Eq => {
            let l = eval_value_ast_concrete_sig(sig, args[0], inputs);
            if l.trap {
                return l;
            }
            let r = eval_value_ast_concrete_sig(sig, args[1], inputs);
            if r.trap {
                return r;
            }
            eval_relop(l.value, r.value, NumType::I64, WasmRelOp::Eq)
        }
        I64Ne => {
            let l = eval_value_ast_concrete_sig(sig, args[0], inputs);
            if l.trap {
                return l;
            }
            let r = eval_value_ast_concrete_sig(sig, args[1], inputs);
            if r.trap {
                return r;
            }
            eval_relop(l.value, r.value, NumType::I64, WasmRelOp::Ne)
        }
        I64LtS => {
            let l = eval_value_ast_concrete_sig(sig, args[0], inputs);
            if l.trap {
                return l;
            }
            let r = eval_value_ast_concrete_sig(sig, args[1], inputs);
            if r.trap {
                return r;
            }
            eval_relop(l.value, r.value, NumType::I64, WasmRelOp::Lt(Sign::S))
        }
        I64LeS => {
            let l = eval_value_ast_concrete_sig(sig, args[0], inputs);
            if l.trap {
                return l;
            }
            let r = eval_value_ast_concrete_sig(sig, args[1], inputs);
            if r.trap {
                return r;
            }
            eval_relop(l.value, r.value, NumType::I64, WasmRelOp::Le(Sign::S))
        }
        I64GtS => {
            let l = eval_value_ast_concrete_sig(sig, args[0], inputs);
            if l.trap {
                return l;
            }
            let r = eval_value_ast_concrete_sig(sig, args[1], inputs);
            if r.trap {
                return r;
            }
            eval_relop(l.value, r.value, NumType::I64, WasmRelOp::Gt(Sign::S))
        }
        I32Eqz => {
            let c = eval_value_ast_concrete_sig(sig, args[0], inputs);
            if c.trap {
                return c;
            }
            eval_testop(c.value, NumType::I32, WasmTestOp::Eqz)
        }
        I64Eqz => {
            let c = eval_value_ast_concrete_sig(sig, args[0], inputs);
            if c.trap {
                return c;
            }
            eval_testop(c.value, NumType::I64, WasmTestOp::Eqz)
        }
        I32Clz => {
            let c = eval_value_ast_concrete_sig(sig, args[0], inputs);
            if c.trap {
                return c;
            }
            eval_unop_list(c.value, NumType::I32, WasmUnOp::Clz)
        }
        I32Ctz => {
            let c = eval_value_ast_concrete_sig(sig, args[0], inputs);
            if c.trap {
                return c;
            }
            eval_unop_list(c.value, NumType::I32, WasmUnOp::Ctz)
        }
        I32Popcnt => {
            let c = eval_value_ast_concrete_sig(sig, args[0], inputs);
            if c.trap {
                return c;
            }
            eval_unop_list(c.value, NumType::I32, WasmUnOp::Popcnt)
        }
        I64Clz => {
            let c = eval_value_ast_concrete_sig(sig, args[0], inputs);
            if c.trap {
                return c;
            }
            eval_unop_list(c.value, NumType::I64, WasmUnOp::Clz)
        }
        I64Ctz => {
            let c = eval_value_ast_concrete_sig(sig, args[0], inputs);
            if c.trap {
                return c;
            }
            eval_unop_list(c.value, NumType::I64, WasmUnOp::Ctz)
        }
        I64Popcnt => {
            let c = eval_value_ast_concrete_sig(sig, args[0], inputs);
            if c.trap {
                return c;
            }
            eval_unop_list(c.value, NumType::I64, WasmUnOp::Popcnt)
        }
        I64ExtendI32S => {
            let c = eval_value_ast_concrete_sig(sig, args[0], inputs);
            if c.trap {
                return c;
            }
            ValueAstResult {
                value: extend_i32_to_i64(c.value, true),
                trap: false,
            }
        }
        I64ExtendI32U => {
            let c = eval_value_ast_concrete_sig(sig, args[0], inputs);
            if c.trap {
                return c;
            }
            ValueAstResult {
                value: extend_i32_to_i64(c.value, false),
                trap: false,
            }
        }
        I32WrapI64 => {
            let c = eval_value_ast_concrete_sig(sig, args[0], inputs);
            if c.trap {
                return c;
            }
            ValueAstResult {
                value: wrap_i64_to_i32(c.value),
                trap: false,
            }
        }
        F32Add => eval_partial_list(args[0], args[1], sig, inputs, NumType::F32, WasmBinOp::Add),
        F32Sub => eval_partial_list(args[0], args[1], sig, inputs, NumType::F32, WasmBinOp::Sub),
        F32Mul => eval_partial_list(args[0], args[1], sig, inputs, NumType::F32, WasmBinOp::Mul),
        F32Div => eval_partial_list(
            args[0],
            args[1],
            sig,
            inputs,
            NumType::F32,
            WasmBinOp::FloatDiv,
        ),
        F32Min => eval_partial_list(args[0], args[1], sig, inputs, NumType::F32, WasmBinOp::Min),
        F32Max => eval_partial_list(args[0], args[1], sig, inputs, NumType::F32, WasmBinOp::Max),
        F32Copysign => eval_partial_list(
            args[0],
            args[1],
            sig,
            inputs,
            NumType::F32,
            WasmBinOp::Copysign,
        ),
        F64Add => eval_partial_list(args[0], args[1], sig, inputs, NumType::F64, WasmBinOp::Add),
        F64Sub => eval_partial_list(args[0], args[1], sig, inputs, NumType::F64, WasmBinOp::Sub),
        F64Mul => eval_partial_list(args[0], args[1], sig, inputs, NumType::F64, WasmBinOp::Mul),
        F64Div => eval_partial_list(
            args[0],
            args[1],
            sig,
            inputs,
            NumType::F64,
            WasmBinOp::FloatDiv,
        ),
        F64Min => eval_partial_list(args[0], args[1], sig, inputs, NumType::F64, WasmBinOp::Min),
        F64Max => eval_partial_list(args[0], args[1], sig, inputs, NumType::F64, WasmBinOp::Max),
        F64Copysign => eval_partial_list(
            args[0],
            args[1],
            sig,
            inputs,
            NumType::F64,
            WasmBinOp::Copysign,
        ),
        F32Eq => eval_float_relop(args, sig, inputs, NumType::F32, WasmRelOp::Eq),
        F32Ne => eval_float_relop(args, sig, inputs, NumType::F32, WasmRelOp::Ne),
        F32Lt => eval_float_relop(args, sig, inputs, NumType::F32, WasmRelOp::Flt),
        F32Le => eval_float_relop(args, sig, inputs, NumType::F32, WasmRelOp::Fle),
        F32Gt => eval_float_relop(args, sig, inputs, NumType::F32, WasmRelOp::Fgt),
        F32Ge => eval_float_relop(args, sig, inputs, NumType::F32, WasmRelOp::Fge),
        F64Eq => eval_float_relop(args, sig, inputs, NumType::F64, WasmRelOp::Eq),
        F64Ne => eval_float_relop(args, sig, inputs, NumType::F64, WasmRelOp::Ne),
        F64Lt => eval_float_relop(args, sig, inputs, NumType::F64, WasmRelOp::Flt),
        F64Le => eval_float_relop(args, sig, inputs, NumType::F64, WasmRelOp::Fle),
        F64Gt => eval_float_relop(args, sig, inputs, NumType::F64, WasmRelOp::Fgt),
        F64Ge => eval_float_relop(args, sig, inputs, NumType::F64, WasmRelOp::Fge),
        F32Abs => eval_float_unop(args, sig, inputs, NumType::F32, WasmUnOp::Abs),
        F32Neg => eval_float_unop(args, sig, inputs, NumType::F32, WasmUnOp::Neg),
        F32Sqrt => eval_float_unop(args, sig, inputs, NumType::F32, WasmUnOp::Sqrt),
        F32Ceil => eval_float_unop(args, sig, inputs, NumType::F32, WasmUnOp::Ceil),
        F32Floor => eval_float_unop(args, sig, inputs, NumType::F32, WasmUnOp::Floor),
        F32Trunc => eval_float_unop(args, sig, inputs, NumType::F32, WasmUnOp::Trunc),
        F32Nearest => eval_float_unop(args, sig, inputs, NumType::F32, WasmUnOp::Nearest),
        F64Abs => eval_float_unop(args, sig, inputs, NumType::F64, WasmUnOp::Abs),
        F64Neg => eval_float_unop(args, sig, inputs, NumType::F64, WasmUnOp::Neg),
        F64Sqrt => eval_float_unop(args, sig, inputs, NumType::F64, WasmUnOp::Sqrt),
        F64Ceil => eval_float_unop(args, sig, inputs, NumType::F64, WasmUnOp::Ceil),
        F64Floor => eval_float_unop(args, sig, inputs, NumType::F64, WasmUnOp::Floor),
        F64Trunc => eval_float_unop(args, sig, inputs, NumType::F64, WasmUnOp::Trunc),
        F64Nearest => eval_float_unop(args, sig, inputs, NumType::F64, WasmUnOp::Nearest),
    }
}

fn eval_float_relop(
    args: &[&ValueAst],
    sig: &RuleSignature,
    inputs: &[i64],
    nt: NumType,
    relop: WasmRelOp,
) -> ValueAstResult {
    let l = eval_value_ast_concrete_sig(sig, args[0], inputs);
    if l.trap {
        return l;
    }
    let r = eval_value_ast_concrete_sig(sig, args[1], inputs);
    if r.trap {
        return r;
    }
    eval_relop(l.value, r.value, nt, relop)
}

fn eval_float_unop(
    args: &[&ValueAst],
    sig: &RuleSignature,
    inputs: &[i64],
    nt: NumType,
    unop: WasmUnOp,
) -> ValueAstResult {
    let c = eval_value_ast_concrete_sig(sig, args[0], inputs);
    if c.trap {
        return c;
    }
    eval_unop_list(c.value, nt, unop)
}

/// Concrete evaluation of a [`ValueAst`] under a rule signature.
pub fn eval_value_ast_concrete_sig(
    sig: &RuleSignature,
    ast: &ValueAst,
    inputs: &[i64],
) -> ValueAstResult {
    match ast {
        ValueAst::Symbol(i) => ValueAstResult {
            value: inputs[*i],
            trap: false,
        },
        ValueAst::Const { value, .. } => ValueAstResult {
            value: *value,
            trap: false,
        },
        ValueAst::App { op, args } => {
            let refs: Vec<&ValueAst> = args.iter().collect();
            eval_op(sig, *op, &refs, inputs)
        }
    }
}

/// Concrete evaluation of a [`ValueAst`] as homogeneous i32 (legacy).
#[cfg(test)]
pub fn eval_value_ast_concrete(ast: &ValueAst, inputs: &[i32]) -> ValueAstResult {
    let inputs64: Vec<i64> = inputs.iter().map(|&v| v as i64).collect();
    let sig = RuleSignature {
        inputs: vec![crate::semantics::StackTy::I32; inputs64.len()],
        output: crate::semantics::StackTy::I32,
    };
    eval_value_ast_concrete_sig(&sig, ast, &inputs64)
}
