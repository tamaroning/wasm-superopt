//! Evaluate [`ValueAst`](crate::value::ValueAst) via AL `$fn` helpers.

use super::call_func;
use super::super::error::EvalError;
use super::super::value::{i32_to_nat, nat_to_i32, AlValue, ValueAstResult};
use crate::al::ast::{NumType, Sign, WasmBinOp, WasmRelOp, WasmTestOp, WasmUnOp};
use crate::value::ValueAst;

fn eval_partial_list(
    left: &ValueAst,
    right: &ValueAst,
    inputs: &[i32],
    binop: WasmBinOp,
) -> ValueAstResult {
    let l = eval_value_ast_concrete(left, inputs);
    if l.trap {
        return l;
    }
    let r = eval_value_ast_concrete(right, inputs);
    if r.trap {
        return r;
    }
    eval_binop_list(l.value, r.value, binop)
}

fn eval_binop_list(a: i32, b: i32, binop: WasmBinOp) -> ValueAstResult {
    let args = vec![
        AlValue::NumType(NumType::I32),
        AlValue::BinOp(binop),
        AlValue::Nat(i32_to_nat(a)),
        AlValue::Nat(i32_to_nat(b)),
    ];
    match call_func("binop_", args) {
        Ok(list) if list.is_empty_list_or_opt() => ValueAstResult {
            value: 0,
            trap: true,
        },
        Ok(list) => match list.choose_singleton() {
            Some(v) => ValueAstResult {
                value: nat_to_i32(v.as_nat().unwrap_or(0)),
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

fn eval_unop_list(a: i32, unop: WasmUnOp) -> ValueAstResult {
    let args = vec![
        AlValue::NumType(NumType::I32),
        AlValue::UnOp(unop),
        AlValue::Nat(i32_to_nat(a)),
    ];
    match call_func("unop_", args) {
        Ok(list) if list.is_empty_list_or_opt() => ValueAstResult {
            value: 0,
            trap: true,
        },
        Ok(list) => match list.choose_singleton() {
            Some(v) => ValueAstResult {
                value: nat_to_i32(v.as_nat().unwrap_or(0)),
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

fn eval_relop(a: i32, b: i32, relop: WasmRelOp) -> ValueAstResult {
    let args = vec![
        AlValue::NumType(NumType::I32),
        AlValue::RelOp(relop),
        AlValue::Nat(i32_to_nat(a)),
        AlValue::Nat(i32_to_nat(b)),
    ];
    match call_func("relop_", args) {
        Ok(v) => ValueAstResult {
            value: nat_to_i32(v.as_nat().unwrap_or(0)),
            trap: false,
        },
        Err(_) => ValueAstResult {
            value: 0,
            trap: true,
        },
    }
}

fn eval_testop(a: i32, testop: WasmTestOp) -> ValueAstResult {
    let args = vec![
        AlValue::NumType(NumType::I32),
        AlValue::TestOp(testop),
        AlValue::Nat(i32_to_nat(a)),
    ];
    match call_func("testop_", args) {
        Ok(v) => ValueAstResult {
            value: nat_to_i32(v.as_nat().unwrap_or(0)),
            trap: false,
        },
        Err(_) => ValueAstResult {
            value: 0,
            trap: true,
        },
    }
}

/// Concrete evaluation of a [`ValueAst`] via AL semantics.
pub fn eval_value_ast_concrete(ast: &ValueAst, inputs: &[i32]) -> ValueAstResult {
    match ast {
        ValueAst::Symbol(i) => ValueAstResult {
            value: inputs[*i],
            trap: false,
        },
        ValueAst::Const(n) => ValueAstResult {
            value: *n,
            trap: false,
        },
        ValueAst::Add(l, r) => eval_partial_list(l, r, inputs, WasmBinOp::Add),
        ValueAst::Sub(l, r) => eval_partial_list(l, r, inputs, WasmBinOp::Sub),
        ValueAst::Mul(l, r) => eval_partial_list(l, r, inputs, WasmBinOp::Mul),
        ValueAst::DivU(l, r) => eval_partial_list(l, r, inputs, WasmBinOp::Div(Sign::U)),
        ValueAst::DivS(l, r) => eval_partial_list(l, r, inputs, WasmBinOp::Div(Sign::S)),
        ValueAst::RemU(l, r) => eval_partial_list(l, r, inputs, WasmBinOp::Rem(Sign::U)),
        ValueAst::RemS(l, r) => eval_partial_list(l, r, inputs, WasmBinOp::Rem(Sign::S)),
        ValueAst::Shl(l, r) => eval_partial_list(l, r, inputs, WasmBinOp::Shl),
        ValueAst::And(l, r) => eval_partial_list(l, r, inputs, WasmBinOp::And),
        ValueAst::Or(l, r) => eval_partial_list(l, r, inputs, WasmBinOp::Or),
        ValueAst::Xor(l, r) => eval_partial_list(l, r, inputs, WasmBinOp::Xor),
        ValueAst::ShrU(l, r) => eval_partial_list(l, r, inputs, WasmBinOp::Shr(Sign::U)),
        ValueAst::ShrS(l, r) => eval_partial_list(l, r, inputs, WasmBinOp::Shr(Sign::S)),
        ValueAst::Rotl(l, r) => eval_partial_list(l, r, inputs, WasmBinOp::Rotl),
        ValueAst::Rotr(l, r) => eval_partial_list(l, r, inputs, WasmBinOp::Rotr),
        ValueAst::Eq(l, r) => {
            let l = eval_value_ast_concrete(l, inputs);
            if l.trap {
                return l;
            }
            let r = eval_value_ast_concrete(r, inputs);
            if r.trap {
                return r;
            }
            eval_relop(l.value, r.value, WasmRelOp::Eq)
        }
        ValueAst::Ne(l, r) => {
            let l = eval_value_ast_concrete(l, inputs);
            if l.trap {
                return l;
            }
            let r = eval_value_ast_concrete(r, inputs);
            if r.trap {
                return r;
            }
            eval_relop(l.value, r.value, WasmRelOp::Ne)
        }
        ValueAst::LtS(l, r) => {
            let l = eval_value_ast_concrete(l, inputs);
            if l.trap {
                return l;
            }
            let r = eval_value_ast_concrete(r, inputs);
            if r.trap {
                return r;
            }
            eval_relop(l.value, r.value, WasmRelOp::Lt(Sign::S))
        }
        ValueAst::LeS(l, r) => {
            let l = eval_value_ast_concrete(l, inputs);
            if l.trap {
                return l;
            }
            let r = eval_value_ast_concrete(r, inputs);
            if r.trap {
                return r;
            }
            eval_relop(l.value, r.value, WasmRelOp::Le(Sign::S))
        }
        ValueAst::GtS(l, r) => {
            let l = eval_value_ast_concrete(l, inputs);
            if l.trap {
                return l;
            }
            let r = eval_value_ast_concrete(r, inputs);
            if r.trap {
                return r;
            }
            eval_relop(l.value, r.value, WasmRelOp::Gt(Sign::S))
        }
        ValueAst::Eqz(c) => {
            let c = eval_value_ast_concrete(c, inputs);
            if c.trap {
                return c;
            }
            eval_testop(c.value, WasmTestOp::Eqz)
        }
        ValueAst::Clz(c) => {
            let c = eval_value_ast_concrete(c, inputs);
            if c.trap {
                return c;
            }
            eval_unop_list(c.value, WasmUnOp::Clz)
        }
        ValueAst::Ctz(c) => {
            let c = eval_value_ast_concrete(c, inputs);
            if c.trap {
                return c;
            }
            eval_unop_list(c.value, WasmUnOp::Ctz)
        }
        ValueAst::Popcnt(c) => {
            let c = eval_value_ast_concrete(c, inputs);
            if c.trap {
                return c;
            }
            eval_unop_list(c.value, WasmUnOp::Popcnt)
        }
    }
}

pub fn concrete_valid_rewrite(lhs: &ValueAst, rhs: &ValueAst, inputs: &[i32]) -> bool {
    let l = eval_value_ast_concrete(lhs, inputs);
    let r = eval_value_ast_concrete(rhs, inputs);
    if l.trap != r.trap {
        return false;
    }
    l.trap || l.value == r.value
}

/// Map AL evaluation failure to trap for symbolic path consistency.
pub fn eval_error_to_trap(_: EvalError) -> ValueAstResult {
    ValueAstResult {
        value: 0,
        trap: true,
    }
}
