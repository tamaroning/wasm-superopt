//! AL semantics regression tests for ValueAst evaluation.

use crate::al::ast::{NumType, Sign, WasmBinOp};
use crate::al::eval::concrete::call_func;
use crate::al::eval::value::{i32_to_nat, AlValue};
use crate::al::eval::concrete::eval_value_ast_concrete;
use crate::value::{ValueAst, asts_valid_rewrite_z3};

#[test]
fn div_s_min_over_neg_one_traps_via_al() {
    let args = vec![
        AlValue::NumType(NumType::I32),
        AlValue::BinOp(WasmBinOp::Div(Sign::S)),
        AlValue::Nat(i32_to_nat(i32::MIN)),
        AlValue::Nat(i32_to_nat(-1)),
    ];
    let list = call_func("binop_", args).unwrap();
    assert!(list.is_empty_list_or_opt());
}

#[test]
fn value_ast_div_s_min_over_neg_one_traps() {
    let ast = ValueAst::DivS(
        Box::new(ValueAst::Const(i32::MIN)),
        Box::new(ValueAst::Const(-1)),
    );
    let r = eval_value_ast_concrete(&ast, &[]);
    assert!(r.trap);
}

#[test]
fn mul_by_two_equals_shl_one_z3() {
    let ctx = crate::al::z3_context();
    let lhs = ValueAst::Mul(
        Box::new(ValueAst::Symbol(0)),
        Box::new(ValueAst::Const(2)),
    );
    let rhs = ValueAst::Shl(
        Box::new(ValueAst::Symbol(0)),
        Box::new(ValueAst::Const(1)),
    );
    assert!(asts_valid_rewrite_z3(&ctx, 1, &lhs, &rhs));
}

#[test]
fn sizenn_i32_works() {
    use crate::al::ast::NumType;
    use crate::al::eval::concrete::call_func;
    use crate::al::eval::value::AlValue;

    let r = call_func("sizenn", vec![AlValue::NumType(NumType::I32)]).unwrap();
    assert_eq!(r.as_nat(), Some(32));
}

#[test]
fn binop_shr_s_and_xor_concrete() {
    use crate::al::ast::{NumType, Sign, WasmBinOp};
    use crate::al::eval::concrete::call_func;
    use crate::al::eval::value::{i32_to_nat, nat_to_i32, AlValue};

    for (binop, a, b, expect) in [
        (WasmBinOp::Add, 4i32, 1i32, 5i32),
        (WasmBinOp::Shr(Sign::S), 1i32, 4i32, 0i32),
        (WasmBinOp::Xor, 4i32, 1i32, 5i32),
    ] {
        let args = vec![
            AlValue::NumType(NumType::I32),
            AlValue::BinOp(binop),
            AlValue::Nat(i32_to_nat(a)),
            AlValue::Nat(i32_to_nat(b)),
        ];
        let list = call_func("binop_", args).expect("binop call");
        assert!(!list.is_empty_list_or_opt(), "{binop:?} should not trap");
        let v = nat_to_i32(list.choose_singleton().unwrap().as_nat().unwrap());
        assert_eq!(v, expect, "{binop:?} {a} {b}");
    }
}

#[test]
fn suspicious_shr_xor_rule_is_invalid() {
    use crate::value::{asts_valid_rewrite_random, asts_valid_rewrite_z3, parse_value_expr};

    let lhs = parse_value_expr("(i32.shr_s ?b ?a)");
    let rhs = parse_value_expr("(i32.xor ?a ?b)");
    let lhs_ast = crate::value::value_ast_from_expr(&lhs).unwrap();
    let rhs_ast = crate::value::value_ast_from_expr(&rhs).unwrap();

    assert!(
        !asts_valid_rewrite_random(2, &lhs_ast, &rhs_ast, 100),
        "concrete random should reject shr_s/xor"
    );
    let ctx = crate::al::z3_context();
    assert!(
        !asts_valid_rewrite_z3(&ctx, 2, &lhs_ast, &rhs_ast),
        "Z3 should reject shr_s/xor"
    );
}

#[test]
fn add_wraps_at_max() {
    let ast = ValueAst::Add(
        Box::new(ValueAst::Const(i32::MAX)),
        Box::new(ValueAst::Const(1)),
    );
    let r = eval_value_ast_concrete(&ast, &[]);
    assert!(!r.trap);
    assert_eq!(r.value, i32::MIN);
}
