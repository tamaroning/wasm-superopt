//! AL semantics regression tests for ValueAst evaluation.

use crate::al::ast::{NumType, Sign, WasmBinOp};
use crate::al::eval::concrete::call_func;
use crate::al::eval::concrete::eval_value_ast_concrete;
use crate::al::eval::value::AlValue;
use crate::semantics::StackTy;
use crate::value::{RuleSignature, ValueAst, ValueOp, asts_valid_rewrite_z3};

fn i32_sig(arity: usize) -> RuleSignature {
    RuleSignature {
        inputs: vec![StackTy::I32; arity],
        output: StackTy::I32,
    }
}

#[test]
fn div_s_min_over_neg_one_traps_via_al() {
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
fn value_ast_div_s_min_over_neg_one_traps() {
    let ast = ValueAst::app(
        ValueOp::I32DivS,
        vec![
            ValueAst::const_ty(StackTy::I32, i32::MIN as i64),
            ValueAst::const_ty(StackTy::I32, -1),
        ],
    );
    let r = eval_value_ast_concrete(&ast, &[]);
    assert!(r.trap);
}

#[test]
fn mul_by_two_equals_shl_one_z3() {
    let ctx = crate::al::z3_context();
    let sig = i32_sig(1);
    let lhs = ValueAst::app(
        ValueOp::I32Mul,
        vec![ValueAst::symbol(0), ValueAst::const_ty(StackTy::I32, 2)],
    );
    let rhs = ValueAst::app(
        ValueOp::I32Shl,
        vec![ValueAst::symbol(0), ValueAst::const_ty(StackTy::I32, 1)],
    );
    assert!(asts_valid_rewrite_z3(&ctx, &sig, &lhs, &rhs));
}

#[test]
fn sizenn_i64_works() {
    let r = call_func("sizenn", vec![AlValue::NumType(NumType::I64)]).unwrap();
    assert_eq!(r.as_nat(), Some(64));
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
    use crate::al::eval::value::AlValue;

    for (binop, a, b, expect) in [
        (WasmBinOp::Add, 4i32, 1i32, 5i32),
        (WasmBinOp::Shr(Sign::S), 1i32, 4i32, 0i32),
        (WasmBinOp::Xor, 4i32, 1i32, 5i32),
    ] {
        let args = vec![
            AlValue::NumType(NumType::I32),
            AlValue::BinOp(binop),
            AlValue::Nat(a as u32 as u64),
            AlValue::Nat(b as u32 as u64),
        ];
        let list = call_func("binop_", args).expect("binop call");
        assert!(!list.is_empty_list_or_opt(), "{binop:?} should not trap");
        let v = list.choose_singleton().unwrap().as_nat().unwrap() as u32 as i32;
        assert_eq!(v, expect, "{binop:?} {a} {b}");
    }
}

#[test]
fn f32_double_neg_is_identity() {
    use crate::al::eval_value_ast_concrete_sig;

    let sig = RuleSignature {
        inputs: vec![StackTy::F32],
        output: StackTy::F32,
    };
    let x = ValueAst::symbol(0);
    let double_neg = ValueAst::app(
        ValueOp::F32Neg,
        vec![ValueAst::app(ValueOp::F32Neg, vec![x.clone()])],
    );
    for bits in [
        0u32,
        f32::to_bits(1.0),
        f32::to_bits(-1.0),
        f32::to_bits(3.5),
        f32::to_bits(f32::NAN),
        f32::to_bits(f32::INFINITY),
    ] {
        let inputs = vec![crate::value::f32_bits_to_i64(bits)];
        let lhs = eval_value_ast_concrete_sig(&sig, &double_neg, &inputs);
        let rhs = eval_value_ast_concrete_sig(&sig, &x, &inputs);
        assert!(!lhs.trap && !rhs.trap, "bits={bits:#x}");
        assert_eq!(lhs.value, rhs.value, "bits={bits:#x}");
    }
}

#[test]
fn suspicious_shr_xor_rule_is_invalid() {
    use crate::value::{asts_valid_rewrite_random, parse_value_expr};

    let sig = i32_sig(2);
    let lhs = parse_value_expr("(i32.shr_s ?b ?a)");
    let rhs = parse_value_expr("(i32.xor ?a ?b)");
    let lhs_ast = crate::value::value_ast_from_expr(&lhs).unwrap();
    let rhs_ast = crate::value::value_ast_from_expr(&rhs).unwrap();

    assert!(
        !asts_valid_rewrite_random(&sig, &lhs_ast, &rhs_ast, 100),
        "concrete random should reject shr_s/xor"
    );
    let ctx = crate::al::z3_context();
    assert!(
        !asts_valid_rewrite_z3(&ctx, &sig, &lhs_ast, &rhs_ast),
        "Z3 should reject shr_s/xor"
    );
}

#[test]
fn add_wraps_at_max() {
    let ast = ValueAst::app(
        ValueOp::I32Add,
        vec![
            ValueAst::const_ty(StackTy::I32, i32::MAX as i64),
            ValueAst::const_ty(StackTy::I32, 1),
        ],
    );
    let r = eval_value_ast_concrete(&ast, &[]);
    assert!(!r.trap);
    assert_eq!(r.value, i32::MIN as i64);
}
