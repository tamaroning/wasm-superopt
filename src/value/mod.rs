//! Pure value DAG (no stack/local containers) for equality saturation.

mod ast;
mod ops;

pub use crate::semantics::StackTy;
pub use ast::{
    ValueAst, is_ast_rewrite_pair, is_directed_ast_pair, value_ast_from_expr, value_ast_to_expr,
};
pub use ops::{
    RuleSignature, ValueOp, enumerate_signatures, f32_bits_to_i64, f64_bits_to_i64, is_reachable,
};

use crate::al::asts_valid_rewrite_z3 as al_asts_valid_rewrite_z3;
use crate::al::eval_value_ast_concrete_sig;
use crate::lang::ValueLang;
use egg::RecExpr;

#[derive(Clone, Debug, PartialEq, Eq)]
struct AstEvalResult {
    value: i64,
    trap: bool,
}

fn eval_ast_concrete(sig: &RuleSignature, ast: &ValueAst, inputs: &[i64]) -> AstEvalResult {
    let r = eval_value_ast_concrete_sig(sig, ast, inputs);
    AstEvalResult {
        value: r.value,
        trap: r.trap,
    }
}

fn concrete_valid_ast_rewrite(lhs: &AstEvalResult, rhs: &AstEvalResult) -> bool {
    if lhs.trap != rhs.trap {
        return false;
    }
    lhs.trap || lhs.value == rhs.value
}

const AST_CORNER_INPUTS_I32: [i64; 6] = [0, 1, -1, 2, i32::MIN as i64, i32::MAX as i64];
const AST_CORNER_INPUTS_I64: [i64; 6] = [0, 1, -1, 2, i64::MIN, i64::MAX];
const AST_CORNER_INPUTS_F32: [u64; 6] = [
    0,
    f32::to_bits(1.0) as u64,
    f32::to_bits(-1.0) as u64,
    f32::to_bits(2.0) as u64,
    f32::to_bits(f32::NAN) as u64,
    f32::to_bits(f32::INFINITY) as u64,
];
const AST_CORNER_INPUTS_F64: [u64; 6] = [
    0,
    f64::to_bits(1.0),
    f64::to_bits(-1.0),
    f64::to_bits(2.0),
    f64::to_bits(f64::NAN),
    f64::to_bits(f64::INFINITY),
];

fn corner_row(sig: &RuleSignature, v: i64) -> Vec<i64> {
    sig.inputs
        .iter()
        .map(|&ty| match ty {
            StackTy::I32 => v as i32 as i64,
            StackTy::I64 => v,
            StackTy::F32 => v as u32 as i32 as i64,
            StackTy::F64 => v,
        })
        .collect()
}

fn corner_row_float(sig: &RuleSignature, bits: u64) -> Vec<i64> {
    sig.inputs
        .iter()
        .map(|&ty| match ty {
            StackTy::F32 => f32_bits_to_i64(bits as u32),
            StackTy::F64 => f64_bits_to_i64(bits),
            StackTy::I32 => bits as u32 as i32 as i64,
            StackTy::I64 => bits as i64,
        })
        .collect()
}

fn sig_uses_float(sig: &RuleSignature) -> bool {
    sig.inputs.iter().any(|ty| ty.is_float()) || sig.output.is_float()
}

fn asts_match_on_inputs(
    sig: &RuleSignature,
    lhs: &ValueAst,
    rhs: &ValueAst,
    inputs: &[i64],
) -> bool {
    let lhs_r = eval_ast_concrete(sig, lhs, inputs);
    let rhs_r = eval_ast_concrete(sig, rhs, inputs);
    concrete_valid_ast_rewrite(&lhs_r, &rhs_r)
}

/// Fast filter: returns `false` if a concrete counterexample is found.
pub fn asts_valid_rewrite_random(
    sig: &RuleSignature,
    lhs: &ValueAst,
    rhs: &ValueAst,
    num_tests: usize,
) -> bool {
    for &v in &AST_CORNER_INPUTS_I32 {
        let inputs = corner_row(sig, v);
        if !asts_match_on_inputs(sig, lhs, rhs, &inputs) {
            return false;
        }
    }
    for &v in &AST_CORNER_INPUTS_I64 {
        let inputs = corner_row(sig, v);
        if !asts_match_on_inputs(sig, lhs, rhs, &inputs) {
            return false;
        }
    }
    for &bits in &AST_CORNER_INPUTS_F32 {
        let inputs = corner_row_float(sig, bits);
        if !asts_match_on_inputs(sig, lhs, rhs, &inputs) {
            return false;
        }
    }
    for &bits in &AST_CORNER_INPUTS_F64 {
        let inputs = corner_row_float(sig, bits);
        if !asts_match_on_inputs(sig, lhs, rhs, &inputs) {
            return false;
        }
    }

    let mut rng = AstLcg::new(0xE6A3_9A1B_CDE2_4701);
    for _ in 0..num_tests {
        let inputs: Vec<i64> = sig
            .inputs
            .iter()
            .map(|&ty| match ty {
                StackTy::I32 => rng.next_i32() as i64,
                StackTy::I64 => rng.next_i64(),
                StackTy::F32 => f32_bits_to_i64(rng.next_u32()),
                StackTy::F64 => f64_bits_to_i64(rng.next_u64()),
            })
            .collect();
        if !asts_match_on_inputs(sig, lhs, rhs, &inputs) {
            return false;
        }
    }
    true
}

struct AstLcg(u64);

impl AstLcg {
    fn new(seed: u64) -> Self {
        Self(seed)
    }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1);
        self.0
    }

    fn next_i32(&mut self) -> i32 {
        self.next_u64() as i32
    }

    fn next_i64(&mut self) -> i64 {
        self.next_u64() as i64
    }

    fn next_u32(&mut self) -> u32 {
        self.next_u64() as u32
    }
}

/// Z3 proof only (call after `asts_valid_rewrite_random` passes).
pub fn asts_valid_rewrite_z3(
    ctx: &z3::Context,
    sig: &RuleSignature,
    lhs: &ValueAst,
    rhs: &ValueAst,
) -> bool {
    // Float semantics use IEEE builtins; Z3 FP encoding is not wired yet.
    if sig_uses_float(sig) {
        return true;
    }
    al_asts_valid_rewrite_z3(ctx, sig, lhs, rhs)
}

/// Fixed concrete inputs for characteristic-vector matching (Ruler-style cvecs).
pub fn cvec_test_inputs(sig: &RuleSignature) -> Vec<Vec<i64>> {
    let mut out: Vec<Vec<i64>> = AST_CORNER_INPUTS_I32
        .iter()
        .chain(AST_CORNER_INPUTS_I64.iter())
        .map(|&v| corner_row(sig, v))
        .collect();
    out.extend(
        AST_CORNER_INPUTS_F32
            .iter()
            .chain(AST_CORNER_INPUTS_F64.iter())
            .map(|&bits| corner_row_float(sig, bits)),
    );
    let mut rng = AstLcg::new(0xC0FF_EE42);
    for _ in 0..32 {
        let inputs: Vec<i64> = sig
            .inputs
            .iter()
            .map(|&ty| match ty {
                StackTy::I32 => rng.next_i32() as i64,
                StackTy::I64 => rng.next_i64(),
                StackTy::F32 => f32_bits_to_i64(rng.next_u32()),
                StackTy::F64 => f64_bits_to_i64(rng.next_u64()),
            })
            .collect();
        out.push(inputs);
    }
    out
}

/// Characteristic vector: concrete evaluation on a fixed input suite.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AstEvalSignature {
    samples: Vec<(bool, i64)>,
}

impl AstEvalSignature {
    pub fn of(ast: &ValueAst, sig: &RuleSignature, test_inputs: &[Vec<i64>]) -> Self {
        let samples = test_inputs
            .iter()
            .map(|inputs| {
                let r = eval_ast_concrete(sig, ast, inputs);
                (r.trap, r.value)
            })
            .collect();
        Self { samples }
    }
}

/// Parse a s-expression into a [`ValueLang`] DAG (used by symbolic forward execution).
pub fn parse_value_expr(s: &str) -> RecExpr<ValueLang> {
    s.parse().expect("invalid ValueLang RecExpr")
}
