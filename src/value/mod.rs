//! Pure value DAG (no stack/local containers) for equality saturation.

mod ast;
mod ops;

pub use ast::{
    ValueAst, enumerate_value_asts, is_ast_rewrite_pair, is_directed_ast_pair, synthesis_symbol,
    value_ast_from_expr, value_ast_to_expr,
};
pub use ops::{RuleSignature, ValueOp, enumerate_signatures, is_reachable};
pub use crate::semantics::StackTy;

use crate::al::eval_value_ast_concrete_sig;
use crate::al::{asts_valid_rewrite_z3 as al_asts_valid_rewrite_z3, eval_value_ast_concrete, ValueAstResult};
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

fn corner_row(sig: &RuleSignature, v: i64) -> Vec<i64> {
    sig.inputs
        .iter()
        .map(|&ty| match ty {
            StackTy::I32 => v as i32 as i64,
            StackTy::I64 => v,
        })
        .collect()
}

fn asts_match_on_inputs(sig: &RuleSignature, lhs: &ValueAst, rhs: &ValueAst, inputs: &[i64]) -> bool {
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

    let mut rng = AstLcg::new(0xE6A3_9A1B_CDE2_4701);
    for _ in 0..num_tests {
        let inputs: Vec<i64> = sig
            .inputs
            .iter()
            .map(|&ty| match ty {
                StackTy::I32 => rng.next_i32() as i64,
                StackTy::I64 => rng.next_i64(),
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
}

/// Z3 proof only (call after `asts_valid_rewrite_random` passes).
pub fn asts_valid_rewrite_z3(
    ctx: &z3::Context,
    sig: &RuleSignature,
    lhs: &ValueAst,
    rhs: &ValueAst,
) -> bool {
    al_asts_valid_rewrite_z3(ctx, sig, lhs, rhs)
}

/// Fixed concrete inputs for characteristic-vector matching (Ruler-style cvecs).
pub fn cvec_test_inputs(sig: &RuleSignature) -> Vec<Vec<i64>> {
    let mut out: Vec<Vec<i64>> = AST_CORNER_INPUTS_I32
        .iter()
        .chain(AST_CORNER_INPUTS_I64.iter())
        .map(|&v| corner_row(sig, v))
        .collect();
    let mut rng = AstLcg::new(0xC0FF_EE42);
    for _ in 0..32 {
        let inputs: Vec<i64> = sig
            .inputs
            .iter()
            .map(|&ty| match ty {
                StackTy::I32 => rng.next_i32() as i64,
                StackTy::I64 => rng.next_i64(),
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

/// Legacy i32 concrete eval for AL tests.
pub fn eval_value_ast_concrete_i32(ast: &ValueAst, inputs: &[i32]) -> ValueAstResult {
    let sig = RuleSignature {
        inputs: vec![StackTy::I32; inputs.len()],
        output: StackTy::I32,
    };
    let inputs64: Vec<i64> = inputs.iter().map(|&v| v as i64).collect();
    eval_value_ast_concrete_sig(&sig, ast, &inputs64)
}
