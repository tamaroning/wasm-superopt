//! Exhaustive rule candidate generation and Z3 equivalence checking.
//! Term enumeration follows Ruler (OOPSLA '21): e-graph hash-consing plus
//! equality-saturation compaction between size extensions.

use crate::al::z3_context;
use crate::lang::ValueLang;
use crate::ruler::discover_rules_for_input;
use crate::semantics::{StackTy, synthesis_inputs};
use crate::value::ValueAst;
use egg::{Pattern, Rewrite};
use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::fs;
use std::io::{self, Write};
use std::path::PathBuf;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SynthesizedRule {
    pub name: String,
    pub lhs: String,
    pub rhs: String,
    pub input: Vec<StackTy>,
}

fn format_input_stack(input: &[StackTy]) -> String {
    if input.is_empty() {
        "[]".to_string()
    } else {
        format!(
            "[{}]",
            input.iter().map(|_| "I32").collect::<Vec<_>>().join(", ")
        )
    }
}

fn report_progress(msg: &str) {
    let _ = writeln!(io::stderr(), "{msg}");
    let _ = io::stderr().flush();
}

fn rules_cache_path(max_ast_size: usize) -> PathBuf {
    PathBuf::from(format!("rules-ast{max_ast_size}.cache"))
}

const RULES_CACHE_FORMAT_VERSION: u32 = 12;

/// AST size used in integration tests (≈ old `max_seq_len` 2).
#[cfg(test)]
pub const TEST_SYNTHESIS_AST_SIZE: usize = 3;

#[derive(Serialize, Deserialize)]
struct CachedRules {
    format_version: u32,
    max_ast_size: usize,
    random_tests: usize,
    rules: Vec<SynthesizedRule>,
}

pub fn load_cached_rules(max_ast_size: usize) -> Option<Vec<SynthesizedRule>> {
    let path = rules_cache_path(max_ast_size);
    let data = fs::read_to_string(&path).ok()?;
    let cached: CachedRules = serde_json::from_str(&data).ok()?;
    if cached.format_version != RULES_CACHE_FORMAT_VERSION || cached.max_ast_size != max_ast_size {
        return None;
    }
    report_progress(&format!(
        "Loaded {} rules from {}",
        cached.rules.len(),
        path.display()
    ));
    Some(cached.rules)
}

fn save_cached_rules(max_ast_size: usize, random_tests: usize, rules: &[SynthesizedRule]) {
    let path = rules_cache_path(max_ast_size);
    let cached = CachedRules {
        format_version: RULES_CACHE_FORMAT_VERSION,
        max_ast_size,
        random_tests,
        rules: rules.to_vec(),
    };
    let json = serde_json::to_string_pretty(&cached).expect("serialize rules cache");
    fs::write(&path, json).expect("write rules cache");
    report_progress(&format!(
        "Saved {} rules to {}",
        rules.len(),
        path.display()
    ));
}

pub fn load_or_synthesize_rules(
    max_ast_size: usize,
    random_tests: usize,
    jobs: usize,
) -> Vec<SynthesizedRule> {
    if let Some(rules) = load_cached_rules(max_ast_size) {
        return rules;
    }
    let rules = synthesize_rules(max_ast_size, random_tests, jobs);
    save_cached_rules(max_ast_size, random_tests, &rules);
    rules
}

pub fn synthesize_rules(max_ast_size: usize, random_tests: usize, jobs: usize) -> Vec<SynthesizedRule> {
    let inputs = synthesis_inputs();
    let mut proven = Vec::new();
    let mut seen = HashSet::new();
    let mut pairs_checked = 0usize;
    let mut z3_queries = 0usize;

    report_progress(&format!(
        "synthesis (Ruler): max_ast_size={max_ast_size}, random_tests={random_tests}, jobs={jobs}, {} input stacks",
        inputs.len()
    ));

    crate::parallel::run_with_threads(jobs, || {
        let ctx = z3_context();
        for (input_idx, input) in inputs.iter().enumerate() {
            let num_inputs = input.len();
            let stack_desc = format_input_stack(input);
            report_progress(&format!(
                "[{}/{}] input stack {stack_desc}",
                input_idx + 1,
                inputs.len()
            ));

            let mut local_rules = Vec::new();
            let (checked, z3) = discover_rules_for_input(
                num_inputs,
                max_ast_size,
                random_tests,
                jobs,
                &ctx,
                &mut seen,
                &mut local_rules,
            );
            pairs_checked += checked;
            z3_queries += z3;

            let added_here = local_rules.len();
            for (lhs, rhs) in local_rules {
                let name = format!("syn-{}", proven.len());
                proven.push(SynthesizedRule {
                    name,
                    lhs,
                    rhs,
                    input: input.clone(),
                });
            }

            report_progress(&format!(
                "  done {stack_desc}: +{added_here} rules ({total} total)",
                total = proven.len()
            ));
        }
    });

    report_progress(&format!(
        "synthesis complete: {pairs_checked} pairs checked, {z3_queries} Z3 queries, {} rules",
        proven.len()
    ));

    proven
}

fn collect_candidate_indices(num_inputs: usize, asts: &[ValueAst]) -> Vec<(usize, usize)> {
    let mut indices = Vec::new();
    for i in 0..asts.len() {
        for j in 0..asts.len() {
            if i == j {
                continue;
            }
            let lhs = &asts[i];
            let rhs = &asts[j];
            if crate::value::is_directed_ast_pair(lhs, rhs)
                && crate::value::is_ast_rewrite_pair(num_inputs, lhs, rhs)
            {
                indices.push((i, j));
            }
        }
    }
    indices
}

pub fn synthesized_to_rewrites(rules: &[SynthesizedRule]) -> Vec<Rewrite<ValueLang, ()>> {
    rules
        .iter()
        .filter_map(|r| parse_rewrite(&r.name, &r.lhs, &r.rhs).ok())
        .collect()
}

fn parse_rewrite(name: &str, lhs: &str, rhs: &str) -> Result<Rewrite<ValueLang, ()>, String> {
    let lhs_pat: Pattern<ValueLang> = lhs.parse().map_err(|e| format!("lhs {lhs}: {e}"))?;
    let rhs_pat: Pattern<ValueLang> = rhs.parse().map_err(|e| format!("rhs {rhs}: {e}"))?;
    Rewrite::new(name.to_string(), lhs_pat, rhs_pat).map_err(|e| e.to_string())
}

#[derive(Serialize)]
struct SynthesizedRulesOutput<'a> {
    random_tests_per_candidate: usize,
    count: usize,
    rules: &'a [SynthesizedRule],
}

pub fn print_synthesized_json(rules: &[SynthesizedRule], random_tests: usize) {
    let output = SynthesizedRulesOutput {
        random_tests_per_candidate: random_tests,
        count: rules.len(),
        rules,
    };
    let json = serde_json::to_string_pretty(&output).expect("serialize synthesized rules");
    println!("{json}");
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::semantics::synthesis_inputs;
    use crate::value::{ValueAst, enumerate_value_asts, is_directed_ast_pair};

    #[test]
    fn synthesis_inputs_excludes_empty() {
        let inputs = synthesis_inputs();
        assert_eq!(inputs.len(), 3);
        assert!(inputs.iter().all(|input| !input.is_empty()));
    }

    #[test]
    fn ast_pattern_for_mul_const2() {
        let mul = ValueAst::Mul(Box::new(ValueAst::Symbol(0)), Box::new(ValueAst::Const(2)));
        assert_eq!(mul.to_pattern(), "(i32.mul ?a 2)");
        assert!(!mul.to_pattern().contains("stack"));
    }

    #[test]
    fn ast_pattern_for_unary_ops() {
        let eqz = ValueAst::Eqz(Box::new(ValueAst::Symbol(0)));
        assert_eq!(eqz.to_pattern(), "(i32.eqz ?a)");
        let clz = ValueAst::Clz(Box::new(ValueAst::Symbol(0)));
        assert_eq!(clz.to_pattern(), "(i32.clz ?a)");
    }

    #[test]
    fn ast_pattern_for_relop() {
        let eq = ValueAst::Eq(
            Box::new(ValueAst::Symbol(0)),
            Box::new(ValueAst::Symbol(1)),
        );
        assert_eq!(eq.to_pattern(), "(i32.eq ?a ?b)");
    }

    #[test]
    fn ast_pattern_for_sub() {
        let sub = ValueAst::Sub(
            Box::new(ValueAst::Symbol(0)),
            Box::new(ValueAst::Const(1)),
        );
        assert_eq!(sub.to_pattern(), "(i32.sub ?a 1)");
    }

    #[test]
    fn value_ast_expr_roundtrip() {
        let ast = ValueAst::Mul(
            Box::new(ValueAst::Add(
                Box::new(ValueAst::Symbol(0)),
                Box::new(ValueAst::Const(1)),
            )),
            Box::new(ValueAst::Const(2)),
        );
        let expr = crate::value::value_ast_to_expr(&ast);
        let back = crate::value::value_ast_from_expr(&expr).expect("roundtrip");
        assert_eq!(ast, back);
    }

    #[test]
    fn directed_ast_pair_skips_larger_rhs() {
        let short = ValueAst::Mul(Box::new(ValueAst::Symbol(0)), Box::new(ValueAst::Const(2)));
        let long = ValueAst::Add(Box::new(ValueAst::Const(1)), Box::new(short.clone()));
        assert!(!is_directed_ast_pair(&short, &long));
        assert!(is_directed_ast_pair(&long, &short));
    }

    #[test]
    fn count_enumeration_scale_after_pruning() {
        let mut total_pairs = 0usize;
        for input in synthesis_inputs() {
            let asts: Vec<ValueAst> = enumerate_value_asts(4, input.len())
                .into_iter()
                .filter(|ast| ast.uses_each_symbol_once(input.len()))
                .collect();
            total_pairs += collect_candidate_indices(input.len(), &asts).len();
        }
        assert!(
            total_pairs < 6_000_000,
            "expected pruned pair count under 6M, got {total_pairs}"
        );
    }
}
