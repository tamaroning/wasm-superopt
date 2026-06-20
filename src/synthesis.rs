//! Exhaustive rule candidate generation and Z3 equivalence checking.

use crate::lang::ValueLang;
use crate::semantics::{StackTy, synthesis_inputs, z3_context};
use crate::value::{
    asts_valid_rewrite_random, asts_valid_rewrite_z3, enumerate_value_asts, is_ast_rewrite_pair,
    is_directed_ast_pair, ValueAst,
};
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

const RULES_CACHE_FORMAT_VERSION: u32 = 7;

/// AST size used in integration tests (≈ old `max_seq_len` 2).
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
    if cached.format_version != RULES_CACHE_FORMAT_VERSION
        || cached.max_ast_size != max_ast_size
    {
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
    report_progress(&format!("Saved {} rules to {}", rules.len(), path.display()));
}

pub fn load_or_synthesize_rules(max_ast_size: usize, random_tests: usize) -> Vec<SynthesizedRule> {
    if let Some(rules) = load_cached_rules(max_ast_size) {
        return rules;
    }
    let rules = synthesize_rules(max_ast_size, random_tests);
    save_cached_rules(max_ast_size, random_tests, &rules);
    rules
}

pub fn synthesize_rules(max_ast_size: usize, random_tests: usize) -> Vec<SynthesizedRule> {
    let ctx = z3_context();
    let inputs = synthesis_inputs();
    let mut proven = Vec::new();
    let mut seen = HashSet::new();
    let mut pairs_checked = 0usize;
    let mut z3_queries = 0usize;

    report_progress(&format!(
        "synthesis: max_ast_size={max_ast_size}, random_tests={random_tests}, {} input stacks",
        inputs.len()
    ));

    for (input_idx, input) in inputs.iter().enumerate() {
        let num_inputs = input.len();
        let stack_desc = format_input_stack(input);
        report_progress(&format!(
            "[{}/{}] input stack {stack_desc}: enumerating ASTs…",
            input_idx + 1,
            inputs.len()
        ));

        let asts: Vec<ValueAst> = enumerate_value_asts(max_ast_size, num_inputs)
            .into_iter()
            .filter(|ast| ast.uses_each_symbol_once(num_inputs))
            .collect();
        let total_pairs = count_candidate_pairs(num_inputs, &asts);

        report_progress(&format!(
            "  {} ASTs (all symbols used), {total_pairs} candidate pairs",
            asts.len()
        ));

        let mut pairs_in_input = 0usize;
        for i in 0..asts.len() {
            for j in 0..asts.len() {
                if i == j {
                    continue;
                }
                let lhs = &asts[i];
                let rhs = &asts[j];
                if !is_directed_ast_pair(lhs, rhs) {
                    continue;
                }
                if !is_ast_rewrite_pair(num_inputs, lhs, rhs) {
                    continue;
                }
                pairs_checked += 1;
                pairs_in_input += 1;

                let report_interval = (total_pairs / 20).clamp(1, 100);
                if pairs_in_input == 1
                    || pairs_in_input.is_multiple_of(report_interval)
                    || pairs_in_input == total_pairs
                {
                    report_progress(&format!(
                        "  pairs {pairs_in_input}/{total_pairs} (total {pairs_checked}), Z3 {z3_queries}, rules {}",
                        proven.len()
                    ));
                }

                if !asts_valid_rewrite_random(num_inputs, lhs, rhs, random_tests) {
                    continue;
                }
                z3_queries += 1;
                if !asts_valid_rewrite_z3(&ctx, num_inputs, lhs, rhs) {
                    continue;
                }
                let lhs_pat = lhs.to_pattern();
                let rhs_pat = rhs.to_pattern();
                let key = canonical_key(&lhs_pat, &rhs_pat);
                if !seen.insert(key) {
                    continue;
                }
                let name = format!("syn-{}", proven.len());
                proven.push(SynthesizedRule {
                    name,
                    lhs: lhs_pat,
                    rhs: rhs_pat,
                    input: input.clone(),
                });
                report_progress(&format!(
                    "  + rule {} ({} rules total)",
                    proven.last().expect("just pushed").name,
                    proven.len()
                ));
            }
        }

        report_progress(&format!(
            "  done input stack {stack_desc}: {} rules so far",
            proven.len()
        ));
    }

    report_progress(&format!(
        "synthesis complete: {pairs_checked} pairs checked, {z3_queries} Z3 queries, {} rules",
        proven.len()
    ));

    proven
}

fn count_candidate_pairs(num_inputs: usize, asts: &[ValueAst]) -> usize {
    let mut n = 0usize;
    for i in 0..asts.len() {
        for j in 0..asts.len() {
            if i == j {
                continue;
            }
            let lhs = &asts[i];
            let rhs = &asts[j];
            if is_directed_ast_pair(lhs, rhs) && is_ast_rewrite_pair(num_inputs, lhs, rhs) {
                n += 1;
            }
        }
    }
    n
}

fn canonical_key(lhs: &str, rhs: &str) -> (String, String) {
    if lhs <= rhs {
        (lhs.to_string(), rhs.to_string())
    } else {
        (rhs.to_string(), lhs.to_string())
    }
}

pub fn synthesized_to_rewrites(
    rules: &[SynthesizedRule],
) -> Vec<Rewrite<ValueLang, ()>> {
    rules
        .iter()
        .filter_map(|r| parse_rewrite(&r.name, &r.lhs, &r.rhs).ok())
        .collect()
}

fn parse_rewrite(
    name: &str,
    lhs: &str,
    rhs: &str,
) -> Result<Rewrite<ValueLang, ()>, String> {
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

pub fn print_synthesized(rules: &[SynthesizedRule], random_tests: usize) {
    println!("=== Synthesized rules (random + Z3-verified) ===");
    println!("random tests per candidate: {random_tests}");
    println!("count: {}", rules.len());
    for r in rules {
        println!(r#"rw!("{}"; "{}" => "{}")"#, r.name, r.lhs, r.rhs);
    }
    println!();
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
    use crate::value::{enumerate_value_asts, is_directed_ast_pair, ValueAst};

    #[test]
    fn synthesis_inputs_excludes_empty() {
        let inputs = synthesis_inputs();
        assert_eq!(inputs.len(), 3);
        assert!(inputs.iter().all(|input| !input.is_empty()));
    }

    #[test]
    fn ast_pattern_for_mul_const2() {
        let mul = ValueAst::Mul(
            Box::new(ValueAst::Symbol(0)),
            Box::new(ValueAst::Const(2)),
        );
        assert_eq!(mul.to_pattern(), "(i32.mul ?a 2)");
        assert!(!mul.to_pattern().contains("stack"));
    }

    #[test]
    fn directed_ast_pair_skips_larger_rhs() {
        let short = ValueAst::Mul(
            Box::new(ValueAst::Symbol(0)),
            Box::new(ValueAst::Const(2)),
        );
        let long = ValueAst::Add(
            Box::new(ValueAst::Const(1)),
            Box::new(short.clone()),
        );
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
            total_pairs += count_candidate_pairs(input.len(), &asts);
        }
        assert!(
            total_pairs < 100_000,
            "expected pruned pair count under 100k, got {total_pairs}"
        );
    }
}
