//! Exhaustive rule candidate generation and Z3 equivalence checking.

use crate::al::z3_context;
use crate::lang::ValueLang;
use crate::semantics::{StackTy, synthesis_inputs};
use crate::value::{
    ValueAst, asts_valid_rewrite_random, asts_valid_rewrite_z3, enumerate_value_asts,
    is_ast_rewrite_pair, is_directed_ast_pair,
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

const RULES_CACHE_FORMAT_VERSION: u32 = 10;

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
        "synthesis: max_ast_size={max_ast_size}, random_tests={random_tests}, jobs={jobs}, {} input stacks",
        inputs.len()
    ));

    crate::parallel::run_with_threads(jobs, || {
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
            let candidates = collect_candidate_indices(num_inputs, &asts);
            let total_pairs = candidates.len();

            report_progress(&format!(
                "  {} ASTs (all symbols used), {total_pairs} candidate pairs",
                asts.len()
            ));

            let batch = if jobs <= 1 {
                check_candidates_sequential(
                    num_inputs,
                    &asts,
                    &candidates,
                    random_tests,
                    &mut pairs_checked,
                    &mut z3_queries,
                    total_pairs,
                    proven.len(),
                )
            } else {
                let (batch, checked, z3) = check_candidates_parallel(
                    num_inputs,
                    &asts,
                    &candidates,
                    random_tests,
                    jobs,
                    proven.len(),
                );
                pairs_checked += checked;
                z3_queries += z3;
                batch
            };

            for rule in batch {
                if seen.insert(rule.key) {
                    let name = format!("syn-{}", proven.len());
                    proven.push(SynthesizedRule {
                        name,
                        lhs: rule.lhs_pat,
                        rhs: rule.rhs_pat,
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
    });

    report_progress(&format!(
        "synthesis complete: {pairs_checked} pairs checked, {z3_queries} Z3 queries, {} rules",
        proven.len()
    ));

    proven
}

struct CandidateRule {
    key: (String, String),
    lhs_pat: String,
    rhs_pat: String,
}

const PAIR_REPORT_INTERVAL: usize = 1000;

fn should_report_pair_progress(done: usize, total_pairs: usize) -> bool {
    done.is_multiple_of(PAIR_REPORT_INTERVAL) || done == total_pairs
}

fn check_candidates_sequential(
    num_inputs: usize,
    asts: &[ValueAst],
    candidates: &[(usize, usize)],
    random_tests: usize,
    pairs_checked: &mut usize,
    z3_queries: &mut usize,
    total_pairs: usize,
    rules_so_far: usize,
) -> Vec<CandidateRule> {
    let ctx = z3_context();
    let mut found = Vec::new();
    for (pairs_in_input, &(i, j)) in candidates.iter().enumerate() {
        let lhs = &asts[i];
        let rhs = &asts[j];
        *pairs_checked += 1;
        let done = pairs_in_input + 1;

        if should_report_pair_progress(done, total_pairs) {
            report_progress(&format!(
                "  pairs {done}/{total_pairs} (total {pairs_checked}), Z3 {z3_queries}, rules {}",
                rules_so_far + found.len(),
            ));
        }

        if !asts_valid_rewrite_random(num_inputs, lhs, rhs, random_tests) {
            continue;
        }
        *z3_queries += 1;
        if !asts_valid_rewrite_z3(&ctx, num_inputs, lhs, rhs) {
            continue;
        }
        let lhs_pat = lhs.to_pattern();
        let rhs_pat = rhs.to_pattern();
        found.push(CandidateRule {
            key: canonical_key(&lhs_pat, &rhs_pat),
            lhs_pat,
            rhs_pat,
        });
    }
    found
}

fn check_candidates_parallel(
    num_inputs: usize,
    asts: &[ValueAst],
    candidates: &[(usize, usize)],
    random_tests: usize,
    jobs: usize,
    rules_so_far: usize,
) -> (Vec<CandidateRule>, usize, usize) {
    use rayon::prelude::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    let pairs_done = AtomicUsize::new(0);
    let z3_done = AtomicUsize::new(0);
    let rules_found = AtomicUsize::new(0);
    let total_pairs = candidates.len();

    report_progress(&format!("  checking {total_pairs} pairs with {jobs} threads…"));

    let found: Vec<CandidateRule> = candidates
        .par_iter()
        .filter_map(|&(i, j)| {
            let lhs = &asts[i];
            let rhs = &asts[j];
            let n = pairs_done.fetch_add(1, Ordering::Relaxed) + 1;
            if should_report_pair_progress(n, total_pairs) {
                report_progress(&format!(
                    "  pairs {n}/{total_pairs}, Z3 {}, rules {}",
                    z3_done.load(Ordering::Relaxed),
                    rules_so_far + rules_found.load(Ordering::Relaxed),
                ));
            }
            if !asts_valid_rewrite_random(num_inputs, lhs, rhs, random_tests) {
                return None;
            }
            z3_done.fetch_add(1, Ordering::Relaxed);
            let ctx = z3_context();
            if !asts_valid_rewrite_z3(&ctx, num_inputs, lhs, rhs) {
                return None;
            }
            rules_found.fetch_add(1, Ordering::Relaxed);
            let lhs_pat = lhs.to_pattern();
            let rhs_pat = rhs.to_pattern();
            Some(CandidateRule {
                key: canonical_key(&lhs_pat, &rhs_pat),
                lhs_pat,
                rhs_pat,
            })
        })
        .collect();

    let checked = pairs_done.load(Ordering::Relaxed);
    let z3 = z3_done.load(Ordering::Relaxed);
    report_progress(&format!(
        "  parallel check done: {checked} pairs, {z3} Z3 queries, {} candidates, {} rules",
        found.len(),
        rules_so_far + rules_found.load(Ordering::Relaxed),
    ));
    (found, checked, z3)
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
            if is_directed_ast_pair(lhs, rhs) && is_ast_rewrite_pair(num_inputs, lhs, rhs) {
                indices.push((i, j));
            }
        }
    }
    indices
}

fn canonical_key(lhs: &str, rhs: &str) -> (String, String) {
    if lhs <= rhs {
        (lhs.to_string(), rhs.to_string())
    } else {
        (rhs.to_string(), lhs.to_string())
    }
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
