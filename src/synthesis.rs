//! Exhaustive rule candidate generation and Z3 equivalence checking.

use crate::lang::WasmLang;
use crate::semantics::{
    OpCatalog, StackTy, concrete_ops, enumerate_sequences_by_output, exploration_inputs,
    is_type_valid, same_stack_effect, sequences_valid_rewrite_random, sequences_valid_rewrite_z3,
    uses_all_input_slots, z3_context,
};
use crate::stack::sem_sequence_to_pattern;
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

fn rules_cache_path(max_len: usize) -> PathBuf {
    PathBuf::from(format!("rules-len{max_len}.cache"))
}

const RULES_CACHE_FORMAT_VERSION: u32 = 2;

#[derive(Serialize, Deserialize)]
struct CachedRules {
    format_version: u32,
    max_seq_len: usize,
    random_tests: usize,
    rules: Vec<SynthesizedRule>,
}

pub fn load_cached_rules(max_len: usize) -> Option<Vec<SynthesizedRule>> {
    let path = rules_cache_path(max_len);
    let data = fs::read_to_string(&path).ok()?;
    let cached: CachedRules = serde_json::from_str(&data).ok()?;
    if cached.format_version != RULES_CACHE_FORMAT_VERSION || cached.max_seq_len != max_len {
        return None;
    }
    report_progress(&format!(
        "loaded {} rules from {}",
        cached.rules.len(),
        path.display()
    ));
    Some(cached.rules)
}

fn save_cached_rules(max_len: usize, random_tests: usize, rules: &[SynthesizedRule]) {
    let path = rules_cache_path(max_len);
    let cached = CachedRules {
        format_version: RULES_CACHE_FORMAT_VERSION,
        max_seq_len: max_len,
        random_tests,
        rules: rules.to_vec(),
    };
    let json = serde_json::to_string_pretty(&cached).expect("serialize rules cache");
    fs::write(&path, json).expect("write rules cache");
    report_progress(&format!("saved {} rules to {}", rules.len(), path.display()));
}

pub fn load_or_synthesize_rules(max_len: usize, random_tests: usize) -> Vec<SynthesizedRule> {
    if let Some(rules) = load_cached_rules(max_len) {
        return rules;
    }
    let rules = synthesize_rules(max_len, random_tests);
    save_cached_rules(max_len, random_tests, &rules);
    rules
}

pub fn synthesize_rules(max_len: usize, random_tests: usize) -> Vec<SynthesizedRule> {
    let ctx = z3_context();
    let ops = concrete_ops();
    let catalog = OpCatalog::from_ops(&ops);
    let inputs = exploration_inputs();
    let mut proven = Vec::new();
    let mut seen = HashSet::new();
    let mut pairs_checked = 0usize;
    let mut z3_queries = 0usize;

    report_progress(&format!(
        "synthesis: max_seq_len={max_len}, random_tests={random_tests}, {} input stacks",
        inputs.len()
    ));

    for (input_idx, input) in inputs.iter().enumerate() {
        let stack_desc = format_input_stack(input);
        report_progress(&format!(
            "[{}/{}] input stack {stack_desc}: enumerating sequences…",
            input_idx + 1,
            inputs.len()
        ));

        let by_output = enumerate_sequences_by_output(input, &catalog, max_len);
        let sequence_count: usize = by_output.values().map(|seqs| seqs.len()).sum();

        let total_pairs: usize = by_output
            .values()
            .map(|seqs| {
                let n = seqs.len();
                n.saturating_mul(n.saturating_sub(1)) / 2
            })
            .sum();

        report_progress(&format!(
            "  {sequence_count} sequences, {} output classes, {total_pairs} candidate pairs",
            by_output.len()
        ));

        let mut pairs_in_input = 0usize;
        for (out_sig, seqs) in &by_output {
            for i in 0..seqs.len() {
                for j in (i + 1)..seqs.len() {
                    let lhs = &seqs[i];
                    let rhs = &seqs[j];
                    if lhs == rhs
                        || !is_type_valid(input, lhs)
                        || !is_type_valid(input, rhs)
                        || !uses_all_input_slots(input, lhs)
                        || !uses_all_input_slots(input, rhs)
                        || !same_stack_effect(input, lhs, rhs)
                    {
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

                    if !sequences_valid_rewrite_random(input, lhs, rhs, random_tests) {
                        continue;
                    }
                    z3_queries += 1;
                    if !sequences_valid_rewrite_z3(&ctx, input, lhs, rhs) {
                        continue;
                    }
                    let Some(lhs_pat) = sem_sequence_to_pattern(input, lhs) else {
                        continue;
                    };
                    let Some(rhs_pat) = sem_sequence_to_pattern(input, rhs) else {
                        continue;
                    };
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
                    let _ = out_sig;
                }
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

fn canonical_key(lhs: &str, rhs: &str) -> (String, String) {
    if lhs <= rhs {
        (lhs.to_string(), rhs.to_string())
    } else {
        (rhs.to_string(), lhs.to_string())
    }
}

pub fn synthesized_to_rewrites(
    rules: &[SynthesizedRule],
) -> Vec<Rewrite<WasmLang, ()>> {
    rules
        .iter()
        .filter_map(|r| parse_rewrite(&r.name, &r.lhs, &r.rhs).ok())
        .collect()
}

fn parse_rewrite(
    name: &str,
    lhs: &str,
    rhs: &str,
) -> Result<Rewrite<WasmLang, ()>, String> {
    let lhs_pat: Pattern<WasmLang> = lhs.parse().map_err(|e| format!("lhs {lhs}: {e}"))?;
    let rhs_pat: Pattern<WasmLang> = rhs.parse().map_err(|e| format!("rhs {rhs}: {e}"))?;
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
