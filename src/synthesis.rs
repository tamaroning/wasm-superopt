//! Exhaustive rule candidate generation and Z3 equivalence checking.
//! Term enumeration follows Ruler (OOPSLA '21): e-graph hash-consing plus
//! equality-saturation compaction between size extensions.

use crate::al::z3_context;
use crate::lang::ValueLang;
use crate::ruler::{canonical_rewrite_key, discover_rules_for_signature};
use crate::value::{RuleSignature, enumerate_signatures, is_reachable};
use egg::{Pattern, Rewrite};
use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::fs;
use std::io::{self, Write};
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SynthesizedRule {
    pub name: String,
    pub lhs: String,
    pub rhs: String,
    pub signature: RuleSignature,
}

fn report_progress(msg: &str) {
    let _ = writeln!(io::stderr(), "{msg}");
    let _ = io::stderr().flush();
}

fn rules_cache_path(max_ast_size: usize) -> PathBuf {
    PathBuf::from(format!("rules-ast{max_ast_size}.cache"))
}

const RULES_CACHE_FORMAT_VERSION: u32 = 18;

/// AST size used in integration tests (≈ old `max_seq_len` 2).
#[cfg(test)]
pub const TEST_SYNTHESIS_AST_SIZE: usize = 3;

#[cfg(test)]
pub const TEST_SYNTHESIS_MAX_ARITY: usize = 3;

#[cfg(test)]
use std::sync::OnceLock;

#[cfg(test)]
static TEST_RULES_CACHE: OnceLock<Vec<SynthesizedRule>> = OnceLock::new();

/// Load rules for integration tests from `rules-ast{N}.cache` (never synthesizes).
#[cfg(test)]
pub fn test_synthesized_rules() -> &'static [SynthesizedRule] {
    TEST_RULES_CACHE.get_or_init(|| {
        load_cached_rules(TEST_SYNTHESIS_AST_SIZE, TEST_SYNTHESIS_MAX_ARITY).unwrap_or_else(
            || {
                panic!(
                    "missing {} — generate with: cargo run -- --synthesize-only --max-ast-size {} --max-arity {}",
                    rules_cache_path(TEST_SYNTHESIS_AST_SIZE).display(),
                    TEST_SYNTHESIS_AST_SIZE,
                    TEST_SYNTHESIS_MAX_ARITY,
                )
            },
        )
    })
}

#[cfg(test)]
pub fn test_synthesis_rewrites() -> Vec<Rewrite<ValueLang, ()>> {
    synthesized_to_rewrites(test_synthesized_rules())
}

#[derive(Serialize, Deserialize)]
struct CachedRules {
    format_version: u32,
    max_ast_size: usize,
    max_arity: usize,
    random_tests: usize,
    rules: Vec<SynthesizedRule>,
}

pub fn load_cached_rules(max_ast_size: usize, max_arity: usize) -> Option<Vec<SynthesizedRule>> {
    let path = rules_cache_path(max_ast_size);
    let data = fs::read_to_string(&path).ok()?;
    let cached: CachedRules = serde_json::from_str(&data).ok()?;
    if cached.format_version != RULES_CACHE_FORMAT_VERSION
        || cached.max_ast_size != max_ast_size
        || cached.max_arity != max_arity
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

fn save_cached_rules(
    max_ast_size: usize,
    max_arity: usize,
    random_tests: usize,
    rules: &[SynthesizedRule],
) {
    let path = rules_cache_path(max_ast_size);
    let cached = CachedRules {
        format_version: RULES_CACHE_FORMAT_VERSION,
        max_ast_size,
        max_arity,
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
    max_arity: usize,
    random_tests: usize,
    jobs: usize,
) -> Vec<SynthesizedRule> {
    if let Some(rules) = load_cached_rules(max_ast_size, max_arity) {
        return rules;
    }
    let rules = synthesize_rules(max_ast_size, max_arity, random_tests, jobs);
    save_cached_rules(max_ast_size, max_arity, random_tests, &rules);
    rules
}

pub fn synthesize_rules(
    max_ast_size: usize,
    max_arity: usize,
    random_tests: usize,
    jobs: usize,
) -> Vec<SynthesizedRule> {
    let signatures: Vec<RuleSignature> = enumerate_signatures(max_arity)
        .into_iter()
        .filter(|sig| is_reachable(sig))
        .collect();
    let total_sigs = signatures.len();

    report_progress(&format!(
        "synthesis (Ruler): max_ast_size={max_ast_size}, max_arity={max_arity}, random_tests={random_tests}, jobs={jobs}, {total_sigs} signatures"
    ));

    struct SigWork {
        sig: RuleSignature,
        rules: Vec<(String, String)>,
        pairs_checked: usize,
        z3_queries: usize,
    }

    fn synthesize_one_signature(
        sig: &RuleSignature,
        max_ast_size: usize,
        random_tests: usize,
        verify_jobs: usize,
    ) -> SigWork {
        let ctx = z3_context();
        let mut local_seen = HashSet::new();
        let mut local_rules = Vec::new();
        let (pairs_checked, z3_queries) = discover_rules_for_signature(
            sig,
            max_ast_size,
            random_tests,
            verify_jobs,
            &ctx,
            &mut local_seen,
            &mut local_rules,
        );
        SigWork {
            sig: sig.clone(),
            rules: local_rules,
            pairs_checked,
            z3_queries,
        }
    }

    let parallel_sigs = jobs > 1;
    let verify_jobs = if parallel_sigs { 1 } else { jobs.max(1) };

    let results: Vec<SigWork> = crate::parallel::run_with_threads(jobs, || {
        if parallel_sigs {
            use rayon::prelude::*;
            let done = AtomicUsize::new(0);
            signatures
                .par_iter()
                .map(|sig| {
                    let n = done.fetch_add(1, Ordering::Relaxed) + 1;
                    report_progress(&format!("[{n}/{total_sigs}] signature {sig}"));
                    synthesize_one_signature(sig, max_ast_size, random_tests, verify_jobs)
                })
                .collect()
        } else {
            let mut out = Vec::with_capacity(total_sigs);
            for (sig_idx, sig) in signatures.iter().enumerate() {
                report_progress(&format!("[{}/{}] signature {sig}", sig_idx + 1, total_sigs));
                out.push(synthesize_one_signature(
                    sig,
                    max_ast_size,
                    random_tests,
                    verify_jobs,
                ));
            }
            out
        }
    });

    let mut seen = HashSet::new();
    let mut proven = Vec::new();
    let mut pairs_checked = 0usize;
    let mut z3_queries = 0usize;

    for work in results {
        pairs_checked += work.pairs_checked;
        z3_queries += work.z3_queries;
        let added_here = work.rules.len();
        for (lhs, rhs) in work.rules {
            let key = canonical_rewrite_key(&lhs, &rhs);
            if !seen.insert(key) {
                continue;
            }
            let name = format!("syn-{}", proven.len());
            proven.push(SynthesizedRule {
                name,
                lhs,
                rhs,
                signature: work.sig.clone(),
            });
        }
        report_progress(&format!(
            "  done {}: +{added_here} rules ({total} total)",
            work.sig,
            total = proven.len()
        ));
    }

    report_progress(&format!(
        "synthesis complete: {pairs_checked} pairs checked, {z3_queries} Z3 queries, {} rules",
        proven.len()
    ));

    proven
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::semantics::StackTy;
    use crate::value::{ValueAst, ValueOp, is_ast_rewrite_pair, is_directed_ast_pair};

    #[test]
    fn constant_fold_rhs_allowed_in_rewrite_pair() {
        let sig = RuleSignature {
            inputs: vec![StackTy::I32],
            output: StackTy::I32,
        };
        let mul0 = ValueAst::app(
            ValueOp::I32Mul,
            vec![ValueAst::symbol(0), ValueAst::const_ty(StackTy::I32, 0)],
        );
        let zero = ValueAst::const_ty(StackTy::I32, 0);
        assert!(is_ast_rewrite_pair(&sig, &mul0, &zero));
    }

    #[test]
    fn reachable_signatures_exclude_unreachable_output() {
        let sigs: Vec<_> = enumerate_signatures(2)
            .into_iter()
            .filter(|sig| is_reachable(sig))
            .collect();
        assert!(sigs.iter().all(|sig| !sig.inputs.is_empty()));
        assert!(
            sigs.iter()
                .any(|sig| { sig.inputs == vec![StackTy::I32] && sig.output == StackTy::I64 })
        );
    }

    #[test]
    fn ast_pattern_for_mul_const2() {
        let mul = ValueAst::app(
            ValueOp::I32Mul,
            vec![ValueAst::symbol(0), ValueAst::const_ty(StackTy::I32, 2)],
        );
        assert_eq!(mul.to_pattern(), "(i32.mul ?a 2)");
        assert!(!mul.to_pattern().contains("stack"));
    }

    #[test]
    fn ast_pattern_for_unary_ops() {
        let eqz = ValueAst::app(ValueOp::I32Eqz, vec![ValueAst::symbol(0)]);
        assert_eq!(eqz.to_pattern(), "(i32.eqz ?a)");
        let clz = ValueAst::app(ValueOp::I32Clz, vec![ValueAst::symbol(0)]);
        assert_eq!(clz.to_pattern(), "(i32.clz ?a)");
    }

    #[test]
    fn ast_pattern_for_relop() {
        let eq = ValueAst::app(
            ValueOp::I32Eq,
            vec![ValueAst::symbol(0), ValueAst::symbol(1)],
        );
        assert_eq!(eq.to_pattern(), "(i32.eq ?a ?b)");
    }

    #[test]
    fn ast_pattern_for_sub() {
        let sub = ValueAst::app(
            ValueOp::I32Sub,
            vec![ValueAst::symbol(0), ValueAst::const_ty(StackTy::I32, 1)],
        );
        assert_eq!(sub.to_pattern(), "(i32.sub ?a 1)");
    }

    #[test]
    fn f32_ast_pattern_uses_float_literals() {
        let add = ValueAst::app(
            ValueOp::F32Add,
            vec![
                ValueAst::symbol(0),
                ValueAst::const_ty(StackTy::F32, f32::to_bits(-1.0) as i32 as i64),
            ],
        );
        assert_eq!(add.to_pattern(), "(f32.add ?a -1.0)");
        add.to_pattern()
            .parse::<egg::Pattern<crate::lang::ValueLang>>()
            .expect("f32 float literal pattern");
    }

    #[test]
    fn i64_ast_pattern_for_mul_const2() {
        let mul = ValueAst::app(
            ValueOp::I64Mul,
            vec![ValueAst::symbol(0), ValueAst::const_ty(StackTy::I64, 2)],
        );
        assert_eq!(mul.to_pattern(), "(i64.mul ?a 2)");
    }

    #[test]
    fn rules_cache_path_is_unified() {
        assert_eq!(rules_cache_path(3), PathBuf::from("rules-ast3.cache"));
    }

    #[test]
    fn value_ast_expr_roundtrip() {
        let ast = ValueAst::app(
            ValueOp::I32Mul,
            vec![
                ValueAst::app(
                    ValueOp::I32Add,
                    vec![ValueAst::symbol(0), ValueAst::const_ty(StackTy::I32, 1)],
                ),
                ValueAst::const_ty(StackTy::I32, 2),
            ],
        );
        let expr = crate::value::value_ast_to_expr(&ast);
        let back = crate::value::value_ast_from_expr(&expr).expect("roundtrip");
        assert_eq!(ast, back);
    }

    #[test]
    fn directed_ast_pair_skips_larger_rhs() {
        let short = ValueAst::app(
            ValueOp::I32Mul,
            vec![ValueAst::symbol(0), ValueAst::const_ty(StackTy::I32, 2)],
        );
        let long = ValueAst::app(
            ValueOp::I32Add,
            vec![ValueAst::const_ty(StackTy::I32, 1), short.clone()],
        );
        assert!(!is_directed_ast_pair(&short, &long));
        assert!(is_directed_ast_pair(&long, &short));
    }
}
