//! Ruler-style term enumeration modulo equivalence (OOPSLA '21 §3.2).
//!
//! Terms live in an e-graph (hash-consing). After each size extension we equality-
//! saturate with proven rules, then match characteristic vectors across e-classes.

use crate::lang::ValueLang;
use crate::semantics::{StackTy, synthesis_const_values};
use crate::value::{
    AstEvalSignature, RuleSignature, ValueAst, ValueOp, asts_valid_rewrite_random,
    asts_valid_rewrite_z3, cvec_test_inputs, is_ast_rewrite_pair, is_directed_ast_pair,
    value_ast_from_expr, value_ast_to_expr,
};
use egg::{AstSize, EGraph, Extractor, Id, Pattern, RecExpr, Rewrite, Runner};
use std::collections::{HashMap, HashSet};
use std::io::{self, Write};

const EQSAT_ITER_LIMIT: usize = 20;
const EQSAT_NODE_LIMIT: usize = 100_000;

/// Stack sorts for which Ruler term enumeration builds e-graph terms each size step.
const SYNTH_SORTS: [StackTy; 4] = [StackTy::I32, StackTy::I64, StackTy::F32, StackTy::F64];

fn report(msg: &str) {
    let _ = writeln!(io::stderr(), "{msg}");
    let _ = io::stderr().flush();
}

/// Term set `T` backed by an e-graph, with Ruler-style incremental enumeration.
pub struct RulerTermSet {
    sig: RuleSignature,
    egraph: EGraph<ValueLang, ()>,
    /// Per-sort buckets of canonical e-class ids by AST size.
    classes_by_size: HashMap<StackTy, Vec<HashSet<usize>>>,
    class_cvec: HashMap<usize, AstEvalSignature>,
    test_inputs: Vec<Vec<i64>>,
}

impl RulerTermSet {
    pub fn new(sig: RuleSignature) -> Self {
        Self {
            test_inputs: cvec_test_inputs(&sig),
            sig,
            egraph: EGraph::default(),
            classes_by_size: HashMap::new(),
            class_cvec: HashMap::new(),
        }
    }

    pub fn num_classes(&self) -> usize {
        self.egraph.number_of_classes()
    }

    pub fn num_nodes(&self) -> usize {
        self.egraph.total_size()
    }

    /// Add all well-typed terms of sort `sort` with AST node count `size`.
    pub fn add_terms_of_size(&mut self, sort: StackTy, size: usize) {
        if size == 0 {
            return;
        }
        self.ensure_size_buckets(sort, size);

        if size == 1 {
            let sym_indices: Vec<usize> = self
                .sig
                .inputs
                .iter()
                .enumerate()
                .filter(|(_, ty)| **ty == sort)
                .map(|(i, _)| i)
                .collect();
            for i in sym_indices {
                self.add_ast(&ValueAst::symbol(i));
            }
            for &c in synthesis_const_values(sort) {
                self.add_ast(&ValueAst::const_ty(sort, c));
            }
            return;
        }

        for op in ValueOp::ops_with_result(sort) {
            let pops = op.pops();
            match pops.len() {
                1 => {
                    let child_sort = pops[0];
                    let child_classes = self.classes_for_sort(child_sort, size - 1);
                    for &class in &child_classes {
                        let child = Id::from(class);
                        let id = self.egraph.add(op.to_enode(&[child]));
                        self.register_id(id);
                    }
                }
                2 => {
                    let left_sort = pops[0];
                    let right_sort = pops[1];
                    for left_sz in 1..size {
                        let right_sz = size - 1 - left_sz;
                        if right_sz == 0 {
                            continue;
                        }
                        let left_classes = self.classes_for_sort(left_sort, left_sz);
                        let right_classes = self.classes_for_sort(right_sort, right_sz);
                        for &left in &left_classes {
                            for &right in &right_classes {
                                let l = Id::from(left);
                                let r = Id::from(right);
                                let id = self.egraph.add(op.to_enode(&[l, r]));
                                self.register_id(id);
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }

    /// Equality-saturate a copy of `T` with `rules`, then merge learned equivalences back.
    pub fn compact_with_rules(&mut self, rules: &[Rewrite<ValueLang, ()>]) {
        if rules.is_empty() {
            return;
        }
        let original_size = self.egraph.total_size();
        if original_size == 0 {
            return;
        }
        report(&format!(
            "  compacting {original_size} e-nodes with {} rules…",
            rules.len()
        ));
        let snapshot = self.egraph.clone();
        let saturated = Runner::default()
            .with_iter_limit(EQSAT_ITER_LIMIT)
            .with_node_limit(EQSAT_NODE_LIMIT)
            .with_egraph(snapshot)
            .run(rules);

        apply_saturation_merges(&mut self.egraph, &saturated.egraph, original_size);
        self.rebuild_class_index();
        report(&format!(
            "  compacted to {} e-classes",
            self.egraph.number_of_classes()
        ));
    }

    /// Pairs of ASTs from distinct e-classes with matching characteristic vectors.
    pub fn cvec_match_pairs(&self) -> Vec<(ValueAst, ValueAst)> {
        if self.class_cvec.is_empty() {
            return Vec::new();
        }
        report(&format!(
            "  cvec matching {} classes…",
            self.class_cvec.len()
        ));

        let mut rep_cache: HashMap<usize, ValueAst> = HashMap::with_capacity(self.class_cvec.len());
        for &class in self.class_cvec.keys() {
            if let Some(ast) = self.class_rep(class) {
                rep_cache.insert(class, ast);
            }
        }

        let mut by_sig: HashMap<&AstEvalSignature, Vec<usize>> = HashMap::new();
        for (&class, sig) in &self.class_cvec {
            by_sig.entry(sig).or_default().push(class);
        }

        let mut pairs = Vec::new();
        let mut seen = HashSet::new();

        for classes in by_sig.values() {
            if classes.len() < 2 {
                continue;
            }
            for i in 0..classes.len() {
                for j in 0..classes.len() {
                    if i == j {
                        continue;
                    }
                    let lhs = rep_cache.get(&classes[i]);
                    let rhs = rep_cache.get(&classes[j]);
                    let (Some(lhs), Some(rhs)) = (lhs, rhs) else {
                        continue;
                    };
                    if !is_ast_rewrite_pair(&self.sig, lhs, rhs) {
                        continue;
                    }
                    if !is_directed_ast_pair(lhs, rhs) {
                        continue;
                    }
                    let key = (lhs.to_pattern(), rhs.to_pattern());
                    if seen.insert(key) {
                        pairs.push((lhs.clone(), rhs.clone()));
                    }
                }
            }
        }
        if !pairs.is_empty() {
            report(&format!("  found {} cvec candidate pairs", pairs.len()));
        }
        pairs
    }

    fn classes_for_sort(&self, sort: StackTy, size: usize) -> HashSet<usize> {
        self.classes_by_size
            .get(&sort)
            .and_then(|buckets| buckets.get(size.saturating_sub(1)))
            .cloned()
            .unwrap_or_default()
    }

    fn ensure_size_buckets(&mut self, sort: StackTy, size: usize) {
        let buckets = self.classes_by_size.entry(sort).or_default();
        while buckets.len() < size {
            buckets.push(HashSet::new());
        }
    }

    fn add_ast(&mut self, ast: &ValueAst) {
        let expr = value_ast_to_expr(ast);
        let id = self.egraph.add_expr(&expr);
        self.register_id(id);
    }

    fn register_id(&mut self, id: Id) {
        let class = usize::from(self.egraph.find(id));
        let Some(ast) = self.class_rep(class) else {
            return;
        };
        if let Some(sort) = ast.type_of(&self.sig) {
            let sz = ast.size();
            self.ensure_size_buckets(sort, sz);
            self.classes_by_size
                .get_mut(&sort)
                .unwrap()
                .get_mut(sz - 1)
                .unwrap()
                .insert(class);
        }
        if ast.uses_each_symbol_once(&self.sig)
            || matches!(ast, ValueAst::Const { ty, .. } if ty == self.sig.output)
        {
            let sig = AstEvalSignature::of(&ast, &self.sig, &self.test_inputs);
            self.class_cvec.insert(class, sig);
        }
    }

    fn rebuild_class_index(&mut self) {
        self.classes_by_size.clear();
        self.class_cvec.clear();
        let class_ids: Vec<Id> = self.egraph.classes().map(|c| c.id).collect();
        let total = class_ids.len();
        if total > 1_000 {
            report(&format!("  reindexing {total} e-classes…"));
        }
        for (n, id) in class_ids.iter().enumerate() {
            self.register_id(*id);
            if total > 1_000 && (n + 1).is_multiple_of(2_000) {
                report(&format!("  reindexing {}/{} e-classes…", n + 1, total));
            }
        }
    }

    fn class_rep(&self, class: usize) -> Option<ValueAst> {
        let id = Id::from(class);
        if usize::from(id) >= self.egraph.total_size() {
            return None;
        }
        let extractor = Extractor::new(&self.egraph, AstSize);
        let (_, best): (usize, RecExpr<ValueLang>) = extractor.find_best(id);
        value_ast_from_expr(&best)
    }
}

fn apply_saturation_merges(
    egraph: &mut EGraph<ValueLang, ()>,
    saturated: &EGraph<ValueLang, ()>,
    original_size: usize,
) {
    let mut groups: HashMap<usize, Vec<usize>> = HashMap::new();
    for i in 0..original_size {
        let id = Id::from(i);
        let canon = usize::from(saturated.find(id));
        groups.entry(canon).or_default().push(i);
    }
    for members in groups.values() {
        if members.len() < 2 {
            continue;
        }
        let leader = Id::from(members[0]);
        for &m in &members[1..] {
            egraph.union(leader, Id::from(m));
        }
    }
    egraph.rebuild();
}

const VERIFY_REPORT_INTERVAL: usize = 500;

fn report_verify_progress(done: usize, total: usize) {
    if done == total || done.is_multiple_of(VERIFY_REPORT_INTERVAL) {
        report(&format!("  verifying {done}/{total} candidates…"));
    }
}

/// Ruler core loop for one rule signature: enumerate by size, compact, cvec-match, verify.
///
/// `verify_jobs`: parallel candidate verification (`par_iter`); use `1` when signatures
/// are already processed in parallel to avoid oversubscribing threads.
pub fn discover_rules_for_signature(
    sig: &RuleSignature,
    max_ast_size: usize,
    random_tests: usize,
    verify_jobs: usize,
    ctx: &z3::Context,
    proven_keys: &mut HashSet<(String, String)>,
    rules_out: &mut Vec<(String, String)>,
) -> (usize, usize) {
    let mut rewrites: Vec<Rewrite<ValueLang, ()>> = Vec::new();
    let mut term_set = RulerTermSet::new(sig.clone());
    let mut pairs_checked = 0usize;
    let mut z3_queries = 0usize;

    for size in 1..=max_ast_size {
        for &sort in &SYNTH_SORTS {
            term_set.add_terms_of_size(sort, size);
        }
        report(&format!(
            "  size {size}: {} e-classes, {} e-nodes",
            term_set.num_classes(),
            term_set.num_nodes()
        ));

        loop {
            term_set.compact_with_rules(&rewrites);
            let candidates = minimize_rhs_per_lhs(term_set.cvec_match_pairs());
            if candidates.is_empty() {
                break;
            }

            report(&format!(
                "  size {size}: verifying {} candidates…",
                candidates.len()
            ));

            let new_rules = if verify_jobs <= 1 {
                verify_candidates(
                    sig,
                    &candidates,
                    random_tests,
                    ctx,
                    proven_keys,
                    &mut pairs_checked,
                    &mut z3_queries,
                )
            } else {
                verify_candidates_parallel(
                    sig,
                    &candidates,
                    random_tests,
                    proven_keys,
                    &mut pairs_checked,
                    &mut z3_queries,
                )
            };

            if new_rules.is_empty() {
                break;
            }

            let before = rules_out.len();
            for (lhs_pat, rhs_pat) in new_rules {
                let name = format!("syn-{}", rules_out.len());
                match Rewrite::<ValueLang, ()>::new(
                    name,
                    lhs_pat.parse::<Pattern<ValueLang>>().expect("lhs pattern"),
                    rhs_pat.parse::<Pattern<ValueLang>>().expect("rhs pattern"),
                ) {
                    Ok(rw) => {
                        rewrites.push(rw);
                        rules_out.push((lhs_pat, rhs_pat));
                    }
                    Err(_) => {}
                }
            }
            let added = rules_out.len() - before;
            if added > 0 {
                report(&format!(
                    "  size {size}: checked {} candidates, +{added} rules ({})",
                    candidates.len(),
                    rules_out.len()
                ));
            }
        }
    }

    (pairs_checked, z3_queries)
}

fn verify_candidates(
    sig: &RuleSignature,
    candidates: &[(ValueAst, ValueAst)],
    random_tests: usize,
    ctx: &z3::Context,
    proven_keys: &mut HashSet<(String, String)>,
    pairs_checked: &mut usize,
    z3_queries: &mut usize,
) -> Vec<(String, String)> {
    let total = candidates.len();
    let mut found = Vec::new();
    for (n, (lhs, rhs)) in candidates.iter().enumerate() {
        *pairs_checked += 1;
        report_verify_progress(n + 1, total);
        if !asts_valid_rewrite_random(sig, lhs, rhs, random_tests) {
            continue;
        }
        *z3_queries += 1;
        if !asts_valid_rewrite_z3(ctx, sig, lhs, rhs) {
            continue;
        }
        let lhs_pat = lhs.to_pattern();
        let rhs_pat = rhs.to_pattern();
        let key = canonical_key(&lhs_pat, &rhs_pat);
        if proven_keys.insert(key) {
            found.push((lhs_pat, rhs_pat));
        }
    }
    found
}

fn verify_candidates_parallel(
    sig: &RuleSignature,
    candidates: &[(ValueAst, ValueAst)],
    random_tests: usize,
    proven_keys: &mut HashSet<(String, String)>,
    pairs_checked: &mut usize,
    z3_queries: &mut usize,
) -> Vec<(String, String)> {
    use rayon::prelude::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    let z3_done = AtomicUsize::new(0);
    let total = candidates.len();
    let done = AtomicUsize::new(0);
    let found: Vec<(String, String)> = candidates
        .par_iter()
        .filter_map(|(lhs, rhs)| {
            let n = done.fetch_add(1, Ordering::Relaxed) + 1;
            report_verify_progress(n, total);
            if !asts_valid_rewrite_random(sig, lhs, rhs, random_tests) {
                return None;
            }
            let ctx = crate::al::z3_context();
            if !asts_valid_rewrite_z3(&ctx, sig, lhs, rhs) {
                return None;
            }
            z3_done.fetch_add(1, Ordering::Relaxed);
            let lhs_pat = lhs.to_pattern();
            let rhs_pat = rhs.to_pattern();
            Some((lhs_pat, rhs_pat))
        })
        .collect();

    *pairs_checked += candidates.len();
    *z3_queries += z3_done.load(Ordering::Relaxed);

    let mut unique = Vec::new();
    for (lhs_pat, rhs_pat) in found {
        let key = canonical_key(&lhs_pat, &rhs_pat);
        if proven_keys.insert(key) {
            unique.push((lhs_pat, rhs_pat));
        }
    }
    unique
}

fn canonical_key(lhs: &str, rhs: &str) -> (String, String) {
    if lhs <= rhs {
        (lhs.to_string(), rhs.to_string())
    } else {
        (rhs.to_string(), lhs.to_string())
    }
}

/// Dedup key for rewrite rules merged across parallel signature workers.
pub fn canonical_rewrite_key(lhs: &str, rhs: &str) -> (String, String) {
    canonical_key(lhs, rhs)
}

/// For each LHS pattern, keep only the smallest RHS (prefer `0` over `(i32.shr_s 0 ?a)`).
fn minimize_rhs_per_lhs(pairs: Vec<(ValueAst, ValueAst)>) -> Vec<(ValueAst, ValueAst)> {
    let mut best: HashMap<String, (ValueAst, ValueAst)> = HashMap::new();
    for (lhs, rhs) in pairs {
        let key = lhs.to_pattern();
        let replace = match best.get(&key) {
            None => true,
            Some((_, prev_rhs)) => rhs.size() < prev_rhs.size(),
        };
        if replace {
            best.insert(key, (lhs, rhs));
        }
    }
    best.into_values().collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::{RuleSignature, StackTy};

    #[test]
    fn i64_add_zero_concrete_matches_symbol() {
        use crate::al::eval_value_ast_concrete_sig;

        let sig = RuleSignature {
            inputs: vec![StackTy::I64],
            output: StackTy::I64,
        };
        let sym = ValueAst::symbol(0);
        let add0 = ValueAst::app(
            ValueOp::I64Add,
            vec![ValueAst::symbol(0), ValueAst::const_ty(StackTy::I64, 0)],
        );
        let xor0 = ValueAst::app(
            ValueOp::I64Xor,
            vec![ValueAst::symbol(0), ValueAst::const_ty(StackTy::I64, 0)],
        );
        for &v in &[0i64, 1, -1, 2, i64::MIN, i64::MAX] {
            let inputs = vec![v];
            let sym_r = eval_value_ast_concrete_sig(&sig, &sym, &inputs);
            let add_r = eval_value_ast_concrete_sig(&sig, &add0, &inputs);
            let xor_r = eval_value_ast_concrete_sig(&sig, &xor0, &inputs);
            eprintln!(
                "v={v:#x}: sym={:?} add={:?} xor={:?}",
                sym_r, add_r, xor_r
            );
            assert_eq!(
                (sym_r.trap, sym_r.value),
                (add_r.trap, add_r.value),
                "i64.add ?a 0 should equal ?a at v={v}"
            );
        }
    }

    #[test]
    fn i64_add_zero_should_rewrite_to_symbol() {
        use crate::al::z3_context;
        use crate::value::{asts_valid_rewrite_random, asts_valid_rewrite_z3};

        let sig = RuleSignature {
            inputs: vec![StackTy::I64],
            output: StackTy::I64,
        };
        let lhs = ValueAst::app(
            ValueOp::I64Add,
            vec![ValueAst::symbol(0), ValueAst::const_ty(StackTy::I64, 0)],
        );
        let rhs = ValueAst::symbol(0);
        let xor_rhs = ValueAst::app(
            ValueOp::I64Xor,
            vec![
                ValueAst::const_ty(StackTy::I64, 0),
                ValueAst::symbol(0),
            ],
        );
        assert!(
            asts_valid_rewrite_random(&sig, &lhs, &rhs, 100),
            "i64.add ?a 0 should match ?a on random inputs"
        );
        let ctx = z3_context();
        assert!(
            asts_valid_rewrite_z3(&ctx, &sig, &lhs, &rhs),
            "Z3 should prove i64.add ?a 0 = ?a"
        );
        assert!(
            asts_valid_rewrite_z3(&ctx, &sig, &xor_rhs, &rhs),
            "Z3 should prove i64.xor 0 ?a = ?a"
        );
    }

    #[test]
    fn i64_unary_signature_discovers_zero_add_identity() {
        use crate::al::z3_context;
        use std::collections::HashSet;

        let sig = RuleSignature {
            inputs: vec![StackTy::I64],
            output: StackTy::I64,
        };
        let ctx = z3_context();
        let mut proven = HashSet::new();
        let mut rules = Vec::new();
        let (pairs, z3) = discover_rules_for_signature(&sig, 3, 100, 1, &ctx, &mut proven, &mut rules);
        eprintln!("i64 unary: {pairs} pairs, {z3} z3 queries, {} rules", rules.len());
        for (lhs, rhs) in &rules {
            if lhs.contains("add") && lhs.contains("0") {
                eprintln!("  add-zero rule: {lhs} -> {rhs}");
            }
            if lhs.contains("xor") && lhs.contains("0") {
                eprintln!("  xor-zero rule: {lhs} -> {rhs}");
            }
        }
        assert!(
            rules
                .iter()
                .any(|(lhs, rhs)| lhs == "(i64.add ?a 0)" && rhs == "?a"),
            "expected (i64.add ?a 0) -> ?a, got add rules: {:?}",
            rules
                .iter()
                .filter(|(l, _)| l.contains("add"))
                .collect::<Vec<_>>()
        );
        assert!(
            rules
                .iter()
                .any(|(lhs, rhs)| lhs == "(i64.xor 0 ?a)" && rhs == "?a"),
            "expected (i64.xor 0 ?a) -> ?a for transitive identity, got xor rules: {:?}",
            rules
                .iter()
                .filter(|(l, _)| l.contains("xor"))
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn f32_signature_builds_float_terms() {
        let sig = RuleSignature {
            inputs: vec![StackTy::F32],
            output: StackTy::F32,
        };
        let mut term_set = RulerTermSet::new(sig);
        for size in 1..=3 {
            for &sort in &SYNTH_SORTS {
                term_set.add_terms_of_size(sort, size);
            }
        }
        assert!(
            term_set.num_classes() > 4,
            "F32 sig should grow beyond input/const leaves, got {} classes",
            term_set.num_classes()
        );
    }
}
