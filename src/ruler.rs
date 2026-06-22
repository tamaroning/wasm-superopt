//! Ruler-style term enumeration modulo equivalence (OOPSLA '21 §3.2).
//!
//! Terms live in an e-graph (hash-consing). After each size extension we equality-
//! saturate with proven rules, then match characteristic vectors across e-classes.

use crate::lang::ValueLang;
use crate::semantics::synthesis_constants;
use crate::value::{
    AstEvalSignature, ValueAst, ValueBinOp, ValueUnOp, asts_valid_rewrite_random,
    asts_valid_rewrite_z3, binop_enode, cvec_test_inputs, is_ast_rewrite_pair,
    is_directed_ast_pair, unop_enode, value_ast_from_expr,
    value_ast_to_expr,
};
use egg::{AstSize, EGraph, Extractor, Id, Pattern, RecExpr, Rewrite, Runner};
use std::collections::{HashMap, HashSet};
use std::io::{self, Write};

const EQSAT_ITER_LIMIT: usize = 20;
const EQSAT_NODE_LIMIT: usize = 100_000;

fn report(msg: &str) {
    let _ = writeln!(io::stderr(), "{msg}");
    let _ = io::stderr().flush();
}

/// Term set `T` backed by an e-graph, with Ruler-style incremental enumeration.
pub struct RulerTermSet {
    egraph: EGraph<ValueLang, ()>,
    /// Canonical e-class ids that have a valid representative of each AST size.
    classes_by_size: Vec<HashSet<usize>>,
    class_cvec: HashMap<usize, AstEvalSignature>,
    test_inputs: Vec<Vec<i32>>,
}

impl RulerTermSet {
    pub fn new(num_inputs: usize) -> Self {
        Self {
            egraph: EGraph::default(),
            classes_by_size: Vec::new(),
            class_cvec: HashMap::new(),
            test_inputs: cvec_test_inputs(num_inputs),
        }
    }

    pub fn num_classes(&self) -> usize {
        self.egraph.number_of_classes()
    }

    pub fn num_nodes(&self) -> usize {
        self.egraph.total_size()
    }

    /// Add all terms with AST node count `size` (enumeration modulo equivalence).
    pub fn add_terms_of_size(&mut self, size: usize, num_inputs: usize) {
        if size == 0 {
            return;
        }
        self.ensure_size_buckets(size);

        if size == 1 {
            for i in 0..num_inputs {
                self.add_ast(&ValueAst::Symbol(i), num_inputs);
            }
            for &c in synthesis_constants() {
                self.add_ast(&ValueAst::Const(c), num_inputs);
            }
            return;
        }

        let child_size = size - 1;
        let child_classes = self.classes_by_size[child_size - 1].clone();

        for &class in &child_classes {
            let child = Id::from(class);
            for op in ValueUnOp::all() {
                let id = self.egraph.add(unop_enode(op, child));
                self.register_id(id, num_inputs);
            }
        }

        for left_sz in 1..size {
            let right_sz = size - 1 - left_sz;
            if right_sz == 0 {
                continue;
            }
            let left_classes = self.classes_by_size[left_sz - 1].clone();
            let right_classes = self.classes_by_size[right_sz - 1].clone();
            for &left in &left_classes {
                for &right in &right_classes {
                    let l = Id::from(left);
                    let r = Id::from(right);
                    for op in ValueBinOp::all() {
                        let id = self.egraph.add(binop_enode(op, l, r));
                        self.register_id(id, num_inputs);
                    }
                }
            }
        }
    }

    /// Equality-saturate a copy of `T` with `rules`, then merge learned equivalences back.
    ///
    /// Saturation may add new e-nodes on the copy; only equivalences among *original*
    /// node ids are merged into `self` (Ruler §3.2 — avoid polluting `T`).
    pub fn compact_with_rules(&mut self, rules: &[Rewrite<ValueLang, ()>], num_inputs: usize) {
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
        self.rebuild_class_index(num_inputs);
        report(&format!(
            "  compacted to {} e-classes",
            self.egraph.number_of_classes()
        ));
    }

    /// Pairs of ASTs from distinct e-classes with matching characteristic vectors.
    pub fn cvec_match_pairs(&self, num_inputs: usize) -> Vec<(ValueAst, ValueAst)> {
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
                    if !is_ast_rewrite_pair(num_inputs, lhs, rhs) {
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

    fn ensure_size_buckets(&mut self, size: usize) {
        while self.classes_by_size.len() < size {
            self.classes_by_size.push(HashSet::new());
        }
    }

    fn add_ast(&mut self, ast: &ValueAst, num_inputs: usize) {
        let expr = value_ast_to_expr(ast);
        let id = self.egraph.add_expr(&expr);
        self.register_id(id, num_inputs);
    }

    fn register_id(&mut self, id: Id, num_inputs: usize) {
        let class = usize::from(self.egraph.find(id));
        let Some(ast) = self.class_rep(class) else {
            return;
        };
        let sz = ast.size();
        self.ensure_size_buckets(sz);
        self.classes_by_size[sz - 1].insert(class);
        if ast.uses_each_symbol_once(num_inputs) {
            let sig = AstEvalSignature::of(&ast, &self.test_inputs);
            self.class_cvec.insert(class, sig);
        }
    }

    fn rebuild_class_index(&mut self, num_inputs: usize) {
        self.classes_by_size.clear();
        self.class_cvec.clear();
        let class_ids: Vec<Id> = self.egraph.classes().map(|c| c.id).collect();
        let total = class_ids.len();
        if total > 1_000 {
            report(&format!("  reindexing {total} e-classes…"));
        }
        for (n, id) in class_ids.iter().enumerate() {
            self.register_id(*id, num_inputs);
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

/// Copy e-class merges learned on `saturated` (which may contain extra nodes) back onto
/// `egraph`, touching only node ids `0..original_size`.
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

/// Ruler core loop for one input arity: enumerate by size, compact, cvec-match, verify.
pub fn discover_rules_for_input(
    num_inputs: usize,
    max_ast_size: usize,
    random_tests: usize,
    jobs: usize,
    ctx: &z3::Context,
    proven_keys: &mut HashSet<(String, String)>,
    rules_out: &mut Vec<(String, String)>,
) -> (usize, usize) {
    let mut rewrites: Vec<Rewrite<ValueLang, ()>> = Vec::new();
    let mut term_set = RulerTermSet::new(num_inputs);
    let mut pairs_checked = 0usize;
    let mut z3_queries = 0usize;

    for size in 1..=max_ast_size {
        term_set.add_terms_of_size(size, num_inputs);
        report(&format!(
            "  size {size}: {} e-classes, {} e-nodes",
            term_set.num_classes(),
            term_set.num_nodes()
        ));

        loop {
            term_set.compact_with_rules(&rewrites, num_inputs);
            let candidates = term_set.cvec_match_pairs(num_inputs);
            if candidates.is_empty() {
                break;
            }

            report(&format!(
                "  size {size}: verifying {} candidates…",
                candidates.len()
            ));

            let new_rules = if jobs <= 1 {
                verify_candidates(
                    num_inputs,
                    &candidates,
                    random_tests,
                    ctx,
                    proven_keys,
                    &mut pairs_checked,
                    &mut z3_queries,
                )
            } else {
                verify_candidates_parallel(
                    num_inputs,
                    &candidates,
                    random_tests,
                    jobs,
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
    num_inputs: usize,
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
        if !asts_valid_rewrite_random(num_inputs, lhs, rhs, random_tests) {
            continue;
        }
        *z3_queries += 1;
        if !asts_valid_rewrite_z3(ctx, num_inputs, lhs, rhs) {
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
    num_inputs: usize,
    candidates: &[(ValueAst, ValueAst)],
    random_tests: usize,
    _jobs: usize,
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
            if !asts_valid_rewrite_random(num_inputs, lhs, rhs, random_tests) {
                return None;
            }
            let ctx = crate::al::z3_context();
            if !asts_valid_rewrite_z3(&ctx, num_inputs, lhs, rhs) {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::ValueAst;

    #[test]
    fn compact_with_rules_does_not_union_saturation_only_nodes() {
        let mut term_set = RulerTermSet::new(1);
        term_set.add_terms_of_size(1, 1);
        term_set.add_terms_of_size(2, 1);
        term_set.add_terms_of_size(3, 1);
        let before = term_set.num_nodes();

        let mul = ValueAst::Mul(
            Box::new(ValueAst::Symbol(0)),
            Box::new(ValueAst::Const(2)),
        );
        let shl = ValueAst::Shl(
            Box::new(ValueAst::Symbol(0)),
            Box::new(ValueAst::Const(1)),
        );
        let rw = Rewrite::<ValueLang, ()>::new(
            "mul-shl",
            mul.to_pattern().parse::<Pattern<ValueLang>>().unwrap(),
            shl.to_pattern().parse::<Pattern<ValueLang>>().unwrap(),
        )
        .unwrap();

        term_set.compact_with_rules(&[rw], 1);
        assert_eq!(term_set.num_nodes(), before);
        assert!(
            term_set.num_classes() < term_set.num_nodes(),
            "expected some e-class merges"
        );
    }
}
