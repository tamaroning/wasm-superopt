//! Value canonicalization via equality saturation.

use crate::lang::ValueLang;
use crate::semantics::{inst_kind_from_value_op, InstKind};
use crate::value::ValueOp;
use egg::{AstSize, Extractor, Id, RecExpr, Rewrite, Runner};
use std::collections::{HashMap, HashSet};

pub type ValueExpr = RecExpr<ValueLang>;
pub type CanonId = u32;

/// Normal form ⌈G⌉ for memoization (idea.md §8).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct NormalizedGoal {
    pub stack: Vec<CanonId>,
    /// `(slot, c(v))` for required locals; `★` slots are pruned.
    pub locals: Vec<(u32, CanonId)>,
}

const EQSAT_ITER_LIMIT: usize = 20;
const EQSAT_NODE_LIMIT: usize = 10_000;

pub struct Canonizer {
    rules: Vec<Rewrite<ValueLang, ()>>,
    str_cache: HashMap<String, CanonId>,
    /// Maps e-class ids in the persistent e-graph to canon ids.
    class_to_id: HashMap<usize, CanonId>,
    next_id: CanonId,
    runner: Runner<ValueLang, ()>,
}

impl Canonizer {
    pub fn new(rules: Vec<Rewrite<ValueLang, ()>>) -> Self {
        Self {
            rules,
            str_cache: HashMap::new(),
            class_to_id: HashMap::new(),
            next_id: 0,
            runner: Runner::default()
                .with_iter_limit(EQSAT_ITER_LIMIT)
                .with_node_limit(EQSAT_NODE_LIMIT),
        }
    }

    pub fn canon(&mut self, expr: &ValueExpr) -> CanonId {
        let key = expr.to_string();
        if let Some(&id) = self.str_cache.get(&key) {
            return id;
        }
        // Bare symbols never share ids with saturated expressions.
        if matches!(&expr[expr.root()], ValueLang::Symbol(_)) {
            let id = self.next_id;
            self.next_id += 1;
            self.str_cache.insert(key, id);
            return id;
        }

        let root = self.register_and_saturate(expr);
        let class = usize::from(self.runner.egraph.find(root));
        if let Some(&id) = self.class_to_id.get(&class) {
            self.str_cache.insert(key, id);
            return id;
        }

        let extractor = Extractor::new(&self.runner.egraph, AstSize);
        let (_, best) = extractor.find_best(root);
        let canon_str = best.to_string();
        let id = if let Some(&existing) = self.str_cache.get(&canon_str) {
            existing
        } else {
            let id = self.next_id;
            self.next_id += 1;
            self.str_cache.insert(canon_str, id);
            id
        };
        self.str_cache.insert(key, id);
        self.class_to_id.insert(class, id);
        id
    }

    pub fn values_equivalent(&mut self, a: &ValueExpr, b: &ValueExpr) -> bool {
        if a.to_string() == b.to_string() {
            return true;
        }
        if self.canon(a) == self.canon(b) {
            return true;
        }
        self.joint_saturate_equivalent(a, b)
    }

    /// Add both expressions to the persistent e-graph, saturate once, and compare e-classes.
    ///
    /// Catches equivalences (e.g. commutative `add`) that separate `canon` calls may miss.
    fn joint_saturate_equivalent(&mut self, a: &ValueExpr, b: &ValueExpr) -> bool {
        let id_a = self.runner.egraph.add_expr(a);
        let id_b = self.runner.egraph.add_expr(b);
        if self.runner.egraph.find(id_a) == self.runner.egraph.find(id_b) {
            self.unify_expr_cache(a, b, id_a);
            return true;
        }
        self.runner.roots.push(id_a);
        self.runner.roots.push(id_b);
        let egraph = std::mem::take(&mut self.runner.egraph);
        let roots = self.runner.roots.clone();
        self.runner = Runner::default()
            .with_iter_limit(EQSAT_ITER_LIMIT)
            .with_node_limit(EQSAT_NODE_LIMIT)
            .with_egraph(egraph)
            .run(&self.rules);
        self.runner.roots = roots;
        let equivalent = self.runner.egraph.find(id_a) == self.runner.egraph.find(id_b);
        if equivalent {
            self.unify_expr_cache(a, b, id_a);
        }
        equivalent
    }

    /// After a joint saturation merge, point both expression strings at the same `CanonId`.
    fn unify_expr_cache(&mut self, a: &ValueExpr, b: &ValueExpr, merged_root: Id) {
        let class = usize::from(self.runner.egraph.find(merged_root));
        let id = if let Some(&existing) = self.class_to_id.get(&class) {
            existing
        } else {
            let extractor = Extractor::new(&self.runner.egraph, AstSize);
            let (_, best) = extractor.find_best(merged_root);
            let canon_str = best.to_string();
            if let Some(&existing) = self.str_cache.get(&canon_str) {
                existing
            } else {
                let id = self.next_id;
                self.next_id += 1;
                self.str_cache.insert(canon_str, id);
                id
            }
        };
        self.class_to_id.insert(class, id);
        self.str_cache.insert(a.to_string(), id);
        self.str_cache.insert(b.to_string(), id);
    }

    /// Residual goal key `⌈G⌉ = ⟨[c(s)], {x ↦ c(M[x]) | M[x] ≠ ★}⟩`.
    pub fn normalize_state(&mut self, state: &crate::sym::SymState) -> NormalizedGoal {
        use crate::sym::LocalReq;

        let stack = state.stack.iter().map(|e| self.canon(e)).collect();
        let locals = state
            .locals
            .iter()
            .filter_map(|(&slot, req)| match req {
                LocalReq::Need(v) => Some((slot, self.canon(v))),
                LocalReq::DontCare => None,
            })
            .collect();
        NormalizedGoal { stack, locals }
    }

    pub fn saturate(&self, expr: &ValueExpr) -> Runner<ValueLang, ()> {
        Runner::default()
            .with_iter_limit(EQSAT_ITER_LIMIT)
            .with_node_limit(EQSAT_NODE_LIMIT)
            .with_expr(expr)
            .run(&self.rules)
    }

    pub fn expr_from_runner(&self, runner: &Runner<ValueLang, ()>, id: Id) -> ValueExpr {
        runner.egraph.id_to_expr(id)
    }

    /// Partition `exprs` by ≡_R e-class after a single joint equality saturation.
    ///
    /// Returns one class id per expression (parallel to `exprs`). Used to close opaque
    /// operand pins over the full equivalence class, not just per-call `canon()` ids.
    pub fn equiv_partition(&self, exprs: &[ValueExpr]) -> Vec<usize> {
        if exprs.is_empty() {
            return Vec::new();
        }
        let mut runner = Runner::default()
            .with_iter_limit(EQSAT_ITER_LIMIT)
            .with_node_limit(EQSAT_NODE_LIMIT);
        let ids: Vec<Id> = exprs.iter().map(|e| runner.egraph.add_expr(e)).collect();
        let runner = runner.run(&self.rules);
        let mut eclass_to_idx: HashMap<Id, usize> = HashMap::new();
        let mut next = 0usize;
        ids.iter()
            .map(|id| {
                let ec = runner.egraph.find(*id);
                *eclass_to_idx.entry(ec).or_insert_with(|| {
                    let idx = next;
                    next += 1;
                    idx
                })
            })
            .collect()
    }

    pub fn binop_decompositions(&self, expr: &ValueExpr) -> Vec<(InstKind, ValueExpr, ValueExpr)> {
        let runner = self.saturate(expr);
        let root = runner.roots[0];
        let class_id = runner.egraph.find(root);
        let eclass = &runner.egraph[class_id];
        let mut out = Vec::new();
        let mut seen = HashSet::new();
        for node in eclass.iter() {
            let parsed = ValueOp::from_lang(node).and_then(|(op, args)| {
                if args.len() != 2 {
                    return None;
                }
                Some((inst_kind_from_value_op(op), args[0], args[1]))
            });
            if let Some((kind, a, b)) = parsed {
                let a = runner.egraph.find(a);
                let b = runner.egraph.find(b);
                if !seen.insert((kind, a, b)) {
                    continue;
                }
                let e1 = self.expr_from_runner(&runner, a);
                let e2 = self.expr_from_runner(&runner, b);
                out.push((kind, e1, e2));
            }
        }
        out
    }

    fn register_and_saturate(&mut self, expr: &ValueExpr) -> Id {
        let id = self.runner.egraph.add_expr(expr);
        self.runner.roots.push(id);
        let egraph = std::mem::take(&mut self.runner.egraph);
        let roots = self.runner.roots.clone();
        self.runner = Runner::default()
            .with_iter_limit(EQSAT_ITER_LIMIT)
            .with_node_limit(EQSAT_NODE_LIMIT)
            .with_egraph(egraph)
            .run(&self.rules);
        self.runner.roots = roots;
        id
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use crate::synthesis::test_synthesis_rewrites;
    use crate::value::parse_value_expr;

    fn rules() -> Vec<egg::Rewrite<crate::lang::ValueLang, ()>> {
        test_synthesis_rewrites()
    }

    #[test]
    fn i64_binop_decompositions_nonempty() {
        let canon = Canonizer::new(rules());
        let top = parse_value_expr("(i64.mul ?L0 2)");
        let decomps = canon.binop_decompositions(&top);
        assert!(
            decomps.iter().any(|(k, _, _)| {
                matches!(k, InstKind::Pure(crate::value::ValueOp::I64Mul))
            }),
            "expected i64.mul decomposition: {decomps:?}"
        );
    }

    #[test]
    fn distinct_shifts_get_distinct_canon_ids() {
        let mut canon = Canonizer::new(rules());
        let a = parse_value_expr("(i32.shl ?L0 3)");
        let b = parse_value_expr("(i32.shl ?L0 1)");
        assert_ne!(canon.canon(&a), canon.canon(&b));
        assert!(!canon.values_equivalent(&a, &b));
    }

    #[test]
    fn sound_mul_shl_equivalence_shares_canon_id() {
        let mut canon = Canonizer::new(rules());
        let mul = parse_value_expr("(i32.mul (i32.add ?L0 1) 2)");
        let shl = parse_value_expr("(i32.shl (i32.add ?L0 1) 1)");
        assert_eq!(canon.canon(&mul), canon.canon(&shl));
    }

    #[test]
    fn commutative_add_operands_share_equiv_partition_class() {
        let canon = Canonizer::new(rules());
        let a = parse_value_expr("(i32.add (i32.sub ?L4 1) ?L1)");
        let b = parse_value_expr("(i32.add ?L1 (i32.sub ?L4 1))");
        let parts = canon.equiv_partition(&[a.clone(), b.clone()]);
        assert_eq!(parts.len(), 2);
        assert_eq!(parts[0], parts[1], "commutative add operands should share e-class");
    }

    #[test]
    fn commutative_add_operands_equivalent_via_joint_saturation() {
        let mut canon = Canonizer::new(rules());
        let a = parse_value_expr("(i32.add (i32.sub ?L4 1) ?L1)");
        let b = parse_value_expr("(i32.add ?L1 (i32.sub ?L4 1))");
        assert!(canon.values_equivalent(&a, &b));
        // After merge, both strings share one canon id.
        assert_eq!(canon.canon(&a), canon.canon(&b));
    }
}
