//! Value canonicalization via equality saturation.

use crate::lang::ValueLang;
use crate::semantics::InstKind;
use egg::{AstSize, Extractor, Id, RecExpr, Rewrite, Runner};
use std::collections::{HashMap, HashSet};

pub type ValueExpr = RecExpr<ValueLang>;
pub type CanonId = u32;

const SAT_ITER_LIMIT: usize = 20;
const SAT_NODE_LIMIT: usize = 10_000;

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
                .with_iter_limit(SAT_ITER_LIMIT)
                .with_node_limit(SAT_NODE_LIMIT),
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
        self.canon(a) == self.canon(b)
    }

    pub fn saturate(&self, expr: &ValueExpr) -> Runner<ValueLang, ()> {
        Runner::default()
            .with_iter_limit(SAT_ITER_LIMIT)
            .with_node_limit(SAT_NODE_LIMIT)
            .with_expr(expr)
            .run(&self.rules)
    }

    pub fn expr_from_runner(&self, runner: &Runner<ValueLang, ()>, id: Id) -> ValueExpr {
        runner.egraph.id_to_expr(id)
    }

    pub fn binop_decompositions(&self, expr: &ValueExpr) -> Vec<(InstKind, ValueExpr, ValueExpr)> {
        let runner = self.saturate(expr);
        let root = runner.roots[0];
        let class_id = runner.egraph.find(root);
        let eclass = &runner.egraph[class_id];
        let mut out = Vec::new();
        let mut seen = HashSet::new();
        for node in eclass.iter() {
            let parsed = match node {
                ValueLang::I32Add([a, b]) => Some((InstKind::I32Add, *a, *b)),
                ValueLang::I32Mul([a, b]) => Some((InstKind::I32Mul, *a, *b)),
                ValueLang::I32Shl([a, b]) => Some((InstKind::I32Shl, *a, *b)),
                ValueLang::I32DivU([a, b]) => Some((InstKind::I32DivU, *a, *b)),
                ValueLang::I32DivS([a, b]) => Some((InstKind::I32DivS, *a, *b)),
                _ => None,
            };
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
            .with_iter_limit(SAT_ITER_LIMIT)
            .with_node_limit(SAT_NODE_LIMIT)
            .with_egraph(egraph)
            .run(&self.rules);
        self.runner.roots = roots;
        id
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::synthesis::{
        TEST_SYNTHESIS_AST_SIZE, load_or_synthesize_rules, synthesized_to_rewrites,
    };
    use crate::value::parse_value_expr;

    fn rules() -> Vec<egg::Rewrite<crate::lang::ValueLang, ()>> {
        synthesized_to_rewrites(&load_or_synthesize_rules(TEST_SYNTHESIS_AST_SIZE, 10))
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
}
