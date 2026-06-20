//! Value canonicalization via equality saturation.

use super::goal::{LocalReq, MachineState};
use crate::lang::ValueLang;
use crate::semantics::InstKind;
use egg::{AstSize, Extractor, Id, RecExpr, Rewrite, Runner};
use std::collections::{HashMap, HashSet};

pub type ValueExpr = RecExpr<ValueLang>;
pub type CanonId = u32;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct NormalGoal {
    pub stack: Vec<CanonId>,
    pub locals: Vec<(u32, CanonId)>,
}

pub struct Canonizer {
    rules: Vec<Rewrite<ValueLang, ()>>,
    str_cache: HashMap<String, CanonId>,
    class_cache: HashMap<usize, CanonId>,
    next_id: CanonId,
}

impl Canonizer {
    pub fn new(rules: Vec<Rewrite<ValueLang, ()>>) -> Self {
        Self {
            rules,
            str_cache: HashMap::new(),
            class_cache: HashMap::new(),
            next_id: 0,
        }
    }

    pub fn canon(&mut self, expr: &ValueExpr) -> CanonId {
        let key = expr.to_string();
        if let Some(&id) = self.str_cache.get(&key) {
            return id;
        }
        let runner = Runner::default()
            .with_iter_limit(20)
            .with_node_limit(10_000)
            .with_expr(expr)
            .run(&self.rules);
        let root = runner.roots[0];
        let class = usize::from(runner.egraph.find(root));
        if let Some(&id) = self.class_cache.get(&class) {
            self.str_cache.insert(key, id);
            return id;
        }
        let extractor = Extractor::new(&runner.egraph, AstSize);
        let (_, best) = extractor.find_best(root);
        let canon_str = best.to_string();
        if let Some(&id) = self.str_cache.get(&canon_str) {
            self.class_cache.insert(class, id);
            self.str_cache.insert(key, id);
            return id;
        }
        let id = self.next_id;
        self.next_id += 1;
        self.str_cache.insert(key, id);
        self.str_cache.insert(canon_str, id);
        self.class_cache.insert(class, id);
        id
    }

    pub fn values_equivalent(&mut self, a: &ValueExpr, b: &ValueExpr) -> bool {
        self.canon(a) == self.canon(b)
    }

    pub fn normal_goal(&mut self, g: &MachineState) -> NormalGoal {
        NormalGoal {
            stack: g.stack.iter().map(|e| self.canon(e)).collect(),
            locals: g
                .locals
                .iter()
                .filter_map(|(&slot, req)| match req {
                    LocalReq::DontCare => None,
                    LocalReq::Need(e) => Some((slot, self.canon(e))),
                })
                .collect(),
        }
    }

    pub fn saturate(&self, expr: &ValueExpr) -> Runner<ValueLang, ()> {
        Runner::default()
            .with_iter_limit(20)
            .with_node_limit(10_000)
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
}
