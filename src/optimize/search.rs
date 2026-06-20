//! Backward goal search: BFS, greedy inverse, and A*.

use super::canon::{Canonizer, NormalizedGoal};
use super::heuristic::h_goal;
use super::inverse::{PeelAction, applicable_peels};
use crate::lang::ValueLang;
use crate::semantics::SemOp;
use crate::sym::{LocalReq, MAX_LOCAL_SLOT, SymState};
use egg::Rewrite;
use std::cmp::Ordering;
use std::collections::{BinaryHeap, HashMap, VecDeque};

pub const DEFAULT_MAX_DEPTH: usize = 16;

/// Whether residual goal `state` matches initial conditions `init` under canonicalization.
pub fn is_grounded(state: &SymState, init: &SymState, canon: &mut Canonizer) -> bool {
    if state.stack.len() != init.stack.len() {
        return false;
    }
    for (a, b) in state.stack.iter().zip(init.stack.iter()) {
        if canon.canon(a) != canon.canon(b) {
            return false;
        }
    }
    for slot in 0..=MAX_LOCAL_SLOT {
        let cur = state.locals.get(&slot);
        let expected = init.locals.get(&slot);
        match (cur, expected) {
            (None | Some(LocalReq::DontCare), None) => {}
            (Some(LocalReq::DontCare), _) | (None, Some(LocalReq::DontCare)) => {}
            (Some(LocalReq::Need(v)), Some(LocalReq::Need(init_v))) => {
                if canon.canon(v) != canon.canon(init_v) {
                    return false;
                }
            }
            _ => return false,
        }
    }
    true
}

#[derive(Clone, Debug)]
pub struct SearchConfig {
    pub max_depth: usize,
}

impl Default for SearchConfig {
    fn default() -> Self {
        Self {
            max_depth: DEFAULT_MAX_DEPTH,
        }
    }
}

fn reverse_ops(path: &[SemOp]) -> Vec<SemOp> {
    let mut out = path.to_vec();
    out.reverse();
    out
}

/// Memo key `⌈G⌉` (idea.md §8). Returns `true` if already expanded at ≤ `cost`.
fn memo_seen(
    memo: &HashMap<NormalizedGoal, usize>,
    g: &SymState,
    cost: usize,
    canon: &mut Canonizer,
) -> bool {
    let key = canon.normalize_state(g);
    memo.get(&key).is_some_and(|&best| best <= cost)
}

fn memo_record(
    memo: &mut HashMap<NormalizedGoal, usize>,
    g: &SymState,
    cost: usize,
    canon: &mut Canonizer,
) {
    let key = canon.normalize_state(g);
    memo.insert(key, cost);
}

pub fn solve_bfs(
    init: &SymState,
    fin: &SymState,
    rules: &[Rewrite<ValueLang, ()>],
    cfg: &SearchConfig,
) -> Option<Vec<SemOp>> {
    let mut canon = Canonizer::new(rules.to_vec());
    let mut memo = HashMap::new();
    let mut queue = VecDeque::new();
    queue.push_back((fin.clone(), Vec::new(), 0usize));
    while let Some((g, path, depth)) = queue.pop_front() {
        if memo_seen(&memo, &g, depth, &mut canon) {
            continue;
        }
        if is_grounded(&g, init, &mut canon) {
            return Some(reverse_ops(&path));
        }
        memo_record(&mut memo, &g, depth, &mut canon);
        if depth >= cfg.max_depth {
            continue;
        }
        for (PeelAction::Forward(op), next) in applicable_peels(&g, &mut canon) {
            let mut next_path = path.clone();
            next_path.push(op);
            queue.push_back((next, next_path, depth + 1));
        }
    }
    None
}

pub fn solve_greedy_inv(
    init: &SymState,
    fin: &SymState,
    rules: &[Rewrite<ValueLang, ()>],
    cfg: &SearchConfig,
) -> Option<Vec<SemOp>> {
    let mut canon = Canonizer::new(rules.to_vec());
    let mut g = fin.clone();
    let mut path = Vec::new();
    for _ in 0..cfg.max_depth {
        if is_grounded(&g, init, &mut canon) {
            return Some(reverse_ops(&path));
        }
        let peels = applicable_peels(&g, &mut canon);
        let best = peels
            .into_iter()
            .min_by_key(|(_, next)| h_goal(next, init, &mut canon))?;
        let (PeelAction::Forward(op), next) = best;
        path.push(op);
        g = next;
    }
    if is_grounded(&g, init, &mut canon) {
        Some(reverse_ops(&path))
    } else {
        None
    }
}

#[derive(Eq, PartialEq)]
struct AstarNode {
    f: usize,
    g: usize,
    goal: SymState,
    path: Vec<SemOp>,
}

impl Ord for AstarNode {
    fn cmp(&self, other: &Self) -> Ordering {
        other.f.cmp(&self.f).then_with(|| other.g.cmp(&self.g))
    }
}

impl PartialOrd for AstarNode {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

pub fn solve_astar(
    init: &SymState,
    fin: &SymState,
    rules: &[Rewrite<ValueLang, ()>],
    cfg: &SearchConfig,
) -> Option<Vec<SemOp>> {
    let mut canon = Canonizer::new(rules.to_vec());
    let mut best_path = solve_greedy_inv(init, fin, rules, cfg);
    let mut best = best_path.as_ref().map(|p| p.len()).unwrap_or(cfg.max_depth);

    let mut memo = HashMap::new();
    let mut heap = BinaryHeap::new();
    let h0 = h_goal(fin, init, &mut canon);
    heap.push(AstarNode {
        f: h0,
        g: 0,
        goal: fin.clone(),
        path: vec![],
    });

    while let Some(AstarNode { f, g, goal, path }) = heap.pop() {
        if f >= best {
            continue;
        }
        if memo_seen(&memo, &goal, g, &mut canon) {
            continue;
        }
        if is_grounded(&goal, init, &mut canon) {
            if g <= best {
                best = g;
                best_path = Some(reverse_ops(&path));
            }
            continue;
        }
        memo_record(&mut memo, &goal, g, &mut canon);
        if g >= cfg.max_depth.min(best) {
            continue;
        }
        for (PeelAction::Forward(op), next) in applicable_peels(&goal, &mut canon) {
            let ng = g + 1;
            let nh = h_goal(&next, init, &mut canon);
            let nf = ng + nh;
            if nf <= best {
                let mut npath = path.clone();
                npath.push(op);
                heap.push(AstarNode {
                    f: nf,
                    g: ng,
                    goal: next,
                    path: npath,
                });
            }
        }
    }

    best_path
}

pub fn format_ops(ops: &[SemOp]) -> String {
    ops.iter()
        .map(|op| op.to_string())
        .collect::<Vec<_>>()
        .join("; ")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::optimize::fixtures::{fin, init};
    use crate::synthesis::{
        TEST_SYNTHESIS_AST_SIZE, load_or_synthesize_rules, synthesized_to_rewrites,
    };

    fn test_rules() -> Vec<egg::Rewrite<crate::lang::ValueLang, ()>> {
        synthesized_to_rewrites(&load_or_synthesize_rules(TEST_SYNTHESIS_AST_SIZE, 10))
    }

    #[test]
    fn solve_example_bfs() {
        let init = init();
        let fin = fin();
        let rules = test_rules();
        let ops = solve_bfs(&init, &fin, &rules, &SearchConfig::default()).expect("solution");
        assert!(!ops.is_empty(), "ops: {}", format_ops(&ops));
        assert!(ops.len() <= 7, "ops: {}", format_ops(&ops));
    }

    #[test]
    fn optimized_example_preserves_fin_state() {
        use crate::optimize::fixtures::{fin, init};
        use crate::optimize::search::{SearchConfig, format_ops, is_grounded, solve_astar};
        use crate::sym::SymMachine;

        let init = init();
        let fin = fin();
        let rules = test_rules();
        let ops = solve_astar(&init, &fin, &rules, &SearchConfig::default()).expect("solution");
        assert_eq!(ops.len(), 7, "ops: {}", format_ops(&ops));

        let mut m = SymMachine::function_entry(1, 1);
        for op in &ops {
            m.exec(op).unwrap();
        }
        let got = m.to_fin_state();
        let mut canon = crate::optimize::canon::Canonizer::new(rules);
        assert!(is_grounded(&got, &fin, &mut canon));
    }

    #[test]
    fn normalized_memo_key_merges_mul_and_shl_peel_paths() {
        use crate::optimize::canon::Canonizer;
        use crate::semantics::InstKind;
        use crate::sym::LocalReq;
        use crate::value::parse_value_expr;

        let rules = test_rules();
        let mut canon = Canonizer::new(rules);
        let top = parse_value_expr("(i32.mul (i32.add ?L0 1) 2)");
        let l_plus_1 = parse_value_expr("(i32.add ?L0 1)");
        let mut locals = std::collections::BTreeMap::new();
        locals.insert(0, LocalReq::Need(l_plus_1));
        let g = SymState {
            stack: vec![top],
            locals,
        };
        let decomps = canon.binop_decompositions(g.top().unwrap());
        let (_, e1, e2) = decomps
            .iter()
            .find(|(k, _, _)| *k == InstKind::I32Mul)
            .unwrap();
        let mut after_mul = g.clone();
        after_mul.stack.pop();
        after_mul.stack.push(e1.clone());
        after_mul.stack.push(e2.clone());
        after_mul.stack.pop();
        let (_, e1s, e2s) = decomps
            .iter()
            .find(|(k, _, _)| *k == InstKind::I32Shl)
            .unwrap();
        let mut after_shl = g.clone();
        after_shl.stack.pop();
        after_shl.stack.push(e1s.clone());
        after_shl.stack.push(e2s.clone());
        after_shl.stack.pop();
        assert_eq!(
            canon.normalize_state(&after_mul),
            canon.normalize_state(&after_shl)
        );
    }

    #[test]
    fn solve_example_astar() {
        let init = init();
        let fin = fin();
        let rules = test_rules();
        let ops = solve_astar(&init, &fin, &rules, &SearchConfig::default()).expect("solution");
        assert!(!ops.is_empty());
        assert!(ops.len() <= 7);
    }
}
