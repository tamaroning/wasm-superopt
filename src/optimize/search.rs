//! Backward goal search: BFS, greedy inverse, and A*.

use super::canon::Canonizer;
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

/// Structural memo key (exact `SymState`). Returns `true` if already expanded at ≤ `cost`.
fn memo_seen(memo: &HashMap<SymState, usize>, g: &SymState, cost: usize) -> bool {
    memo.get(g).is_some_and(|&best| best <= cost)
}

fn memo_record(memo: &mut HashMap<SymState, usize>, g: &SymState, cost: usize) {
    memo.insert(g.clone(), cost);
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
        if memo_seen(&memo, &g, depth) {
            continue;
        }
        if is_grounded(&g, init, &mut canon) {
            return Some(reverse_ops(&path));
        }
        memo_record(&mut memo, &g, depth);
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
        if memo_seen(&memo, &goal, g) {
            continue;
        }
        if is_grounded(&goal, init, &mut canon) {
            if g <= best {
                best = g;
                best_path = Some(reverse_ops(&path));
            }
            continue;
        }
        memo_record(&mut memo, &goal, g);
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
    fn solve_example_astar() {
        let init = init();
        let fin = fin();
        let rules = test_rules();
        let ops = solve_astar(&init, &fin, &rules, &SearchConfig::default()).expect("solution");
        assert!(!ops.is_empty());
        assert!(ops.len() <= 7);
    }
}
