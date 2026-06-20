//! Backward goal search: BFS, greedy inverse, and A*.

use crate::canon::Canonizer;
use crate::goal::{concrete_local, MachineState, MAX_LOCAL_SLOT};
use crate::heuristic::h_goal;
use crate::inverse::{applicable_peels, PeelAction};
use crate::lang::ValueLang;
use crate::semantics::{exec_sequence_concrete, ConcreteState, SemOp};
use egg::Rewrite;
use std::collections::{BinaryHeap, HashMap, VecDeque};
use std::cmp::Ordering;

pub const DEFAULT_MAX_DEPTH: usize = 16;

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

pub fn verify_forward(
    fin: &MachineState,
    ops: &[SemOp],
    l0: i32,
) -> bool {
    let mut locals = [0i32; 8];
    locals[0] = l0;
    let state = ConcreteState::new(locals, [0; 16]);
    let r = exec_sequence_concrete(ops, vec![], state);
    if r.trap {
        return false;
    }
    let expect_stack = crate::goal::concrete_stack(fin, l0);
    if r.stack != expect_stack {
        return false;
    }
    for slot in 0..=MAX_LOCAL_SLOT {
        if let Some(fv) = concrete_local(fin, slot, l0) {
            if r.state.locals[slot as usize] != fv {
                return false;
            }
        }
    }
    true
}

fn reverse_ops(path: &[SemOp]) -> Vec<SemOp> {
    let mut out = path.to_vec();
    out.reverse();
    out
}

pub fn solve_bfs(
    init: &MachineState,
    fin: &MachineState,
    rules: &[Rewrite<ValueLang, ()>],
    cfg: &SearchConfig,
) -> Option<Vec<SemOp>> {
    let mut canon = Canonizer::new(rules.to_vec());
    let mut queue = VecDeque::new();
    queue.push_back((fin.clone(), Vec::new(), 0usize));
    while let Some((g, path, depth)) = queue.pop_front() {
        if g.is_grounded(init, &mut canon) {
            let candidate = reverse_ops(&path);
            if verify_forward(fin, &candidate, 42) {
                return Some(candidate);
            }
            continue;
        }
        if depth >= cfg.max_depth {
            continue;
        }
        // Memo disabled: symbolic canon can collide across semantically distinct goals.
        for (PeelAction::Forward(op), next) in applicable_peels(&g, &mut canon) {
            let mut next_path = path.clone();
            next_path.push(op);
            queue.push_back((next, next_path, depth + 1));
        }
    }
    None
}

pub fn solve_greedy_inv(
    init: &MachineState,
    fin: &MachineState,
    rules: &[Rewrite<ValueLang, ()>],
    cfg: &SearchConfig,
) -> Option<Vec<SemOp>> {
    let mut canon = Canonizer::new(rules.to_vec());
    let mut g = fin.clone();
    let mut path = Vec::new();
    for _ in 0..cfg.max_depth {
        if g.is_grounded(init, &mut canon) {
            return Some(reverse_ops(&path));
        }
        let peels = applicable_peels(&g, &mut canon);
        let best = peels.into_iter().min_by_key(|(_, next)| {
            h_goal(next, init, &mut canon)
        })?;
        let (PeelAction::Forward(op), next) = best;
        path.push(op);
        g = next;
    }
    if g.is_grounded(init, &mut canon) {
        Some(reverse_ops(&path))
    } else {
        None
    }
}

#[derive(Eq, PartialEq)]
struct AstarNode {
    f: usize,
    g: usize,
    goal: MachineState,
    path: Vec<SemOp>,
}

impl Ord for AstarNode {
    fn cmp(&self, other: &Self) -> Ordering {
        other
            .f
            .cmp(&self.f)
            .then_with(|| other.g.cmp(&self.g))
    }
}

impl PartialOrd for AstarNode {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

pub fn solve_astar(
    init: &MachineState,
    fin: &MachineState,
    rules: &[Rewrite<ValueLang, ()>],
    cfg: &SearchConfig,
) -> Option<Vec<SemOp>> {
    let mut canon = Canonizer::new(rules.to_vec());
    let mut best_path = solve_greedy_inv(init, fin, rules, cfg);
    let mut best = best_path
        .as_ref()
        .filter(|p| verify_forward(fin, p, 42))
        .map(|p| p.len())
        .unwrap_or(cfg.max_depth);

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
        if goal.is_grounded(init, &mut canon) {
            let candidate = reverse_ops(&path);
            if verify_forward(fin, &candidate, 42) && g <= best {
                best = g;
                best_path = Some(candidate);
            }
            continue;
        }
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
    use crate::example::{fin, init};
    use crate::synthesis::{
        load_or_synthesize_rules, synthesized_to_rewrites, TEST_SYNTHESIS_AST_SIZE,
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
        assert_eq!(ops.len(), 7, "ops: {}", format_ops(&ops));
        assert!(format_ops(&ops).contains("i32.const 3"));
        assert!(verify_forward(&fin, &ops, 42));
    }

    #[test]
    fn solve_example_astar() {
        let init = init();
        let fin = fin();
        let rules = test_rules();
        let ops = solve_astar(&init, &fin, &rules, &SearchConfig::default()).expect("solution");
        assert_eq!(ops.len(), 7);
        assert!(verify_forward(&fin, &ops, 42));
    }

    #[test]
    fn forward_exec_matches_fin() {
        let fin = fin();
        let rules = test_rules();
        let init = init();
        let ops = solve_bfs(&init, &fin, &rules, &SearchConfig::default()).unwrap();
        assert!(verify_forward(&fin, &ops, 7));
    }
}
