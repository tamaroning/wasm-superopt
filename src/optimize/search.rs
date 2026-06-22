//! Backward goal search: BFS, greedy inverse, and A*.

use super::canon::{Canonizer, NormalizedGoal};
use super::heuristic::h_goal;
use super::inverse::{PeelAction, SearchState, applicable_peels};
use crate::lang::ValueLang;
use crate::semantics::SemOp;
use crate::sym::{LocalReq, SymState};
use crate::wasm::{ops_respect_dependencies, storage_ops_preserved, SegmentBounds, StraightSegment};
use egg::Rewrite;
use std::cmp::Ordering;
use std::collections::{BinaryHeap, HashMap, VecDeque};

pub const DEFAULT_MAX_DEPTH: usize = 16;
/// Default per-segment timeout (seconds), matching SuperStack's base `10 * (1 + storage)`.
pub const DEFAULT_TIMEOUT_BASE_SECS: u64 = 10;
/// Per-segment timeout when `--direct-timeout` is set (SuperStack `-w` / `DIRECT_TIMEOUT`).
pub const DIRECT_TIMEOUT_SECS: u64 = 300;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SearchResult {
    pub ops: Option<Vec<SemOp>>,
    pub timed_out: bool,
}

#[derive(Clone, Debug)]
struct SearchDeadline {
    start: std::time::Instant,
    limit: std::time::Duration,
}

impl SearchDeadline {
    fn new(secs: u64) -> Self {
        Self {
            start: std::time::Instant::now(),
            limit: std::time::Duration::from_secs(secs),
        }
    }

    fn expired(&self) -> bool {
        self.start.elapsed() >= self.limit
    }
}

/// SuperStack: `10 * (1 + #storage_ops)`; arithmetic-only segments use the base 10s.
pub fn segment_timeout_secs(segment: &StraightSegment, direct_timeout: bool) -> u64 {
    if direct_timeout {
        return DIRECT_TIMEOUT_SECS;
    }
    let storage = segment
        .ops
        .iter()
        .filter(|op| op.is_storage_boundary())
        .count();
    DEFAULT_TIMEOUT_BASE_SECS * (1 + storage as u64)
}

/// Whether residual goal `state` matches initial conditions `init` under canonicalization.
pub fn is_grounded(
    state: &SymState,
    init: &SymState,
    bounds: &SegmentBounds,
    canon: &mut Canonizer,
) -> bool {
    if state.stack.len() != init.stack.len() {
        return false;
    }
    for (a, b) in state.stack.iter().zip(init.stack.iter()) {
        if canon.canon(a) != canon.canon(b) {
            return false;
        }
    }
    let mut slots: std::collections::BTreeSet<u32> = init.locals.keys().copied().collect();
    slots.extend(state.locals.keys().copied());
    for slot in slots {
        if slot > bounds.max_local {
            continue;
        }
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

pub fn is_solution(
    state: &SearchState,
    init: &SymState,
    bounds: &SegmentBounds,
    canon: &mut Canonizer,
) -> bool {
    is_grounded(&state.goal, init, bounds, canon) && state.is_complete()
}

pub fn validate_solution_ops(ops: &[SemOp], segment: &StraightSegment) -> bool {
    storage_ops_preserved(&segment.ops, ops)
        && ops_respect_dependencies(ops, &segment.dependencies)
}

#[derive(Clone, Debug)]
pub struct SearchConfig {
    pub max_depth: usize,
    /// When set, search stops after this many seconds (computed per segment in the driver).
    pub timeout_secs: Option<u64>,
    /// Use 300s per segment instead of `10 * (1 + storage)`.
    pub direct_timeout: bool,
}

impl Default for SearchConfig {
    fn default() -> Self {
        Self {
            max_depth: DEFAULT_MAX_DEPTH,
            timeout_secs: None,
            direct_timeout: false,
        }
    }
}

impl SearchConfig {
    pub fn for_segment(&self, segment: &StraightSegment) -> Self {
        Self {
            max_depth: self.max_depth,
            timeout_secs: Some(segment_timeout_secs(segment, self.direct_timeout)),
            direct_timeout: self.direct_timeout,
        }
    }
}

fn reverse_ops(path: &[SemOp]) -> Vec<SemOp> {
    let mut out = path.to_vec();
    out.reverse();
    out
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct MemoKey {
    goal: NormalizedGoal,
    remaining_storage: Vec<u32>,
    used_opaque: Vec<u32>,
}

fn memo_key(state: &SearchState, canon: &mut Canonizer) -> MemoKey {
    MemoKey {
        goal: canon.normalize_state(&state.goal),
        remaining_storage: state.remaining_storage.iter().copied().collect(),
        used_opaque: state.used_opaque.iter().copied().collect(),
    }
}

fn memo_seen(
    memo: &HashMap<MemoKey, usize>,
    state: &SearchState,
    cost: usize,
    canon: &mut Canonizer,
) -> bool {
    let key = memo_key(state, canon);
    memo.get(&key).is_some_and(|&best| best <= cost)
}

fn memo_record(
    memo: &mut HashMap<MemoKey, usize>,
    state: &SearchState,
    cost: usize,
    canon: &mut Canonizer,
) {
    let key = memo_key(state, canon);
    memo.insert(key, cost);
}

fn accept_solution(
    path: &[SemOp],
    segment: &StraightSegment,
    _init: &SymState,
    _bounds: &SegmentBounds,
    _canon: &mut Canonizer,
) -> Option<Vec<SemOp>> {
    let ops = reverse_ops(path);
    if !validate_solution_ops(&ops, segment) {
        return None;
    }
    Some(ops)
}

pub fn solve_bfs(
    segment: &StraightSegment,
    rules: &[Rewrite<ValueLang, ()>],
    cfg: &SearchConfig,
) -> SearchResult {
    let init = &segment.init;
    let bounds = &segment.bounds;
    let deadline = cfg.timeout_secs.map(SearchDeadline::new);
    let mut timed_out = false;
    let mut canon = Canonizer::new(rules.to_vec());
    let mut memo = HashMap::new();
    let mut queue = VecDeque::new();
    queue.push_back((SearchState::initial(segment, &segment.fin), Vec::new(), 0usize));
    let mut best = None;
    while let Some((state, path, depth)) = queue.pop_front() {
        if deadline.as_ref().is_some_and(|d| d.expired()) {
            timed_out = true;
            break;
        }
        if memo_seen(&memo, &state, depth, &mut canon) {
            continue;
        }
        if is_solution(&state, init, bounds, &mut canon) {
            if let Some(ops) = accept_solution(&path, segment, init, bounds, &mut canon) {
                best = Some(ops);
                break;
            }
        }
        memo_record(&mut memo, &state, depth, &mut canon);
        if depth >= cfg.max_depth {
            continue;
        }
        for (PeelAction::Forward(op), next) in applicable_peels(&state, segment, bounds, &mut canon) {
            let mut next_path = path.clone();
            next_path.push(op);
            queue.push_back((next, next_path, depth + 1));
        }
    }
    SearchResult {
        ops: best,
        timed_out,
    }
}

pub fn solve_greedy_inv(
    segment: &StraightSegment,
    rules: &[Rewrite<ValueLang, ()>],
    cfg: &SearchConfig,
) -> SearchResult {
    let init = &segment.init;
    let bounds = &segment.bounds;
    let deadline = cfg.timeout_secs.map(SearchDeadline::new);
    let mut timed_out = false;
    let mut canon = Canonizer::new(rules.to_vec());
    let mut state = SearchState::initial(segment, &segment.fin);
    let mut path = Vec::new();
    for _ in 0..cfg.max_depth {
        if deadline.as_ref().is_some_and(|d| d.expired()) {
            timed_out = true;
            break;
        }
        if is_solution(&state, init, bounds, &mut canon) {
            if let Some(ops) = accept_solution(&path, segment, init, bounds, &mut canon) {
                return SearchResult {
                    ops: Some(ops),
                    timed_out,
                };
            }
            break;
        }
        let peels = applicable_peels(&state, segment, bounds, &mut canon);
        let Some(best) = peels
            .into_iter()
            .min_by_key(|(_, next)| h_goal(&next.goal, init, bounds, &mut canon))
        else {
            break;
        };
        let (PeelAction::Forward(op), next) = best;
        path.push(op);
        state = next;
    }
    SearchResult {
        ops: if is_solution(&state, init, bounds, &mut canon) {
            accept_solution(&path, segment, init, bounds, &mut canon)
        } else {
            None
        },
        timed_out,
    }
}

#[derive(Eq, PartialEq)]
struct AstarNode {
    f: usize,
    g: usize,
    state: SearchState,
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
    segment: &StraightSegment,
    rules: &[Rewrite<ValueLang, ()>],
    cfg: &SearchConfig,
) -> SearchResult {
    let init = &segment.init;
    let bounds = &segment.bounds;
    let deadline = cfg.timeout_secs.map(SearchDeadline::new);
    let mut timed_out = false;
    let mut canon = Canonizer::new(rules.to_vec());
    let greedy = solve_greedy_inv(segment, rules, cfg);
    timed_out |= greedy.timed_out;
    let mut best_path = greedy.ops.clone();
    let mut best = best_path.as_ref().map(|p| p.len()).unwrap_or(cfg.max_depth);

    let mut memo = HashMap::new();
    let mut heap = BinaryHeap::new();
    let initial = SearchState::initial(segment, &segment.fin);
    let h0 = h_goal(&initial.goal, init, bounds, &mut canon);
    heap.push(AstarNode {
        f: h0,
        g: 0,
        state: initial,
        path: vec![],
    });

    while let Some(AstarNode { f, g, state, path }) = heap.pop() {
        if deadline.as_ref().is_some_and(|d| d.expired()) {
            timed_out = true;
            break;
        }
        if f >= best {
            continue;
        }
        if memo_seen(&memo, &state, g, &mut canon) {
            continue;
        }
        if is_solution(&state, init, bounds, &mut canon) {
            if let Some(ops) = accept_solution(&path, segment, init, bounds, &mut canon) {
                if g <= best {
                    best = g;
                    best_path = Some(ops);
                }
            }
            continue;
        }
        memo_record(&mut memo, &state, g, &mut canon);
        if g >= cfg.max_depth.min(best) {
            continue;
        }
        for (PeelAction::Forward(op), next) in applicable_peels(&state, segment, bounds, &mut canon) {
            let ng = g + 1;
            let nh = h_goal(&next.goal, init, bounds, &mut canon);
            let nf = ng + nh;
            if nf <= best {
                let mut npath = path.clone();
                npath.push(op);
                heap.push(AstarNode {
                    f: nf,
                    g: ng,
                    state: next,
                    path: npath,
                });
            }
        }
    }

    SearchResult {
        ops: best_path,
        timed_out,
    }
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
    use crate::sym::SymMachine;
    use crate::wasm::SegmentBounds;

    fn test_rules() -> Vec<egg::Rewrite<crate::lang::ValueLang, ()>> {
        synthesized_to_rewrites(&load_or_synthesize_rules(TEST_SYNTHESIS_AST_SIZE, 10, 1))
    }

    fn example_segment() -> StraightSegment {
        let init = init();
        let fin = fin();
        StraightSegment {
            func_index: 0,
            segment_index: 0,
            split_part: None,
            ops: vec![],
            init: init.clone(),
            fin: fin.clone(),
            bounds: SegmentBounds::new(1, 4),
            opaque_meta: vec![],
            dependencies: vec![],
        }
    }

    #[test]
    fn solve_example_bfs() {
        let segment = example_segment();
        let rules = test_rules();
        let ops = solve_bfs(&segment, &rules, &SearchConfig::default())
            .ops
            .expect("solution");
        assert!(!ops.is_empty(), "ops: {}", format_ops(&ops));
        assert!(ops.len() <= 7, "ops: {}", format_ops(&ops));
    }

    #[test]
    fn optimized_example_preserves_fin_state() {
        let segment = example_segment();
        let rules = test_rules();
        let bounds = segment.bounds;
        let ops = solve_astar(&segment, &rules, &SearchConfig::default())
            .ops
            .expect("solution");
        assert_eq!(ops.len(), 7, "ops: {}", format_ops(&ops));

        let mut m = SymMachine::function_entry(1, 1, bounds.max_stack);
        m.begin_segment();
        for op in &ops {
            m.exec(op).unwrap();
        }
        let got = m.to_fin_state();
        let mut canon = crate::optimize::canon::Canonizer::new(rules);
        assert!(is_grounded(&got, &segment.fin, &bounds, &mut canon));
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
        let segment = example_segment();
        let rules = test_rules();
        let ops = solve_astar(&segment, &rules, &SearchConfig::default())
            .ops
            .expect("solution");
        assert!(!ops.is_empty());
        assert!(ops.len() <= 7);
    }
}
