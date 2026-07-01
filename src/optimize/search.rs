//! Backward goal search with A*.

use super::canon::{Canonizer, NormalizedGoal};
use super::heuristic::h_goal;
use super::inverse::{PeelAction, SearchState, applicable_peels};
use crate::lang::ValueLang;
use crate::semantics::SemOp;
use crate::sym::{LocalReq, SymMachine, SymState};
use crate::value::parse_value_expr;
use crate::wasm::{
    OpaqueMeta, SegmentBounds, StraightSegment, ops_respect_dependencies, storage_ops_preserved,
};
use egg::Rewrite;
use std::cmp::Ordering;
use std::collections::{BinaryHeap, HashMap, HashSet};

pub const DEFAULT_MAX_DEPTH: usize = 16;
/// Default per-segment timeout (seconds), matching SuperStack's base `10 * (1 + storage)`.
pub const DEFAULT_TIMEOUT_BASE_SECS: u64 = 10;
/// Per-segment timeout when `--direct-timeout` is set (SuperStack `-w` / `DIRECT_TIMEOUT`).
pub const DIRECT_TIMEOUT_SECS: u64 = 300;

#[derive(Clone, Debug, Default, PartialEq)]
pub struct SearchResult {
    pub ops: Option<Vec<SemOp>>,
    pub timed_out: bool,
    pub solver_time_secs: f64,
    /// True when the solver proved no shorter valid sequence exists (SAT UNSAT at best length).
    pub proven_optimal: bool,
}

/// How stack/local values are compared during grounding checks.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum GroundEqMode {
    /// Representative `canon()` id equality (A* goal test).
    Canon,
    /// `≡_R` via `values_equivalent` including joint saturation (forward validation).
    Saturate,
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
    grounded_with(state, init, bounds, canon, GroundEqMode::Canon)
}

fn values_match(
    a: &crate::optimize::canon::ValueExpr,
    b: &crate::optimize::canon::ValueExpr,
    canon: &mut Canonizer,
    mode: GroundEqMode,
) -> bool {
    match mode {
        GroundEqMode::Canon => canon.canon(a) == canon.canon(b),
        GroundEqMode::Saturate => canon.values_equivalent(a, b),
    }
}

fn grounded_with(
    state: &SymState,
    init: &SymState,
    bounds: &SegmentBounds,
    canon: &mut Canonizer,
    mode: GroundEqMode,
) -> bool {
    if state.stack.len() != init.stack.len() {
        return false;
    }
    for (a, b) in state.stack.iter().zip(init.stack.iter()) {
        if !values_match(a, b, canon, mode) {
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
                if !values_match(v, init_v, canon, mode) {
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
    storage_ops_preserved(&segment.ops, ops) && ops_respect_dependencies(ops, &segment.dependencies)
}

/// Highest local slot referenced by `ops` (includes synthetic scratch locals).
fn max_local_slot(ops: &[SemOp]) -> Option<u32> {
    ops.iter()
        .filter_map(|op| match op {
            SemOp::LocalGet(s) | SemOp::LocalSet(s) | SemOp::LocalTee(s) => Some(*s),
            _ => None,
        })
        .max()
}

/// Bounds widened so the validation machine can execute synthetic scratch locals in `ops`.
/// `max_stack` is unchanged; only `max_local` grows to cover scratch slots.
fn scratch_extended_bounds(bounds: &SegmentBounds, ops: &[SemOp]) -> SegmentBounds {
    let needed = max_local_slot(ops).unwrap_or(0);
    SegmentBounds {
        max_local: bounds.max_local.max(needed),
        max_stack: bounds.max_stack,
    }
}

/// Whether each opaque op in `ops` consumes operands ≡_R to the original segment.
pub fn opaque_inputs_equivalent(
    ops: &[SemOp],
    segment: &StraightSegment,
    canon: &mut Canonizer,
) -> bool {
    let expected: HashMap<u32, &OpaqueMeta> = segment
        .opaque_meta
        .iter()
        .map(|m| (m.id, m))
        .collect();

    let exec_bounds = scratch_extended_bounds(&segment.bounds, ops);
    let mut m = SymMachine::from_segment_entry(
        segment.num_params,
        &exec_bounds,
        &segment.init,
        segment.bounds.max_stack,
    );

    for op in ops {
        let Some(id) = op.opaque_id() else {
            if m.exec(op).is_err() {
                return false;
            }
            continue;
        };
        let Some(exp) = expected.get(&id) else {
            return false;
        };
        match m.exec_with_meta(op) {
            Ok(Some(actual)) => {
                if actual.input_symbols.len() != exp.input_symbols.len() {
                    return false;
                }
                for (got, want) in actual.input_symbols.iter().zip(exp.input_symbols.iter()) {
                    let got_expr = parse_value_expr(got);
                    let want_expr = parse_value_expr(want);
                    if !canon.values_equivalent(&got_expr, &want_expr) {
                        return false;
                    }
                }
            }
            Ok(None) => return false,
            Err(_) => return false,
        }
    }
    true
}

/// Full candidate validation: structural checks, opaque operand equivalence, and `fin` grounding.
pub fn solution_valid(
    ops: &[SemOp],
    segment: &StraightSegment,
    canon: &mut Canonizer,
) -> bool {
    validate_solution_ops(ops, segment)
        && opaque_inputs_equivalent(ops, segment, canon)
        && solution_forward_valid(ops, segment, &segment.bounds, canon)
}

fn solution_forward_valid(
    ops: &[SemOp],
    segment: &StraightSegment,
    bounds: &SegmentBounds,
    canon: &mut Canonizer,
) -> bool {
    let exec_bounds = scratch_extended_bounds(bounds, ops);
    let mut m = SymMachine::from_segment_entry(
        segment.num_params,
        &exec_bounds,
        &segment.init,
        bounds.max_stack,
    );
    for op in ops {
        if m.exec(op).is_err() {
            return false;
        }
    }
    let got = m.to_fin_state();
    // Ground against the original bounds so scratch slots (> max_local) are ignored.
    grounded_with(&got, &segment.fin, bounds, canon, GroundEqMode::Saturate)
}

/// Default SAT instruction-length cap when `--split 0` (no chunking).
pub const DEFAULT_MAX_SAT_LEN: usize = 40;

/// SAT encoding limit aligned with `--split` (chunk width); unsplit runs use [`DEFAULT_MAX_SAT_LEN`].
pub fn max_sat_len_for_split(split: usize) -> usize {
    if split > 0 {
        split
    } else {
        DEFAULT_MAX_SAT_LEN
    }
}

/// Solver backend for length minimization.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Backend {
    /// Backward shortest-path A* search (idea.md).
    Astar,
    /// Descending Pure-SAT iteration (wasm_superopt_sat_encoding.md).
    ///
    /// **Must not fall back to A* on failure.** Encoding errors, timeouts, and
    /// `ops = None` from [`super::sat::solve_sat`] are final for this backend.
    #[default]
    Sat,
}

impl Backend {
    pub fn label(self) -> &'static str {
        match self {
            Backend::Astar => "A*",
            Backend::Sat => "SAT",
        }
    }
}

#[derive(Clone, Debug)]
pub struct SearchConfig {
    pub max_depth: usize,
    /// When set, search stops after this many seconds (computed per segment in the driver).
    pub timeout_secs: Option<u64>,
    /// Use 300s per segment instead of `10 * (1 + storage)`.
    pub direct_timeout: bool,
    /// Fixed per-segment timeout; overrides `direct_timeout` and storage-based defaults.
    pub fixed_segment_timeout: Option<u64>,
    /// Solver backend (SAT by default).
    pub backend: Backend,
    /// Max segment length for SAT encoding (`0` in segment → use [`DEFAULT_MAX_SAT_LEN`]).
    pub max_sat_len: usize,
    /// Synthetic scratch locals (SuperStack `local.tee[-1]`) added beyond `max_local` for CSE.
    pub scratch_locals: usize,
}

/// Default number of synthetic scratch locals (SuperStack-style `local.tee[-1]`).
pub const DEFAULT_SCRATCH_LOCALS: usize = 1;

impl Default for SearchConfig {
    fn default() -> Self {
        Self {
            max_depth: DEFAULT_MAX_DEPTH,
            timeout_secs: None,
            direct_timeout: false,
            fixed_segment_timeout: None,
            backend: Backend::default(),
            max_sat_len: DEFAULT_MAX_SAT_LEN,
            scratch_locals: DEFAULT_SCRATCH_LOCALS,
        }
    }
}

impl SearchConfig {
    pub fn for_segment(&self, segment: &StraightSegment) -> Self {
        let timeout = self
            .fixed_segment_timeout
            .unwrap_or_else(|| segment_timeout_secs(segment, self.direct_timeout));
        Self {
            max_depth: self.max_depth,
            timeout_secs: Some(timeout),
            direct_timeout: self.direct_timeout,
            fixed_segment_timeout: self.fixed_segment_timeout,
            backend: self.backend,
            max_sat_len: self.max_sat_len,
            scratch_locals: self.scratch_locals,
        }
    }
}

fn reverse_ops(path: &[SemOp]) -> Vec<SemOp> {
    let mut out = path.to_vec();
    out.reverse();
    out
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct MemoKey {
    goal: NormalizedGoal,
    remaining_storage: Vec<u32>,
    used_opaque: Vec<u32>,
}

pub(crate) fn memo_key(state: &SearchState, canon: &mut Canonizer) -> MemoKey {
    MemoKey {
        goal: canon.normalize_state(&state.goal),
        remaining_storage: state.remaining_storage.iter().copied().collect(),
        used_opaque: state.used_opaque.iter().copied().collect(),
    }
}

fn memo_seen(memo: &HashSet<MemoKey>, state: &SearchState, canon: &mut Canonizer) -> bool {
    memo.contains(&memo_key(state, canon))
}

fn memo_record(memo: &mut HashSet<MemoKey>, state: &SearchState, canon: &mut Canonizer) {
    memo.insert(memo_key(state, canon));
}

fn accept_solution(
    path: &[SemOp],
    segment: &StraightSegment,
    _init: &SymState,
    _bounds: &SegmentBounds,
    canon: &mut Canonizer,
) -> Option<Vec<SemOp>> {
    let ops = reverse_ops(path);
    if solution_valid(&ops, segment, canon) {
        Some(ops)
    } else {
        None
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

pub fn solve_astar_traced(
    segment: &StraightSegment,
    rules: &[Rewrite<ValueLang, ()>],
    cfg: &SearchConfig,
    mut trace: Option<&mut super::search_graph::SearchTrace>,
) -> SearchResult {
    use super::search_graph::NodeKind;

    let init = &segment.init;
    let bounds = &segment.bounds;
    let started = std::time::Instant::now();
    let deadline = cfg.timeout_secs.map(SearchDeadline::new);
    let mut timed_out = false;
    let mut canon = Canonizer::new(rules.to_vec());
    let mut best_path = None;
    let mut best = cfg.max_depth;

    let mut memo = HashSet::new();
    let mut parent_map: std::collections::HashMap<MemoKey, MemoKey> =
        std::collections::HashMap::new();
    let mut heap = BinaryHeap::new();
    let initial = SearchState::initial(segment, &segment.fin);
    let h0 = h_goal(&initial.goal, init, bounds, &mut canon);
    if let Some(tr) = trace.as_deref_mut() {
        let key = memo_key(&initial, &mut canon);
        tr.intern(&key, &initial, 0, NodeKind::Root);
    }
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
        let parent_key = memo_key(&state, &mut canon);
        let parent_id = trace.as_ref().and_then(|tr| tr.node_id(&parent_key));
        if memo_seen(&memo, &state, &mut canon) {
            if let (Some(tr), Some(pid)) = (trace.as_deref_mut(), parent_id) {
                tr.mark_memo_skip(pid);
            }
            continue;
        }
        if is_solution(&state, init, bounds, &mut canon) {
            if let Some(tr) = trace.as_deref_mut() {
                let key = memo_key(&state, &mut canon);
                tr.intern(&key, &state, g, NodeKind::Solution);
            }
            if let Some(ops) = accept_solution(&path, segment, init, bounds, &mut canon) {
                if g <= best {
                    best = g;
                    best_path = Some(ops);
                    if let Some(tr) = trace.as_deref_mut() {
                        let solution_key = memo_key(&state, &mut canon);
                        let mut keys = vec![solution_key.clone()];
                        let mut cur = parent_map.get(&solution_key).cloned();
                        while let Some(k) = cur {
                            keys.push(k.clone());
                            cur = parent_map.get(&k).cloned();
                        }
                        keys.reverse();
                        tr.set_solution_path(&keys);
                    }
                }
                memo_record(&mut memo, &state, &mut canon);
            }
            continue;
        }
        memo_record(&mut memo, &state, &mut canon);
        if g >= cfg.max_depth.min(best) {
            continue;
        }
        for (PeelAction::Forward(op), next) in applicable_peels(&state, segment, bounds, &mut canon)
        {
            let ng = g + 1;
            let nh = h_goal(&next.goal, init, bounds, &mut canon);
            let nf = ng + nh;
            if nf <= best {
                let child_key = memo_key(&next, &mut canon);
                let pruned = memo.contains(&child_key);
                if !pruned {
                    parent_map
                        .entry(child_key.clone())
                        .or_insert(parent_key.clone());
                }
                if let (Some(tr), Some(pid)) = (trace.as_deref_mut(), parent_id) {
                    let child_id = tr.intern(&child_key, &next, ng, NodeKind::Intermediate);
                    tr.add_edge(pid, child_id, &op, pruned);
                }
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
        solver_time_secs: started.elapsed().as_secs_f64(),
        proven_optimal: !timed_out,
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
    use super::{opaque_inputs_equivalent, solution_valid};
    use crate::optimize::canon::Canonizer;
    use crate::semantics::InstKind;
    use crate::sym::{LocalReq, SymState};
    use crate::synthesis::test_synthesis_rewrites;
    use crate::value::{parse_value_expr, ValueOp};

    fn test_rules() -> Vec<egg::Rewrite<crate::lang::ValueLang, ()>> {
        test_synthesis_rewrites()
    }

    #[test]
    fn normalized_memo_key_merges_mul_and_shl_peel_paths() {
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
            .find(|(k, _, _)| *k == InstKind::Pure(ValueOp::I32Mul))
            .unwrap();
        let mut after_mul = g.clone();
        after_mul.stack.pop();
        after_mul.stack.push(e1.clone());
        after_mul.stack.push(e2.clone());
        after_mul.stack.pop();
        let (_, e1s, e2s) = decomps
            .iter()
            .find(|(k, _, _)| *k == InstKind::Pure(ValueOp::I32Shl))
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
    fn unsound_rotl_store_rejected_by_opaque_input_check() {
        use crate::semantics::SemOp;
        use crate::wasm::{materialize_segments, parse_wasm_bytes};
        use std::fs;

        let wasm = fs::read("benchmarks/wsouper/sign_test.wasm").expect("sign_test.wasm");
        let info = parse_wasm_bytes(&wasm).unwrap();
        let raw: Vec<_> = info
            .segments
            .into_iter()
            .filter(|s| s.func_index == 69 && s.segment_index == 0)
            .collect();
        let seg = materialize_segments(&raw, 1).into_iter().next().unwrap();
        let unsound = vec![
            SemOp::LocalGet(0),
            SemOp::I64Const(4611686018427387903),
            SemOp::I64Const(0),
            SemOp::Pure(ValueOp::I64Rotl),
            SemOp::Opaque {
                id: 1,
                pops: 2,
                pushes: 0,
                storage: true,
            },
            SemOp::I32Const(608),
            SemOp::LocalGet(0),
            SemOp::Pure(ValueOp::I64Rotr),
            SemOp::I32Const(608),
            SemOp::Call {
                id: 2,
                func_index: 10,
                pops: 2,
                pushes: 1,
            },
        ];
        let mut canon = Canonizer::new(test_rules());
        assert!(
            !opaque_inputs_equivalent(&unsound, &seg, &mut canon),
            "store/call operands must match original opaque inputs"
        );
        assert!(
            !solution_valid(&unsound, &seg, &mut canon),
            "unsound rewrite must fail full solution validation"
        );
        assert!(
            solution_valid(&seg.ops, &seg, &mut canon),
            "original segment must remain valid"
        );
    }
}
