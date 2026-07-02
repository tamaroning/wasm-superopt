//! Pure-SAT backend for straight-line length minimization.
//!
//! Implements the descending Pure-SAT iteration described in
//! `wasm_superopt_sat_encoding.md`: a finite value vocabulary `V` and operation
//! result tables are built up front (as sparse valid-edge lists from equality
//! saturation), the synthesis problem is encoded into CNF
//! with an instruction-length upper bound `L = L_orig`, and the optimal length is
//! found by repeatedly assuming NOP-propagation (`x_{ell+1,NOP} = 1`) and
//! descending `ell` until the solver returns UNSAT.
//!
//! Side effects (memory / global / call / opaque ops) are handled directly,
//! following the SuperStack approach: each side-effecting op is encoded as an
//! uninterpreted instruction that consumes its operand values and produces fresh
//! result symbols. `storage` ops must appear exactly once, non-storage opaque ops
//! at most once, and the segment's dependency list (`deplist`) is enforced as a
//! relative-order constraint between the corresponding steps.
//!
//! **Design invariant:** if SAT encoding or search fails (timeout, too long, CNF
//! build failure, witness UNSAT, etc.), the optimizer **must not** fall back to
//! the A* backend. The driver reports no model (`optimized = None`) and the
//! segment is left unchanged in the output module.

use super::canon::{CanonId, Canonizer};
use super::search::{SearchConfig, SearchResult, solution_valid};
use crate::lang::ValueLang;
use crate::semantics::{
    InstKind, SemOp, StackTy, const_stack_ty, inst_kind_from_sem, inst_kind_from_value_op,
    inst_kind_is_commutative_binop, sat_pure_ops, sem_from_inst_kind, sem_to_value_op,
    synthesis_const_exprs, value_op_is_binop, value_op_is_unop,
};
use crate::sym::{LocalReq, SymMachine, SymState, ValueExpr, all_subtree_exprs, subtree_expr};
use crate::value::{ValueOp, parse_value_expr};
use crate::wasm::{OpaqueMeta, StraightSegment};
use cadical::{Solver, Timeout};
use std::collections::{HashMap, HashSet};
use std::time::Instant;

/// Minimum value-vocabulary size `|V|` (short straight-line chunks).
const MIN_VOCAB: usize = 64;
/// Hard cap on `|V|` — binop tables are `O(|V|²)` and CNF grows with `|V|`.
const MAX_VOCAB_CAP: usize = 500;
/// Extra slots beyond segment length for synthesis constants and saturation.
const VOCAB_HEADROOM: usize = 20;

/// Scale `|V|` with segment length so long unsplit chunks (e.g. `--split 60`) fit trace values.
fn max_vocab_for_segment(segment: &StraightSegment) -> usize {
    segment
        .ops
        .len()
        .saturating_add(VOCAB_HEADROOM)
        .clamp(MIN_VOCAB, MAX_VOCAB_CAP)
}
/// Abort CNF generation beyond this many clauses (heavy sign_test blocks exceed ~1.5M).
const MAX_CNF_CLAUSES: usize = 8_000_000;
/// Equality-saturation limits for the batched operation-result-table build.
/// Stack-height bound `H` for SAT encoding.
///
/// Tee-fusion / spill-to-stack schedules can require a taller stack than the original
/// trace (`max_height`). Extra slack scales with synthetic scratch locals (SuperStack
/// `tee[-1]`): keeping a value on the stack while computing another needs one extra cell
/// per scratch slot beyond the trace peak.
fn stack_height_bound(
    max_height: usize,
    segment: &StraightSegment,
    scratch_locals: usize,
) -> usize {
    (max_height.saturating_add(scratch_locals).saturating_add(1))
        .max(segment.init.stack.len())
        .max(segment.fin.stack.len())
        .max(1)
        .min(segment.bounds.max_stack)
}

fn stack_ty_of_expr(expr: &ValueExpr) -> Option<StackTy> {
    match &expr[expr.root()] {
        ValueLang::I32Const(_) => Some(StackTy::I32),
        ValueLang::I64Const(_) => Some(StackTy::I64),
        ValueLang::F32Const(_) => Some(StackTy::F32),
        ValueLang::F64Const(_) => Some(StackTy::F64),
        node => ValueOp::from_lang(node).map(|(op, _)| op.push()),
    }
}

/// Stack types referenced by the segment (ops + boundary states).
fn types_in_segment(segment: &StraightSegment) -> HashSet<StackTy> {
    let mut types = HashSet::new();
    for sem in &segment.ops {
        if let Some(ty) = const_stack_ty(sem) {
            types.insert(ty);
        }
        if let Some(v) = sem_to_value_op(sem) {
            for &t in v.pops() {
                types.insert(t);
            }
            types.insert(v.push());
        }
    }
    for e in segment.init.stack.iter().chain(segment.fin.stack.iter()) {
        if let Some(ty) = stack_ty_of_expr(e) {
            types.insert(ty);
        }
    }
    for req in segment
        .init
        .locals
        .values()
        .chain(segment.fin.locals.values())
    {
        if let LocalReq::Need(e) = req {
            if let Some(ty) = stack_ty_of_expr(e) {
                types.insert(ty);
            }
        }
    }
    types
}

/// Synthesis leaf constants limited to types that appear in the segment.
fn synthesis_const_exprs_for_types(types: &HashSet<StackTy>) -> Vec<ValueExpr> {
    synthesis_const_exprs()
        .into_iter()
        .filter(|e| stack_ty_of_expr(e).is_some_and(|ty| types.contains(&ty)))
        .collect()
}

/// Types present in `V` or the original segment — used to prune the SAT op tables.
fn types_in_segment_and_vocab(segment: &StraightSegment, vocab: &Vocab) -> HashSet<StackTy> {
    let mut types = types_in_segment(segment);
    for e in &vocab.reals {
        if let Some(ty) = stack_ty_of_expr(e) {
            types.insert(ty);
        }
    }
    types
}

fn sat_binop_kinds_for(segment: &StraightSegment, vocab: &Vocab) -> Vec<InstKind> {
    let types = types_in_segment_and_vocab(segment, vocab);
    sat_pure_ops()
        .into_iter()
        .filter(|op| value_op_is_binop(*op))
        .filter(|op| op.pops().iter().all(|t| types.contains(t)))
        .map(inst_kind_from_value_op)
        .collect()
}

fn sat_unop_kinds_for(segment: &StraightSegment, vocab: &Vocab) -> Vec<InstKind> {
    let types = types_in_segment_and_vocab(segment, vocab);
    sat_pure_ops()
        .into_iter()
        .filter(|op| value_op_is_unop(*op))
        .filter(|op| op.pops().iter().all(|t| types.contains(t)))
        .map(inst_kind_from_value_op)
        .collect()
}

/// Finite value vocabulary `V`: canonical value classes plus `⊥`/`★` (handled by index).
struct Vocab {
    /// Representative expression per real value index.
    reals: Vec<ValueExpr>,
    /// Per-call `canon()` id at insert time (parallel to `reals`; kept for diagnostics).
    #[allow(dead_code)]
    canon_ids: Vec<CanonId>,
    /// Joint-saturation e-class id per real (parallel to `reals`; for opaque operand pins).
    equiv_class: Vec<usize>,
    /// Canon id → real index.
    index_of_canon: HashMap<CanonId, usize>,
    /// False when `|V|` cap or saturation truncation left the closure incomplete.
    complete: bool,
}

impl Vocab {
    fn n(&self) -> usize {
        self.reals.len()
    }

    fn real_of_expr(&self, canon: &mut Canonizer, expr: &ValueExpr) -> Option<usize> {
        self.index_of_canon.get(&canon.canon(expr)).copied()
    }
}

/// SAT instruction alphabet entry.
#[derive(Clone, Debug)]
enum SatOp {
    Nop,
    Const {
        sem: SemOp,
        val: usize,
    },
    Get(u32),
    Set(u32),
    Tee(u32),
    Drop,
    Unop {
        kind: InstKind,
        /// Valid `(operand, result)` transitions from equality saturation (`T_∘`).
        edges: Vec<(usize, usize)>,
    },
    Binop {
        kind: InstKind,
        /// Valid `(arg1, arg0, result)` transitions from equality saturation (`T_⊕`).
        edges: Vec<(usize, usize, usize)>,
    },
    /// Uninterpreted side-effecting op (memory/global/call/opaque), SuperStack-style.
    Opaque {
        sem: SemOp,
        id: u32,
        storage: bool,
        /// Required operand value (real index) at stack top-position `k`, `k = 0..pops`.
        in_reals: Vec<usize>,
        /// Produced result value (real index) at stack top-position `j`, `j = 0..pushes`.
        out_reals: Vec<usize>,
    },
}

impl SatOp {
    fn to_sem(&self) -> Option<SemOp> {
        match self {
            SatOp::Nop => None,
            SatOp::Const { sem, .. } => Some(sem.clone()),
            SatOp::Get(r) => Some(SemOp::LocalGet(*r)),
            SatOp::Set(r) => Some(SemOp::LocalSet(*r)),
            SatOp::Tee(r) => Some(SemOp::LocalTee(*r)),
            SatOp::Drop => Some(SemOp::Drop),
            SatOp::Unop { kind, .. } => sem_from_inst_kind(*kind),
            SatOp::Binop { kind, .. } => sem_from_inst_kind(*kind),
            SatOp::Opaque { sem, .. } => Some(sem.clone()),
        }
    }
}

/// Encoding dimensions and the CNF variable layout.
struct Dims {
    l: usize,
    h: usize,
    r: usize,
    n: usize,
    n_ops: usize,
    /// Stack value-domain size: `n` real values + `⊥` at index `n` + `⊤` at index `n+1`.
    sd: usize,
    /// Local value-domain size: `n` real values + `★` at index `n`.
    ld: usize,
    base_y: i32,
    base_w: i32,
    next_var: i32,
}

impl Dims {
    fn new(l: usize, h: usize, r: usize, n: usize, n_ops: usize) -> Self {
        let sd = n + 2;
        let ld = n + 1;
        let nx = (l * n_ops) as i32;
        let ny = ((l + 1) * h * sd) as i32;
        let nw = ((l + 1) * r * ld) as i32;
        let base_y = nx;
        let base_w = base_y + ny;
        let next_var = base_w + nw + 1;
        Self {
            l,
            h,
            r,
            n,
            n_ops,
            sd,
            ld,
            base_y,
            base_w,
            next_var,
        }
    }

    fn bot(&self) -> usize {
        self.n
    }

    fn star(&self) -> usize {
        self.n
    }

    /// Out-of-vocabulary sink `⊤` (stack only; never matches boundaries or opaque operands).
    fn top(&self) -> usize {
        self.n + 1
    }

    /// `x_{i,o}` — op `o` chosen at step `i` (1-based steps).
    fn x(&self, i: usize, o: usize) -> i32 {
        debug_assert!(i >= 1 && i <= self.l && o < self.n_ops);
        ((i - 1) * self.n_ops + o) as i32 + 1
    }

    /// `y_{i,j,v}` — stack cell `j` holds value `v` after step `i` (0-based, `i=0` is entry).
    fn y(&self, i: usize, j: usize, v: usize) -> i32 {
        debug_assert!(i <= self.l && j < self.h && v < self.sd);
        self.base_y + ((i * self.h + j) * self.sd + v) as i32 + 1
    }

    /// `w_{i,r,v}` — local `r` holds value `v` after step `i`.
    fn w(&self, i: usize, r: usize, v: usize) -> i32 {
        debug_assert!(i <= self.l && r < self.r && v < self.ld);
        self.base_w + ((i * self.r + r) * self.ld + v) as i32 + 1
    }

    fn fresh(&mut self) -> i32 {
        let v = self.next_var;
        self.next_var += 1;
        v
    }
}

/// Accumulates CNF clauses and feeds them to the solver.
struct Cnf {
    clauses: Vec<Vec<i32>>,
    over_limit: bool,
}

impl Cnf {
    fn new() -> Self {
        Self {
            clauses: Vec::new(),
            over_limit: false,
        }
    }

    fn add(&mut self, clause: Vec<i32>) {
        if self.over_limit {
            return;
        }
        if self.clauses.len() >= MAX_CNF_CLAUSES {
            self.over_limit = true;
            return;
        }
        self.clauses.push(clause);
    }

    fn unit(&mut self, lit: i32) {
        self.add(vec![lit]);
    }

    /// `x → (a ↔ b)`.
    fn imply_iff(&mut self, x: i32, a: i32, b: i32) {
        self.add(vec![-x, -a, b]);
        self.add(vec![-x, a, -b]);
    }

    /// At-most-one over `lits` using a sequential (Sinz) encoding.
    fn at_most_one(&mut self, lits: &[i32], dims: &mut Dims) {
        let n = lits.len();
        if n <= 1 {
            return;
        }
        let s: Vec<i32> = (0..n - 1).map(|_| dims.fresh()).collect();
        self.add(vec![-lits[0], s[0]]);
        self.add(vec![-lits[n - 1], -s[n - 2]]);
        for i in 1..n - 1 {
            self.add(vec![-lits[i], s[i]]);
            self.add(vec![-s[i - 1], s[i]]);
            self.add(vec![-lits[i], -s[i - 1]]);
        }
    }

    /// Exactly-one over `lits` using a sequential (Sinz) at-most-one + at-least-one.
    fn exactly_one(&mut self, lits: &[i32], dims: &mut Dims) {
        if lits.is_empty() {
            // Forces UNSAT; should not occur for well-formed dimensions.
            self.add(vec![]);
            return;
        }
        self.add(lits.to_vec());
        if lits.len() == 1 {
            return;
        }
        let n = lits.len();
        let s: Vec<i32> = (0..n - 1).map(|_| dims.fresh()).collect();
        self.add(vec![-lits[0], s[0]]);
        self.add(vec![-lits[n - 1], -s[n - 2]]);
        for i in 1..n - 1 {
            self.add(vec![-lits[i], s[i]]);
            self.add(vec![-s[i - 1], s[i]]);
            self.add(vec![-lits[i], -s[i - 1]]);
        }
    }
}

/// matching forward execution (`SymMachine::exec_with_meta`).
fn opaque_in_at_top(sem: &SemOp, meta: &OpaqueMeta) -> Vec<String> {
    match sem {
        // Call / Opaque collect inputs top-first then reverse, so `input_symbols[k]`
        // sits at top-position `pops-1-k`; reverse back to get top-position order.
        SemOp::Call { .. } | SemOp::Opaque { .. } => {
            meta.input_symbols.iter().rev().cloned().collect()
        }
        // Load / Store / Global* store inputs in pop order (already top first).
        _ => meta.input_symbols.clone(),
    }
}

/// Result value-expr strings produced at stack top-positions `0..pushes` (top first).
/// The last pushed result ends up on top, so top-position `j` is `result_symbols[pushes-1-j]`.
fn opaque_out_at_top(meta: &OpaqueMeta) -> Vec<String> {
    meta.result_symbols.iter().rev().cloned().collect()
}

fn sem_from_const_expr(expr: &ValueExpr) -> Option<SemOp> {
    match &expr[expr.root()] {
        ValueLang::I32Const(c) => Some(SemOp::I32Const(*c)),
        ValueLang::I64Const(c) => Some(SemOp::I64Const(*c)),
        ValueLang::F32Const(bits) => Some(SemOp::F32Const(bits.0)),
        ValueLang::F64Const(bits) => Some(SemOp::F64Const(bits.0)),
        _ => None,
    }
}

fn const_expr(sem: &SemOp) -> Option<ValueExpr> {
    match sem {
        SemOp::I32Const(c) => Some(parse_value_expr(&c.to_string())),
        SemOp::I64Const(c) => {
            let mut e = egg::RecExpr::default();
            e.add(ValueLang::I64Const(*c));
            Some(e)
        }
        SemOp::F32Const(bits) => {
            let mut e = egg::RecExpr::default();
            e.add(ValueLang::F32Const(crate::lang::F32Bits(*bits)));
            Some(e)
        }
        SemOp::F64Const(bits) => {
            let mut e = egg::RecExpr::default();
            e.add(ValueLang::F64Const(crate::lang::F64Bits(*bits)));
            Some(e)
        }
        _ => None,
    }
}

fn dedup_by_string(exprs: &mut Vec<ValueExpr>) {
    let mut seen = std::collections::HashSet::new();
    exprs.retain(|e| seen.insert(e.to_string()));
}

/// Local slots that need `Get`/`Set`/`Tee` in the SAT alphabet for this segment.
fn active_local_slots(segment: &StraightSegment) -> HashSet<u32> {
    let mut slots = HashSet::new();
    for op in &segment.ops {
        match op {
            SemOp::LocalGet(s) | SemOp::LocalSet(s) | SemOp::LocalTee(s) => {
                slots.insert(*s);
            }
            _ => {}
        }
    }
    for slot in 0..=segment.bounds.max_local {
        let init = segment.init.locals.get(&slot);
        let fin = segment.fin.locals.get(&slot);
        if local_boundary_changed(init, fin) {
            slots.insert(slot);
        }
    }
    slots
}

fn local_boundary_changed(init: Option<&LocalReq>, fin: Option<&LocalReq>) -> bool {
    match (init, fin) {
        (Some(LocalReq::Need(a)), Some(LocalReq::Need(b))) => a != b,
        _ => false,
    }
}

/// How each local slot is tracked through the encoding (`w` variables).
#[derive(Clone, Debug)]
enum LocalSlotKind {
    /// `★` for all steps — no `locals_unchanged` propagation needed.
    FixedStar,
    /// Fixed real index for all steps.
    FixedVal(usize),
    /// May change via `set`/`tee` in the segment.
    Active,
}

fn classify_local_slots(
    segment: &StraightSegment,
    r: usize,
    vocab: &Vocab,
    canon: &mut Canonizer,
) -> Option<Vec<LocalSlotKind>> {
    let mut written = HashSet::new();
    for op in &segment.ops {
        match op {
            SemOp::LocalSet(s) | SemOp::LocalTee(s) => {
                written.insert(*s);
            }
            _ => {}
        }
    }
    let mut kinds = Vec::with_capacity(r);
    for rr in 0..r {
        let slot = rr as u32;
        // Synthetic scratch locals (beyond `max_local`) may hold values via set/tee.
        if slot > segment.bounds.max_local {
            kinds.push(LocalSlotKind::Active);
            continue;
        }
        if written.contains(&slot) {
            kinds.push(LocalSlotKind::Active);
            continue;
        }
        match segment.init.locals.get(&slot) {
            Some(LocalReq::Need(v)) => {
                let idx = vocab.real_of_expr(canon, v)?;
                kinds.push(LocalSlotKind::FixedVal(idx));
            }
            _ => kinds.push(LocalSlotKind::FixedStar),
        }
    }
    Some(kinds)
}

fn pin_fixed_locals(cnf: &mut Cnf, dims: &Dims, local_kinds: &[LocalSlotKind]) {
    let star = dims.star();
    for i in 1..=dims.l {
        for (rr, kind) in local_kinds.iter().enumerate() {
            match kind {
                LocalSlotKind::FixedStar => cnf.unit(dims.w(i, rr, star)),
                LocalSlotKind::FixedVal(v) => cnf.unit(dims.w(i, rr, *v)),
                LocalSlotKind::Active => {}
            }
        }
    }
}

fn insert_binop_edge(edges: &mut Vec<(usize, usize, usize)>, edge: (usize, usize, usize)) {
    if !edges.contains(&edge) {
        edges.push(edge);
    }
}

fn symmetrize_commutative_binop_edges(kind: InstKind, edges: &mut Vec<(usize, usize, usize)>) {
    if !inst_kind_is_commutative_binop(kind) {
        return;
    }
    let mut extra = Vec::new();
    for &(a1, a0, res) in edges.iter() {
        let swapped = (a0, a1, res);
        if !edges.contains(&swapped) && !extra.contains(&swapped) {
            extra.push(swapped);
        }
    }
    edges.extend(extra);
}

fn merge_binop_edge(ops: &mut Vec<SatOp>, kind: InstKind, edge: (usize, usize, usize)) {
    let mut to_add = vec![edge];
    if inst_kind_is_commutative_binop(kind) {
        let (a1, a0, res) = edge;
        to_add.push((a0, a1, res));
    }
    if let Some(SatOp::Binop { edges, .. }) = ops
        .iter_mut()
        .find(|o| matches!(o, SatOp::Binop { kind: k, .. } if *k == kind))
    {
        for e in to_add {
            insert_binop_edge(edges, e);
        }
    } else {
        let mut edges = Vec::new();
        for e in to_add {
            insert_binop_edge(&mut edges, e);
        }
        ops.push(SatOp::Binop { kind, edges });
    }
}

fn merge_unop_edge(ops: &mut Vec<SatOp>, kind: InstKind, edge: (usize, usize)) {
    if let Some(SatOp::Unop { edges, .. }) = ops
        .iter_mut()
        .find(|o| matches!(o, SatOp::Unop { kind: k, .. } if *k == kind))
    {
        if !edges.contains(&edge) {
            edges.push(edge);
        }
    } else {
        ops.push(SatOp::Unop {
            kind,
            edges: vec![edge],
        });
    }
}

fn ensure_const_op(ops: &mut Vec<SatOp>, sem: &SemOp, val: usize) {
    if ops
        .iter()
        .any(|o| matches!(o, SatOp::Const { sem: s, val: v } if sem_eq_const(s, sem) && *v == val))
    {
        return;
    }
    ops.push(SatOp::Const {
        sem: sem.clone(),
        val,
    });
}

/// §2.1.4: operational transitions for the original trace (O(|σ|), not O(|V|²)).
///
/// Batched e-graph maps result e-classes via vocab node membership; when a class
/// does not contain any `reals[i]` (or the trace result index differs), this pass
/// adds the missing `T_⊕` / `T_∘` rows needed for a witness at `L_orig`.
fn merge_trace_witness_tables(
    segment: &StraightSegment,
    vocab: &Vocab,
    canon: &mut Canonizer,
    ops: &mut Vec<SatOp>,
) -> Option<()> {
    let mut m = SymMachine::from_segment_entry(
        segment.num_params,
        &segment.bounds,
        &segment.init,
        segment.bounds.max_stack,
    );
    for op in &segment.ops {
        match op {
            SemOp::I32Const(_) | SemOp::I64Const(_) | SemOp::F32Const(_) | SemOp::F64Const(_) => {
                let expr = const_expr(op)?;
                let val = vocab.real_of_expr(canon, &expr)?;
                ensure_const_op(ops, op, val);
            }
            SemOp::LocalGet(_) | SemOp::LocalSet(_) | SemOp::LocalTee(_) | SemOp::Drop => {}
            SemOp::I32Load { .. }
            | SemOp::I32Store { .. }
            | SemOp::Call { .. }
            | SemOp::GlobalGet { .. }
            | SemOp::GlobalSet { .. }
            | SemOp::Opaque { .. } => {}
            other => {
                let vop = sem_to_value_op(other)?;
                let kind = inst_kind_from_sem(other)?;
                if vop.pops().len() == 2 {
                    let st = m.to_carried_init_state();
                    let len = st.stack.len();
                    if len < 2 {
                        return None;
                    }
                    let a0_expr = st.stack[len - 1].clone();
                    let a1_expr = st.stack[len - 2].clone();
                    m.exec(op).ok()?;
                    let st = m.to_carried_init_state();
                    let res_expr = st.stack.last()?.clone();
                    let a1 = vocab.real_of_expr(canon, &a1_expr)?;
                    let a0 = vocab.real_of_expr(canon, &a0_expr)?;
                    let res = vocab.real_of_expr(canon, &res_expr)?;
                    merge_binop_edge(ops, kind, (a1, a0, res));
                } else {
                    let st = m.to_carried_init_state();
                    let len = st.stack.len();
                    if len < 1 {
                        return None;
                    }
                    let a_expr = st.stack[len - 1].clone();
                    m.exec(op).ok()?;
                    let st = m.to_carried_init_state();
                    let res_expr = st.stack.last()?.clone();
                    let a = vocab.real_of_expr(canon, &a_expr)?;
                    let res = vocab.real_of_expr(canon, &res_expr)?;
                    merge_unop_edge(ops, kind, (a, res));
                }
                continue;
            }
        }
        m.exec(op).ok()?;
    }
    Some(())
}

/// Goal-oriented seeds: `fin` stack/local values and their subtrees (SuperStack-style).
fn collect_fin_oriented_seed_exprs(segment: &StraightSegment) -> Vec<ValueExpr> {
    let mut seeds = Vec::new();
    for e in &segment.fin.stack {
        seeds.push(e.clone());
        seeds.extend(all_subtree_exprs(e));
    }
    for req in segment.fin.locals.values() {
        if let LocalReq::Need(v) = req {
            seeds.push(v.clone());
            seeds.extend(all_subtree_exprs(v));
        }
    }
    seeds
}

/// Close pure-op witness tables over all semantically defined pairs in `V` (Denali-style `T` closure).
///
/// Unlike trace-only witnesses, this lets SAT pick operand order and stack schedules whenever
/// both operands and the result already live in `V` (modulo `≡_R`).
fn merge_vocab_operational_witness_tables(
    segment: &StraightSegment,
    vocab: &Vocab,
    canon: &mut Canonizer,
    ops: &mut Vec<SatOp>,
    deadline: Instant,
) -> Option<()> {
    let n = vocab.n();
    let binop_kinds = sat_binop_kinds_for(segment, vocab);
    let unop_kinds = sat_unop_kinds_for(segment, vocab);

    for kind in binop_kinds {
        if Instant::now() >= deadline {
            return None;
        }
        let Some(sem) = sem_from_inst_kind(kind) else {
            continue;
        };
        let Some(vop) = sem_to_value_op(&sem) else {
            continue;
        };
        let pops = vop.pops();
        if pops.len() != 2 {
            continue;
        }
        let (ty1, ty0) = (pops[0], pops[1]);
        for a1 in 0..n {
            if Instant::now() >= deadline {
                return None;
            }
            let e1 = &vocab.reals[a1];
            if stack_ty_of_expr(e1) != Some(ty1) {
                continue;
            }
            for a0 in 0..n {
                let e0 = &vocab.reals[a0];
                if stack_ty_of_expr(e0) != Some(ty0) {
                    continue;
                }
                let mut init = segment.init.clone();
                init.stack = vec![e1.clone(), e0.clone()];
                let mut m = SymMachine::from_segment_entry(
                    segment.num_params,
                    &segment.bounds,
                    &init,
                    segment.bounds.max_stack.max(2),
                );
                if m.exec(&sem).is_err() {
                    continue;
                }
                let Some(res_expr) = m.to_fin_state().stack.last().cloned() else {
                    continue;
                };
                if let Some(res) = vocab.real_of_expr(canon, &res_expr) {
                    merge_binop_edge(ops, kind, (a1, a0, res));
                }
            }
        }
    }

    for kind in unop_kinds {
        if Instant::now() >= deadline {
            return None;
        }
        let Some(sem) = sem_from_inst_kind(kind) else {
            continue;
        };
        let Some(vop) = sem_to_value_op(&sem) else {
            continue;
        };
        let pops = vop.pops();
        if pops.len() != 1 {
            continue;
        }
        let ty = pops[0];
        for a in 0..n {
            let e = &vocab.reals[a];
            if stack_ty_of_expr(e) != Some(ty) {
                continue;
            }
            let mut init = segment.init.clone();
            init.stack = vec![e.clone()];
            let mut m = SymMachine::from_segment_entry(
                segment.num_params,
                &segment.bounds,
                &init,
                segment.bounds.max_stack.max(1),
            );
            if m.exec(&sem).is_err() {
                continue;
            }
            let Some(res_expr) = m.to_fin_state().stack.last().cloned() else {
                continue;
            };
            if let Some(res) = vocab.real_of_expr(canon, &res_expr) {
                merge_unop_edge(ops, kind, (a, res));
            }
        }
    }
    Some(())
}

/// Forward-execute the original ops, collecting all stack/local values and the max stack height.
fn collect_seed_exprs(segment: &StraightSegment) -> (Vec<ValueExpr>, usize) {
    let mut seeds = Vec::new();
    let mut max_height = 0usize;

    let push_state = |seeds: &mut Vec<ValueExpr>, st: &SymState, max_h: &mut usize| {
        *max_h = (*max_h).max(st.stack.len());
        for e in &st.stack {
            seeds.push(e.clone());
        }
        for req in st.locals.values() {
            if let LocalReq::Need(v) = req {
                seeds.push(v.clone());
            }
        }
    };

    push_state(&mut seeds, &segment.init, &mut max_height);
    push_state(&mut seeds, &segment.fin, &mut max_height);

    // Operand and result value-expressions of every opaque op MUST be in `V` so the
    // original (side-effectful) sequence is representable in the encoding.
    for meta in &segment.opaque_meta {
        for sym in meta.input_symbols.iter().chain(meta.result_symbols.iter()) {
            seeds.push(parse_value_expr(sym));
        }
    }

    let mut m = SymMachine::from_segment_entry(
        segment.num_params,
        &segment.bounds,
        &segment.init,
        segment.bounds.max_stack,
    );
    push_state(&mut seeds, &m.to_fin_state(), &mut max_height);
    for op in &segment.ops {
        if m.exec(op).is_err() {
            break;
        }
        push_state(&mut seeds, &m.to_fin_state(), &mut max_height);
    }

    (seeds, max_height)
}

fn build_vocab(
    segment: &StraightSegment,
    canon: &mut Canonizer,
    deadline: Instant,
) -> Option<(Vocab, usize)> {
    build_vocab_with_limit(segment, canon, max_vocab_for_segment(segment), deadline)
}

fn try_insert_vocab(
    e: &ValueExpr,
    canon: &mut Canonizer,
    max_vocab: usize,
    index_of_canon: &mut HashMap<CanonId, usize>,
    reals: &mut Vec<ValueExpr>,
    canon_ids: &mut Vec<CanonId>,
) -> bool {
    if reals.len() >= max_vocab {
        return false;
    }
    let id = canon.canon(e);
    if let std::collections::hash_map::Entry::Vacant(slot) = index_of_canon.entry(id) {
        slot.insert(reals.len());
        canon_ids.push(id);
        reals.push(e.clone());
    }
    true
}

fn build_vocab_with_limit(
    segment: &StraightSegment,
    canon: &mut Canonizer,
    max_vocab: usize,
    deadline: Instant,
) -> Option<(Vocab, usize)> {
    if Instant::now() >= deadline {
        return None;
    }
    let (seeds, max_height) = collect_seed_exprs(segment);

    let mut index_of_canon: HashMap<CanonId, usize> = HashMap::new();
    let mut reals: Vec<ValueExpr> = Vec::new();
    let mut canon_ids: Vec<CanonId> = Vec::new();
    let mut complete = true;

    // V = SubExpr(EqSat(SubExpr(seed))) where seed = trace + boundaries + opaque symbols
    // + fin-oriented values + type-filtered synthesis constants.
    let types = types_in_segment(segment);
    let mut core: Vec<ValueExpr> = seeds;
    core.extend(collect_fin_oriented_seed_exprs(segment));
    core.extend(synthesis_const_exprs_for_types(&types));
    dedup_by_string(&mut core);

    let mut sub0: Vec<ValueExpr> = Vec::new();
    for e in &core {
        sub0.extend(all_subtree_exprs(e));
    }
    dedup_by_string(&mut sub0);

    if Instant::now() >= deadline {
        return None;
    }
    let saturated = canon.joint_saturate_materialize(&sub0);

    let mut closure: Vec<ValueExpr> = Vec::new();
    for e in &saturated {
        closure.extend(all_subtree_exprs(e));
    }
    dedup_by_string(&mut closure);

    for e in &closure {
        if Instant::now() >= deadline {
            return None;
        }
        if reals.len() >= max_vocab {
            complete = false;
            break;
        }
        if !try_insert_vocab(
            e,
            canon,
            max_vocab,
            &mut index_of_canon,
            &mut reals,
            &mut canon_ids,
        ) {
            complete = false;
            break;
        }
    }

    // Core seeds must all be representable for the original-program witness.
    for e in &core {
        let id = canon.canon(e);
        if !index_of_canon.contains_key(&id) {
            return None;
        }
    }

    if reals.is_empty() {
        return None;
    }

    if Instant::now() >= deadline {
        return None;
    }
    let equiv_class = canon.equiv_partition(&reals);

    Some((
        Vocab {
            reals,
            canon_ids,
            equiv_class,
            index_of_canon,
            complete,
        },
        max_height,
    ))
}

/// Relative indices in `V` that are ≡_R-equivalent to `req` (for opaque operand pins).
fn equiv_reals(vocab: &Vocab, req: usize) -> Vec<usize> {
    let target = vocab.equiv_class[req];
    vocab
        .equiv_class
        .iter()
        .enumerate()
        .filter_map(|(i, &ec)| (ec == target).then_some(i))
        .collect()
}

fn same_equiv(vocab: &Vocab, a: usize, b: usize) -> bool {
    vocab.equiv_class[a] == vocab.equiv_class[b]
}

/// When `xio`, stack cell `src(v)` and `dst(v)` must denote the same ≡_R class.
fn pin_transfer_equiv(
    cnf: &mut Cnf,
    xio: i32,
    vocab: &Vocab,
    n: usize,
    src: impl Fn(usize) -> i32,
    dst: impl Fn(usize) -> i32,
) {
    for v1 in 0..n {
        for v2 in 0..n {
            if !same_equiv(vocab, v1, v2) {
                cnf.add(vec![-xio, -src(v1), -dst(v2)]);
            }
        }
    }
}

fn push_binop_edge(
    edges: &mut Vec<(usize, usize, usize)>,
    vocab: &Vocab,
    kind: InstKind,
    a1: usize,
    a0: usize,
    res: usize,
) {
    for e1 in equiv_reals(vocab, a1) {
        for e0 in equiv_reals(vocab, a0) {
            for r in equiv_reals(vocab, res) {
                insert_binop_edge(edges, (e1, e0, r));
                if inst_kind_is_commutative_binop(kind) {
                    insert_binop_edge(edges, (e0, e1, r));
                }
            }
        }
    }
}

fn push_unop_edge(edges: &mut Vec<(usize, usize)>, vocab: &Vocab, a: usize, res: usize) {
    for e in equiv_reals(vocab, a) {
        for r in equiv_reals(vocab, res) {
            let edge = (e, r);
            if !edges.contains(&edge) {
                edges.push(edge);
            }
        }
    }
}

/// Extract pure-op transition tables from structural decompositions present in `V`.
fn extract_pure_edges_from_vocab(
    vocab: &Vocab,
    canon: &mut Canonizer,
    sat_binops: &HashSet<InstKind>,
    sat_unops: &HashSet<InstKind>,
) -> (
    HashMap<InstKind, Vec<(usize, usize, usize)>>,
    HashMap<InstKind, Vec<(usize, usize)>>,
) {
    let mut binop_edges: HashMap<InstKind, Vec<(usize, usize, usize)>> = HashMap::new();
    let mut unop_edges: HashMap<InstKind, Vec<(usize, usize)>> = HashMap::new();

    for (res_idx, expr) in vocab.reals.iter().enumerate() {
        let root = expr.root();
        let Some((vop, child_ids)) = ValueOp::from_lang(&expr[root]) else {
            continue;
        };
        let kind = inst_kind_from_value_op(vop);
        if child_ids.len() == 2 && sat_binops.contains(&kind) {
            let a1_expr = subtree_expr(expr, child_ids[0]);
            let a0_expr = subtree_expr(expr, child_ids[1]);
            if let (Some(a1), Some(a0)) = (
                vocab.real_of_expr(canon, &a1_expr),
                vocab.real_of_expr(canon, &a0_expr),
            ) {
                push_binop_edge(
                    binop_edges.entry(kind).or_default(),
                    vocab,
                    kind,
                    a1,
                    a0,
                    res_idx,
                );
            }
        } else if child_ids.len() == 1 && sat_unops.contains(&kind) {
            let a_expr = subtree_expr(expr, child_ids[0]);
            if let Some(a) = vocab.real_of_expr(canon, &a_expr) {
                push_unop_edge(unop_edges.entry(kind).or_default(), vocab, a, res_idx);
            }
        }
    }

    (binop_edges, unop_edges)
}

/// Build the SAT instruction alphabet (NOP first), pruning ops with no defined result.
///
/// Pure-op tables are extracted from structural decompositions already present in `V`
/// (no `V×V` candidate applications). Trace witness rows are merged separately.
fn build_ops(
    segment: &StraightSegment,
    vocab: &Vocab,
    canon: &mut Canonizer,
    _rules: &[egg::Rewrite<ValueLang, ()>],
    r: usize,
    deadline: Instant,
) -> Option<Vec<SatOp>> {
    if Instant::now() >= deadline {
        return None;
    }
    let mut ops = vec![SatOp::Nop];
    let types = types_in_segment_and_vocab(segment, vocab);
    let sat_binops = sat_binop_kinds_for(segment, vocab);
    let sat_unops = sat_unop_kinds_for(segment, vocab);

    // Constants: synthesis constants (for types in V) plus literals already present.
    let mut const_candidates: Vec<SemOp> = Vec::new();
    for e in synthesis_const_exprs() {
        if let Some(sem) = sem_from_const_expr(&e) {
            if const_stack_ty(&sem).is_some_and(|ty| types.contains(&ty)) {
                const_candidates.push(sem);
            }
        }
    }
    for real in &vocab.reals {
        if let Some(sem) = sem_from_const_expr(real) {
            const_candidates.push(sem);
        }
    }
    const_candidates.sort_by(|a, b| format!("{a:?}").cmp(&format!("{b:?}")));
    const_candidates.dedup_by(|a, b| format!("{a:?}") == format!("{b:?}"));
    for sem in const_candidates {
        let expr = const_expr(&sem)?;
        if let Some(val) = vocab.real_of_expr(canon, &expr) {
            ops.push(SatOp::Const { sem, val });
        }
    }
    let mut active_slots: Vec<u32> = active_local_slots(segment).into_iter().collect();
    active_slots.sort();
    for slot in active_slots {
        ops.push(SatOp::Get(slot));
        ops.push(SatOp::Set(slot));
        ops.push(SatOp::Tee(slot));
    }
    // Synthetic scratch locals (SuperStack `local.tee[-1]`): slots beyond `max_local`.
    for slot in (segment.bounds.max_local + 1)..(r as u32) {
        ops.push(SatOp::Get(slot));
        ops.push(SatOp::Set(slot));
        ops.push(SatOp::Tee(slot));
    }
    ops.push(SatOp::Drop);

    let sat_binop_set: HashSet<InstKind> = sat_binops.into_iter().collect();
    let sat_unop_set: HashSet<InstKind> = sat_unops.into_iter().collect();
    let (binop_edges, unop_edges) =
        extract_pure_edges_from_vocab(vocab, canon, &sat_binop_set, &sat_unop_set);

    if Instant::now() >= deadline {
        return None;
    }

    for (kind, mut edges) in binop_edges {
        symmetrize_commutative_binop_edges(kind, &mut edges);
        if !edges.is_empty() {
            ops.push(SatOp::Binop { kind, edges });
        }
    }
    for (kind, edges) in unop_edges {
        if !edges.is_empty() {
            ops.push(SatOp::Unop { kind, edges });
        }
    }

    merge_trace_witness_tables(segment, vocab, canon, &mut ops)?;
    merge_vocab_operational_witness_tables(segment, vocab, canon, &mut ops, deadline)?;
    for op in ops.iter_mut() {
        if let SatOp::Binop { kind, edges } = op {
            symmetrize_commutative_binop_edges(*kind, edges);
        }
    }

    // Side-effecting / uninterpreted ops (SuperStack-style). Each is one instruction
    // that requires its operand values on top and produces fresh result symbols.
    let sem_by_id: HashMap<u32, &SemOp> = segment
        .ops
        .iter()
        .filter_map(|op| op.opaque_id().map(|id| (id, op)))
        .collect();
    for meta in &segment.opaque_meta {
        let sem = (*sem_by_id.get(&meta.id)?).clone();
        let mut in_reals = Vec::new();
        for sym in opaque_in_at_top(&sem, meta) {
            in_reals.push(vocab.real_of_expr(canon, &parse_value_expr(&sym))?);
        }
        let mut out_reals = Vec::new();
        for sym in opaque_out_at_top(meta) {
            out_reals.push(vocab.real_of_expr(canon, &parse_value_expr(&sym))?);
        }
        ops.push(SatOp::Opaque {
            sem,
            id: meta.id,
            storage: meta.storage,
            in_reals,
            out_reals,
        });
    }

    Some(ops)
}

fn pin_stack_equiv(cnf: &mut Cnf, dims: &Dims, vocab: &Vocab, i: usize, j: usize, req: usize) {
    let lits = equiv_reals(vocab, req)
        .into_iter()
        .map(|v| dims.y(i, j, v))
        .collect();
    cnf.add(lits);
}

fn pin_local_equiv(cnf: &mut Cnf, dims: &Dims, vocab: &Vocab, i: usize, rr: usize, req: usize) {
    let lits = equiv_reals(vocab, req)
        .into_iter()
        .map(|v| dims.w(i, rr, v))
        .collect();
    cnf.add(lits);
}

/// Pin one SAT op per original instruction step (`x_{i,o} = 1`).
fn sat_op_index_for_orig(ops: &[SatOp], sem: &SemOp) -> Option<usize> {
    match sem {
        SemOp::I32Const(_) | SemOp::I64Const(_) | SemOp::F32Const(_) | SemOp::F64Const(_) => ops
            .iter()
            .position(|o| matches!(o, SatOp::Const { sem: s, .. } if sem_eq_const(s, sem))),
        SemOp::LocalGet(s) => ops
            .iter()
            .position(|o| matches!(o, SatOp::Get(slot) if slot == s)),
        SemOp::LocalSet(s) => ops
            .iter()
            .position(|o| matches!(o, SatOp::Set(slot) if slot == s)),
        SemOp::LocalTee(s) => ops
            .iter()
            .position(|o| matches!(o, SatOp::Tee(slot) if slot == s)),
        SemOp::Drop => ops.iter().position(|o| matches!(o, SatOp::Drop)),
        SemOp::I32Load { id, .. }
        | SemOp::I32Store { id, .. }
        | SemOp::Call { id, .. }
        | SemOp::GlobalGet { id, .. }
        | SemOp::GlobalSet { id, .. }
        | SemOp::Opaque { id, .. } => ops
            .iter()
            .position(|o| matches!(o, SatOp::Opaque { id: oid, .. } if oid == id)),
        other => {
            let kind = inst_kind_from_sem(other)?;
            ops.iter().position(|o| match o {
                SatOp::Unop { kind: k, .. } | SatOp::Binop { kind: k, .. } => *k == kind,
                _ => false,
            })
        }
    }
}

fn sem_eq_const(a: &SemOp, b: &SemOp) -> bool {
    match (a, b) {
        (SemOp::I32Const(x), SemOp::I32Const(y)) => x == y,
        (SemOp::I64Const(x), SemOp::I64Const(y)) => x == y,
        (SemOp::F32Const(x), SemOp::F32Const(y)) => x == y,
        (SemOp::F64Const(x), SemOp::F64Const(y)) => x == y,
        _ => false,
    }
}

fn original_witness_assumptions(
    segment: &StraightSegment,
    ops: &[SatOp],
    dims: &Dims,
) -> Option<Vec<i32>> {
    Some(
        segment
            .ops
            .iter()
            .map(|sem| sat_op_index_for_orig(ops, sem))
            .collect::<Option<Vec<_>>>()?
            .into_iter()
            .enumerate()
            .map(|(step, o)| dims.x(step + 1, o))
            .collect(),
    )
}

/// NOP is always the first entry of the instruction alphabet.
const NOP_INDEX: usize = 0;

/// Stack position `j` (0 = top) maps to `SymState.stack[len-1-j]` (bottom-to-top vec).
fn stack_expr_at(state: &SymState, j: usize) -> Option<&ValueExpr> {
    let len = state.stack.len();
    if j < len {
        state.stack.get(len - 1 - j)
    } else {
        None
    }
}

/// Emit binop positive clauses with ≡_R operand matching; keep exact-index forbids.
fn encode_binop_positive_equiv(
    cnf: &mut Cnf,
    dims: &Dims,
    i: usize,
    xio: i32,
    vocab: &Vocab,
    edges: &[(usize, usize, usize)],
) {
    let n = dims.n;
    let mut by_ec_pair: HashMap<(usize, usize), HashSet<usize>> = HashMap::new();
    for &(a1, a0, res) in edges {
        by_ec_pair
            .entry((vocab.equiv_class[a1], vocab.equiv_class[a0]))
            .or_default()
            .insert(vocab.equiv_class[res]);
    }
    for ((ec1, ec0), res_ecs) in &by_ec_pair {
        let reps1: Vec<usize> = (0..n).filter(|&v| vocab.equiv_class[v] == *ec1).collect();
        let reps0: Vec<usize> = (0..n).filter(|&v| vocab.equiv_class[v] == *ec0).collect();
        for &v1 in &reps1 {
            for &v0 in &reps0 {
                let mut clause = vec![-xio, -dims.y(i - 1, 1, v1), -dims.y(i - 1, 0, v0)];
                for &ec_res in res_ecs {
                    for r in 0..n {
                        if vocab.equiv_class[r] == ec_res {
                            clause.push(dims.y(i, 0, r));
                        }
                    }
                }
                cnf.add(clause);
            }
        }
    }
}

/// Emit unop positive clauses with ≡_R operand matching.
fn encode_unop_positive_equiv(
    cnf: &mut Cnf,
    dims: &Dims,
    i: usize,
    xio: i32,
    vocab: &Vocab,
    edges: &[(usize, usize)],
) {
    let n = dims.n;
    let mut by_arg_ec: HashMap<usize, HashSet<usize>> = HashMap::new();
    for &(a, res) in edges {
        by_arg_ec
            .entry(vocab.equiv_class[a])
            .or_default()
            .insert(vocab.equiv_class[res]);
    }
    for (ec_a, res_ecs) in &by_arg_ec {
        for v in 0..n {
            if vocab.equiv_class[v] != *ec_a {
                continue;
            }
            let mut clause = vec![-xio, -dims.y(i - 1, 0, v)];
            for &ec_res in res_ecs {
                for r in 0..n {
                    if vocab.equiv_class[r] == ec_res {
                        clause.push(dims.y(i, 0, r));
                    }
                }
            }
            cnf.add(clause);
        }
    }
}

/// Emit all consistency, boundary, semantics, and NOP-propagation clauses.
fn encode(
    segment: &StraightSegment,
    vocab: &Vocab,
    ops: &[SatOp],
    dims: &mut Dims,
    canon: &mut Canonizer,
    deadline: Instant,
) -> Option<Cnf> {
    let mut cnf = Cnf::new();
    let l = dims.l;
    let h = dims.h;
    let r = dims.r;
    let n = dims.n;
    let sd = dims.sd;
    let ld = dims.ld;
    let bot = dims.bot();
    let star = dims.star();
    let top = dims.top();
    let nop = NOP_INDEX;
    let past = |cnf: &Cnf| Instant::now() >= deadline || cnf.over_limit;
    let local_kinds = classify_local_slots(segment, r, vocab, canon)?;

    // §5.1 instruction uniqueness.
    for i in 1..=l {
        if past(&cnf) {
            return None;
        }
        let lits: Vec<i32> = (0..dims.n_ops).map(|o| dims.x(i, o)).collect();
        cnf.exactly_one(&lits, dims);
    }
    // §5.1 stack/local value uniqueness.
    for i in 0..=l {
        if past(&cnf) {
            return None;
        }
        for j in 0..h {
            let lits: Vec<i32> = (0..sd).map(|v| dims.y(i, j, v)).collect();
            cnf.exactly_one(&lits, dims);
        }
        for rr in 0..r {
            let lits: Vec<i32> = (0..ld).map(|v| dims.w(i, rr, v)).collect();
            cnf.exactly_one(&lits, dims);
        }
    }

    // §5.2 boundary (entry).
    let init = &segment.init;
    for j in 0..h {
        if let Some(e) = stack_expr_at(init, j) {
            let v = vocab.real_of_expr(canon, e)?;
            cnf.unit(dims.y(0, j, v));
        } else {
            cnf.unit(dims.y(0, j, bot));
        }
    }
    for rr in 0..r {
        match init.locals.get(&(rr as u32)) {
            Some(LocalReq::Need(v)) => {
                let idx = vocab.real_of_expr(canon, v)?;
                cnf.unit(dims.w(0, rr, idx));
            }
            _ => cnf.unit(dims.w(0, rr, star)),
        }
    }
    pin_fixed_locals(&mut cnf, dims, &local_kinds);

    // §5.2 boundary (final).
    let fin = &segment.fin;
    for j in 0..h {
        if let Some(e) = stack_expr_at(fin, j) {
            let v = vocab.real_of_expr(canon, e)?;
            pin_stack_equiv(&mut cnf, dims, vocab, l, j, v);
        } else {
            cnf.unit(dims.y(l, j, bot));
        }
    }
    for rr in 0..r {
        // Synthetic scratch locals (beyond `max_local`) are dead at exit → unconstrained.
        if rr as u32 > segment.bounds.max_local {
            continue;
        }
        match fin.locals.get(&(rr as u32)) {
            Some(LocalReq::Need(v)) => {
                let idx = vocab.real_of_expr(canon, v)?;
                pin_local_equiv(&mut cnf, dims, vocab, l, rr, idx);
            }
            Some(LocalReq::DontCare) => {
                // Explicitly dead at exit → unconstrained.
            }
            None => {
                // Absent from `fin` means unchanged from entry (`to_fin_state` only lists
                // changed slots), so the exit value must equal the entry value.
                match init.locals.get(&(rr as u32)) {
                    Some(LocalReq::Need(v)) => {
                        let idx = vocab.real_of_expr(canon, v)?;
                        pin_local_equiv(&mut cnf, dims, vocab, l, rr, idx);
                    }
                    _ => cnf.unit(dims.w(l, rr, star)),
                }
            }
        }
    }

    // §5.3 semantics.
    for i in 1..=l {
        if past(&cnf) {
            return None;
        }
        for (o, op) in ops.iter().enumerate() {
            let xio = dims.x(i, o);
            match op {
                SatOp::Nop => {
                    stack_unchanged(&mut cnf, dims, i, xio);
                    locals_unchanged(&mut cnf, dims, i, xio, &local_kinds);
                }
                SatOp::Const { val, .. } => {
                    cnf.add(vec![-xio, dims.y(i - 1, h - 1, bot)]);
                    cnf.add(vec![-xio, dims.y(i, 0, *val)]);
                    stack_push_shift(&mut cnf, dims, i, xio);
                    locals_unchanged(&mut cnf, dims, i, xio, &local_kinds);
                }
                SatOp::Get(slot) => {
                    let slot = *slot as usize;
                    cnf.add(vec![-xio, -dims.w(i - 1, slot, star)]);
                    cnf.add(vec![-xio, dims.y(i - 1, h - 1, bot)]);
                    pin_transfer_equiv(
                        &mut cnf,
                        xio,
                        vocab,
                        n,
                        |v| dims.w(i - 1, slot, v),
                        |v| dims.y(i, 0, v),
                    );
                    stack_push_shift(&mut cnf, dims, i, xio);
                    locals_unchanged(&mut cnf, dims, i, xio, &local_kinds);
                }
                SatOp::Set(slot) => {
                    let slot = *slot as usize;
                    cnf.add(vec![-xio, -dims.y(i - 1, 0, bot)]);
                    cnf.add(vec![-xio, -dims.y(i - 1, 0, top)]);
                    pin_transfer_equiv(
                        &mut cnf,
                        xio,
                        vocab,
                        n,
                        |v| dims.y(i - 1, 0, v),
                        |v| dims.w(i, slot, v),
                    );
                    locals_unchanged_except(&mut cnf, dims, i, xio, slot, &local_kinds);
                    stack_pop_shift(&mut cnf, dims, i, xio, 0);
                }
                SatOp::Tee(slot) => {
                    let slot = *slot as usize;
                    cnf.add(vec![-xio, -dims.y(i - 1, 0, bot)]);
                    cnf.add(vec![-xio, -dims.y(i - 1, 0, top)]);
                    pin_transfer_equiv(
                        &mut cnf,
                        xio,
                        vocab,
                        n,
                        |v| dims.y(i - 1, 0, v),
                        |v| dims.w(i, slot, v),
                    );
                    locals_unchanged_except(&mut cnf, dims, i, xio, slot, &local_kinds);
                    stack_unchanged(&mut cnf, dims, i, xio);
                }
                SatOp::Drop => {
                    cnf.add(vec![-xio, -dims.y(i - 1, 0, bot)]);
                    stack_pop_shift(&mut cnf, dims, i, xio, 0);
                    locals_unchanged(&mut cnf, dims, i, xio, &local_kinds);
                }
                SatOp::Unop { edges, .. } => {
                    cnf.add(vec![-xio, -dims.y(i - 1, 0, bot)]);
                    cnf.add(vec![-xio, -dims.y(i - 1, 0, top)]);
                    encode_unop_positive_equiv(&mut cnf, dims, i, xio, vocab, edges);
                    let mut allowed_arg_ec: HashSet<usize> = HashSet::new();
                    for &(a, _) in edges {
                        allowed_arg_ec.insert(vocab.equiv_class[a]);
                    }
                    for v in 0..n {
                        if !allowed_arg_ec.contains(&vocab.equiv_class[v]) {
                            cnf.add(vec![-xio, -dims.y(i - 1, 0, v)]);
                        }
                    }
                    for j in 1..h {
                        for v in 0..sd {
                            cnf.imply_iff(xio, dims.y(i, j, v), dims.y(i - 1, j, v));
                        }
                    }
                    locals_unchanged(&mut cnf, dims, i, xio, &local_kinds);
                }
                SatOp::Binop { edges, .. } => {
                    cnf.add(vec![-xio, -dims.y(i - 1, 0, bot)]);
                    cnf.add(vec![-xio, -dims.y(i - 1, 1, bot)]);
                    cnf.add(vec![-xio, -dims.y(i - 1, 0, top)]);
                    cnf.add(vec![-xio, -dims.y(i - 1, 1, top)]);
                    encode_binop_positive_equiv(&mut cnf, dims, i, xio, vocab, edges);
                    let mut allowed_ec_pairs: HashSet<(usize, usize)> = HashSet::new();
                    let mut allowed_first_ec: HashSet<usize> = HashSet::new();
                    for &(a1, a0, _) in edges {
                        allowed_ec_pairs.insert((vocab.equiv_class[a1], vocab.equiv_class[a0]));
                        allowed_first_ec.insert(vocab.equiv_class[a1]);
                    }
                    for ec1 in vocab.equiv_class.iter().copied().collect::<HashSet<_>>() {
                        for ec0 in vocab.equiv_class.iter().copied().collect::<HashSet<_>>() {
                            if allowed_ec_pairs.contains(&(ec1, ec0)) {
                                continue;
                            }
                            for v1 in 0..n {
                                if vocab.equiv_class[v1] != ec1 {
                                    continue;
                                }
                                for v0 in 0..n {
                                    if vocab.equiv_class[v0] != ec0 {
                                        continue;
                                    }
                                    cnf.add(vec![
                                        -xio,
                                        -dims.y(i - 1, 1, v1),
                                        -dims.y(i - 1, 0, v0),
                                    ]);
                                }
                            }
                        }
                    }
                    for v1 in 0..n {
                        if !allowed_first_ec.contains(&vocab.equiv_class[v1]) {
                            cnf.add(vec![-xio, -dims.y(i - 1, 1, v1)]);
                        }
                    }
                    stack_pop_shift(&mut cnf, dims, i, xio, 1);
                    locals_unchanged(&mut cnf, dims, i, xio, &local_kinds);
                }
                SatOp::Opaque {
                    in_reals,
                    out_reals,
                    ..
                } => {
                    encode_opaque(
                        &mut cnf,
                        dims,
                        i,
                        xio,
                        vocab,
                        in_reals,
                        out_reals,
                        &local_kinds,
                    );
                }
            }
        }
    }

    // §5.4 NOP propagation.
    for i in 1..l {
        cnf.add(vec![-dims.x(i, nop), dims.x(i + 1, nop)]);
    }

    // Side-effect bookkeeping (SuperStack): `storage` ops appear exactly once,
    // non-storage opaque ops at most once, and `deplist` order is respected.
    let mut op_index_of_id: HashMap<u32, usize> = HashMap::new();
    for (o, op) in ops.iter().enumerate() {
        if let SatOp::Opaque { id, storage, .. } = op {
            op_index_of_id.insert(*id, o);
            let occ: Vec<i32> = (1..=l).map(|i| dims.x(i, o)).collect();
            if *storage {
                cnf.exactly_one(&occ, dims);
            } else {
                cnf.at_most_one(&occ, dims);
            }
        }
    }
    // Relative-order constraints: `step(before) < step(after)`.
    // Equivalent to ∀ ia≤ib: ¬(after@ia ∧ before@ib), encoded in O(L) clauses per edge.
    for &(before, after) in &segment.dependencies {
        if past(&cnf) {
            return None;
        }
        if let (Some(&ob), Some(&oa)) = (op_index_of_id.get(&before), op_index_of_id.get(&after)) {
            cnf.add(vec![-dims.x(1, oa), -dims.x(1, ob)]);
            for ia in 2..=l {
                let mut clause = vec![-dims.x(ia, oa)];
                for ib in 1..ia {
                    clause.push(dims.x(ib, ob));
                }
                cnf.add(clause);
            }
        }
    }

    if past(&cnf) {
        return None;
    }
    Some(cnf)
}

/// Encode a SuperStack-style uninterpreted op: require `in_reals` (or any ≡_R
/// equivalent) on top, produce `out_reals`, and shift the rest of the stack.
fn encode_opaque(
    cnf: &mut Cnf,
    dims: &Dims,
    i: usize,
    xio: i32,
    vocab: &Vocab,
    in_reals: &[usize],
    out_reals: &[usize],
    local_kinds: &[LocalSlotKind],
) {
    let h = dims.h;
    let sd = dims.sd;
    let n = dims.n;
    let bot = dims.bot();
    let p = in_reals.len();
    let q = out_reals.len();

    // Operands: any real value ≡_R to the required symbol (e.g. ?L6 for 0*40+x).
    for (k, &req) in in_reals.iter().enumerate() {
        let equiv = equiv_reals(vocab, req);
        let equiv_set: HashSet<usize> = equiv.iter().copied().collect();
        let mut clause = vec![-xio];
        for &v in &equiv {
            clause.push(dims.y(i - 1, k, v));
        }
        cnf.add(clause);
        for v in 0..n {
            if !equiv_set.contains(&v) {
                cnf.add(vec![-xio, -dims.y(i - 1, k, v)]);
            }
        }
    }
    // Results occupy the top `q` cells after the step.
    for (j, &v) in out_reals.iter().enumerate() {
        cnf.add(vec![-xio, dims.y(i, j, v)]);
    }
    // Stack below the consumed/produced region shifts by `delta = p - q`.
    let delta = p as isize - q as isize;
    for j in q..h {
        let src = j as isize + delta;
        if src >= 0 && (src as usize) < h {
            for v in 0..sd {
                cnf.imply_iff(xio, dims.y(i, j, v), dims.y(i - 1, src as usize, v));
            }
        } else {
            // Shrinking past the bottom → cell becomes `⊥`.
            cnf.add(vec![-xio, dims.y(i, j, bot)]);
        }
    }
    // Growth (q > p) needs empty space: the bottom `q - p` cells must be `⊥` on entry.
    if q > p {
        for t in 0..(q - p) {
            cnf.add(vec![-xio, dims.y(i - 1, h - 1 - t, bot)]);
        }
    }

    locals_unchanged(cnf, dims, i, xio, local_kinds);
}

fn stack_unchanged(cnf: &mut Cnf, dims: &Dims, i: usize, xio: i32) {
    for j in 0..dims.h {
        for v in 0..dims.sd {
            cnf.imply_iff(xio, dims.y(i, j, v), dims.y(i - 1, j, v));
        }
    }
}

/// Push-by-one: `y[i][0]` is set elsewhere; deeper cells copy from `y[i-1][j-1]`.
fn stack_push_shift(cnf: &mut Cnf, dims: &Dims, i: usize, xio: i32) {
    for j in 1..dims.h {
        for v in 0..dims.sd {
            cnf.imply_iff(xio, dims.y(i, j, v), dims.y(i - 1, j - 1, v));
        }
    }
}

/// Pop `pops` items net 1: `y[i][j] = y[i-1][j+1]` for `j ≥ keep_from`, top filled with `⊥`.
///
/// `keep_from = 0` for `set` (1-in 0-out); `keep_from = 1` for binops (2-in 1-out, top is result).
fn stack_pop_shift(cnf: &mut Cnf, dims: &Dims, i: usize, xio: i32, keep_from: usize) {
    for j in keep_from..dims.h - 1 {
        for v in 0..dims.sd {
            cnf.imply_iff(xio, dims.y(i, j, v), dims.y(i - 1, j + 1, v));
        }
    }
    cnf.add(vec![-xio, dims.y(i, dims.h - 1, dims.bot())]);
}

fn locals_unchanged(cnf: &mut Cnf, dims: &Dims, i: usize, xio: i32, local_kinds: &[LocalSlotKind]) {
    for (rr, kind) in local_kinds.iter().enumerate() {
        if !matches!(kind, LocalSlotKind::Active) {
            continue;
        }
        for v in 0..dims.ld {
            cnf.imply_iff(xio, dims.w(i, rr, v), dims.w(i - 1, rr, v));
        }
    }
}

fn locals_unchanged_except(
    cnf: &mut Cnf,
    dims: &Dims,
    i: usize,
    xio: i32,
    slot: usize,
    local_kinds: &[LocalSlotKind],
) {
    for (rr, kind) in local_kinds.iter().enumerate() {
        if rr == slot || !matches!(kind, LocalSlotKind::Active) {
            continue;
        }
        for v in 0..dims.ld {
            cnf.imply_iff(xio, dims.w(i, rr, v), dims.w(i - 1, rr, v));
        }
    }
}

fn reconstruct(solver: &Solver, dims: &Dims, ops: &[SatOp]) -> Vec<SemOp> {
    let mut seq = Vec::new();
    for i in 1..=dims.l {
        for (o, op) in ops.iter().enumerate() {
            if solver.value(dims.x(i, o)) == Some(true) {
                if let Some(sem) = op.to_sem() {
                    seq.push(sem);
                }
                break;
            }
        }
    }
    seq
}

fn block_current_op_model(solver: &mut Solver, dims: &Dims) -> bool {
    let mut clause = Vec::with_capacity(dims.l);
    for i in 1..=dims.l {
        for o in 0..dims.n_ops {
            if solver.value(dims.x(i, o)) == Some(true) {
                clause.push(-dims.x(i, o));
                break;
            }
        }
    }
    if clause.is_empty() {
        return false;
    }
    solver.add_clause(clause.iter().copied());
    true
}

fn forward_valid(ops: &[SemOp], segment: &StraightSegment, canon: &mut Canonizer) -> bool {
    solution_valid(ops, segment, canon)
}

/// CNF scale and timing breakdown for one segment (debug / benchmark analysis).
#[derive(Clone, Debug)]
pub struct SatCnfProfile {
    pub l: usize,
    pub h: usize,
    pub r: usize,
    pub vocab: usize,
    pub n_ops: usize,
    pub n_binop_ops: usize,
    pub n_binop_edges: usize,
    pub n_unop_edges: usize,
    pub n_opaque_ops: usize,
    pub n_vars: usize,
    pub n_clauses: usize,
    pub max_clause_len: usize,
    pub vocab_ms: f64,
    pub ops_ms: f64,
    pub encode_ms: f64,
    pub add_clauses_ms: f64,
    pub witness_ms: f64,
    pub diagnosis: SatDiagnosis,
}

impl SatCnfProfile {
    pub fn print(&self, block_id: &str) {
        eprintln!("=== SAT profile: {block_id} ===");
        eprintln!(
            "  dims: L={} H={} R={} |V|={} |OP|={} (binop ops={} edges={} unop edges={} opaque={})",
            self.l,
            self.h,
            self.r,
            self.vocab,
            self.n_ops,
            self.n_binop_ops,
            self.n_binop_edges,
            self.n_unop_edges,
            self.n_opaque_ops
        );
        eprintln!(
            "  CNF: {} vars, {} clauses (max width {})",
            self.n_vars, self.n_clauses, self.max_clause_len
        );
        eprintln!(
            "  time: vocab={:.1}ms ops={:.1}ms encode={:.1}ms add_clauses={:.1}ms witness={:.1}ms",
            self.vocab_ms, self.ops_ms, self.encode_ms, self.add_clauses_ms, self.witness_ms
        );
        eprintln!("  diagnosis: {:?}", self.diagnosis);
    }
}

/// Build CNF and run witness SAT; return scale/timing without the descending loop.
pub fn profile_sat(
    segment: &StraightSegment,
    rules: &[egg::Rewrite<crate::lang::ValueLang, ()>],
    cfg: &SearchConfig,
) -> Result<SatCnfProfile, &'static str> {
    let l_orig = segment.ops.len();
    if l_orig == 0 || l_orig > cfg.max_sat_len {
        return Err("too_long");
    }

    let timeout = cfg
        .timeout_secs
        .unwrap_or(super::search::DEFAULT_TIMEOUT_BASE_SECS);
    let deadline = Instant::now() + std::time::Duration::from_secs(timeout);

    let t0 = Instant::now();
    let mut canon = Canonizer::new(rules.to_vec());
    let (vocab, max_height) = build_vocab(segment, &mut canon, deadline).ok_or("vocab")?;
    let vocab_ms = t0.elapsed().as_secs_f64() * 1000.0;

    let t1 = Instant::now();
    let r = (segment.bounds.max_local as usize) + 1 + cfg.scratch_locals;
    let ops = build_ops(segment, &vocab, &mut canon, rules, r, deadline).ok_or("ops")?;
    let ops_ms = t1.elapsed().as_secs_f64() * 1000.0;
    let n_binop_ops = ops
        .iter()
        .filter(|op| matches!(op, SatOp::Binop { .. }))
        .count();
    let n_binop_edges = ops
        .iter()
        .filter_map(|op| match op {
            SatOp::Binop { edges, .. } => Some(edges.len()),
            _ => None,
        })
        .sum();
    let n_unop_edges = ops
        .iter()
        .filter_map(|op| match op {
            SatOp::Unop { edges, .. } => Some(edges.len()),
            _ => None,
        })
        .sum();
    let n_opaque_ops = ops
        .iter()
        .filter(|op| matches!(op, SatOp::Opaque { .. }))
        .count();

    let h = stack_height_bound(max_height, segment, cfg.scratch_locals);

    let t2 = Instant::now();
    let mut dims = Dims::new(l_orig, h, r, vocab.n(), ops.len());
    let cnf = encode(segment, &vocab, &ops, &mut dims, &mut canon, deadline).ok_or("encode")?;
    let encode_ms = t2.elapsed().as_secs_f64() * 1000.0;
    let n_vars = (dims.next_var - 1) as usize;
    let n_clauses = cnf.clauses.len();
    let max_clause_len = cnf.clauses.iter().map(|c| c.len()).max().unwrap_or(0);

    let t3 = Instant::now();
    let mut solver: Solver = Solver::new();
    for clause in &cnf.clauses {
        solver.add_clause(clause.iter().copied());
    }
    let add_clauses_ms = t3.elapsed().as_secs_f64() * 1000.0;

    let remaining = |now: Instant| deadline.saturating_duration_since(now).as_secs_f32();
    let witness = original_witness_assumptions(segment, &ops, &dims);
    let t4 = Instant::now();
    let diagnosis = if witness.is_none() {
        SatDiagnosis::OriginalWitnessMissingOp
    } else {
        solver.set_callbacks(Some(Timeout::new(remaining(Instant::now()).max(0.0))));
        match solver.solve_with(witness.unwrap().iter().copied()) {
            Some(true) => {
                let seq = reconstruct(&solver, &dims, &ops);
                if forward_valid(&seq, segment, &mut canon) {
                    SatDiagnosis::Solved {
                        best_len: l_orig,
                        proven_optimal: false,
                        timed_out: false,
                    }
                } else {
                    SatDiagnosis::OriginalModelInvalid
                }
            }
            Some(false) => SatDiagnosis::OriginalWitnessUnsat,
            None => SatDiagnosis::Solved {
                best_len: l_orig,
                proven_optimal: false,
                timed_out: true,
            },
        }
    };
    let witness_ms = t4.elapsed().as_secs_f64() * 1000.0;

    Ok(SatCnfProfile {
        l: l_orig,
        h,
        r,
        vocab: vocab.n(),
        n_ops: ops.len(),
        n_binop_ops,
        n_binop_edges,
        n_unop_edges,
        n_opaque_ops,
        n_vars,
        n_clauses,
        max_clause_len,
        vocab_ms,
        ops_ms,
        encode_ms,
        add_clauses_ms,
        witness_ms,
        diagnosis,
    })
}

/// Where `solve_sat` stopped (for debugging benchmark gaps vs SuperStack).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SatDiagnosis {
    TooLong {
        l_orig: usize,
        max: usize,
    },
    VocabBuildFailed,
    OpsBuildFailed,
    EncodeFailed {
        vocab: usize,
        n_ops: usize,
        h: usize,
        r: usize,
    },
    /// `sat_op_index_for_orig` failed for at least one original step.
    OriginalWitnessMissingOp,
    /// Witness assumptions built but SAT returned UNSAT.
    OriginalWitnessUnsat,
    OriginalModelInvalid,
    Solved {
        best_len: usize,
        proven_optimal: bool,
        timed_out: bool,
    },
}

/// Inspect SAT pipeline stages without running the full descending loop (unless encoding succeeds).
pub fn diagnose_sat(
    segment: &StraightSegment,
    rules: &[egg::Rewrite<crate::lang::ValueLang, ()>],
    cfg: &SearchConfig,
) -> SatDiagnosis {
    let l_orig = segment.ops.len();
    if l_orig == 0 || l_orig > cfg.max_sat_len {
        return SatDiagnosis::TooLong {
            l_orig,
            max: cfg.max_sat_len,
        };
    }

    let timeout = cfg
        .timeout_secs
        .unwrap_or(super::search::DEFAULT_TIMEOUT_BASE_SECS);
    let deadline = Instant::now() + std::time::Duration::from_secs(timeout);

    let mut canon = Canonizer::new(rules.to_vec());
    let Some((vocab, max_height)) = build_vocab(segment, &mut canon, deadline) else {
        return SatDiagnosis::VocabBuildFailed;
    };

    let r = (segment.bounds.max_local as usize) + 1 + cfg.scratch_locals;
    let Some(ops) = build_ops(segment, &vocab, &mut canon, rules, r, deadline) else {
        return SatDiagnosis::OpsBuildFailed;
    };

    let h = stack_height_bound(max_height, segment, cfg.scratch_locals);

    let mut dims = Dims::new(l_orig, h, r, vocab.n(), ops.len());
    let Some(cnf) = encode(segment, &vocab, &ops, &mut dims, &mut canon, deadline) else {
        return SatDiagnosis::EncodeFailed {
            vocab: vocab.n(),
            n_ops: ops.len(),
            h,
            r,
        };
    };

    let mut solver: Solver = Solver::new();
    for clause in &cnf.clauses {
        solver.add_clause(clause.iter().copied());
    }
    let remaining = |now: Instant| deadline.saturating_duration_since(now).as_secs_f32();
    let Some(witness) = original_witness_assumptions(segment, &ops, &dims) else {
        return SatDiagnosis::OriginalWitnessMissingOp;
    };
    solver.set_callbacks(Some(Timeout::new(remaining(Instant::now()).max(0.0))));
    match solver.solve_with(witness.iter().copied()) {
        Some(true) => {}
        Some(false) => return SatDiagnosis::OriginalWitnessUnsat,
        None => {
            return SatDiagnosis::Solved {
                best_len: l_orig,
                proven_optimal: false,
                timed_out: true,
            };
        }
    }

    let seq = reconstruct(&solver, &dims, &ops);
    if !forward_valid(&seq, segment, &mut canon) {
        return SatDiagnosis::OriginalModelInvalid;
    }

    let mut best_len = seq.len();
    let nop = NOP_INDEX;
    let mut ell = l_orig as isize - 1;
    let mut timed_out = false;
    let mut proven_optimal = false;
    let mut saw_invalid_model = false;
    let encoding_complete = vocab.complete;
    'lengths: while ell >= 0 {
        loop {
            let now = Instant::now();
            if now >= deadline {
                timed_out = true;
                break 'lengths;
            }
            solver.set_callbacks(Some(Timeout::new(remaining(now).max(0.0))));
            let assumption = dims.x((ell as usize) + 1, nop);
            match solver.solve_with([assumption]) {
                Some(true) => {
                    let seq = reconstruct(&solver, &dims, &ops);
                    if forward_valid(&seq, segment, &mut canon) {
                        best_len = best_len.min(seq.len());
                        ell -= 1;
                        break;
                    }
                    saw_invalid_model = true;
                    if !block_current_op_model(&mut solver, &dims) {
                        timed_out = true;
                        break 'lengths;
                    }
                }
                Some(false) => {
                    proven_optimal = true;
                    break 'lengths;
                }
                None => {
                    timed_out = true;
                    break 'lengths;
                }
            }
        }
    }

    proven_optimal = proven_optimal && encoding_complete && !saw_invalid_model && !timed_out;

    SatDiagnosis::Solved {
        best_len,
        proven_optimal,
        timed_out,
    }
}

/// One row of gap analysis output.
#[derive(Clone, Debug)]
pub struct SatGapRow {
    pub diagnosis: SatDiagnosis,
}

/// Load `combined_blocks.csv` and return block ids where SuperStack improved but ewasm
/// did not improve and did not time out.
pub fn problem_blocks_from_csv(csv_path: &std::path::Path) -> std::io::Result<Vec<String>> {
    use std::collections::HashMap;

    let mut by_id: HashMap<String, (usize, usize, String)> = HashMap::new();
    let mut rdr = csv::Reader::from_path(csv_path)?;
    let headers = rdr.headers()?.clone();
    let col = |name: &str| headers.iter().position(|h| h == name);

    let block_id_i = col("block_id").expect("block_id column");
    let saved_i = col("saved_length").expect("saved_length column");
    let outcome_i = col("outcome").expect("outcome column");
    let tool_i = col("tool").expect("tool column");

    for row in rdr.records() {
        let row = row?;
        let Some(bid) = row.get(block_id_i).filter(|s| s.starts_with("function_")) else {
            continue;
        };
        let tool = row.get(tool_i).unwrap_or("");
        let saved: usize = row.get(saved_i).and_then(|s| s.parse().ok()).unwrap_or(0);
        let outcome = row.get(outcome_i).unwrap_or("").to_string();
        let entry = by_id
            .entry(bid.to_string())
            .or_insert((0, 0, String::new()));
        if tool == "superstack" {
            entry.0 = saved;
        } else if tool == "ewasm" {
            entry.1 = saved;
            entry.2 = outcome;
        }
    }

    let mut out = Vec::new();
    for (bid, (ss_saved, ew_saved, ew_outcome)) in by_id {
        if ss_saved == 0 || ew_saved > 0 {
            continue;
        }
        if ew_outcome == "timeout" || ew_outcome == "non_optimal" {
            continue;
        }
        out.push(bid);
    }
    out.sort();
    Ok(out)
}

/// Parallel SAT diagnosis for benchmark gap blocks (`-j` / Rayon).
pub fn classify_sat_gaps_parallel(
    segments: &[StraightSegment],
    problem_ids: &[String],
    rules: &[egg::Rewrite<crate::lang::ValueLang, ()>],
    cfg: &SearchConfig,
    jobs: usize,
) -> Vec<SatGapRow> {
    use crate::optimize::statistics::block_id;
    use rayon::prelude::*;
    use std::collections::HashMap;

    let seg_by_id: HashMap<String, &StraightSegment> =
        segments.iter().map(|s| (block_id(s), s)).collect();

    let work: Vec<(&StraightSegment, &str)> = problem_ids
        .iter()
        .filter_map(|bid| seg_by_id.get(bid).map(|s| (*s, bid.as_str())))
        .collect();

    let classify = |seg: &StraightSegment, _bid: &str| -> SatGapRow {
        SatGapRow {
            diagnosis: diagnose_sat(seg, rules, cfg),
        }
    };

    if jobs <= 1 {
        work.into_iter()
            .map(|(seg, bid)| classify(seg, bid))
            .collect()
    } else {
        crate::parallel::run_with_threads(jobs, || {
            work.par_iter()
                .map(|(seg, bid)| classify(seg, bid))
                .collect()
        })
    }
}

/// Print a summary table of gap diagnoses to stderr.
pub fn print_gap_summary(rows: &[SatGapRow]) {
    use std::collections::BTreeMap;

    let mut counts: BTreeMap<String, usize> = BTreeMap::new();
    for row in rows {
        let key = format!("{:?}", row.diagnosis);
        *counts.entry(key).or_default() += 1;
    }
    eprintln!("\n=== SAT gap classification ({} blocks) ===", rows.len());
    for (k, v) in counts {
        eprintln!("  {v:4} {k}");
    }
}

/// Solve a segment with descending Pure-SAT iteration (side effects included).
///
/// On any failure path, returns `ops = None`. The caller **must not** invoke A*
/// as a fallback; [`super::optimize_segment_with_trace`] relies on this contract.
pub fn solve_sat(
    segment: &StraightSegment,
    rules: &[egg::Rewrite<crate::lang::ValueLang, ()>],
    cfg: &SearchConfig,
) -> SearchResult {
    let started = Instant::now();
    let timeout = cfg
        .timeout_secs
        .unwrap_or(super::search::DEFAULT_TIMEOUT_BASE_SECS);
    let deadline = started + std::time::Duration::from_secs(timeout);
    let timed_out_now = || Instant::now() >= deadline;
    let timeout_result = || SearchResult {
        ops: None,
        timed_out: true,
        solver_time_secs: started.elapsed().as_secs_f64(),
        proven_optimal: false,
    };

    let l_orig = segment.ops.len();
    // Hard failure: no model. Do not fall back to A* — see module-level invariant.
    let fail = || SearchResult {
        ops: None,
        timed_out: false,
        solver_time_secs: started.elapsed().as_secs_f64(),
        proven_optimal: false,
    };

    if l_orig == 0 || l_orig > cfg.max_sat_len {
        return fail();
    }

    let mut canon = Canonizer::new(rules.to_vec());
    let Some((vocab, max_height)) = build_vocab(segment, &mut canon, deadline) else {
        if timed_out_now() {
            return timeout_result();
        }
        return fail();
    };
    if timed_out_now() {
        return timeout_result();
    }

    let r = (segment.bounds.max_local as usize) + 1 + cfg.scratch_locals;
    let Some(ops) = build_ops(segment, &vocab, &mut canon, rules, r, deadline) else {
        if timed_out_now() {
            return timeout_result();
        }
        return fail();
    };
    if timed_out_now() {
        return timeout_result();
    }

    // Stack-height bound: original max height (+1 slack), capped by segment bounds.
    let h = stack_height_bound(max_height, segment, cfg.scratch_locals);

    let mut dims = Dims::new(l_orig, h, r, vocab.n(), ops.len());
    let Some(cnf) = encode(segment, &vocab, &ops, &mut dims, &mut canon, deadline) else {
        if timed_out_now() {
            return timeout_result();
        }
        return fail();
    };
    if timed_out_now() {
        return timeout_result();
    }

    let mut solver: Solver = Solver::new();
    for clause in &cnf.clauses {
        if timed_out_now() {
            return timeout_result();
        }
        solver.add_clause(clause.iter().copied());
    }

    let nop = NOP_INDEX;
    let remaining = |now: Instant| deadline.saturating_duration_since(now).as_secs_f32();

    // Step 1: the original program must be a model (witness at L_orig).
    let Some(witness) = original_witness_assumptions(segment, &ops, &dims) else {
        return fail();
    };
    solver.set_callbacks(Some(Timeout::new(remaining(Instant::now()).max(0.0))));
    match solver.solve_with(witness.iter().copied()) {
        Some(true) => {}
        Some(false) => return fail(), // encoding incomplete → keep original
        None => {
            return SearchResult {
                ops: None,
                timed_out: true,
                solver_time_secs: started.elapsed().as_secs_f64(),
                proven_optimal: false,
            };
        }
    }

    let mut best: Option<Vec<SemOp>> = {
        let seq = reconstruct(&solver, &dims, &ops);
        if forward_valid(&seq, segment, &mut canon) {
            Some(seq)
        } else {
            return fail();
        }
    };

    let mut timed_out = false;
    let mut proven_optimal = false;
    let mut saw_invalid_model = false;
    let encoding_complete = vocab.complete;
    let mut ell = l_orig as isize - 1;
    'lengths: while ell >= 0 {
        loop {
            let now = Instant::now();
            if now >= deadline {
                timed_out = true;
                break 'lengths;
            }
            solver.set_callbacks(Some(Timeout::new(remaining(now).max(0.0))));
            let assumption = dims.x((ell as usize) + 1, nop);
            match solver.solve_with([assumption]) {
                Some(true) => {
                    let seq = reconstruct(&solver, &dims, &ops);
                    if forward_valid(&seq, segment, &mut canon) {
                        best = Some(seq);
                        ell -= 1;
                        break;
                    }
                    saw_invalid_model = true;
                    if !block_current_op_model(&mut solver, &dims) {
                        timed_out = true;
                        break 'lengths;
                    }
                }
                Some(false) => {
                    proven_optimal = true;
                    break 'lengths;
                }
                None => {
                    timed_out = true;
                    break 'lengths;
                }
            }
        }
    }

    proven_optimal = proven_optimal && encoding_complete && !saw_invalid_model && !timed_out;

    SearchResult {
        ops: best,
        timed_out,
        solver_time_secs: started.elapsed().as_secs_f64(),
        proven_optimal,
    }
}

/// Solve assuming the first NOP appears at step `first_nop_step` (length = `first_nop_step - 1`).
#[cfg(test)]
pub(crate) fn solve_at_length_with_h(
    segment: &StraightSegment,
    rules: &[egg::Rewrite<crate::lang::ValueLang, ()>],
    cfg: &super::search::SearchConfig,
    h: usize,
    first_nop_step: usize,
    deadline: Instant,
) -> Option<SolveAtLengthResult> {
    let l_orig = segment.ops.len();
    if l_orig == 0 || first_nop_step == 0 || first_nop_step > l_orig {
        return None;
    }
    let mut canon = Canonizer::new(rules.to_vec());
    let (vocab, _) = build_vocab(segment, &mut canon, deadline)?;
    let r = (segment.bounds.max_local as usize) + 1 + cfg.scratch_locals;
    let ops = build_ops(segment, &vocab, &mut canon, rules, r, deadline)?;
    let mut dims = Dims::new(l_orig, h, r, vocab.n(), ops.len());
    let cnf = encode(segment, &vocab, &ops, &mut dims, &mut canon, deadline)?;
    let mut solver: Solver = Solver::new();
    for clause in &cnf.clauses {
        solver.add_clause(clause.iter().copied());
    }
    let remaining = |now: Instant| deadline.saturating_duration_since(now).as_secs_f32();
    let nop = NOP_INDEX;
    let assumption = dims.x(first_nop_step, nop);
    loop {
        let now = Instant::now();
        if now >= deadline {
            return Some(SolveAtLengthResult {
                sat: false,
                valid: false,
                seq: None,
                timed_out: true,
            });
        }
        solver.set_callbacks(Some(Timeout::new(remaining(now).max(0.0))));
        match solver.solve_with([assumption]) {
            Some(true) => {
                let seq = reconstruct(&solver, &dims, &ops);
                let valid = forward_valid(&seq, segment, &mut canon);
                if valid {
                    return Some(SolveAtLengthResult {
                        sat: true,
                        valid: true,
                        seq: Some(seq),
                        timed_out: false,
                    });
                }
                if !block_current_op_model(&mut solver, &dims) {
                    return Some(SolveAtLengthResult {
                        sat: true,
                        valid: false,
                        seq: None,
                        timed_out: true,
                    });
                }
            }
            Some(false) => {
                return Some(SolveAtLengthResult {
                    sat: false,
                    valid: false,
                    seq: None,
                    timed_out: false,
                });
            }
            None => {
                return Some(SolveAtLengthResult {
                    sat: false,
                    valid: false,
                    seq: None,
                    timed_out: true,
                });
            }
        }
    }
}

/// Solve at one step below `segment.ops.len()` with an explicit stack-height bound (diagnostics).
#[cfg(test)]
pub(crate) fn solve_at_length_minus_one_with_h(
    segment: &StraightSegment,
    rules: &[egg::Rewrite<crate::lang::ValueLang, ()>],
    cfg: &super::search::SearchConfig,
    h: usize,
    deadline: Instant,
) -> Option<SolveAtLengthResult> {
    let l_orig = segment.ops.len();
    if l_orig == 0 {
        return None;
    }
    let mut canon = Canonizer::new(rules.to_vec());
    let (vocab, _) = build_vocab(segment, &mut canon, deadline)?;
    let r = (segment.bounds.max_local as usize) + 1 + cfg.scratch_locals;
    let ops = build_ops(segment, &vocab, &mut canon, rules, r, deadline)?;
    let mut dims = Dims::new(l_orig, h, r, vocab.n(), ops.len());
    let cnf = encode(segment, &vocab, &ops, &mut dims, &mut canon, deadline)?;
    let mut solver: Solver = Solver::new();
    for clause in &cnf.clauses {
        solver.add_clause(clause.iter().copied());
    }
    let remaining = |now: Instant| deadline.saturating_duration_since(now).as_secs_f32();
    let nop = NOP_INDEX;
    let assumption = dims.x(l_orig, nop);
    loop {
        let now = Instant::now();
        if now >= deadline {
            return Some(SolveAtLengthResult {
                sat: false,
                valid: false,
                seq: None,
                timed_out: true,
            });
        }
        solver.set_callbacks(Some(Timeout::new(remaining(now).max(0.0))));
        match solver.solve_with([assumption]) {
            Some(true) => {
                let seq = reconstruct(&solver, &dims, &ops);
                let valid = forward_valid(&seq, segment, &mut canon);
                if valid {
                    return Some(SolveAtLengthResult {
                        sat: true,
                        valid: true,
                        seq: Some(seq),
                        timed_out: false,
                    });
                }
                if !block_current_op_model(&mut solver, &dims) {
                    return Some(SolveAtLengthResult {
                        sat: true,
                        valid: false,
                        seq: None,
                        timed_out: true,
                    });
                }
            }
            Some(false) => {
                return Some(SolveAtLengthResult {
                    sat: false,
                    valid: false,
                    seq: None,
                    timed_out: false,
                });
            }
            None => {
                return Some(SolveAtLengthResult {
                    sat: false,
                    valid: false,
                    seq: None,
                    timed_out: true,
                });
            }
        }
    }
}

/// Outcome of a fixed-length SAT probe (test diagnostics).
#[cfg(test)]
#[derive(Clone, Debug)]
pub(crate) struct SolveAtLengthResult {
    pub sat: bool,
    pub valid: bool,
    pub seq: Option<Vec<SemOp>>,
    pub timed_out: bool,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::synthesis::test_synthesis_rewrites;
    use crate::value::parse_value_expr;
    use crate::wasm::{materialize_segments, parse_wasm_file, split_raw_segments};

    fn rules() -> Vec<egg::Rewrite<crate::lang::ValueLang, ()>> {
        test_synthesis_rewrites()
    }

    /// Phase-1 core vocabulary size (unique ≡_R classes) without subtree/saturation expansion.
    fn core_vocab_size(
        segment: &StraightSegment,
        rules: &[egg::Rewrite<crate::lang::ValueLang, ()>],
    ) -> usize {
        let mut canon = Canonizer::new(rules.to_vec());
        let limit = max_vocab_for_segment(segment);
        build_vocab_with_limit(
            segment,
            &mut canon,
            limit,
            Instant::now() + std::time::Duration::from_secs(120),
        )
        .map(|(v, _)| v.n())
        .expect("core vocab build")
    }

    #[test]
    fn mul_zero_add_folds_to_local() {
        let mut canon = Canonizer::new(rules());
        let folded = parse_value_expr("(i32.add (i32.mul 0 40) ?L6)");
        let l6 = parse_value_expr("?L6");
        assert_eq!(
            canon.canon(&folded),
            canon.canon(&l6),
            "0*40+x should canon to ?L6 via builtin rewrite rules"
        );
    }

    #[test]
    fn topsink_totalization_enables_tee_fusion() {
        use crate::optimize::search::{Backend, SearchConfig};
        use crate::optimize::statistics::block_id;
        let path = std::path::Path::new("benchmarks/wsouper/sign_test.wasm");
        if !path.is_file() {
            return;
        }
        let info = parse_wasm_file(path).expect("parse sign_test");
        let raw = split_raw_segments(&info.segments, 12);
        let segments = materialize_segments(&raw, 1);
        let rules_v = rules();
        let cfg = SearchConfig {
            backend: Backend::Sat,
            max_sat_len: 12,
            fixed_segment_timeout: Some(60),
            scratch_locals: 1,
            ..SearchConfig::default()
        };
        for (bid, expected_len) in [("function_94_block_8", 8), ("function_18_block_12", 11)] {
            let seg = segments.iter().find(|s| block_id(s) == bid).unwrap();
            let scfg = cfg.for_segment(seg);
            let res = solve_sat(seg, &rules_v, &scfg);
            assert_eq!(
                res.ops.as_ref().map(|o| o.len()),
                Some(expected_len),
                "{bid}: expected {expected_len}-instruction fused solution"
            );
            assert!(
                res.proven_optimal,
                "{bid}: should prove optimality after ⊤-sink totalization"
            );
        }
    }

    #[test]
    fn equiv_reals_uses_joint_equiv_class_not_canon_ids() {
        let a = parse_value_expr("(i32.add (i32.sub ?L4 1) ?L1)");
        let b = parse_value_expr("(i32.add ?L1 (i32.sub ?L4 1))");
        // Simulate two trace forms that share ≡_R but got distinct per-call canon ids on insert.
        let vocab = Vocab {
            reals: vec![a, b],
            canon_ids: vec![10, 11],
            equiv_class: vec![0, 0],
            index_of_canon: [(10, 0), (11, 1)].into_iter().collect(),
            complete: true,
        };
        assert_eq!(equiv_reals(&vocab, 0), vec![0, 1]);
        assert_eq!(equiv_reals(&vocab, 1), vec![0, 1]);
        let canon_only: Vec<usize> = vocab
            .canon_ids
            .iter()
            .enumerate()
            .filter(|(_, id)| **id == vocab.canon_ids[0])
            .map(|(i, _)| i)
            .collect();
        assert_eq!(
            canon_only,
            vec![0],
            "canon_ids partition alone misses index 1"
        );
    }

    #[test]
    fn build_vocab_equiv_class_covers_all_reals() {
        let path = std::path::Path::new("benchmarks/wsouper/mux1_1.wasm");
        if !path.is_file() {
            return;
        }
        let info = parse_wasm_file(path).expect("parse");
        let raw = split_raw_segments(&info.segments, 12);
        let segments = materialize_segments(&raw, 1);
        let rules_v = rules();
        let deadline = Instant::now() + std::time::Duration::from_secs(120);
        let seg = segments.first().expect("nonempty");
        let mut canon = Canonizer::new(rules_v);
        let (vocab, _) = build_vocab(seg, &mut canon, deadline).unwrap();
        assert_eq!(vocab.equiv_class.len(), vocab.reals.len());
        for (i, ec) in vocab.equiv_class.iter().enumerate() {
            assert_eq!(*ec, vocab.equiv_class[i]);
            assert!(equiv_reals(&vocab, i).contains(&i));
        }
    }

    #[test]
    fn opaque_eclass_closure_preserves_soundness_and_improves_known_opaque_blocks() {
        use crate::optimize::search::{Backend, SearchConfig};
        use crate::optimize::statistics::block_id;
        let path = std::path::Path::new("benchmarks/wsouper/sign_test.wasm");
        if !path.is_file() {
            return;
        }
        let info = parse_wasm_file(path).expect("parse sign_test");
        let raw = split_raw_segments(&info.segments, 12);
        let segments = materialize_segments(&raw, 1);
        let rules_v = rules();
        let cfg = SearchConfig {
            backend: Backend::Sat,
            max_sat_len: 12,
            fixed_segment_timeout: Some(60),
            scratch_locals: 1,
            ..SearchConfig::default()
        };
        // ⊤-sink + commutative-add reorder + tee fusion (fixed by prior work + opaque e-class).
        let bid = "function_94_block_2";
        let seg = segments
            .iter()
            .find(|s| block_id(s) == bid)
            .unwrap_or_else(|| panic!("{bid} present at split 12"));
        let res = solve_sat(seg, &rules_v, &cfg.for_segment(seg));
        assert_eq!(
            res.ops.as_ref().map(|o| o.len()),
            Some(seg.original_len() - 1),
            "{bid}: should still find 1-instruction reduction"
        );
        assert!(res.proven_optimal, "{bid}: should prove optimality");
    }

    #[test]
    fn scratch_local_enables_tee_fusion_gap_blocks() {
        use crate::optimize::search::{Backend, SearchConfig};
        use crate::optimize::statistics::block_id;
        let path = std::path::Path::new("benchmarks/wsouper/sign_test.wasm");
        if !path.is_file() {
            return;
        }
        let info = parse_wasm_file(path).expect("parse sign_test");
        let raw = split_raw_segments(&info.segments, 12);
        let segments = materialize_segments(&raw, 1);
        let r = rules();

        let cfg = |scratch: usize| SearchConfig {
            backend: Backend::Sat,
            max_sat_len: 12,
            fixed_segment_timeout: Some(30),
            scratch_locals: scratch,
            ..SearchConfig::default()
        };

        // `local.tee[-1]` gap blocks: each needs one synthetic scratch local for CSE.
        // (`function_94_block_2` looks similar but is an existing-local `tee[3]` fusion with a
        // commutative-add reorder, so it is a separate encoding gap and not covered here.)
        let gap_blocks = [
            "function_41_block_4",
            "function_42_block_2",
            "function_43_block_2",
            "function_61_block_4",
            "function_69_block_1",
        ];
        for bid in gap_blocks {
            let seg = segments
                .iter()
                .find(|s| block_id(s) == bid)
                .unwrap_or_else(|| panic!("{bid} present at split 12"));

            let with_scratch = solve_sat(seg, &r, &cfg(1).for_segment(seg));
            let no_scratch = solve_sat(seg, &r, &cfg(0).for_segment(seg));
            let len_with = with_scratch.ops.as_ref().map(|o| o.len());
            let len_without = no_scratch.ops.as_ref().map(|o| o.len());
            eprintln!(
                "{bid}: scratch=1 -> {len_with:?}, scratch=0 -> {len_without:?} (orig {})",
                seg.original_len()
            );

            assert_eq!(
                len_without,
                Some(seg.original_len()),
                "{bid}: without scratch it should stay at original length"
            );
            assert_eq!(
                len_with,
                Some(seg.original_len() - 1),
                "{bid}: scratch local should enable a 1-instruction reduction"
            );
        }
    }

    #[test]
    fn sign_test_split_60_core_vocab_within_dynamic_limit() {
        let path = std::path::Path::new("benchmarks/wsouper/sign_test.wasm");
        if !path.is_file() {
            return;
        }
        let info = parse_wasm_file(path).expect("parse sign_test");
        let raw = split_raw_segments(&info.segments, 60);
        let segments = materialize_segments(&raw, 1);
        let r = rules();
        let mut max_core = 0usize;
        let mut worst = String::new();
        for seg in &segments {
            let n = core_vocab_size(seg, &r);
            if n > max_core {
                max_core = n;
                worst = crate::optimize::statistics::block_id(seg);
            }
            assert!(
                n <= max_vocab_for_segment(seg),
                "core |V|={n} exceeds limit {} for {}",
                max_vocab_for_segment(seg),
                crate::optimize::statistics::block_id(seg)
            );
        }
        eprintln!("sign_test split=60: max core |V|={max_core} ({worst})");
        assert!(max_core <= MAX_VOCAB_CAP);
    }

    #[test]
    fn max_vocab_scales_with_segment_length() {
        let wasm = wat::parse_str(r#"(module (func (param i32) local.get 0 i32.const 1 i32.add))"#)
            .unwrap();
        let info = crate::wasm::parse_wasm_bytes(&wasm).unwrap();
        let short = materialize_segments(&info.segments, 1).pop().unwrap();
        assert_eq!(max_vocab_for_segment(&short), MIN_VOCAB);

        let long_ops: Vec<SemOp> = (0..60).map(|_| SemOp::LocalGet(0)).collect();
        let long = StraightSegment {
            ops: long_ops,
            ..short.clone()
        };
        assert_eq!(max_vocab_for_segment(&long), 80);
    }

    /// Regression: i64 mul/add/shr chains must witness the original program.
    #[test]
    fn i64_chain_witnesses_original_program() {
        let wasm = wat::parse_str(
            r#"(module
              (func (param i64 i64) (result i64)
                local.get 0
                local.get 1
                i64.mul
                i64.const 1
                i64.add
                i64.const 2
                i64.shr_u))"#,
        )
        .unwrap();
        let info = crate::wasm::parse_wasm_bytes(&wasm).unwrap();
        let seg = materialize_segments(&info.segments, 1)
            .pop()
            .expect("segment");
        let r = rules();
        let cfg = SearchConfig::default();
        let diag = diagnose_sat(&seg, &r, &cfg);
        assert!(
            !matches!(
                diag,
                SatDiagnosis::OriginalWitnessMissingOp | SatDiagnosis::OriginalWitnessUnsat
            ),
            "{diag:?}"
        );
        assert!(
            !matches!(diag, SatDiagnosis::EncodeFailed { .. }),
            "encode failed: {diag:?}"
        );
    }

    fn load_wsouper_segments(split: usize) -> Vec<StraightSegment> {
        let path = std::path::Path::new("benchmarks/wsouper/sign_test.wasm");
        let info = parse_wasm_file(path).expect("parse sign_test");
        let raw = split_raw_segments(&info.segments, split);
        materialize_segments(&raw, 1)
    }

    fn find_residual_gap_segment(segments: &[StraightSegment], func_index: u32) -> StraightSegment {
        segments
            .iter()
            .find(|s| {
                s.func_index == func_index
                    && s.original_len() == 12
                    && storage_ops_in_trace_order(s).len() == 2
                    && s.disasm_by_id.values().any(|d| d.contains("i64.store32"))
            })
            .cloned()
            .unwrap_or_else(|| {
                panic!("no 12-instruction i64.store32 gap segment for function_{func_index}")
            })
    }

    fn storage_ops_in_trace_order(segment: &StraightSegment) -> Vec<SemOp> {
        segment
            .ops
            .iter()
            .filter(|op| op.is_storage_boundary())
            .cloned()
            .collect()
    }

    fn peak_stack_height(segment: &StraightSegment, ops: &[SemOp]) -> usize {
        use crate::sym::SymMachine;
        use crate::wasm::SegmentBounds;

        let mut max_local = segment.bounds.max_local;
        for op in ops {
            if let SemOp::LocalGet(s) | SemOp::LocalSet(s) | SemOp::LocalTee(s) = op {
                max_local = max_local.max(*s);
            }
        }
        let bounds = SegmentBounds {
            max_local,
            max_stack: segment.bounds.max_stack,
        };
        let mut m = SymMachine::from_segment_entry(
            segment.num_params,
            &bounds,
            &segment.init,
            bounds.max_stack,
        );
        let mut peak = m.to_fin_state().stack.len();
        for op in ops {
            m.exec(op).expect("solution should be executable");
            peak = peak.max(m.to_fin_state().stack.len());
        }
        peak
    }

    fn ss_solution_14_block_0_76(segment: &StraightSegment) -> Vec<SemOp> {
        use crate::value::ValueOp;
        let stores = storage_ops_in_trace_order(segment);
        assert_eq!(stores.len(), 2, "expected two i64.store32 ops");
        vec![
            SemOp::LocalGet(1),
            SemOp::LocalGet(2),
            stores[0].clone(),
            SemOp::LocalGet(1),
            SemOp::LocalGet(3),
            SemOp::LocalTee(4),
            SemOp::LocalGet(3),
            SemOp::I64Const(32),
            SemOp::Pure(ValueOp::I64ShrU),
            SemOp::LocalSet(5),
            stores[1].clone(),
        ]
    }

    fn ss_solution_24_block_0_132(segment: &StraightSegment) -> Vec<SemOp> {
        use crate::value::ValueOp;
        let stores = storage_ops_in_trace_order(segment);
        assert_eq!(stores.len(), 2, "expected two i64.store32 ops");
        vec![
            SemOp::LocalGet(4),
            SemOp::I64Const(32),
            SemOp::Pure(ValueOp::I64ShrU),
            SemOp::LocalGet(2),
            SemOp::LocalGet(3),
            stores[0].clone(),
            SemOp::LocalTee(3),
            SemOp::Pure(ValueOp::I32WrapI64),
            SemOp::LocalGet(2),
            SemOp::LocalGet(4),
            stores[1].clone(),
        ]
    }

    fn vocab_missing_for_solution(
        segment: &StraightSegment,
        rules: &[egg::Rewrite<crate::lang::ValueLang, ()>],
        ops: &[SemOp],
    ) -> Vec<String> {
        use crate::sym::{LocalReq, SymMachine};
        use crate::wasm::SegmentBounds;

        let deadline = Instant::now() + std::time::Duration::from_secs(120);
        let mut canon = Canonizer::new(rules.to_vec());
        let (vocab, _) = build_vocab(segment, &mut canon, deadline).expect("vocab");
        let mut max_local = segment.bounds.max_local;
        for op in ops {
            if let SemOp::LocalGet(s) | SemOp::LocalSet(s) | SemOp::LocalTee(s) = op {
                max_local = max_local.max(*s);
            }
        }
        let bounds = SegmentBounds {
            max_local,
            max_stack: segment.bounds.max_stack,
        };
        let mut m = SymMachine::from_segment_entry(
            segment.num_params,
            &bounds,
            &segment.init,
            bounds.max_stack,
        );
        let mut missing = Vec::new();
        let mut note_state = |m: &SymMachine| {
            for e in &m.to_fin_state().stack {
                if vocab.real_of_expr(&mut canon, e).is_none() {
                    missing.push(e.to_string());
                }
            }
            for req in m.to_fin_state().locals.values() {
                if let LocalReq::Need(v) = req {
                    if vocab.real_of_expr(&mut canon, v).is_none() {
                        missing.push(v.to_string());
                    }
                }
            }
        };
        note_state(&m);
        for op in ops {
            m.exec(op).expect("solution should be executable");
            note_state(&m);
        }
        missing.sort();
        missing.dedup();
        missing
    }

    #[test]
    fn residual_gap_height_diagnosis() {
        use crate::optimize::search::{
            Backend, SearchConfig, opaque_inputs_equivalent, validate_solution_ops,
        };

        let rules_v = rules();
        let segments = load_wsouper_segments(12);
        let seg14 = find_residual_gap_segment(&segments, 14);
        let seg24 = find_residual_gap_segment(&segments, 24);
        let ss14 = ss_solution_14_block_0_76(&seg14);
        let ss24 = ss_solution_24_block_0_132(&seg24);

        assert_eq!(ss14.len(), 11);
        assert_eq!(ss24.len(), 11);
        assert!(
            validate_solution_ops(&ss14, &seg14),
            "SS-shaped 14_block_0_76 should respect storage/deps"
        );
        assert!(
            validate_solution_ops(&ss24, &seg24),
            "SS-shaped 24_block_0_132 should respect storage/deps"
        );
        let mut canon = Canonizer::new(rules_v.clone());
        assert!(
            opaque_inputs_equivalent(&ss14, &seg14, &mut canon),
            "SS-shaped 14_block_0_76 operands should be ≡_R to original"
        );
        canon = Canonizer::new(rules_v.clone());
        assert!(
            opaque_inputs_equivalent(&ss24, &seg24, &mut canon),
            "SS-shaped 24_block_0_132 operands should be ≡_R to original"
        );

        assert_eq!(peak_stack_height(&seg14, &ss14), 4, "SS 14 peak height");
        assert_eq!(peak_stack_height(&seg24, &ss24), 3, "SS 24 peak height");

        let (_, max_h14) = collect_seed_exprs(&seg14);
        let (_, max_h24) = collect_seed_exprs(&seg24);
        let old_h14 = (max_h14 + 1)
            .max(seg14.init.stack.len())
            .max(seg14.fin.stack.len())
            .max(1)
            .min(seg14.bounds.max_stack);
        let new_h14 = stack_height_bound(max_h14, &seg14, 1);
        eprintln!(
            "gap14: max_height={max_h14} old_h={old_h14} new_h={new_h14} ss_peak=4 block_id={}",
            crate::optimize::statistics::block_id(&seg14)
        );
        assert!(
            old_h14 < peak_stack_height(&seg14, &ss14),
            "legacy h should be below SS peak for block 14"
        );
        assert_eq!(
            new_h14,
            peak_stack_height(&seg14, &ss14),
            "relaxed H should match SS peak for block 14"
        );
        assert!(
            stack_height_bound(max_h24, &seg24, 1) >= peak_stack_height(&seg24, &ss24),
            "relaxed H should cover SS peak for block 24"
        );

        assert!(
            vocab_missing_for_solution(&seg14, &rules_v, &ss14).is_empty(),
            "vocabulary should already cover SS 14 intermediates"
        );
        assert!(
            vocab_missing_for_solution(&seg24, &rules_v, &ss24).is_empty(),
            "vocabulary should already cover SS 24 intermediates"
        );

        let cfg = SearchConfig {
            backend: Backend::Sat,
            max_sat_len: 12,
            scratch_locals: 1,
            ..SearchConfig::default()
        };
        let deadline = Instant::now() + std::time::Duration::from_secs(120);

        let at_h_old = solve_at_length_minus_one_with_h(&seg14, &rules_v, &cfg, old_h14, deadline)
            .expect("probe should complete");
        let at_h_new = solve_at_length_minus_one_with_h(&seg14, &rules_v, &cfg, new_h14, deadline)
            .expect("probe should complete");
        assert!(
            at_h_new.sat && at_h_new.valid,
            "relaxed h should admit a valid 11-instr schedule"
        );
        assert_eq!(at_h_new.seq.as_ref().map(|s| s.len()), Some(11));
        if at_h_old.sat && at_h_old.valid {
            eprintln!("note: legacy h={old_h14} also admits a valid 11-instr schedule");
        } else {
            eprintln!("legacy h={old_h14} does not admit valid 11-instr schedule (expected)");
        }

        let at_h24 = solve_at_length_minus_one_with_h(
            &seg24,
            &rules_v,
            &cfg,
            stack_height_bound(max_h24, &seg24, 1),
            deadline,
        )
        .expect("probe should complete");
        assert!(
            at_h24.sat && at_h24.valid,
            "block 24 should admit valid 11-instr schedule at its stack height"
        );
    }

    #[test]
    fn residual_gap_block14_reaches_superstack_at_bench_timeout() {
        use crate::optimize::search::{Backend, SearchConfig};

        let path = std::path::Path::new("benchmarks/wsouper/sign_test.wasm");
        if !path.is_file() {
            return;
        }
        let rules_v = rules();
        let cfg = SearchConfig {
            backend: Backend::Sat,
            max_sat_len: 12,
            fixed_segment_timeout: Some(5),
            scratch_locals: 1,
            ..SearchConfig::default()
        };

        let segments = load_wsouper_segments(12);
        let seg = find_residual_gap_segment(&segments, 14);
        let res = solve_sat(&seg, &rules_v, &cfg.for_segment(&seg));
        assert_eq!(
            res.ops.as_ref().map(|o| o.len()),
            Some(seg.original_len() - 1),
            "function_14 gap block should close at 5s (block_id={}) timed_out={}",
            crate::optimize::statistics::block_id(&seg),
            res.timed_out
        );
    }

    #[test]
    fn residual_gap_blocks_reach_superstack_length() {
        use crate::optimize::search::{Backend, SearchConfig};

        let path = std::path::Path::new("benchmarks/wsouper/sign_test.wasm");
        if !path.is_file() {
            return;
        }
        let rules_v = rules();
        let cfg = SearchConfig {
            backend: Backend::Sat,
            max_sat_len: 12,
            fixed_segment_timeout: Some(60),
            scratch_locals: 1,
            ..SearchConfig::default()
        };

        let segments = load_wsouper_segments(12);
        for (func_index, label) in [(14, "function_14"), (24, "function_24")] {
            let seg = find_residual_gap_segment(&segments, func_index);
            let scfg = cfg.for_segment(&seg);
            let res = solve_sat(&seg, &rules_v, &scfg);
            assert_eq!(
                res.ops.as_ref().map(|o| o.len()),
                Some(seg.original_len() - 1),
                "{label}: expected one-instruction reduction (block_id={})",
                crate::optimize::statistics::block_id(&seg)
            );
            assert!(
                res.proven_optimal,
                "{label}: should prove optimality with relaxed stack height (block_id={})",
                crate::optimize::statistics::block_id(&seg)
            );
        }
    }

    #[test]
    fn symbolic_constant_fold_seeds_synthetic_constants() {
        use crate::optimize::statistics::block_id;

        let path = std::path::Path::new("benchmarks/wsouper/sign_test.wasm");
        if !path.is_file() {
            return;
        }
        let segments = load_wsouper_segments(12);
        let seg = segments
            .iter()
            .find(|s| block_id(s) == "function_111_block_8_4")
            .expect("function_111_block_8_4");
        let rules_v = rules();
        let deadline = Instant::now() + std::time::Duration::from_secs(120);
        let mut canon = Canonizer::new(rules_v);
        let (vocab, _) = build_vocab(seg, &mut canon, deadline).expect("vocab");
        let c280 = parse_value_expr("280");
        let c160 = parse_value_expr("160");
        assert!(
            vocab.real_of_expr(&mut canon, &c280).is_some(),
            "symbolic execution should seed i32.const 280"
        );
        assert!(
            vocab.real_of_expr(&mut canon, &c160).is_some(),
            "symbolic execution should seed i32.const 160"
        );
    }

    #[test]
    fn constant_fold_gap_function_111_reaches_superstack_length() {
        use crate::optimize::search::{Backend, SearchConfig};
        use crate::optimize::statistics::block_id;

        let path = std::path::Path::new("benchmarks/wsouper/sign_test.wasm");
        if !path.is_file() {
            return;
        }
        let rules_v = rules();
        let cfg = SearchConfig {
            backend: Backend::Sat,
            max_sat_len: 12,
            fixed_segment_timeout: Some(60),
            scratch_locals: 1,
            ..SearchConfig::default()
        };
        let segments = load_wsouper_segments(12);
        let seg = segments
            .iter()
            .find(|s| block_id(s) == "function_111_block_8_4")
            .expect("function_111_block_8_4");
        let scfg = cfg.for_segment(seg);
        let res = solve_sat(seg, &rules_v, &scfg);
        assert!(
            res.ops
                .as_ref()
                .is_some_and(|o| o.len() < seg.original_len()),
            "function_111_block_8_4: symbolic constant fold should shorten the segment"
        );
        assert_eq!(
            res.ops.as_ref().map(|o| o.len()),
            Some(8),
            "function_111_block_8_4: should reach SS-length solution"
        );
        assert!(
            res.proven_optimal,
            "function_111_block_8_4: should prove optimality"
        );
        let ops = res.ops.as_ref().expect("solution");
        let mut canon = Canonizer::new(rules_v);
        assert!(
            solution_valid(ops, seg, &mut canon),
            "function_111 solution must be sound"
        );
    }

    #[test]
    fn constant_tee_gap_function_14_block_0_remains_sound() {
        use crate::optimize::search::{Backend, SearchConfig};
        use crate::optimize::statistics::block_id;

        let path = std::path::Path::new("benchmarks/wsouper/sign_test.wasm");
        if !path.is_file() {
            return;
        }
        let rules_v = rules();
        let cfg = SearchConfig {
            backend: Backend::Sat,
            max_sat_len: 12,
            fixed_segment_timeout: Some(60),
            scratch_locals: 1,
            ..SearchConfig::default()
        };
        let segments = load_wsouper_segments(12);
        let seg = segments
            .iter()
            .find(|s| block_id(s) == "function_14_block_0_0")
            .expect("function_14_block_0_0");
        let scfg = cfg.for_segment(seg);
        let res = solve_sat(seg, &rules_v, &scfg);
        let ops = res
            .ops
            .as_ref()
            .expect("function_14 should remain solvable");
        let mut canon = Canonizer::new(rules_v);
        let (vocab, _) = build_vocab(
            seg,
            &mut canon,
            Instant::now() + std::time::Duration::from_secs(120),
        )
        .expect("vocab");
        assert!(
            solution_valid(ops, seg, &mut canon),
            "function_14 solution must be sound"
        );
        let c0 = const_expr(&SemOp::I64Const(0)).expect("i64 const expr");
        assert!(
            vocab.real_of_expr(&mut canon, &c0).is_some(),
            "zero literal should be in V for tee propagation"
        );
        // Full SS-length (4) needs greedy tee seed / upper bound (follow-up work).
        assert!(
            ops.len() <= seg.original_len(),
            "function_14_block_0_0: should not lengthen the segment"
        );
    }

    #[test]
    fn analyze_function_14_block_0_13_root_cause() {
        use crate::optimize::search::{solution_valid, validate_solution_ops};
        use crate::value::ValueOp;

        let path = std::path::Path::new("benchmarks/wsouper/sign_test.wasm");
        if !path.is_file() {
            return;
        }
        let rules_v = rules();
        let segments = load_wsouper_segments(12);
        let seg = segments
            .iter()
            .find(|s| crate::optimize::statistics::block_id(s) == "function_14_block_0_13")
            .expect("function_14_block_0_13");

        eprintln!("=== segment ===");
        eprintln!("ops ({}): {:?}", seg.original_len(), seg.ops);
        eprintln!("opaque_meta: {}", seg.opaque_meta.len());
        eprintln!("dependencies: {:?}", seg.dependencies);
        eprintln!("init stack len: {}", seg.init.stack.len());
        eprintln!("fin stack len: {}", seg.fin.stack.len());
        eprintln!("max_stack: {}", seg.bounds.max_stack);

        // SS schedule from bench CSV (11 instr).
        let ss_ops = vec![
            SemOp::Pure(ValueOp::I64Add),
            SemOp::LocalTee(2),
            SemOp::I64Const(32),
            SemOp::Pure(ValueOp::I64ShrU),
            SemOp::LocalGet(3),
            SemOp::Pure(ValueOp::I64Add),
            SemOp::LocalGet(5),
            SemOp::Pure(ValueOp::I64Add),
            SemOp::LocalSet(3),
            SemOp::LocalGet(1),
            SemOp::LocalGet(2),
        ];

        let mut canon = Canonizer::new(rules_v.clone());
        eprintln!(
            "SS solution_valid: {}",
            solution_valid(&ss_ops, seg, &mut canon)
        );
        eprintln!(
            "SS validate_solution_ops: {}",
            validate_solution_ops(&ss_ops, seg)
        );

        let missing = vocab_missing_for_solution(seg, &rules_v, &ss_ops);
        eprintln!("SS vocab missing ({}): {missing:?}", missing.len());

        let deadline = Instant::now() + std::time::Duration::from_secs(120);
        let mut canon2 = Canonizer::new(rules_v.clone());
        let (vocab, max_h) = build_vocab(seg, &mut canon2, deadline).expect("vocab");
        let cfg = crate::optimize::search::SearchConfig {
            backend: crate::optimize::search::Backend::Sat,
            max_sat_len: 12,
            scratch_locals: 1,
            ..Default::default()
        };
        let h = stack_height_bound(max_h, seg, 1);
        eprintln!("|V|={} max_h={max_h} H={h}", vocab.n());

        let probe = solve_at_length_minus_one_with_h(seg, &rules_v, &cfg.for_segment(seg), h, deadline);
        eprintln!(
            "probe L=11: sat={} valid={} timed_out={}",
            probe.as_ref().map(|p| p.sat).unwrap_or(false),
            probe.as_ref().map(|p| p.valid).unwrap_or(false),
            probe.as_ref().map(|p| p.timed_out).unwrap_or(false),
        );

        // Stack trace comparison via SymMachine
        use crate::sym::SymMachine;
        let trace = |label: &str, ops: &[SemOp]| {
            let mut m = SymMachine::from_segment_entry(
                seg.num_params,
                &seg.bounds,
                &seg.init,
                seg.bounds.max_stack,
            );
            eprintln!("--- {label} ---");
            eprintln!("  init stack: {:?}", m.to_fin_state().stack.iter().map(|e| e.to_string()).collect::<Vec<_>>());
            for (i, op) in ops.iter().enumerate() {
                m.exec(op).expect("exec");
                let st = m.to_fin_state();
                eprintln!(
                    "  step {i} {op:?} -> stack[{}]: {:?}",
                    st.stack.len(),
                    st.stack.iter().map(|e| e.to_string()).collect::<Vec<_>>()
                );
            }
        };
        trace("original", &seg.ops);
        trace("SS", &ss_ops);

        // Compare stack cell V-indices at shr step
        let mut canon3 = Canonizer::new(rules_v.clone());
        let (vocab2, _) = build_vocab(seg, &mut canon3, deadline).expect("vocab");
        let mut idx_at = |ops: &[SemOp], step: usize| -> Option<(usize, String)> {
            let mut m = SymMachine::from_segment_entry(
                seg.num_params,
                &seg.bounds,
                &seg.init,
                seg.bounds.max_stack,
            );
            for (i, op) in ops.iter().enumerate() {
                if i == step {
                    let st = m.to_fin_state();
                    let top = st.stack.last()?;
                    let idx = vocab2.real_of_expr(&mut canon3, top)?;
                    return Some((idx, top.to_string()));
                }
                m.exec(op).ok()?;
            }
            None
        };
        // Original: shr at step 5 (0-indexed), SS: shr at step 3
        eprintln!(
            "stack top before shr (orig step 5): {:?}",
            idx_at(&seg.ops, 5)
        );
        eprintln!("stack top before shr (SS step 3): {:?}", idx_at(&ss_ops, 3));
        eprintln!(
            "stack top before shr (orig step 4 get2): {:?}",
            idx_at(&seg.ops, 4)
        );

        assert!(
            probe.as_ref().is_some_and(|p| p.sat),
            "L=11 probe should be SAT after commutative binop edge symmetrization"
        );
        assert_eq!(missing.len(), 0, "SS solution should have no missing vocab");

        // Build ops + SS witness CNF check.
        let r_ops = (seg.bounds.max_local as usize) + 1 + 1;
        let ops_sat = build_ops(seg, &vocab2, &mut canon3, &rules_v, r_ops, deadline).expect("ops");
        for op in &ops_sat {
            if let SatOp::Binop { kind, edges } = op {
                eprintln!("binop {:?} edges ({}):", kind, edges.len());
                for (a1, a0, res) in edges.iter().take(20) {
                    eprintln!(
                        "  ({a1},{a0})-> {res}  [{}] op [{}] = [{}]",
                        vocab2.reals.get(*a1).map(|e| e.to_string()).unwrap_or_default(),
                        vocab2.reals.get(*a0).map(|e| e.to_string()).unwrap_or_default(),
                        vocab2.reals.get(*res).map(|e| e.to_string()).unwrap_or_default(),
                    );
                }
            }
        }

        let mut dims = Dims::new(seg.original_len(), h, r_ops, vocab2.n(), ops_sat.len());
        let cnf = encode(seg, &vocab2, &ops_sat, &mut dims, &mut canon3, deadline).expect("encode");
        let mut solver: Solver = Solver::new();
        for clause in &cnf.clauses {
            solver.add_clause(clause.iter().copied());
        }
        let ss_assumptions: Option<Vec<i32>> = ss_ops
            .iter()
            .enumerate()
            .map(|(step, sem)| {
                let o = sat_op_index_for_orig(&ops_sat, sem)?;
                Some(dims.x(step + 1, o))
            })
            .collect::<Option<Vec<_>>>()
            .map(|mut v| {
                v.push(dims.x(seg.original_len(), NOP_INDEX));
                v
            });
        if let Some(assumptions) = ss_assumptions {
            match solver.solve_with(assumptions.iter().copied()) {
                Some(true) => eprintln!("SS witness: SAT (encoding accepts SS schedule)"),
                Some(false) => panic!("SS witness: UNSAT (encoding REJECTS SS schedule)"),
                None => panic!("SS witness: solver timeout"),
            }
        } else {
            panic!("SS witness: failed to map SS ops to SatOp indices");
        }

        // ec-pair orientation check at SS add-after-get3 (step 5).
        let mut m = SymMachine::from_segment_entry(
            seg.num_params,
            &seg.bounds,
            &seg.init,
            seg.bounds.max_stack,
        );
        for op in &ss_ops[..5] {
            m.exec(op).unwrap();
        }
        let st = m.to_fin_state();
        let top = st.stack.last().unwrap();
        let second = st.stack.get(st.stack.len().wrapping_sub(2)).unwrap();
        let top_idx = vocab2.real_of_expr(&mut canon3, top);
        let second_idx = vocab2.real_of_expr(&mut canon3, second);
        eprintln!(
            "SS pre-add stack: pos0={top_idx:?} ec={:?}, pos1={second_idx:?} ec={:?}",
            top_idx.map(|i| vocab2.equiv_class[i]),
            second_idx.map(|i| vocab2.equiv_class[i]),
        );
        eprintln!(
            "allowed add ec-pairs: {:?}",
            ops_sat.iter().filter_map(|o| {
                if let SatOp::Binop { kind: InstKind::Pure(ValueOp::I64Add), edges } = o {
                    Some(edges.iter().map(|&(a1,a0,_)| (vocab2.equiv_class[a1], vocab2.equiv_class[a0])).collect::<Vec<_>>())
                } else { None }
            }).next()
        );
        m.exec(&ss_ops[5]).unwrap();
        let st_after = m.to_fin_state();
        let after = st_after.stack.last().unwrap();
        let after_idx = vocab2.real_of_expr(&mut canon3, after);
        eprintln!(
            "SS add step5 result idx={after_idx:?} ec={:?}, orig edge19 ec={:?}",
            after_idx.map(|i| vocab2.equiv_class[i]),
            vocab2.equiv_class[19]
        );
        let allowed_pairs: Vec<_> = ops_sat
            .iter()
            .filter_map(|o| {
                if let SatOp::Binop {
                    kind: InstKind::Pure(ValueOp::I64Add),
                    edges,
                } = o
                {
                    Some(
                        edges
                            .iter()
                            .map(|&(a1, a0, _)| (vocab2.equiv_class[a1], vocab2.equiv_class[a0]))
                            .collect::<Vec<_>>(),
                    )
                } else {
                    None
                }
            })
            .next()
            .expect("I64Add binop table");
        assert!(
            allowed_pairs.contains(&(18, 5)),
            "commutative add should allow reversed ec-pair (18, 5), got {allowed_pairs:?}"
        );
    }

    #[test]
    fn analyze_function_14_block_0_52_root_cause() {
        use crate::optimize::search::{solution_valid, validate_solution_ops};
        use crate::value::ValueOp;

        let path = std::path::Path::new("benchmarks/wsouper/sign_test.wasm");
        if !path.is_file() {
            return;
        }
        let rules_v = rules();
        let segments = load_wsouper_segments(12);
        let seg = segments
            .iter()
            .find(|s| crate::optimize::statistics::block_id(s) == "function_14_block_0_52")
            .expect("function_14_block_0_52");

        // SuperStack 6-instr schedule (sign_test combined_blocks.csv).
        let ss_ops = vec![
            SemOp::LocalGet(7),
            SemOp::LocalGet(13),
            SemOp::Pure(ValueOp::I64Mul),
            SemOp::I64Const(0),
            SemOp::LocalSet(3),
            SemOp::LocalSet(2),
        ];

        let mut canon = Canonizer::new(rules_v.clone());
        eprintln!("orig len={} ops: {:?}", seg.original_len(), seg.ops);
        eprintln!(
            "SS solution_valid={} validate_solution_ops={}",
            solution_valid(&ss_ops, seg, &mut canon),
            validate_solution_ops(&ss_ops, seg)
        );

        let missing = vocab_missing_for_solution(seg, &rules_v, &ss_ops);
        eprintln!("SS vocab missing ({}): {missing:?}", missing.len());

        let deadline = Instant::now() + std::time::Duration::from_secs(120);
        let mut canon2 = Canonizer::new(rules_v.clone());
        let (vocab, max_h) = build_vocab(seg, &mut canon2, deadline).expect("vocab");
        let cfg = crate::optimize::search::SearchConfig {
            backend: crate::optimize::search::Backend::Sat,
            max_sat_len: 12,
            scratch_locals: 1,
            ..Default::default()
        };
        let h = stack_height_bound(max_h, seg, 1);
        eprintln!("|V|={} max_h={max_h} H={h}", vocab.n());

        for target_len in [6usize, 7] {
            let probe = solve_at_length_with_h(
                seg,
                &rules_v,
                &cfg.for_segment(seg),
                h,
                target_len + 1,
                deadline,
            );
            eprintln!(
                "probe L={target_len}: sat={} valid={} seq={:?}",
                probe.as_ref().map(|p| p.sat).unwrap_or(false),
                probe.as_ref().map(|p| p.valid).unwrap_or(false),
                probe.as_ref().and_then(|p| p.seq.as_ref()),
            );
        }

        let res = solve_sat(seg, &rules_v, &cfg.for_segment(seg));
        eprintln!(
            "solve_sat: len={:?} proven={} ops={:?}",
            res.ops.as_ref().map(|o| o.len()),
            res.proven_optimal,
            res.ops
        );

        let r_ops = (seg.bounds.max_local as usize) + 1 + 1;
        let mut canon3 = Canonizer::new(rules_v.clone());
        let (vocab2, _) = build_vocab(seg, &mut canon3, deadline).expect("vocab");
        let ops_sat = build_ops(seg, &vocab2, &mut canon3, &rules_v, r_ops, deadline).expect("ops");
        let mut dims = Dims::new(seg.original_len(), h, r_ops, vocab2.n(), ops_sat.len());
        let cnf = encode(seg, &vocab2, &ops_sat, &mut dims, &mut canon3, deadline).expect("encode");
        let mut solver: Solver = Solver::new();
        for clause in &cnf.clauses {
            solver.add_clause(clause.iter().copied());
        }
        let ss_assumptions: Option<Vec<i32>> = ss_ops
            .iter()
            .enumerate()
            .map(|(step, sem)| {
                let o = sat_op_index_for_orig(&ops_sat, sem)?;
                Some(dims.x(step + 1, o))
            })
            .collect::<Option<Vec<_>>>()
            .map(|mut v| {
                v.push(dims.x(7, NOP_INDEX));
                v
            });
        match ss_assumptions {
            Some(assumptions) => match solver.solve_with(assumptions.iter().copied()) {
                Some(true) => eprintln!("SS witness @L=6: SAT"),
                Some(false) => eprintln!("SS witness @L=6: UNSAT (encoding gap)"),
                None => eprintln!("SS witness @L=6: timeout"),
            },
            None => eprintln!("SS witness: failed to map ops"),
        }

        assert!(
            missing.is_empty(),
            "SS schedule values should be representable in V"
        );
    }

    #[test]
    fn gap_probe_csv_blocks() {
        use crate::optimize::canon::Canonizer;
        use crate::optimize::sat::{solve_at_length_minus_one_with_h, stack_height_bound};
        use crate::optimize::search::{Backend, SearchConfig};
        use crate::optimize::statistics::block_id;
        use crate::wasm::{materialize_segments, parse_wasm_file, split_raw_segments};
        use std::time::Instant;

        let rules = rules();
        let cfg = SearchConfig {
            backend: Backend::Sat,
            max_sat_len: 12,
            fixed_segment_timeout: Some(60),
            scratch_locals: 1,
            ..SearchConfig::default()
        };
        let deadline = Instant::now() + std::time::Duration::from_secs(120);

        // (wasm path, block_id, SuperStack optimized_length)
        let probes: Vec<(&str, &str, usize)> = vec![
            ("benchmarks/wsouper/sign_test.wasm", "function_14_block_0_13", 11),
            ("benchmarks/wsouper/sign_test.wasm", "function_25_block_0_10", 11),
            ("benchmarks/wsouper/sign_test.wasm", "function_24_block_0_75", 9),
            ("benchmarks/wsouper/sign_test.wasm", "function_24_block_0_101", 11),
            ("benchmarks/wsouper/sign_test.wasm", "function_14_block_0_52", 6),
            ("benchmarks/wsouper/sign_test.wasm", "function_24_block_0_7", 11),
            (
                "benchmarks/wsouper/mux1_1.wasm",
                "function_24_block_0_109",
                11,
            ),
        ];

        for (wasm_path, bid, ss_len) in probes {
            let path = std::path::Path::new(wasm_path);
            if !path.is_file() {
                eprintln!("skip {bid}: {wasm_path} not found");
                continue;
            }
            let info = parse_wasm_file(path).expect("parse");
            let segments = materialize_segments(&split_raw_segments(&info.segments, 12), 1);
            let seg = segments
                .iter()
                .find(|s| block_id(s) == bid)
                .unwrap_or_else(|| panic!("{bid} in {wasm_path}"));
            let scfg = cfg.for_segment(seg);
            let res = solve_sat(seg, &rules, &scfg);
            let mut canon = Canonizer::new(rules.clone());
            let (vocab, max_h) = build_vocab(seg, &mut canon, deadline).expect("vocab");
            let h = stack_height_bound(max_h, seg, 1);
            let probe = solve_at_length_minus_one_with_h(seg, &rules, &scfg, h, deadline);
            eprintln!(
                "{bid}: orig={} ss={ss_len} solve={:?} proven={} probe@{} sat={} valid={} H={} |V|={}",
                seg.original_len(),
                res.ops.as_ref().map(|o| o.len()),
                res.proven_optimal,
                seg.original_len().saturating_sub(1),
                probe.as_ref().map(|p| p.sat).unwrap_or(false),
                probe.as_ref().map(|p| p.valid).unwrap_or(false),
                h,
                vocab.n(),
            );
        }
    }

    /// P2 acceptance: representative gap blocks should reach SuperStack length when possible.
    #[test]
    fn p2_schedule_gap_blocks_reach_superstack_length() {
        use crate::optimize::search::{Backend, SearchConfig, solution_valid};
        use crate::optimize::statistics::block_id;

        let cases: Vec<(&str, &str, usize)> = vec![
            ("benchmarks/wsouper/sign_test.wasm", "function_14_block_0_52", 6),
            ("benchmarks/wsouper/sign_test.wasm", "function_24_block_0_7", 11),
            (
                "benchmarks/wsouper/mux1_1.wasm",
                "function_24_block_0_109",
                11,
            ),
        ];
        let rules = rules();
        let cfg = SearchConfig {
            backend: Backend::Sat,
            max_sat_len: 12,
            fixed_segment_timeout: Some(60),
            scratch_locals: 1,
            ..SearchConfig::default()
        };

        for (wasm_path, bid, ss_len) in cases {
            let path = std::path::Path::new(wasm_path);
            if !path.is_file() {
                continue;
            }
            let info = parse_wasm_file(path).expect("parse");
            let segments = materialize_segments(&split_raw_segments(&info.segments, 12), 1);
            let seg = segments
                .iter()
                .find(|s| block_id(s) == bid)
                .expect(bid);
            let res = solve_sat(seg, &rules, &cfg.for_segment(seg));
            let got = res.ops.as_ref().map(|o| o.len());
            eprintln!("{bid}: ss={ss_len} solve={got:?} proven={}", res.proven_optimal);
            assert!(
                got.is_some_and(|n| n <= ss_len),
                "{bid}: expected len <= {ss_len}, got {got:?}"
            );
            if let Some(ops) = &res.ops {
                let mut canon = Canonizer::new(rules.clone());
                assert!(
                    solution_valid(ops, seg, &mut canon),
                    "{bid}: solution must be sound"
                );
            }
        }
    }
}
