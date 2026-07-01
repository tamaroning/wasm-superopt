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
    const_stack_ty, inst_kind_from_sem, inst_kind_from_value_op, sat_pure_ops, sem_from_inst_kind,
    sem_to_value_op, synthesis_const_exprs, value_op_from_inst_kind, value_op_is_binop,
    value_op_is_unop, InstKind, SemOp, StackTy,
};
use crate::sym::{LocalReq, SymMachine, SymState, ValueExpr, all_subtree_exprs};
use crate::value::{parse_value_expr, ValueOp};
use crate::wasm::{OpaqueMeta, StraightSegment};
use cadical::{Solver, Timeout};
use egg::{Id, Runner};
use std::collections::{HashMap, HashSet};
use std::time::Instant;

/// Minimum value-vocabulary size `|V|` (short straight-line chunks).
const MIN_VOCAB: usize = 64;
/// Hard cap on `|V|` — binop tables are `O(|V|²)` and CNF grows with `|V|`.
const MAX_VOCAB_CAP: usize = 160;
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
/// Equivalence-saturation rounds for vocabulary expansion (`k_sat`).
const K_SAT: usize = 2;
/// Equality-saturation limits for the batched operation-result-table build.
const TABLE_ITER_LIMIT: usize = 12;
const TABLE_NODE_LIMIT: usize = 100_000;

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
    for e in segment
        .init
        .stack
        .iter()
        .chain(segment.fin.stack.iter())
    {
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
        .filter(|e| {
            stack_ty_of_expr(e)
                .is_some_and(|ty| types.contains(&ty))
        })
        .collect()
}

/// Types present in `V` or the original segment — used to prune the SAT op tables.
fn types_in_segment_and_vocab(
    segment: &StraightSegment,
    vocab: &Vocab,
) -> HashSet<StackTy> {
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
    /// `≡_R` class id per real (parallel to `reals`; avoids re-saturating during encode).
    canon_ids: Vec<CanonId>,
    /// Canon id → real index.
    index_of_canon: HashMap<CanonId, usize>,
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
    /// Stack value-domain size: `n` real values + `⊥` at index `n`.
    sd: usize,
    /// Local value-domain size: `n` real values + `★` at index `n`.
    ld: usize,
    base_y: i32,
    base_w: i32,
    next_var: i32,
}

impl Dims {
    fn new(l: usize, h: usize, r: usize, n: usize, n_ops: usize) -> Self {
        let sd = n + 1;
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

fn kind_pattern(kind: InstKind) -> &'static str {
    value_op_from_inst_kind(kind)
        .expect("pure SAT op")
        .pattern_name()
}

fn binop_expr(kind: InstKind, a1: &ValueExpr, a0: &ValueExpr) -> ValueExpr {
    parse_value_expr(&format!("({} {a1} {a0})", kind_pattern(kind)))
}

fn unop_expr(kind: InstKind, a: &ValueExpr) -> ValueExpr {
    parse_value_expr(&format!("({} {a})", kind_pattern(kind)))
}

/// Operand value-expr strings required at stack top-positions `0..pops` (top first),
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

fn build_vocab(segment: &StraightSegment, canon: &mut Canonizer, deadline: Instant) -> Option<(Vocab, usize)> {
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

    // Phase 1 — core vocabulary (trace + type-filtered synthesis constants). These MUST
    // all fit so the original sequence is representable (first descending solve is SAT).
    let types = types_in_segment(segment);
    let mut core: Vec<ValueExpr> = seeds;
    core.extend(synthesis_const_exprs_for_types(&types));
    dedup_by_string(&mut core);

    for e in &core {
        if Instant::now() >= deadline {
            return None;
        }
        if !try_insert_vocab(
            e,
            canon,
            max_vocab,
            &mut index_of_canon,
            &mut reals,
            &mut canon_ids,
        ) {
            return None; // core alone exceeds |V| cap
        }
    }

    // Phase 2 — subtree expansion (best-effort): dedupe by string before canon to avoid
    // repeated e-graph work; stop at |V| cap without failing.
    let mut subtree_candidates: Vec<ValueExpr> = Vec::new();
    for e in &core {
        subtree_candidates.extend(all_subtree_exprs(e));
    }
    dedup_by_string(&mut subtree_candidates);
    for e in &subtree_candidates {
        if Instant::now() >= deadline {
            return None;
        }
        if reals.len() >= max_vocab {
            break;
        }
        let _ = try_insert_vocab(
            e,
            canon,
            max_vocab,
            &mut index_of_canon,
            &mut reals,
            &mut canon_ids,
        );
    }

    // Phase 3 — equivalence saturation (best-effort, capped): mul/shl decompositions, etc.
    let mut frontier: Vec<ValueExpr> = reals.clone();
    'rounds: for _ in 0..K_SAT {
        if Instant::now() >= deadline {
            return None;
        }
        let mut next: Vec<ValueExpr> = Vec::new();
        for e in &frontier {
            if Instant::now() >= deadline {
                return None;
            }
            for (_, e1, e2) in canon.binop_decompositions(e) {
                for cand in all_subtree_exprs(&e1)
                    .into_iter()
                    .chain(all_subtree_exprs(&e2))
                {
                    if !try_insert_vocab(
                        &cand,
                        canon,
                        max_vocab,
                        &mut index_of_canon,
                        &mut reals,
                        &mut canon_ids,
                    ) {
                        break 'rounds;
                    }
                    next.push(cand);
                }
            }
        }
        if next.is_empty() {
            break;
        }
        frontier = next;
    }

    if reals.is_empty() {
        return None;
    }

    Some((
        Vocab {
            reals,
            canon_ids,
            index_of_canon,
        },
        max_height,
    ))
}

/// Build the SAT instruction alphabet (NOP first), pruning ops with no defined result.
///
/// The unary/binary result tables `T_∘` / `T_⊕` (§2.3) are computed with a single
/// batched equality saturation over all `V × V` applications, rather than one
/// `Canonizer::canon` call per pair (which re-saturates a growing e-graph and is
/// prohibitively slow).
fn build_ops(
    segment: &StraightSegment,
    vocab: &Vocab,
    canon: &mut Canonizer,
    rules: &[egg::Rewrite<ValueLang, ()>],
    r: usize,
    deadline: Instant,
) -> Option<Vec<SatOp>> {
    if Instant::now() >= deadline {
        return None;
    }
    let n = vocab.n();
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

    for slot in 0..r as u32 {
        ops.push(SatOp::Get(slot));
        ops.push(SatOp::Set(slot));
        ops.push(SatOp::Tee(slot));
    }
    ops.push(SatOp::Drop);

    // One e-graph holding every real value and every candidate application.
    let mut runner = Runner::default()
        .with_iter_limit(TABLE_ITER_LIMIT)
        .with_node_limit(TABLE_NODE_LIMIT);
    let real_ids: Vec<Id> = vocab
        .reals
        .iter()
        .map(|e| runner.egraph.add_expr(e))
        .collect();

    let mut uni_ids: Vec<Vec<Id>> = Vec::with_capacity(sat_unops.len());
    for &kind in &sat_unops {
        let mut col = Vec::with_capacity(n);
        for a in 0..n {
            col.push(runner.egraph.add_expr(&unop_expr(kind, &vocab.reals[a])));
        }
        uni_ids.push(col);
    }
    let mut bin_ids: Vec<Vec<Id>> = Vec::with_capacity(sat_binops.len());
    for &kind in &sat_binops {
        let mut col = Vec::with_capacity(n * n);
        for a1 in 0..n {
            for a0 in 0..n {
                col.push(runner.egraph.add_expr(&binop_expr(
                    kind,
                    &vocab.reals[a1],
                    &vocab.reals[a0],
                )));
            }
        }
        bin_ids.push(col);
    }

    if Instant::now() >= deadline {
        return None;
    }
    let runner = runner.run(rules);
    if Instant::now() >= deadline {
        return None;
    }
    let mut class_to_real: HashMap<Id, usize> = HashMap::new();
    for (i, id) in real_ids.iter().enumerate() {
        class_to_real.entry(runner.egraph.find(*id)).or_insert(i);
    }
    let lookup = |id: Id| class_to_real.get(&runner.egraph.find(id)).copied();

    for (ki, &kind) in sat_unops.iter().enumerate() {
        let mut edges = Vec::new();
        for a in 0..n {
            if let Some(res) = lookup(uni_ids[ki][a]) {
                edges.push((a, res));
            }
        }
        if !edges.is_empty() {
            ops.push(SatOp::Unop { kind, edges });
        }
    }
    for (ki, &kind) in sat_binops.iter().enumerate() {
        let mut edges = Vec::new();
        for a1 in 0..n {
            for a0 in 0..n {
                if let Some(res) = lookup(bin_ids[ki][a1 * n + a0]) {
                    edges.push((a1, a0, res));
                }
            }
        }
        if !edges.is_empty() {
            ops.push(SatOp::Binop { kind, edges });
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

/// Relative indices in `V` that are ≡_R-equivalent to `req` (for opaque operand pins).
fn equiv_reals(vocab: &Vocab, req: usize) -> Vec<usize> {
    let target = vocab.canon_ids[req];
    vocab
        .canon_ids
        .iter()
        .enumerate()
        .filter_map(|(i, &id)| (id == target).then_some(i))
        .collect()
}

/// Pin one SAT op per original instruction step (`x_{i,o} = 1`).
fn sat_op_index_for_orig(ops: &[SatOp], sem: &SemOp) -> Option<usize> {
    match sem {
        SemOp::I32Const(_)
        | SemOp::I64Const(_)
        | SemOp::F32Const(_)
        | SemOp::F64Const(_) => ops.iter().position(|o| {
            matches!(o, SatOp::Const { sem: s, .. } if sem_eq_const(s, sem))
        }),
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
    let nop = NOP_INDEX;
    let past = |cnf: &Cnf| Instant::now() >= deadline || cnf.over_limit;

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

    // §5.2 boundary (final).
    let fin = &segment.fin;
    for j in 0..h {
        if let Some(e) = stack_expr_at(fin, j) {
            let v = vocab.real_of_expr(canon, e)?;
            cnf.unit(dims.y(l, j, v));
        } else {
            cnf.unit(dims.y(l, j, bot));
        }
    }
    for rr in 0..r {
        match fin.locals.get(&(rr as u32)) {
            Some(LocalReq::Need(v)) => {
                let idx = vocab.real_of_expr(canon, v)?;
                cnf.unit(dims.w(l, rr, idx));
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
                        cnf.unit(dims.w(l, rr, idx));
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
                    locals_unchanged(&mut cnf, dims, i, xio);
                }
                SatOp::Const { val, .. } => {
                    cnf.add(vec![-xio, dims.y(i - 1, h - 1, bot)]);
                    cnf.add(vec![-xio, dims.y(i, 0, *val)]);
                    stack_push_shift(&mut cnf, dims, i, xio);
                    locals_unchanged(&mut cnf, dims, i, xio);
                }
                SatOp::Get(slot) => {
                    let slot = *slot as usize;
                    cnf.add(vec![-xio, -dims.w(i - 1, slot, star)]);
                    cnf.add(vec![-xio, dims.y(i - 1, h - 1, bot)]);
                    for v in 0..n {
                        cnf.imply_iff(xio, dims.y(i, 0, v), dims.w(i - 1, slot, v));
                    }
                    stack_push_shift(&mut cnf, dims, i, xio);
                    locals_unchanged(&mut cnf, dims, i, xio);
                }
                SatOp::Set(slot) => {
                    let slot = *slot as usize;
                    cnf.add(vec![-xio, -dims.y(i - 1, 0, bot)]);
                    for v in 0..n {
                        cnf.imply_iff(xio, dims.w(i, slot, v), dims.y(i - 1, 0, v));
                    }
                    locals_unchanged_except(&mut cnf, dims, i, xio, slot);
                    stack_pop_shift(&mut cnf, dims, i, xio, 0);
                }
                SatOp::Tee(slot) => {
                    let slot = *slot as usize;
                    cnf.add(vec![-xio, -dims.y(i - 1, 0, bot)]);
                    for v in 0..n {
                        cnf.imply_iff(xio, dims.w(i, slot, v), dims.y(i - 1, 0, v));
                    }
                    locals_unchanged_except(&mut cnf, dims, i, xio, slot);
                    stack_unchanged(&mut cnf, dims, i, xio);
                }
                SatOp::Drop => {
                    cnf.add(vec![-xio, -dims.y(i - 1, 0, bot)]);
                    stack_pop_shift(&mut cnf, dims, i, xio, 0);
                    locals_unchanged(&mut cnf, dims, i, xio);
                }
                SatOp::Unop { edges, .. } => {
                    cnf.add(vec![-xio, -dims.y(i - 1, 0, bot)]);
                    let mut domain = vec![-xio];
                    for &(a, res) in edges {
                        domain.push(dims.y(i - 1, 0, a));
                        cnf.add(vec![-xio, -dims.y(i - 1, 0, a), dims.y(i, 0, res)]);
                    }
                    cnf.add(domain);
                    // Top changes; deeper cells unchanged.
                    for j in 1..h {
                        for v in 0..sd {
                            cnf.imply_iff(xio, dims.y(i, j, v), dims.y(i - 1, j, v));
                        }
                    }
                    locals_unchanged(&mut cnf, dims, i, xio);
                }
                SatOp::Binop { edges, .. } => {
                    cnf.add(vec![-xio, -dims.y(i - 1, 0, bot)]);
                    cnf.add(vec![-xio, -dims.y(i - 1, 1, bot)]);
                    // E-graph valid edges only: positive transitions + per-arg1 domain.
                    let mut by_a1: HashMap<usize, Vec<usize>> = HashMap::new();
                    for &(a1, a0, res) in edges {
                        by_a1.entry(a1).or_default().push(a0);
                        cnf.add(vec![
                            -xio,
                            -dims.y(i - 1, 1, a1),
                            -dims.y(i - 1, 0, a0),
                            dims.y(i, 0, res),
                        ]);
                    }
                    for (a1, a0s) in by_a1 {
                        let mut clause = vec![-xio, -dims.y(i - 1, 1, a1)];
                        for a0 in a0s {
                            clause.push(dims.y(i - 1, 0, a0));
                        }
                        cnf.add(clause);
                    }
                    stack_pop_shift(&mut cnf, dims, i, xio, 1);
                    locals_unchanged(&mut cnf, dims, i, xio);
                }
                SatOp::Opaque {
                    in_reals,
                    out_reals,
                    ..
                } => {
                    encode_opaque(&mut cnf, dims, i, xio, vocab, in_reals, out_reals);
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

    locals_unchanged(cnf, dims, i, xio);
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

fn locals_unchanged(cnf: &mut Cnf, dims: &Dims, i: usize, xio: i32) {
    for rr in 0..dims.r {
        for v in 0..dims.ld {
            cnf.imply_iff(xio, dims.w(i, rr, v), dims.w(i - 1, rr, v));
        }
    }
}

fn locals_unchanged_except(cnf: &mut Cnf, dims: &Dims, i: usize, xio: i32, slot: usize) {
    for rr in 0..dims.r {
        if rr == slot {
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
            self.vocab_ms,
            self.ops_ms,
            self.encode_ms,
            self.add_clauses_ms,
            self.witness_ms
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
    let r = (segment.bounds.max_local as usize) + 1;
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

    let h = (max_height + 1)
        .max(segment.init.stack.len())
        .max(segment.fin.stack.len())
        .max(1)
        .min(segment.bounds.max_stack);

    let t2 = Instant::now();
    let mut dims = Dims::new(l_orig, h, r, vocab.n(), ops.len());
    let cnf = encode(
        segment,
        &vocab,
        &ops,
        &mut dims,
        &mut canon,
        deadline,
    )
    .ok_or("encode")?;
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
        SatDiagnosis::OriginalUnsat
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
            Some(false) => SatDiagnosis::OriginalUnsat,
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
    OriginalUnsat,
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

    let r = (segment.bounds.max_local as usize) + 1;
    let Some(ops) = build_ops(segment, &vocab, &mut canon, rules, r, deadline) else {
        return SatDiagnosis::OpsBuildFailed;
    };

    let h = (max_height + 1)
        .max(segment.init.stack.len())
        .max(segment.fin.stack.len())
        .max(1)
        .min(segment.bounds.max_stack);

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
        return SatDiagnosis::OriginalUnsat;
    };
    solver.set_callbacks(Some(Timeout::new(remaining(Instant::now()).max(0.0))));
    match solver.solve_with(witness.iter().copied()) {
        Some(true) => {}
        Some(false) => return SatDiagnosis::OriginalUnsat,
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
    while ell >= 0 {
        let now = Instant::now();
        if now >= deadline {
            timed_out = true;
            break;
        }
        solver.set_callbacks(Some(Timeout::new(remaining(now).max(0.0))));
        let assumption = dims.x((ell as usize) + 1, nop);
        match solver.solve_with([assumption]) {
            Some(true) => {
                let seq = reconstruct(&solver, &dims, &ops);
                if forward_valid(&seq, segment, &mut canon) {
                    best_len = best_len.min(seq.len());
                }
                ell -= 1;
            }
            Some(false) => {
                proven_optimal = true;
                break;
            }
            None => {
                timed_out = true;
                break;
            }
        }
    }

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
    };

    let l_orig = segment.ops.len();
    // Hard failure: no model. Do not fall back to A* — see module-level invariant.
    let fail = || SearchResult {
        ops: None,
        timed_out: false,
        solver_time_secs: started.elapsed().as_secs_f64(),
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

    let r = (segment.bounds.max_local as usize) + 1;
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
    let h = (max_height + 1)
        .max(segment.init.stack.len())
        .max(segment.fin.stack.len())
        .max(1)
        .min(segment.bounds.max_stack);

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
    let Some(witness) =
        original_witness_assumptions(segment, &ops, &dims)
    else {
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
    let mut ell = l_orig as isize - 1;
    while ell >= 0 {
        let now = Instant::now();
        if now >= deadline {
            timed_out = true;
            break;
        }
        solver.set_callbacks(Some(Timeout::new(remaining(now).max(0.0))));
        let assumption = dims.x((ell as usize) + 1, nop);
        match solver.solve_with([assumption]) {
            Some(true) => {
                let seq = reconstruct(&solver, &dims, &ops);
                if forward_valid(&seq, segment, &mut canon) {
                    best = Some(seq);
                }
                ell -= 1;
            }
            Some(false) => break, // proven optimal
            None => {
                timed_out = true;
                break;
            }
        }
    }

    SearchResult {
        ops: best,
        timed_out,
        solver_time_secs: started.elapsed().as_secs_f64(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::synthesis::test_synthesis_rewrites;
    use crate::wasm::{materialize_segments, parse_wasm_file, split_raw_segments};

    fn rules() -> Vec<egg::Rewrite<crate::lang::ValueLang, ()>> {
        test_synthesis_rewrites()
    }

    /// Phase-1 core vocabulary size (unique ≡_R classes) without subtree/saturation expansion.
    fn core_vocab_size(segment: &StraightSegment, rules: &[egg::Rewrite<crate::lang::ValueLang, ()>]) -> usize {
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
        let wasm = wat::parse_str(
            r#"(module (func (param i32) local.get 0 i32.const 1 i32.add))"#,
        )
        .unwrap();
        let info = crate::wasm::parse_wasm_bytes(&wasm).unwrap();
        let short = materialize_segments(&info.segments, 1).pop().unwrap();
        assert_eq!(max_vocab_for_segment(&short), MIN_VOCAB);

        let long_ops: Vec<SemOp> = (0..60)
            .map(|_| SemOp::LocalGet(0))
            .collect();
        let long = StraightSegment {
            ops: long_ops,
            ..short.clone()
        };
        assert_eq!(max_vocab_for_segment(&long), 80);
    }
}
