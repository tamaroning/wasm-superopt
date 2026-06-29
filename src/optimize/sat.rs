//! Pure-SAT backend for straight-line length minimization.
//!
//! Implements the descending Pure-SAT iteration described in
//! `wasm_superopt_sat_encoding.md`: a finite value vocabulary `V` and operation
//! result tables are built up front, the synthesis problem is encoded into CNF
//! with an instruction-length upper bound `L = L_orig`, and the optimal length is
//! found by repeatedly assuming NOP-propagation (`x_{ell+1,NOP} = 1`) and
//! descending `ell` until the solver returns UNSAT.
//!
//! Side effects (memory / global / call / opaque ops) are handled directly,
//! following the SuperStack approach: each side-effecting op is encoded as an
//! uninterpreted instruction that consumes its operand values and produces fresh
//! result symbols. `storage` ops must appear exactly once, non-storage opaque ops
//! at most once, and the segment's dependency list (`deplist`) is enforced as a
//! relative-order constraint between the corresponding steps. There is no A*
//! fallback: if a segment cannot be encoded/improved, the original is kept.

use super::canon::{CanonId, Canonizer};
use super::search::{SearchConfig, SearchResult, is_grounded, validate_solution_ops};
use crate::lang::ValueLang;
use crate::semantics::{InstKind, SemOp};
use crate::sym::{LocalReq, SymMachine, SymState, ValueExpr, all_subtree_exprs};
use crate::value::parse_value_expr;
use crate::wasm::{OpaqueMeta, StraightSegment};
use cadical::{Solver, Timeout};
use egg::{Id, Runner};
use std::collections::HashMap;
use std::time::Instant;

/// Max instruction-length upper bound `L` for SAT encoding; longer segments fall back.
const MAX_SAT_LEN: usize = 40;
/// Max value-vocabulary size `|V|`; larger problems fall back to A*.
/// mux1_1 gap blocks need at most 53 base values (measured); 64 leaves headroom.
const MAX_VOCAB: usize = 64;
/// Equivalence-saturation rounds for vocabulary expansion (`k_sat`).
const K_SAT: usize = 2;
/// Equality-saturation limits for the batched operation-result-table build.
const TABLE_ITER_LIMIT: usize = 12;
const TABLE_NODE_LIMIT: usize = 100_000;

const SAT_BINOPS: &[InstKind] = &[
    InstKind::I32Add,
    InstKind::I32Sub,
    InstKind::I32Mul,
    InstKind::I32DivU,
    InstKind::I32DivS,
    InstKind::I32RemU,
    InstKind::I32RemS,
    InstKind::I32Shl,
    InstKind::I32And,
    InstKind::I32Or,
    InstKind::I32Xor,
    InstKind::I32ShrU,
    InstKind::I32ShrS,
    InstKind::I32Rotl,
    InstKind::I32Rotr,
    InstKind::I32Eq,
    InstKind::I32Ne,
    InstKind::I32LtS,
    InstKind::I32LeS,
    InstKind::I32GtS,
];

const SAT_UNOPS: &[InstKind] = &[
    InstKind::I32Eqz,
    InstKind::I32Clz,
    InstKind::I32Ctz,
    InstKind::I32Popcnt,
];

/// Finite value vocabulary `V`: canonical value classes plus `⊥`/`★` (handled by index).
struct Vocab {
    /// Representative expression per real value index.
    reals: Vec<ValueExpr>,
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
    Const { c: i32, val: usize },
    Get(u32),
    Set(u32),
    Tee(u32),
    Drop,
    Unop { kind: InstKind, table: Vec<Option<usize>> },
    Binop { kind: InstKind, table: Vec<Vec<Option<usize>>> },
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
            SatOp::Const { c, .. } => Some(SemOp::I32Const(*c)),
            SatOp::Get(r) => Some(SemOp::LocalGet(*r)),
            SatOp::Set(r) => Some(SemOp::LocalSet(*r)),
            SatOp::Tee(r) => Some(SemOp::LocalTee(*r)),
            SatOp::Drop => Some(SemOp::Drop),
            SatOp::Unop { kind, .. } => Some(unop_kind_to_sem(*kind)),
            SatOp::Binop { kind, .. } => Some(binop_kind_to_sem(*kind)),
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
}

impl Cnf {
    fn new() -> Self {
        Self {
            clauses: Vec::new(),
        }
    }

    fn add(&mut self, clause: Vec<i32>) {
        self.clauses.push(clause);
    }

    fn unit(&mut self, lit: i32) {
        self.clauses.push(vec![lit]);
    }

    /// `x → (a ↔ b)`.
    fn imply_iff(&mut self, x: i32, a: i32, b: i32) {
        self.clauses.push(vec![-x, -a, b]);
        self.clauses.push(vec![-x, a, -b]);
    }

    /// At-most-one over `lits` using a sequential (Sinz) encoding.
    fn at_most_one(&mut self, lits: &[i32], dims: &mut Dims) {
        let n = lits.len();
        if n <= 1 {
            return;
        }
        let s: Vec<i32> = (0..n - 1).map(|_| dims.fresh()).collect();
        self.clauses.push(vec![-lits[0], s[0]]);
        self.clauses.push(vec![-lits[n - 1], -s[n - 2]]);
        for i in 1..n - 1 {
            self.clauses.push(vec![-lits[i], s[i]]);
            self.clauses.push(vec![-s[i - 1], s[i]]);
            self.clauses.push(vec![-lits[i], -s[i - 1]]);
        }
    }

    /// Exactly-one over `lits` using a sequential (Sinz) at-most-one + at-least-one.
    fn exactly_one(&mut self, lits: &[i32], dims: &mut Dims) {
        if lits.is_empty() {
            // Forces UNSAT; should not occur for well-formed dimensions.
            self.clauses.push(vec![]);
            return;
        }
        self.clauses.push(lits.to_vec());
        if lits.len() == 1 {
            return;
        }
        let n = lits.len();
        let s: Vec<i32> = (0..n - 1).map(|_| dims.fresh()).collect();
        self.clauses.push(vec![-lits[0], s[0]]);
        self.clauses.push(vec![-lits[n - 1], -s[n - 2]]);
        for i in 1..n - 1 {
            self.clauses.push(vec![-lits[i], s[i]]);
            self.clauses.push(vec![-s[i - 1], s[i]]);
            self.clauses.push(vec![-lits[i], -s[i - 1]]);
        }
    }
}

fn binop_wat(kind: InstKind) -> &'static str {
    match kind {
        InstKind::I32Add => "i32.add",
        InstKind::I32Sub => "i32.sub",
        InstKind::I32Mul => "i32.mul",
        InstKind::I32DivU => "i32.div_u",
        InstKind::I32DivS => "i32.div_s",
        InstKind::I32RemU => "i32.rem_u",
        InstKind::I32RemS => "i32.rem_s",
        InstKind::I32Shl => "i32.shl",
        InstKind::I32And => "i32.and",
        InstKind::I32Or => "i32.or",
        InstKind::I32Xor => "i32.xor",
        InstKind::I32ShrU => "i32.shr_u",
        InstKind::I32ShrS => "i32.shr_s",
        InstKind::I32Rotl => "i32.rotl",
        InstKind::I32Rotr => "i32.rotr",
        InstKind::I32Eq => "i32.eq",
        InstKind::I32Ne => "i32.ne",
        InstKind::I32LtS => "i32.lt_s",
        InstKind::I32LeS => "i32.le_s",
        InstKind::I32GtS => "i32.gt_s",
        other => panic!("not a SAT binop: {other:?}"),
    }
}

fn unop_wat(kind: InstKind) -> &'static str {
    match kind {
        InstKind::I32Eqz => "i32.eqz",
        InstKind::I32Clz => "i32.clz",
        InstKind::I32Ctz => "i32.ctz",
        InstKind::I32Popcnt => "i32.popcnt",
        other => panic!("not a SAT unop: {other:?}"),
    }
}

fn binop_kind_to_sem(kind: InstKind) -> SemOp {
    match kind {
        InstKind::I32Add => SemOp::I32Add,
        InstKind::I32Sub => SemOp::I32Sub,
        InstKind::I32Mul => SemOp::I32Mul,
        InstKind::I32DivU => SemOp::I32DivU,
        InstKind::I32DivS => SemOp::I32DivS,
        InstKind::I32RemU => SemOp::I32RemU,
        InstKind::I32RemS => SemOp::I32RemS,
        InstKind::I32Shl => SemOp::I32Shl,
        InstKind::I32And => SemOp::I32And,
        InstKind::I32Or => SemOp::I32Or,
        InstKind::I32Xor => SemOp::I32Xor,
        InstKind::I32ShrU => SemOp::I32ShrU,
        InstKind::I32ShrS => SemOp::I32ShrS,
        InstKind::I32Rotl => SemOp::I32Rotl,
        InstKind::I32Rotr => SemOp::I32Rotr,
        InstKind::I32Eq => SemOp::I32Eq,
        InstKind::I32Ne => SemOp::I32Ne,
        InstKind::I32LtS => SemOp::I32LtS,
        InstKind::I32LeS => SemOp::I32LeS,
        InstKind::I32GtS => SemOp::I32GtS,
        other => panic!("not a SAT binop: {other:?}"),
    }
}

fn unop_kind_to_sem(kind: InstKind) -> SemOp {
    match kind {
        InstKind::I32Eqz => SemOp::I32Eqz,
        InstKind::I32Clz => SemOp::I32Clz,
        InstKind::I32Ctz => SemOp::I32Ctz,
        InstKind::I32Popcnt => SemOp::I32Popcnt,
        other => panic!("not a SAT unop: {other:?}"),
    }
}

fn binop_expr(kind: InstKind, a1: &ValueExpr, a0: &ValueExpr) -> ValueExpr {
    parse_value_expr(&format!("({} {a1} {a0})", binop_wat(kind)))
}

fn unop_expr(kind: InstKind, a: &ValueExpr) -> ValueExpr {
    parse_value_expr(&format!("({} {a})", unop_wat(kind)))
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

fn build_vocab(segment: &StraightSegment, canon: &mut Canonizer) -> Option<(Vocab, usize)> {
    build_vocab_with_limit(segment, canon, MAX_VOCAB)
}

/// Base vocabulary size before the `MAX_VOCAB` cap (for tuning / diagnostics).
pub fn base_vocab_len(segment: &StraightSegment, rules: &[egg::Rewrite<crate::lang::ValueLang, ()>]) -> usize {
    let mut canon = Canonizer::new(rules.to_vec());
    let (seeds, _) = collect_seed_exprs(segment);
    let mut index_of_canon: HashMap<CanonId, usize> = HashMap::new();
    let mut base: Vec<ValueExpr> = Vec::new();
    for e in &seeds {
        for sub in all_subtree_exprs(e) {
            base.push(sub);
        }
    }
    for &c in crate::semantics::synthesis_constants() {
        base.push(parse_value_expr(&c.to_string()));
    }
    dedup_by_string(&mut base);
    let mut count = 0usize;
    for e in &base {
        let id = canon.canon(e);
        if index_of_canon.insert(id, count).is_none() {
            count += 1;
        }
    }
    count
}

fn build_vocab_with_limit(
    segment: &StraightSegment,
    canon: &mut Canonizer,
    max_vocab: usize,
) -> Option<(Vocab, usize)> {
    let (seeds, max_height) = collect_seed_exprs(segment);

    let mut index_of_canon: HashMap<CanonId, usize> = HashMap::new();
    let mut reals: Vec<ValueExpr> = Vec::new();

    // Base vocabulary: every subexpression of init/fin and all original intermediate
    // values, plus the synthesis constants. These MUST all fit so that the original
    // sequence is representable (the first descending solve is then trivially SAT).
    let mut base: Vec<ValueExpr> = Vec::new();
    for e in &seeds {
        for sub in all_subtree_exprs(e) {
            base.push(sub);
        }
    }
    for &c in crate::semantics::synthesis_constants() {
        base.push(parse_value_expr(&c.to_string()));
    }
    dedup_by_string(&mut base);

    for e in &base {
        let id = canon.canon(e);
        if let std::collections::hash_map::Entry::Vacant(slot) = index_of_canon.entry(id) {
            if reals.len() >= max_vocab {
                return None; // base alone too large; let the caller fall back to A*
            }
            slot.insert(reals.len());
            reals.push(e.clone());
        }
    }

    // Equivalence saturation (best-effort, capped): pull in alternative arithmetic
    // decompositions (mul/shl, …) and their operand constants so the SAT search can
    // pick a shorter form. Capped so the encoding stays tractable.
    let mut frontier: Vec<ValueExpr> = reals.clone();
    'rounds: for _ in 0..K_SAT {
        let mut next: Vec<ValueExpr> = Vec::new();
        for e in &frontier {
            for (_, e1, e2) in canon.binop_decompositions(e) {
                for cand in all_subtree_exprs(&e1)
                    .into_iter()
                    .chain(all_subtree_exprs(&e2))
                {
                    let id = canon.canon(&cand);
                    if let std::collections::hash_map::Entry::Vacant(slot) =
                        index_of_canon.entry(id)
                    {
                        if reals.len() >= max_vocab {
                            break 'rounds;
                        }
                        slot.insert(reals.len());
                        reals.push(cand.clone());
                        next.push(cand);
                    }
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
) -> Option<Vec<SatOp>> {
    let n = vocab.n();
    let mut ops = vec![SatOp::Nop];

    // Constants: synthesis constants plus any literal already present in V.
    let mut const_candidates: Vec<i32> = crate::semantics::synthesis_constants().to_vec();
    for real in &vocab.reals {
        if let ValueLang::I32Const(c) = real[real.root()] {
            const_candidates.push(c);
        }
    }
    const_candidates.sort_unstable();
    const_candidates.dedup();
    for c in const_candidates {
        let expr = parse_value_expr(&c.to_string());
        if let Some(val) = vocab.real_of_expr(canon, &expr) {
            ops.push(SatOp::Const { c, val });
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

    let mut uni_ids: Vec<Vec<Id>> = Vec::with_capacity(SAT_UNOPS.len());
    for &kind in SAT_UNOPS {
        let mut col = Vec::with_capacity(n);
        for a in 0..n {
            col.push(runner.egraph.add_expr(&unop_expr(kind, &vocab.reals[a])));
        }
        uni_ids.push(col);
    }
    let mut bin_ids: Vec<Vec<Id>> = Vec::with_capacity(SAT_BINOPS.len());
    for &kind in SAT_BINOPS {
        let mut col = Vec::with_capacity(n * n);
        for a1 in 0..n {
            for a0 in 0..n {
                col.push(
                    runner
                        .egraph
                        .add_expr(&binop_expr(kind, &vocab.reals[a1], &vocab.reals[a0])),
                );
            }
        }
        bin_ids.push(col);
    }

    let runner = runner.run(rules);
    let mut class_to_real: HashMap<Id, usize> = HashMap::new();
    for (i, id) in real_ids.iter().enumerate() {
        class_to_real.entry(runner.egraph.find(*id)).or_insert(i);
    }
    let lookup = |id: Id| class_to_real.get(&runner.egraph.find(id)).copied();

    for (ki, &kind) in SAT_UNOPS.iter().enumerate() {
        let mut table = vec![None; n];
        let mut any = false;
        for a in 0..n {
            if let Some(idx) = lookup(uni_ids[ki][a]) {
                table[a] = Some(idx);
                any = true;
            }
        }
        if any {
            ops.push(SatOp::Unop { kind, table });
        }
    }
    for (ki, &kind) in SAT_BINOPS.iter().enumerate() {
        let mut table = vec![vec![None; n]; n];
        let mut any = false;
        for a1 in 0..n {
            for a0 in 0..n {
                if let Some(idx) = lookup(bin_ids[ki][a1 * n + a0]) {
                    table[a1][a0] = Some(idx);
                    any = true;
                }
            }
        }
        if any {
            ops.push(SatOp::Binop { kind, table });
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
fn equiv_reals(vocab: &Vocab, canon: &mut Canonizer, req: usize) -> Vec<usize> {
    let target = canon.canon(&vocab.reals[req]);
    (0..vocab.n())
        .filter(|&v| canon.canon(&vocab.reals[v]) == target)
        .collect()
}

/// Pin one SAT op per original instruction step (`x_{i,o} = 1`).
fn sat_op_index_for_orig(ops: &[SatOp], sem: &SemOp) -> Option<usize> {
    match sem {
        SemOp::I32Const(c) => ops.iter().position(|o| {
            matches!(o, SatOp::Const { c: cc, .. } if cc == c)
        }),
        SemOp::LocalGet(s) => ops.iter().position(|o| matches!(o, SatOp::Get(slot) if slot == s)),
        SemOp::LocalSet(s) => ops.iter().position(|o| matches!(o, SatOp::Set(slot) if slot == s)),
        SemOp::LocalTee(s) => ops.iter().position(|o| matches!(o, SatOp::Tee(slot) if slot == s)),
        SemOp::Drop => ops.iter().position(|o| matches!(o, SatOp::Drop)),
        SemOp::I32Add => ops.iter().position(|o| matches!(o, SatOp::Binop { kind: InstKind::I32Add, .. })),
        SemOp::I32Sub => ops.iter().position(|o| matches!(o, SatOp::Binop { kind: InstKind::I32Sub, .. })),
        SemOp::I32Mul => ops.iter().position(|o| matches!(o, SatOp::Binop { kind: InstKind::I32Mul, .. })),
        SemOp::I32Load { id, .. }
        | SemOp::I32Store { id, .. }
        | SemOp::Call { id, .. }
        | SemOp::GlobalGet { id, .. }
        | SemOp::GlobalSet { id, .. }
        | SemOp::Opaque { id, .. } => ops
            .iter()
            .position(|o| matches!(o, SatOp::Opaque { id: oid, .. } if oid == id)),
        other => {
            let kind = match other {
                SemOp::I32DivU => InstKind::I32DivU,
                SemOp::I32DivS => InstKind::I32DivS,
                SemOp::I32RemU => InstKind::I32RemU,
                SemOp::I32RemS => InstKind::I32RemS,
                SemOp::I32Shl => InstKind::I32Shl,
                SemOp::I32And => InstKind::I32And,
                SemOp::I32Or => InstKind::I32Or,
                SemOp::I32Xor => InstKind::I32Xor,
                SemOp::I32ShrU => InstKind::I32ShrU,
                SemOp::I32ShrS => InstKind::I32ShrS,
                SemOp::I32Rotl => InstKind::I32Rotl,
                SemOp::I32Rotr => InstKind::I32Rotr,
                SemOp::I32Eq => InstKind::I32Eq,
                SemOp::I32Ne => InstKind::I32Ne,
                SemOp::I32LtS => InstKind::I32LtS,
                SemOp::I32LeS => InstKind::I32LeS,
                SemOp::I32GtS => InstKind::I32GtS,
                SemOp::I32Eqz => InstKind::I32Eqz,
                SemOp::I32Clz => InstKind::I32Clz,
                SemOp::I32Ctz => InstKind::I32Ctz,
                SemOp::I32Popcnt => InstKind::I32Popcnt,
                _ => return None,
            };
            ops.iter().position(|o| match o {
                SatOp::Unop { kind: k, .. } => *k == kind,
                SatOp::Binop { kind: k, .. } => *k == kind,
                _ => false,
            })
        }
    }
}

fn original_witness_assumptions(
    segment: &StraightSegment,
    ops: &[SatOp],
    dims: &Dims,
) -> Option<Vec<i32>> {
    let mut assumptions = Vec::with_capacity(segment.ops.len());
    for (step, sem) in segment.ops.iter().enumerate() {
        let o = sat_op_index_for_orig(ops, sem)?;
        assumptions.push(dims.x(step + 1, o));
    }
    Some(assumptions)
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

    // §5.1 instruction uniqueness.
    for i in 1..=l {
        let lits: Vec<i32> = (0..dims.n_ops).map(|o| dims.x(i, o)).collect();
        cnf.exactly_one(&lits, dims);
    }
    // §5.1 stack/local value uniqueness.
    for i in 0..=l {
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
                SatOp::Unop { table, .. } => {
                    cnf.add(vec![-xio, -dims.y(i - 1, 0, bot)]);
                    for a in 0..n {
                        match table[a] {
                            Some(res) => {
                                cnf.add(vec![-xio, -dims.y(i - 1, 0, a), dims.y(i, 0, res)])
                            }
                            None => cnf.add(vec![-xio, -dims.y(i - 1, 0, a)]),
                        }
                    }
                    // Top changes; deeper cells unchanged.
                    for j in 1..h {
                        for v in 0..sd {
                            cnf.imply_iff(xio, dims.y(i, j, v), dims.y(i - 1, j, v));
                        }
                    }
                    locals_unchanged(&mut cnf, dims, i, xio);
                }
                SatOp::Binop { table, .. } => {
                    cnf.add(vec![-xio, -dims.y(i - 1, 0, bot)]);
                    cnf.add(vec![-xio, -dims.y(i - 1, 1, bot)]);
                    // Domain restriction (avoids O(n^2) forbid clauses): for each first
                    // operand, require a defined second operand, and pin the result.
                    for a1 in 0..n {
                        let mut clause = vec![-xio, -dims.y(i - 1, 1, a1)];
                        for a0 in 0..n {
                            if let Some(res) = table[a1][a0] {
                                clause.push(dims.y(i - 1, 0, a0));
                                cnf.add(vec![
                                    -xio,
                                    -dims.y(i - 1, 1, a1),
                                    -dims.y(i - 1, 0, a0),
                                    dims.y(i, 0, res),
                                ]);
                            }
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
                    encode_opaque(&mut cnf, dims, i, xio, vocab, canon, in_reals, out_reals);
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
        if let SatOp::Opaque {
            id, storage, ..
        } = op
        {
            op_index_of_id.insert(*id, o);
            let occ: Vec<i32> = (1..=l).map(|i| dims.x(i, o)).collect();
            if *storage {
                cnf.exactly_one(&occ, dims);
            } else {
                cnf.at_most_one(&occ, dims);
            }
        }
    }
    // Relative-order constraints: for each `(before, after)`, forbid `after` at a step
    // earlier-or-equal to `before` (i.e. `step(before) < step(after)`).
    for &(before, after) in &segment.dependencies {
        if let (Some(&ob), Some(&oa)) =
            (op_index_of_id.get(&before), op_index_of_id.get(&after))
        {
            for ib in 1..=l {
                for ia in 1..=ib {
                    // `after` at step ia, `before` at step ib >= ia → violates order.
                    cnf.add(vec![-dims.x(ia, oa), -dims.x(ib, ob)]);
                }
            }
        }
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
    canon: &mut Canonizer,
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
        let equiv = equiv_reals(vocab, canon, req);
        let mut clause = vec![-xio];
        for &v in &equiv {
            clause.push(dims.y(i - 1, k, v));
        }
        cnf.add(clause);
        for v in 0..n {
            if !equiv.contains(&v) {
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
    let bounds = &segment.bounds;
    let mut m = SymMachine::from_segment_entry(
        segment.num_params,
        bounds,
        &segment.init,
        bounds.max_stack,
    );
    for op in ops {
        if m.exec(op).is_err() {
            return false;
        }
    }
    is_grounded(&m.to_fin_state(), &segment.fin, bounds, canon)
}

/// Why the witness SAT model fails `forward_valid` / `validate_solution_ops`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WitnessFailure {
    OpsMismatch { step: usize, expected: String, got: String },
    ForwardExec { step: usize, op: String },
    NotGrounded { stack: bool, locals: String },
    ValidateSolutionOps,
}

/// Build encoding and solve with original-instruction witness assumptions only.
/// `Some(true)` / `Some(false)` = SAT / UNSAT; `None` = could not build or pin ops.
pub fn original_witness_sat(
    segment: &StraightSegment,
    rules: &[egg::Rewrite<crate::lang::ValueLang, ()>],
) -> Option<bool> {
    let l_orig = segment.ops.len();
    if l_orig == 0 || l_orig > MAX_SAT_LEN {
        return None;
    }
    let mut canon = Canonizer::new(rules.to_vec());
    let (vocab, max_height) = build_vocab(segment, &mut canon)?;
    let r = (segment.bounds.max_local as usize) + 1;
    let ops = build_ops(segment, &vocab, &mut canon, rules, r)?;
    let h = (max_height + 1)
        .max(segment.init.stack.len())
        .max(segment.fin.stack.len())
        .max(1)
        .min(segment.bounds.max_stack);
    let mut dims = Dims::new(l_orig, h, r, vocab.n(), ops.len());
    let cnf = encode(segment, &vocab, &ops, &mut dims, &mut canon)?;
    let mut solver: Solver = Solver::new();
    for clause in &cnf.clauses {
        solver.add_clause(clause.iter().copied());
    }
    let witness = original_witness_assumptions(segment, &ops, &dims)?;
    Some(solver.solve_with(witness.iter().copied()) == Some(true))
}

/// After a successful witness solve, explain why the reconstructed model is rejected.
pub fn witness_failure(
    segment: &StraightSegment,
    rules: &[egg::Rewrite<crate::lang::ValueLang, ()>],
) -> Option<WitnessFailure> {
    let l_orig = segment.ops.len();
    if l_orig == 0 || l_orig > MAX_SAT_LEN {
        return None;
    }
    let mut canon = Canonizer::new(rules.to_vec());
    let (vocab, max_height) = build_vocab(segment, &mut canon)?;
    let r = (segment.bounds.max_local as usize) + 1;
    let ops = build_ops(segment, &vocab, &mut canon, rules, r)?;
    let h = (max_height + 1)
        .max(segment.init.stack.len())
        .max(segment.fin.stack.len())
        .max(1)
        .min(segment.bounds.max_stack);
    let mut dims = Dims::new(l_orig, h, r, vocab.n(), ops.len());
    let cnf = encode(segment, &vocab, &ops, &mut dims, &mut canon)?;
    let mut solver: Solver = Solver::new();
    for clause in &cnf.clauses {
        solver.add_clause(clause.iter().copied());
    }
    let witness = original_witness_assumptions(segment, &ops, &dims)?;
    if solver.solve_with(witness.iter().copied()) != Some(true) {
        return None;
    }
    let seq = reconstruct(&solver, &dims, &ops);
    for (step, (exp, got)) in segment.ops.iter().zip(seq.iter()).enumerate() {
        if exp != got {
            return Some(WitnessFailure::OpsMismatch {
                step,
                expected: format!("{exp:?}"),
                got: format!("{got:?}"),
            });
        }
    }
    if seq.len() != segment.ops.len() {
        return Some(WitnessFailure::OpsMismatch {
            step: seq.len().min(segment.ops.len()),
            expected: format!("{} ops", segment.ops.len()),
            got: format!("{} ops", seq.len()),
        });
    }
    let bounds = &segment.bounds;
    let mut m = SymMachine::from_segment_entry(
        segment.num_params,
        bounds,
        &segment.init,
        bounds.max_stack,
    );
    for (step, op) in seq.iter().enumerate() {
        if m.exec(op).is_err() {
            return Some(WitnessFailure::ForwardExec {
                step,
                op: format!("{op:?}"),
            });
        }
    }
    let fin = m.to_fin_state();
    if !is_grounded(&fin, &segment.fin, bounds, &mut canon) {
        let stack_ok = fin.stack.len() == segment.fin.stack.len()
            && fin
                .stack
                .iter()
                .zip(segment.fin.stack.iter())
                .all(|(a, b)| canon.canon(a) == canon.canon(b));
        let mut local_mismatches = Vec::new();
        let mut slots: std::collections::BTreeSet<u32> =
            segment.fin.locals.keys().copied().collect();
        slots.extend(fin.locals.keys().copied());
        for slot in slots {
            if slot > bounds.max_local {
                continue;
            }
            let cur = fin.locals.get(&slot);
            let expected = segment.fin.locals.get(&slot);
            let ok = match (cur, expected) {
                (None | Some(LocalReq::DontCare), None) => true,
                (Some(LocalReq::DontCare), _) | (None, Some(LocalReq::DontCare)) => true,
                (Some(LocalReq::Need(a)), Some(LocalReq::Need(b))) => canon.canon(a) == canon.canon(b),
                _ => false,
            };
            if !ok {
                local_mismatches.push(format!("L{slot}: {cur:?} vs {expected:?}"));
            }
        }
        return Some(WitnessFailure::NotGrounded {
            stack: stack_ok,
            locals: local_mismatches.join("; "),
        });
    }
    if !validate_solution_ops(&seq, segment) {
        return Some(WitnessFailure::ValidateSolutionOps);
    }
    None
}

/// Where `solve_sat` stopped (for debugging benchmark gaps vs SuperStack).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SatDiagnosis {
    TooLong { l_orig: usize, max: usize },
    VocabBuildFailed,
    OpsBuildFailed,
    EncodeFailed { vocab: usize, n_ops: usize, h: usize, r: usize },
    OriginalUnsat,
    OriginalModelInvalid,
    Solved { best_len: usize, proven_optimal: bool, timed_out: bool },
}

/// Inspect SAT pipeline stages without running the full descending loop (unless encoding succeeds).
pub fn diagnose_sat(
    segment: &StraightSegment,
    rules: &[egg::Rewrite<crate::lang::ValueLang, ()>],
    cfg: &SearchConfig,
) -> SatDiagnosis {
    let l_orig = segment.ops.len();
    if l_orig == 0 || l_orig > MAX_SAT_LEN {
        return SatDiagnosis::TooLong {
            l_orig,
            max: MAX_SAT_LEN,
        };
    }

    let mut canon = Canonizer::new(rules.to_vec());
    let Some((vocab, max_height)) = build_vocab(segment, &mut canon) else {
        return SatDiagnosis::VocabBuildFailed;
    };

    let r = (segment.bounds.max_local as usize) + 1;
    let Some(ops) = build_ops(segment, &vocab, &mut canon, rules, r) else {
        return SatDiagnosis::OpsBuildFailed;
    };

    let h = (max_height + 1)
        .max(segment.init.stack.len())
        .max(segment.fin.stack.len())
        .max(1)
        .min(segment.bounds.max_stack);

    let mut dims = Dims::new(l_orig, h, r, vocab.n(), ops.len());
    let Some(cnf) = encode(segment, &vocab, &ops, &mut dims, &mut canon) else {
        return SatDiagnosis::EncodeFailed {
            vocab: vocab.n(),
            n_ops: ops.len(),
            h,
            r,
        };
    };

    let timeout = cfg.timeout_secs.unwrap_or(super::search::DEFAULT_TIMEOUT_BASE_SECS);
    let mut solver: Solver = Solver::new();
    for clause in &cnf.clauses {
        solver.add_clause(clause.iter().copied());
    }
    let deadline = Instant::now() + std::time::Duration::from_secs(timeout);
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
    if !forward_valid(&seq, segment, &mut canon) || !validate_solution_ops(&seq, segment) {
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
                if forward_valid(&seq, segment, &mut canon) && validate_solution_ops(&seq, segment) {
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

/// One row of gap analysis: SuperStack improved, ewasm did not (and did not time out).
#[derive(Clone, Debug)]
pub struct SatGapRow {
    pub block_id: String,
    pub ss_saved: usize,
    pub ew_outcome: String,
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
        let entry = by_id.entry(bid.to_string()).or_insert((0, 0, String::new()));
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

/// Parallel witness-only scan for gap blocks (no descending SAT loop). Much faster than `classify_sat_gaps_parallel`.
pub fn scan_gap_witness_parallel(
    segments: &[StraightSegment],
    problem_ids: &[String],
    rules: &[egg::Rewrite<crate::lang::ValueLang, ()>],
    jobs: usize,
) -> Vec<(String, Option<bool>)> {
    use crate::optimize::statistics::block_id;
    use rayon::prelude::*;
    use std::collections::HashMap;

    let seg_by_id: HashMap<String, &StraightSegment> = segments
        .iter()
        .map(|s| (block_id(s), s))
        .collect();

    let work: Vec<(&StraightSegment, &str)> = problem_ids
        .iter()
        .filter_map(|bid| seg_by_id.get(bid).map(|s| (*s, bid.as_str())))
        .collect();

    let scan = |seg: &StraightSegment, bid: &str| -> (String, Option<bool>) {
        (bid.to_string(), original_witness_sat(seg, rules))
    };

    if jobs <= 1 {
        work.into_iter()
            .map(|(seg, bid)| scan(seg, bid))
            .collect()
    } else {
        crate::parallel::run_with_threads(jobs, || {
            work.par_iter()
                .map(|(seg, bid)| scan(seg, bid))
                .collect()
        })
    }
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

    let seg_by_id: HashMap<String, &StraightSegment> = segments
        .iter()
        .map(|s| (block_id(s), s))
        .collect();

    let work: Vec<(&StraightSegment, &str)> = problem_ids
        .iter()
        .filter_map(|bid| seg_by_id.get(bid).map(|s| (*s, bid.as_str())))
        .collect();

    let classify = |seg: &StraightSegment, bid: &str| -> SatGapRow {
        SatGapRow {
            block_id: bid.to_string(),
            ss_saved: 0,
            ew_outcome: String::new(),
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
/// Returns `ops = None` (and `timed_out = false`) when the encoding could not be
/// built or no improving model was found; the caller then keeps the original
/// sequence (there is no A* fallback).
pub fn solve_sat(
    segment: &StraightSegment,
    rules: &[egg::Rewrite<crate::lang::ValueLang, ()>],
    cfg: &SearchConfig,
) -> SearchResult {
    let started = Instant::now();
    let timeout = cfg.timeout_secs.unwrap_or(super::search::DEFAULT_TIMEOUT_BASE_SECS);

    let l_orig = segment.ops.len();
    let fail = || SearchResult {
        ops: None,
        timed_out: false,
        solver_time_secs: started.elapsed().as_secs_f64(),
    };

    if l_orig == 0 || l_orig > MAX_SAT_LEN {
        return fail();
    }

    let mut canon = Canonizer::new(rules.to_vec());
    let Some((vocab, max_height)) = build_vocab(segment, &mut canon) else {
        return fail();
    };

    let r = (segment.bounds.max_local as usize) + 1;
    let Some(ops) = build_ops(segment, &vocab, &mut canon, rules, r) else {
        return fail();
    };

    // Stack-height bound: original max height (+1 slack), capped by segment bounds.
    let h = (max_height + 1)
        .max(segment.init.stack.len())
        .max(segment.fin.stack.len())
        .max(1)
        .min(segment.bounds.max_stack);

    let mut dims = Dims::new(l_orig, h, r, vocab.n(), ops.len());
    let Some(cnf) = encode(segment, &vocab, &ops, &mut dims, &mut canon) else {
        return fail();
    };

    let mut solver: Solver = Solver::new();
    for clause in &cnf.clauses {
        solver.add_clause(clause.iter().copied());
    }

    let nop = NOP_INDEX;
    // Budget the solving phase by `timeout`; e-graph preprocessing above is not counted
    // against it (but is included in the reported `solver_time_secs`).
    let deadline = Instant::now() + std::time::Duration::from_secs(timeout);
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
            };
        }
    }

    let mut best: Option<Vec<SemOp>> = {
        let seq = reconstruct(&solver, &dims, &ops);
        if forward_valid(&seq, segment, &mut canon) && validate_solution_ops(&seq, segment) {
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
                if forward_valid(&seq, segment, &mut canon) && validate_solution_ops(&seq, segment) {
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
    use crate::optimize::format_ops;
    use crate::synthesis::test_synthesis_rewrites;

    fn rules() -> Vec<egg::Rewrite<crate::lang::ValueLang, ()>> {
        test_synthesis_rewrites()
    }

    fn segment_from_wat(wat: &str) -> StraightSegment {
        let wasm = wat::parse_str(wat).unwrap();
        let info = crate::wasm::parse_wasm_bytes(&wasm).unwrap();
        info.segments.into_iter().next().expect("one segment")
    }

    #[test]
    fn measure_base_vocab_for_gap_blocks() {
        use crate::wasm::{parse_wasm_file, split_segments};

        let path = std::path::Path::new("benchmarks/wsouper/mux1_1.wasm");
        let csv_path = std::path::Path::new("bench-results/wsouper/combined_blocks.csv");
        if !path.exists() || !csv_path.exists() {
            return;
        }
        let info = parse_wasm_file(path).expect("parse");
        let segments = split_segments(&info.segments, 12);
        let rules = rules();
        let problem_ids = problem_blocks_from_csv(csv_path).expect("csv");

        use crate::optimize::statistics::block_id;
        use std::collections::HashMap;
        let seg_by_id: HashMap<String, _> = segments.iter().map(|s| (block_id(s), s)).collect();

        let mut max_base = 0usize;
        let mut over48 = 0usize;
        for bid in &problem_ids {
            let Some(seg) = seg_by_id.get(bid) else { continue };
            let n = base_vocab_len(seg, &rules);
            max_base = max_base.max(n);
            if n > 48 {
                over48 += 1;
            }
        }
        eprintln!(
            "gap blocks: {}, max base_vocab_len: {}, over48: {}",
            problem_ids.len(),
            max_base,
            over48
        );
    }

    #[test]
    fn sat_finds_shortest_on_running_example() {
        // Pure (side-effect-free) version of the idea.md §12 example: redundant
        // 10-instruction sequence whose optimum is 7.
        let segment = segment_from_wat(
            r#"(module
                (func (param i32) (result i32 i32)
                  local.get 0
                  local.get 0
                  i32.const 1
                  i32.shl
                  local.set 0
                  i32.const 2
                  i32.mul
                  i32.const 4
                  i32.mul
                  local.get 0
                )
            )"#,
        );
        let result = solve_sat(&segment, &rules(), &SearchConfig::default());
        let ops = result.ops.expect("sat solution");
        assert_eq!(ops.len(), 7, "got: {}", format_ops(&ops));
        let mut canon = Canonizer::new(rules());
        assert!(forward_valid(&ops, &segment, &mut canon));
    }

    #[test]
    fn sat_matches_astar_on_small_tee_fusion() {
        let segment = segment_from_wat(
            r#"(module
                (func (param i32 i32)
                  local.get 1
                  i32.const 1
                  i32.add
                  local.set 1
                  local.get 1
                  local.get 0
                  i32.lt_s
                )
            )"#,
        );
        let orig = segment.original_len();
        let sat = solve_sat(&segment, &rules(), &SearchConfig::default());
        let astar = crate::optimize::search::solve_astar(&segment, &rules(), &SearchConfig::default());
        let sat_ops = sat.ops.expect("sat solution");
        let astar_ops = astar.ops.expect("astar solution");
        assert!(sat_ops.len() < orig, "sat: {}", format_ops(&sat_ops));
        assert_eq!(
            sat_ops.len(),
            astar_ops.len(),
            "sat {} vs astar {}",
            format_ops(&sat_ops),
            format_ops(&astar_ops)
        );
    }

    #[test]
    fn sat_handles_memory_segment_without_fallback() {
        // A side-effecting segment (store) is now encoded directly by the SAT backend
        // instead of falling back to A*.
        let segment = segment_from_wat(
            r#"(module
                (memory 1)
                (func (param i32)
                  local.get 0
                  i32.const 1
                  i32.add
                  i32.const 0
                  i32.store
                )
            )"#,
        );
        assert!(!segment.opaque_meta.is_empty(), "expected an opaque store op");
        let sat = solve_sat(&segment, &rules(), &SearchConfig::default());
        let ops = sat.ops.expect("sat solution for side-effecting segment");
        assert!(ops.len() <= segment.original_len(), "got: {}", format_ops(&ops));
        let mut canon = Canonizer::new(rules());
        assert!(forward_valid(&ops, &segment, &mut canon));
        assert!(crate::optimize::search::validate_solution_ops(&ops, &segment));
        // The store must be preserved exactly once.
        assert_eq!(
            ops.iter().filter(|op| matches!(op, SemOp::I32Store { .. })).count(),
            1
        );
    }

    #[test]
    #[ignore = "slow; use: ewasm mux1_1.wasm --classify-sat-gaps combined_blocks.csv -j16 --solver sat --split 12 --segment-timeout 10"]
    fn classify_mux1_1_sat_gaps() {
        use crate::wasm::{parse_wasm_file, split_segments};
        use std::collections::BTreeMap;

        let path = std::path::Path::new("benchmarks/wsouper/mux1_1.wasm");
        if !path.exists() {
            return;
        }
        let info = parse_wasm_file(path).expect("parse mux1_1");
        let segments = split_segments(&info.segments, 12);
        let cfg = SearchConfig {
            fixed_segment_timeout: Some(10),
            backend: super::super::Backend::Sat,
            ..SearchConfig::default()
        };
        let rules = rules();

        let csv_path = std::path::Path::new("bench-results/wsouper/combined_blocks.csv");
        if !csv_path.exists() {
            return;
        }
        let problem_ids = problem_blocks_from_csv(csv_path).expect("csv");
        let jobs = std::env::var("SAT_CLASSIFY_JOBS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(8);
        eprintln!("classify_mux1_1_sat_gaps: {} blocks, jobs={jobs}", problem_ids.len());
        let rows = classify_sat_gaps_parallel(&segments, &problem_ids, &rules, &cfg, jobs);
        let mut counts: BTreeMap<String, usize> = BTreeMap::new();
        for row in &rows {
            *counts.entry(format!("{:?}", row.diagnosis)).or_default() += 1;
        }
        eprintln!("problem blocks: {}", rows.len());
        for (k, v) in counts {
            eprintln!("  {v} {k}");
        }
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
    fn mux1_1_gap_regressions() {
        use crate::optimize::statistics::block_id;
        use crate::wasm::{parse_wasm_file, split_segments};

        let path = std::path::Path::new("benchmarks/wsouper/mux1_1.wasm");
        if !path.exists() {
            return;
        }
        let info = parse_wasm_file(path).expect("parse mux1_1");
        let segments = split_segments(&info.segments, 12);
        let rules = rules();
        let cfg = SearchConfig {
            fixed_segment_timeout: Some(10),
            backend: super::super::Backend::Sat,
            ..SearchConfig::default()
        };

        // i64 opaque split chunk: original must be SAT after per-chunk opaque_meta refresh.
        let seg = segments
            .iter()
            .find(|s| block_id(s) == "function_14_block_0_52")
            .expect("segment");
        assert!(
            !matches!(diagnose_sat(seg, &rules, &cfg), SatDiagnosis::OriginalUnsat),
            "function_14_block_0_52 should encode the original program"
        );

        // load/call chunk: witness path must not spuriously fail under timeout.
        let seg = segments
            .iter()
            .find(|s| block_id(s) == "function_117_block_16_2")
            .expect("segment");
        assert_ne!(
            diagnose_sat(seg, &rules, &cfg),
            SatDiagnosis::OriginalModelInvalid,
            "function_117_block_16_2 witness should be valid"
        );

        // arithmetic fold 0*40+x → x: superstack finds length 3.
        let seg = segments
            .iter()
            .find(|s| block_id(s) == "function_117_block_13")
            .expect("segment");
        let result = solve_sat(seg, &rules, &cfg);
        let ops = result.ops.expect("should improve function_117_block_13");
        assert!(
            ops.len() < seg.original_len(),
            "expected shorter than {}, got {}",
            seg.original_len(),
            format_ops(&ops)
        );
    }

    fn mux1_1_segment<'a>(
        segments: &'a [StraightSegment],
        target: &str,
    ) -> &'a StraightSegment {
        use crate::optimize::statistics::block_id;
        segments
            .iter()
            .find(|s| block_id(s) == target)
            .unwrap_or_else(|| panic!("segment {target} not found"))
    }

    /// Fast witness check only (no descending SAT loop). Use for gap debugging.
    fn assert_witness_valid(target: &str) {
        use crate::wasm::{parse_wasm_file, split_segments};

        let path = std::path::Path::new("benchmarks/wsouper/mux1_1.wasm");
        if !path.exists() {
            return;
        }
        let info = parse_wasm_file(path).expect("parse mux1_1");
        let segments = split_segments(&info.segments, 12);
        let seg = mux1_1_segment(&segments, target);
        let rules = rules();
        if let Some(reason) = witness_failure(seg, &rules) {
            panic!("{target}: witness invalid: {reason:?}\n  ops: {}", format_ops(&seg.ops));
        }
    }

    #[test]
    #[ignore = "debug: BLOCK=function_106_block_7_2 cargo test print_segment_init_fin -- --ignored --nocapture"]
    fn print_segment_init_fin() {
        use crate::sym::SymMachine;
        use crate::wasm::{parse_wasm_file, split_segments};

        let target = std::env::var("BLOCK").unwrap_or_else(|_| "function_106_block_7_2".into());
        let path = std::path::Path::new("benchmarks/wsouper/mux1_1.wasm");
        if !path.exists() {
            return;
        }
        let info = parse_wasm_file(path).expect("parse");
        let segments = split_segments(&info.segments, 12);
        let seg = mux1_1_segment(&segments, &target);
        eprintln!("{target} part={:?}", seg.split_part);
        eprintln!("init: {:?}", seg.init);
        eprintln!("fin: {:?}", seg.fin);
        let mut m = SymMachine::from_segment_entry(
            seg.num_params,
            &seg.bounds,
            &seg.init,
            seg.bounds.max_stack,
        );
        for op in &seg.ops {
            m.exec(op).unwrap();
        }
        eprintln!("exec fin: {:?}", m.to_fin_state());
    }

    fn gap_scan_jobs() -> usize {
        std::env::var("SAT_CLASSIFY_JOBS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(8)
    }

    #[test]
    fn witness_valid_function_69_block_1() {
        assert_witness_valid("function_69_block_1");
    }

    #[test]
    fn find_original_unsat_gap() {
        use crate::wasm::{parse_wasm_file, split_segments};

        let path = std::path::Path::new("benchmarks/wsouper/mux1_1.wasm");
        let csv_path = std::path::Path::new("bench-results/wsouper/combined_blocks.csv");
        if !path.exists() || !csv_path.exists() {
            return;
        }
        let info = parse_wasm_file(path).expect("parse");
        let segments = split_segments(&info.segments, 12);
        let rules = rules();
        let problem_ids = problem_blocks_from_csv(csv_path).expect("csv");
        let jobs = gap_scan_jobs();
        eprintln!("scan_gap_witness_parallel: {} blocks, jobs={jobs}", problem_ids.len());

        let unsat: Vec<_> = scan_gap_witness_parallel(&segments, &problem_ids, &rules, jobs)
            .into_iter()
            .filter(|(_, w)| !matches!(w, Some(true)))
            .collect();
        for (bid, w) in unsat.iter().take(5) {
            eprintln!("{bid}: witness={w:?}");
        }
        let only_unsat: Vec<_> = unsat
            .iter()
            .filter(|(_, w)| matches!(w, Some(false)))
            .map(|(b, _)| b.as_str())
            .collect();
        assert!(
            only_unsat.is_empty(),
            "OriginalUnsat: {only_unsat:?}, all witness issues: {unsat:?}"
        );
    }

    #[test]
    fn mux1_1_gap_witness_valid() {
        use crate::wasm::{parse_wasm_file, split_segments};

        let path = std::path::Path::new("benchmarks/wsouper/mux1_1.wasm");
        let csv_path = std::path::Path::new("bench-results/wsouper/combined_blocks.csv");
        if !path.exists() || !csv_path.exists() {
            return;
        }
        let info = parse_wasm_file(path).expect("parse");
        let segments = split_segments(&info.segments, 12);
        let rules = rules();
        let problem_ids = problem_blocks_from_csv(csv_path).expect("csv");
        let jobs = gap_scan_jobs();
        eprintln!("mux1_1_gap_witness_valid: {} blocks, jobs={jobs}", problem_ids.len());

        let mut bad = Vec::new();
        if jobs <= 1 {
            let seg_by_id: std::collections::HashMap<_, _> = segments
                .iter()
                .map(|s| (crate::optimize::statistics::block_id(s), s))
                .collect();
            for bid in &problem_ids {
                let Some(seg) = seg_by_id.get(bid) else { continue };
                if let Some(reason) = witness_failure(seg, &rules) {
                    bad.push((bid.clone(), reason));
                }
            }
        } else {
            use crate::optimize::statistics::block_id;
            use rayon::prelude::*;
            use std::collections::HashMap;

            let seg_by_id: HashMap<_, _> = segments.iter().map(|s| (block_id(s), s)).collect();
            let work: Vec<_> = problem_ids
                .iter()
                .filter_map(|bid| seg_by_id.get(bid).map(|s| (bid.clone(), *s)))
                .collect();
            bad = crate::parallel::run_with_threads(jobs, || {
                work.par_iter()
                    .filter_map(|(bid, seg)| {
                        witness_failure(seg, &rules).map(|reason| (bid.clone(), reason))
                    })
                    .collect()
            });
        }
        if !bad.is_empty() {
            for (bid, reason) in bad.iter().take(5) {
                eprintln!("{bid}: {reason:?}");
            }
            panic!(
                "{} gap block(s) still fail witness (showing up to 5 above)",
                bad.len()
            );
        }
    }

    #[test]
    fn witness_valid_function_106_block_7_2() {
        assert_witness_valid("function_106_block_7_2");
    }

    #[test]
    #[ignore = "debug one block: cargo test witness_debug_block -- --ignored --nocapture BLOCK=function_106_block_7_2"]
    fn witness_debug_block() {
        use crate::wasm::{parse_wasm_file, split_segments};

        let target = std::env::var("BLOCK").unwrap_or_else(|_| "function_106_block_7_2".into());
        let path = std::path::Path::new("benchmarks/wsouper/mux1_1.wasm");
        if !path.exists() {
            return;
        }
        let info = parse_wasm_file(path).expect("parse mux1_1");
        let segments = split_segments(&info.segments, 12);
        let seg = mux1_1_segment(&segments, &target);
        let rules = rules();
        let reason = witness_failure(seg, &rules);
        eprintln!("{target}: {reason:?}");
        eprintln!("ops: {}", format_ops(&seg.ops));
        eprintln!("diag: {:?}", diagnose_sat(seg, &rules, &SearchConfig {
            fixed_segment_timeout: Some(10),
            backend: super::super::Backend::Sat,
            ..SearchConfig::default()
        }));
    }

    #[test]
    #[ignore = "slow bulk scan; use witness_debug_block per block instead"]
    fn sample_model_invalid_failures() {
        use crate::optimize::statistics::block_id;
        use crate::wasm::{parse_wasm_file, split_segments};
        use std::collections::BTreeMap;

        let path = std::path::Path::new("benchmarks/wsouper/mux1_1.wasm");
        let csv_path = std::path::Path::new("bench-results/wsouper/combined_blocks.csv");
        if !path.exists() || !csv_path.exists() {
            return;
        }
        let info = parse_wasm_file(path).expect("parse");
        let segments = split_segments(&info.segments, 12);
        let rules = rules();
        let problem_ids = problem_blocks_from_csv(csv_path).expect("csv");
        let seg_by_id: std::collections::HashMap<_, _> =
            segments.iter().map(|s| (block_id(s), s)).collect();

        // Only scan no_solution rows; witness_failure is enough (skip diagnose_sat loop).
        let mut failure_counts: BTreeMap<String, usize> = BTreeMap::new();
        let mut samples: Vec<(String, WitnessFailure)> = Vec::new();
        for bid in problem_ids.iter().take(20) {
            let Some(seg) = seg_by_id.get(bid) else { continue };
            let Some(reason) = witness_failure(seg, &rules) else {
                continue;
            };
            let key = format!("{reason:?}");
            *failure_counts.entry(key.clone()).or_default() += 1;
            if samples.len() < 8 {
                samples.push((bid.clone(), reason));
            }
        }
        eprintln!("\n=== ModelInvalid failure kinds ===");
        for (k, v) in &failure_counts {
            eprintln!("  {v:4} {k}");
        }
        for (bid, reason) in &samples {
            let seg = seg_by_id[bid];
            eprintln!("\n{bid}: {reason:?}");
            eprintln!("  ops: {}", format_ops(&seg.ops));
        }
    }

    #[test]
    fn diagnose_mux1_1_problem_blocks() {
        use crate::optimize::statistics::block_id;
        use crate::wasm::{parse_wasm_file, split_segments};

        let path = std::path::Path::new("benchmarks/wsouper/mux1_1.wasm");
        if !path.exists() {
            eprintln!("skip diagnose_mux1_1_problem_blocks: {path:?} missing");
            return;
        }
        let info = parse_wasm_file(path).expect("parse mux1_1");
        let segments = split_segments(&info.segments, 12);
        let cfg = SearchConfig {
            fixed_segment_timeout: Some(10),
            backend: super::super::Backend::Sat,
            ..SearchConfig::default()
        };

        let targets = [
            "function_117_block_13",      // ew optimal 7, ss 3
            "function_24_block_0_3",      // ew instant no_solution, ss 9
            "function_117_block_16_2",    // ew no_solution, ss 4
            "function_14_block_0_52",     // ew no_solution, ss 6
        ];

        for target in targets {
            let seg = segments
                .iter()
                .find(|s| block_id(s) == target)
                .unwrap_or_else(|| panic!("segment {target} not found"));
            let diag = diagnose_sat(seg, &rules(), &cfg);
            let result = solve_sat(seg, &rules(), &cfg);
            let opt_len = result.ops.as_ref().map(|o| o.len());
            eprintln!(
                "\n{target}: orig={} opaque={} diag={diag:?} solve_opt={opt_len:?} timed_out={}",
                seg.original_len(),
                seg.opaque_meta.len(),
                result.timed_out
            );
            eprintln!("  ops: {}", format_ops(&seg.ops));
        }
    }
}
