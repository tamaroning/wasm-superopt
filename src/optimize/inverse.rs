//! Inverse peel rules (backward search steps).

use super::canon::Canonizer;
use crate::lang::ValueLang;
use crate::semantics::{InstKind, SemOp};
use crate::sym::{LocalReq, SymState, subtree_expr};
use crate::value::parse_value_expr;
use crate::wasm::{SegmentBounds, StraightSegment};
use std::collections::BTreeSet;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PeelAction {
    Forward(SemOp),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SearchState {
    pub goal: SymState,
    pub remaining_storage: BTreeSet<u32>,
    pub used_opaque: BTreeSet<u32>,
}

impl SearchState {
    pub fn initial(segment: &StraightSegment, fin: &SymState) -> Self {
        Self {
            goal: fin.clone(),
            remaining_storage: segment.storage_ids().collect(),
            used_opaque: BTreeSet::new(),
        }
    }

    pub fn is_complete(&self) -> bool {
        self.remaining_storage.is_empty()
    }
}

pub fn applicable_peels(
    state: &SearchState,
    segment: &StraightSegment,
    bounds: &SegmentBounds,
    canon: &mut Canonizer,
) -> Vec<(PeelAction, SearchState)> {
    if !state.goal.validate_bounds(bounds) {
        return vec![];
    }
    let mut out = Vec::new();
    let g = &state.goal;

    for (&slot, req) in &g.locals {
        if slot > bounds.max_local {
            continue;
        }
        if let LocalReq::Need(v) = req {
            let mut next = state.clone();
            next.goal.locals.insert(slot, LocalReq::DontCare);
            next.goal.stack.push(v.clone());
            if next.goal.stack.len() <= bounds.max_stack {
                out.push((PeelAction::Forward(SemOp::LocalSet(slot)), next));
            }
        }
    }

    if let Some(top) = g.top() {
        for (&slot, req) in &g.locals {
            if slot > bounds.max_local {
                continue;
            }
            if let LocalReq::Need(v) = req {
                if canon.values_equivalent(top, v) {
                    let mut next = state.clone();
                    next.goal.locals.insert(slot, LocalReq::DontCare);
                    out.push((PeelAction::Forward(SemOp::LocalTee(slot)), next));
                }
            }
        }
    }

    if let Some(top) = g.top().cloned() {
        if let ValueLang::I32Const(c) = &top[top.root()] {
            let mut next = state.clone();
            next.goal.stack.pop();
            out.push((PeelAction::Forward(SemOp::I32Const(*c)), next));
        }

        if let Some((sem, a, b)) = structural_binop_peel(&top) {
            push_binop_peel(&mut out, state, sem, a, b, bounds);
        }

        let mut decomps = canon.binop_decompositions(&top);
        if let Some((sem, _, _)) = structural_binop_peel(&top) {
            let root_kind = sem_to_inst_kind(sem);
            decomps.sort_by_key(|(k, _, _)| decomp_priority(root_kind, *k));
        }
        for (kind, e1, e2) in decomps {
            push_binop_peel(
                &mut out,
                state,
                inst_kind_to_sem(kind),
                e1,
                e2,
                bounds,
            );
        }

        if let Some((sem, a)) = structural_unop_peel(&top) {
            push_unop_peel(&mut out, state, sem, a, bounds);
        }

        if !g.stack.is_empty() {
            let v = top;
            for slot in 0..=bounds.max_local {
                let mut next = state.clone();
                next.goal.stack.pop();
                match next.goal.locals.get(&slot) {
                    Some(LocalReq::Need(existing)) if canon.values_equivalent(existing, &v) => {}
                    Some(LocalReq::DontCare) | None => {
                        next.goal.locals.insert(slot, LocalReq::Need(v.clone()));
                    }
                    Some(LocalReq::Need(_)) => continue,
                }
                out.push((PeelAction::Forward(SemOp::LocalGet(slot)), next));
            }
        }
    }

    for meta in &segment.opaque_meta {
        if state.used_opaque.contains(&meta.id) {
            continue;
        }
        let Some(op) = find_op_by_id(segment, meta.id) else {
            continue;
        };

        if meta.storage {
            if !state.remaining_storage.contains(&meta.id) {
                continue;
            }
            if can_peel_storage(state, meta, canon) {
                if let Some(next) = peel_storage_op(state, op, meta) {
                    if next.goal.validate_bounds(bounds) {
                        out.push((PeelAction::Forward(op.clone()), next));
                    }
                }
            }
        } else if can_peel_result_op(state, meta, canon) {
            if let Some(next) = peel_result_op(state, op, meta) {
                if next.goal.validate_bounds(bounds) {
                    out.push((PeelAction::Forward(op.clone()), next));
                }
            }
        }
    }

    out
}

fn find_op_by_id(segment: &StraightSegment, id: u32) -> Option<&SemOp> {
    segment.ops.iter().find(|op| op.opaque_id() == Some(id))
}

fn symbol_at_stack(g: &SymState, idx_from_top: usize, sym: &str, canon: &mut Canonizer) -> bool {
    let expr = parse_value_expr(sym);
    let Some(idx) = g.stack.len().checked_sub(1 + idx_from_top) else {
        return false;
    };
    g.stack
        .get(idx)
        .is_some_and(|e| canon.values_equivalent(e, &expr))
}

fn can_peel_result_op(state: &SearchState, meta: &crate::wasm::OpaqueMeta, canon: &mut Canonizer) -> bool {
    if meta.result_symbols.is_empty() {
        return false;
    }
    for (i, sym) in meta.result_symbols.iter().enumerate().rev() {
        if !symbol_at_stack(&state.goal, i, sym, canon) {
            return false;
        }
    }
    true
}

fn can_peel_storage(state: &SearchState, meta: &crate::wasm::OpaqueMeta, canon: &mut Canonizer) -> bool {
    if meta.result_symbols.is_empty() {
        return true;
    }
    can_peel_result_op(state, meta, canon)
}

fn peel_result_op(
    state: &SearchState,
    _op: &SemOp,
    meta: &crate::wasm::OpaqueMeta,
) -> Option<SearchState> {
    let mut next = state.clone();
    for _ in 0..meta.result_symbols.len() {
        next.goal.stack.pop()?;
    }
    push_inputs(&mut next.goal, meta)?;
    next.used_opaque.insert(meta.id);
    Some(next)
}

fn peel_storage_op(
    state: &SearchState,
    op: &SemOp,
    meta: &crate::wasm::OpaqueMeta,
) -> Option<SearchState> {
    let mut next = state.clone();
    if !meta.result_symbols.is_empty() {
        for _ in 0..meta.result_symbols.len() {
            next.goal.stack.pop()?;
        }
    }
    push_inputs(&mut next.goal, meta)?;
    next.used_opaque.insert(meta.id);
    next.remaining_storage.remove(&meta.id);
    let _ = op;
    Some(next)
}

fn push_inputs(g: &mut SymState, meta: &crate::wasm::OpaqueMeta) -> Option<()> {
    // Forward opaque ops pop inputs top-first; backward pushes bottom-first.
    for sym in meta.input_symbols.iter().rev() {
        g.stack.push(parse_value_expr(sym));
    }
    Some(())
}

fn push_binop_peel(
    out: &mut Vec<(PeelAction, SearchState)>,
    state: &SearchState,
    sem: SemOp,
    e1: crate::sym::ValueExpr,
    e2: crate::sym::ValueExpr,
    bounds: &SegmentBounds,
) {
    let mut next = state.clone();
    next.goal.stack.pop();
    next.goal.stack.push(e1);
    next.goal.stack.push(e2);
    if next.goal.stack.len() > bounds.max_stack {
        return;
    }
    if out.iter().any(|(PeelAction::Forward(existing), s)| existing == &sem && s == &next) {
        return;
    }
    out.push((PeelAction::Forward(sem), next));
}

fn push_unop_peel(
    out: &mut Vec<(PeelAction, SearchState)>,
    state: &SearchState,
    sem: SemOp,
    a: crate::sym::ValueExpr,
    bounds: &SegmentBounds,
) {
    let mut next = state.clone();
    next.goal.stack.pop();
    next.goal.stack.push(a);
    if next.goal.stack.len() > bounds.max_stack {
        return;
    }
    if out.iter().any(|(PeelAction::Forward(existing), s)| existing == &sem && s == &next) {
        return;
    }
    out.push((PeelAction::Forward(sem), next));
}

/// Peel the stack-top binop as its syntactic form.
///
/// Arithmetic ops also appear in [`Canonizer::binop_decompositions`]; dedup happens in
/// [`push_binop_peel`].
fn structural_binop_peel(top: &crate::sym::ValueExpr) -> Option<(SemOp, crate::sym::ValueExpr, crate::sym::ValueExpr)> {
    let root = top.root();
    let (a, b) = match &top[root] {
        ValueLang::I32Add([a, b])
        | ValueLang::I32Sub([a, b])
        | ValueLang::I32Mul([a, b])
        | ValueLang::I32DivU([a, b])
        | ValueLang::I32DivS([a, b])
        | ValueLang::I32RemU([a, b])
        | ValueLang::I32RemS([a, b])
        | ValueLang::I32Shl([a, b])
        | ValueLang::I32And([a, b])
        | ValueLang::I32Or([a, b])
        | ValueLang::I32Xor([a, b])
        | ValueLang::I32ShrU([a, b])
        | ValueLang::I32ShrS([a, b])
        | ValueLang::I32Rotl([a, b])
        | ValueLang::I32Rotr([a, b])
        | ValueLang::I32Eq([a, b])
        | ValueLang::I32Ne([a, b])
        | ValueLang::I32LtS([a, b])
        | ValueLang::I32LeS([a, b])
        | ValueLang::I32GtS([a, b]) => (*a, *b),
        _ => return None,
    };
    let sem = match &top[root] {
        ValueLang::I32Add(_) => SemOp::I32Add,
        ValueLang::I32Sub(_) => SemOp::I32Sub,
        ValueLang::I32Mul(_) => SemOp::I32Mul,
        ValueLang::I32DivU(_) => SemOp::I32DivU,
        ValueLang::I32DivS(_) => SemOp::I32DivS,
        ValueLang::I32RemU(_) => SemOp::I32RemU,
        ValueLang::I32RemS(_) => SemOp::I32RemS,
        ValueLang::I32Shl(_) => SemOp::I32Shl,
        ValueLang::I32And(_) => SemOp::I32And,
        ValueLang::I32Or(_) => SemOp::I32Or,
        ValueLang::I32Xor(_) => SemOp::I32Xor,
        ValueLang::I32ShrU(_) => SemOp::I32ShrU,
        ValueLang::I32ShrS(_) => SemOp::I32ShrS,
        ValueLang::I32Rotl(_) => SemOp::I32Rotl,
        ValueLang::I32Rotr(_) => SemOp::I32Rotr,
        ValueLang::I32Eq(_) => SemOp::I32Eq,
        ValueLang::I32Ne(_) => SemOp::I32Ne,
        ValueLang::I32LtS(_) => SemOp::I32LtS,
        ValueLang::I32LeS(_) => SemOp::I32LeS,
        ValueLang::I32GtS(_) => SemOp::I32GtS,
        _ => unreachable!(),
    };
    Some((sem, subtree_expr(top, a), subtree_expr(top, b)))
}

/// Peel the stack-top unop as its syntactic form.
fn structural_unop_peel(top: &crate::sym::ValueExpr) -> Option<(SemOp, crate::sym::ValueExpr)> {
    let root = top.root();
    let (sem, child) = match &top[root] {
        ValueLang::I32Eqz([a]) => (SemOp::I32Eqz, *a),
        ValueLang::I32Clz([a]) => (SemOp::I32Clz, *a),
        ValueLang::I32Ctz([a]) => (SemOp::I32Ctz, *a),
        ValueLang::I32Popcnt([a]) => (SemOp::I32Popcnt, *a),
        _ => return None,
    };
    Some((sem, subtree_expr(top, child)))
}

fn sem_to_inst_kind(sem: SemOp) -> InstKind {
    match sem {
        SemOp::I32Add => InstKind::I32Add,
        SemOp::I32Sub => InstKind::I32Sub,
        SemOp::I32Mul => InstKind::I32Mul,
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
        other => panic!("not a peelable binop: {other:?}"),
    }
}

fn decomp_priority(root: InstKind, kind: InstKind) -> u8 {
    if rewrite_alternative(root, kind) {
        return 0;
    }
    if kind == root {
        // Syntactic peel is emitted separately; deprioritize same-kind e-class variants.
        return 1;
    }
    2
}

fn rewrite_alternative(root: InstKind, kind: InstKind) -> bool {
    matches!(
        (root, kind),
        (InstKind::I32Mul, InstKind::I32Shl)
            | (InstKind::I32Shl, InstKind::I32Mul)
    )
}

fn inst_kind_to_sem(kind: InstKind) -> SemOp {
    match kind {
        InstKind::I32Add => SemOp::I32Add,
        InstKind::I32Sub => SemOp::I32Sub,
        InstKind::I32Mul => SemOp::I32Mul,
        InstKind::I32Shl => SemOp::I32Shl,
        InstKind::I32DivU => SemOp::I32DivU,
        InstKind::I32DivS => SemOp::I32DivS,
        InstKind::I32RemU => SemOp::I32RemU,
        InstKind::I32RemS => SemOp::I32RemS,
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
        other => panic!("not a peelable binop: {other:?}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::optimize::fixtures::{fin, init};
    use crate::synthesis::{
        TEST_SYNTHESIS_AST_SIZE, load_or_synthesize_rules, synthesized_to_rewrites,
    };
    use crate::value::parse_value_expr;
    use crate::wasm::SegmentBounds;

    fn applicable_peels_arithmetic_only(
        g: &SymState,
        bounds: &SegmentBounds,
        canon: &mut Canonizer,
    ) -> Vec<(PeelAction, SymState)> {
        let state = SearchState {
            goal: g.clone(),
            remaining_storage: BTreeSet::new(),
            used_opaque: BTreeSet::new(),
        };
        let empty = StraightSegment {
            func_index: 0,
            segment_index: 0,
            split_part: None,
            ops: vec![],
            init: g.clone(),
            fin: g.clone(),
            bounds: *bounds,
            opaque_meta: vec![],
            dependencies: vec![],
        };
        applicable_peels(&state, &empty, bounds, canon)
            .into_iter()
            .map(|(a, s)| (a, s.goal))
            .collect()
    }

    fn canonizer() -> Canonizer {
        Canonizer::new(synthesized_to_rewrites(&load_or_synthesize_rules(
            TEST_SYNTHESIS_AST_SIZE,
            10,
            1,
        )))
    }

    #[test]
    fn structural_unop_peel_covers_all_value_lang_unops() {
        let cases = [
            ("(i32.eqz (i32.add ?L0 1))", SemOp::I32Eqz),
            ("(i32.clz (i32.add ?L0 1))", SemOp::I32Clz),
            ("(i32.ctz (i32.add ?L0 1))", SemOp::I32Ctz),
            ("(i32.popcnt (i32.add ?L0 1))", SemOp::I32Popcnt),
        ];
        for (expr, want) in cases {
            let top = parse_value_expr(expr);
            let got = structural_unop_peel(&top).map(|(s, _)| s);
            assert_eq!(got.as_ref(), Some(&want), "expr {expr}");
        }
    }

    #[test]
    fn binop_peel_dedup_keeps_distinct_ops_for_same_stack() {
        let mut canon = canonizer();
        let top = parse_value_expr("(i32.mul ?L0 2)");
        let state = SearchState {
            goal: SymState {
                stack: vec![top],
                locals: [(0, crate::sym::LocalReq::DontCare)].into_iter().collect(),
            },
            remaining_storage: Default::default(),
            used_opaque: Default::default(),
        };
        let empty = StraightSegment {
            func_index: 0,
            segment_index: 0,
            split_part: None,
            ops: vec![],
            init: state.goal.clone(),
            fin: state.goal.clone(),
            bounds: SegmentBounds::new(1, 4),
            opaque_meta: vec![],
            dependencies: vec![],
        };
        let peels = applicable_peels(&state, &empty, &SegmentBounds::new(1, 4), &mut canon);
        let binops: Vec<_> = peels
            .iter()
            .filter_map(|(a, s)| match a {
                PeelAction::Forward(op) if matches!(op, SemOp::I32Mul | SemOp::I32Shl | SemOp::I32Sub) => {
                    let stack: Vec<_> = s.goal.stack.iter().map(|e| e.to_string()).collect();
                    Some((op.clone(), stack))
                }
                _ => None,
            })
            .collect();
        assert!(
            binops.iter().any(|(op, st)| *op == SemOp::I32Mul && st == &["?L0", "2"]),
            "missing i32.mul peel: {binops:?}"
        );
        assert!(
            binops.iter().any(|(op, _)| *op == SemOp::I32Mul),
            "i32.mul must not be deduped into i32.sub: {binops:?}"
        );
    }

    #[test]
    fn structural_binop_peel_covers_all_value_lang_binops() {
        let cases = [
            ("(i32.add ?L0 1)", SemOp::I32Add),
            ("(i32.sub ?L0 1)", SemOp::I32Sub),
            ("(i32.mul ?L0 2)", SemOp::I32Mul),
            ("(i32.div_u ?L0 2)", SemOp::I32DivU),
            ("(i32.div_s ?L0 2)", SemOp::I32DivS),
            ("(i32.rem_u ?L0 2)", SemOp::I32RemU),
            ("(i32.rem_s ?L0 2)", SemOp::I32RemS),
            ("(i32.shl ?L0 1)", SemOp::I32Shl),
            ("(i32.and ?L0 1)", SemOp::I32And),
            ("(i32.or ?L0 1)", SemOp::I32Or),
            ("(i32.xor ?L0 1)", SemOp::I32Xor),
            ("(i32.shr_u ?L0 1)", SemOp::I32ShrU),
            ("(i32.shr_s ?L0 1)", SemOp::I32ShrS),
            ("(i32.rotl ?L0 1)", SemOp::I32Rotl),
            ("(i32.rotr ?L0 1)", SemOp::I32Rotr),
            ("(i32.eq ?L0 1)", SemOp::I32Eq),
            ("(i32.ne ?L0 1)", SemOp::I32Ne),
            ("(i32.lt_s ?L0 1)", SemOp::I32LtS),
            ("(i32.le_s ?L0 1)", SemOp::I32LeS),
            ("(i32.gt_s ?L0 1)", SemOp::I32GtS),
        ];
        for (expr, want) in cases {
            let top = parse_value_expr(expr);
            let got = structural_binop_peel(&top).map(|(s, _, _)| s);
            assert_eq!(got.as_ref(), Some(&want), "expr {expr}");
        }
    }

    #[test]
    fn memo_convergence_mul_vs_shl() {
        let mut canon = canonizer();
        let top = parse_value_expr("(i32.mul (i32.add ?L0 1) 2)");
        let l_plus_1 = parse_value_expr("(i32.add ?L0 1)");
        let mut locals = std::collections::BTreeMap::new();
        locals.insert(0, crate::sym::LocalReq::Need(l_plus_1));
        let g = SymState {
            stack: vec![top],
            locals,
        };
        let bounds = SegmentBounds::new(1, 4);
        let top_expr = g.stack.last().expect("top");
        let decomps = canon.binop_decompositions(top_expr);
        assert!(decomps.iter().any(|(k, _, _)| *k == InstKind::I32Mul));
        let (_, e1, e2) = decomps
            .iter()
            .find(|(k, _, _)| *k == InstKind::I32Mul)
            .unwrap();
        let mut after_mul = g.clone();
        after_mul.stack.pop();
        after_mul.stack.push(e1.clone());
        after_mul.stack.push(e2.clone());
        after_mul.stack.pop();
        let key_mul_stack: Vec<_> = after_mul.stack.iter().map(|e| canon.canon(e)).collect();
        let (_, e1s, e2s) = decomps
            .iter()
            .find(|(k, _, _)| *k == InstKind::I32Shl)
            .expect("shl decomposition");
        let mut after_shl = g.clone();
        after_shl.stack.pop();
        after_shl.stack.push(e1s.clone());
        after_shl.stack.push(e2s.clone());
        after_shl.stack.pop();
        let key_shl_stack: Vec<_> = after_shl.stack.iter().map(|e| canon.canon(e)).collect();
        assert_eq!(key_mul_stack, key_shl_stack);
        assert_eq!(key_mul_stack.len(), 1, "both paths require only L+1");
        let _ = bounds;
    }

    #[test]
    fn peel_sequence_reaches_init() {
        let mut canon = canonizer();
        let init = init();
        let mut g = fin();
        let bounds = SegmentBounds::new(1, 4);
        let manual: Vec<SemOp> = vec![
            SemOp::LocalTee(0),
            SemOp::I32Shl,
            SemOp::I32Const(1),
            SemOp::LocalGet(0),
            SemOp::I32Shl,
            SemOp::I32Const(3),
            SemOp::LocalGet(0),
        ];
        for op in manual {
            let peels = applicable_peels_arithmetic_only(&g, &bounds, &mut canon);
            let next = peels
                .into_iter()
                .find(|(a, _)| match (&a, &op) {
                    (PeelAction::Forward(SemOp::I32Const(a)), SemOp::I32Const(b)) => a == b,
                    (PeelAction::Forward(SemOp::LocalGet(a)), SemOp::LocalGet(b)) => a == b,
                    (PeelAction::Forward(SemOp::LocalSet(a)), SemOp::LocalSet(b)) => a == b,
                    (PeelAction::Forward(SemOp::LocalTee(a)), SemOp::LocalTee(b)) => a == b,
                    (PeelAction::Forward(SemOp::I32Mul), SemOp::I32Mul) => true,
                    (PeelAction::Forward(SemOp::I32Add), SemOp::I32Add) => true,
                    (PeelAction::Forward(SemOp::I32Shl), SemOp::I32Shl) => true,
                    _ => false,
                })
                .map(|(_, n)| n)
                .expect("peel step");
            g = next;
        }
        assert!(crate::optimize::search::is_grounded(
            &g,
            &init,
            &bounds,
            &mut canon
        ));
    }
}
