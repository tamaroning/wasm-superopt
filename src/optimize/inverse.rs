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

        for (kind, e1, e2) in canon.binop_decompositions(&top) {
            let sem = inst_kind_to_sem(kind);
            let mut next = state.clone();
            next.goal.stack.pop();
            next.goal.stack.push(e1);
            next.goal.stack.push(e2);
            if next.goal.stack.len() <= bounds.max_stack {
                out.push((PeelAction::Forward(sem), next));
            }
        }

        if let Some((sem, a, b)) = structural_binop_peel(&top) {
            let mut next = state.clone();
            next.goal.stack.pop();
            next.goal.stack.push(a);
            next.goal.stack.push(b);
            if next.goal.stack.len() <= bounds.max_stack {
                out.push((PeelAction::Forward(sem), next));
            }
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

fn structural_binop_peel(top: &crate::sym::ValueExpr) -> Option<(SemOp, crate::sym::ValueExpr, crate::sym::ValueExpr)> {
    let root = top.root();
    match &top[root] {
        ValueLang::I32Sub([a, b]) => Some((
            SemOp::I32Sub,
            subtree_expr(top, *a),
            subtree_expr(top, *b),
        )),
        ValueLang::I32Eq([a, b]) => Some((
            SemOp::I32Eq,
            subtree_expr(top, *a),
            subtree_expr(top, *b),
        )),
        ValueLang::I32Ne([a, b]) => Some((
            SemOp::I32Ne,
            subtree_expr(top, *a),
            subtree_expr(top, *b),
        )),
        ValueLang::I32LtS([a, b]) => Some((
            SemOp::I32LtS,
            subtree_expr(top, *a),
            subtree_expr(top, *b),
        )),
        ValueLang::I32LeS([a, b]) => Some((
            SemOp::I32LeS,
            subtree_expr(top, *a),
            subtree_expr(top, *b),
        )),
        ValueLang::I32GtS([a, b]) => Some((
            SemOp::I32GtS,
            subtree_expr(top, *a),
            subtree_expr(top, *b),
        )),
        _ => None,
    }
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

/// Backward-compatible peel API for arithmetic-only segments/tests.
pub fn applicable_peels_arithmetic_only(
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::optimize::fixtures::{fin, init};
    use crate::synthesis::{
        TEST_SYNTHESIS_AST_SIZE, load_or_synthesize_rules, synthesized_to_rewrites,
    };
    use crate::value::parse_value_expr;
    use crate::wasm::SegmentBounds;

    fn canonizer() -> Canonizer {
        Canonizer::new(synthesized_to_rewrites(&load_or_synthesize_rules(
            TEST_SYNTHESIS_AST_SIZE,
            10,
            1,
        )))
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
