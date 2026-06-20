//! Centralized Wasm instruction semantics: stack types, specs, and stack simulation.
//!
//! Operand stack holds i32 values only. Locals and linear memory are implicit machine
//! state threaded through effectful instructions (mirroring Wasm, not the egg DAG token).

use crate::al::{
    NumType, STRAIGHT_LINE_EMBED, Sign, WasmBinOp, al_spec_for, derive_inst_spec,
    derive_rule_binop_spec, derive_rule_local_get_spec, derive_rule_local_set_spec,
    derive_rule_local_tee_spec, format_al_pretty, format_rule_binop_pretty,
    format_rule_local_pretty,
};
use std::fmt;

// ---------------------------------------------------------------------------
// Stack types (Wasm operand stack)
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum StackTy {
    I32,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SemOp {
    I32Const(i32),
    I32Add,
    I32Mul,
    I32DivU,
    I32DivS,
    I32Shl,
    LocalGet(u32),
    LocalSet(u32),
    LocalTee(u32),
}

impl SemOp {
    pub fn name(&self) -> &'static str {
        match self {
            SemOp::I32Const(_) => "i32.const",
            SemOp::I32Add => "i32.add",
            SemOp::I32Mul => "i32.mul",
            SemOp::I32DivU => "i32.div_u",
            SemOp::I32DivS => "i32.div_s",
            SemOp::I32Shl => "i32.shl",
            SemOp::LocalGet(x) => local_op_name("local.get", *x),
            SemOp::LocalSet(x) => local_op_name("local.set", *x),
            SemOp::LocalTee(x) => local_op_name("local.tee", *x),
        }
    }

    /// Whether this op reads or writes implicit machine state (not representable in the egg DAG).
    pub fn is_effectful(&self) -> bool {
        matches!(
            self,
            SemOp::LocalGet(_) | SemOp::LocalSet(_) | SemOp::LocalTee(_)
        )
    }
}

impl fmt::Display for SemOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SemOp::I32Const(n) => write!(f, "i32.const {n}"),
            SemOp::I32Add => write!(f, "i32.add"),
            SemOp::I32Mul => write!(f, "i32.mul"),
            SemOp::I32DivU => write!(f, "i32.div_u"),
            SemOp::I32DivS => write!(f, "i32.div_s"),
            SemOp::I32Shl => write!(f, "i32.shl"),
            SemOp::LocalGet(x) => write!(f, "local.get {x}"),
            SemOp::LocalSet(x) => write!(f, "local.set {x}"),
            SemOp::LocalTee(x) => write!(f, "local.tee {x}"),
        }
    }
}

fn local_op_name(kind: &'static str, x: u32) -> &'static str {
    match (kind, x) {
        ("local.get", 0) => "local.get 0",
        ("local.get", 1) => "local.get 1",
        ("local.get", 2) => "local.get 2",
        ("local.set", 0) => "local.set 0",
        ("local.set", 1) => "local.set 1",
        ("local.set", 2) => "local.set 2",
        ("local.tee", 0) => "local.tee 0",
        ("local.tee", 1) => "local.tee 1",
        ("local.tee", 2) => "local.tee 2",
        _ => panic!("local op name only defined for indices 0..2"),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum InstKind {
    I32Const,
    I32Add,
    I32Mul,
    I32DivU,
    I32DivS,
    I32Shl,
    LocalGet(u32),
    LocalSet(u32),
    LocalTee(u32),
}

impl InstKind {
    pub fn from_sem_op(op: &SemOp) -> Self {
        match op {
            SemOp::I32Const(_) => InstKind::I32Const,
            SemOp::I32Add => InstKind::I32Add,
            SemOp::I32Mul => InstKind::I32Mul,
            SemOp::I32DivU => InstKind::I32DivU,
            SemOp::I32DivS => InstKind::I32DivS,
            SemOp::I32Shl => InstKind::I32Shl,
            SemOp::LocalGet(x) => InstKind::LocalGet(*x),
            SemOp::LocalSet(x) => InstKind::LocalSet(*x),
            SemOp::LocalTee(x) => InstKind::LocalTee(*x),
        }
    }

    pub fn is_i32_binop(self) -> bool {
        matches!(
            self,
            InstKind::I32Add
                | InstKind::I32Mul
                | InstKind::I32DivU
                | InstKind::I32DivS
                | InstKind::I32Shl
        )
    }

    pub fn is_local(self) -> bool {
        matches!(
            self,
            InstKind::LocalGet(_) | InstKind::LocalSet(_) | InstKind::LocalTee(_)
        )
    }

    pub fn name(self) -> &'static str {
        match self {
            InstKind::I32Const => "i32.const",
            InstKind::I32Add => "i32.add",
            InstKind::I32Mul => "i32.mul",
            InstKind::I32DivU => "i32.div_u",
            InstKind::I32DivS => "i32.div_s",
            InstKind::I32Shl => "i32.shl",
            InstKind::LocalGet(0) => "local.get 0",
            InstKind::LocalGet(1) => "local.get 1",
            InstKind::LocalGet(2) => "local.get 2",
            InstKind::LocalSet(0) => "local.set 0",
            InstKind::LocalSet(1) => "local.set 1",
            InstKind::LocalSet(2) => "local.set 2",
            InstKind::LocalTee(0) => "local.tee 0",
            InstKind::LocalTee(1) => "local.tee 1",
            InstKind::LocalTee(2) => "local.tee 2",
            InstKind::LocalGet(_) | InstKind::LocalSet(_) | InstKind::LocalTee(_) => {
                panic!("InstKind::name only defined for local slots 0..2")
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct InstSpec {
    pub kind: InstKind,
    pub pops: &'static [StackTy],
    pub pushes: &'static [StackTy],
    /// Whether this instruction may trap (trap kind is not distinguished).
    pub can_trap: bool,
}

impl InstSpec {
    pub fn kind_name(&self) -> &'static str {
        self.kind.name()
    }
}

/// Stack effect of a pure DAG-representable op.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DagStackStep {
    /// `i32.const` — immediate carried here (pop 0).
    PushConst(i32),
    /// Any other op: popped operands in stack order (bottom-first), then one push.
    Push { kind: InstKind, args: Vec<egg::Id> },
}

/// Apply `InstSpec` stack effect; `I32Const` reads its immediate from `op`.
pub fn dag_stack_step(
    op: &SemOp,
    spec: &InstSpec,
    stack: &mut Vec<egg::Id>,
) -> Option<DagStackStep> {
    if stack.len() < spec.pops.len() {
        return None;
    }
    if spec.pushes.len() != 1 {
        return None;
    }
    match spec.kind {
        InstKind::I32Const => {
            let SemOp::I32Const(n) = op else {
                return None;
            };
            Some(DagStackStep::PushConst(*n))
        }
        InstKind::LocalGet(_) | InstKind::LocalSet(_) | InstKind::LocalTee(_) => None,
        kind => {
            let mut args = Vec::with_capacity(spec.pops.len());
            for _ in 0..spec.pops.len() {
                args.push(stack.pop()?);
            }
            args.reverse();
            Some(DagStackStep::Push { kind, args })
        }
    }
}

pub fn value_lang_from_kind(kind: InstKind, args: &[egg::Id]) -> crate::lang::ValueLang {
    use crate::lang::ValueLang;
    match (kind, args) {
        (InstKind::I32Add, [a, b]) => ValueLang::I32Add([*a, *b]),
        (InstKind::I32Mul, [a, b]) => ValueLang::I32Mul([*a, *b]),
        (InstKind::I32Shl, [a, b]) => ValueLang::I32Shl([*a, *b]),
        (InstKind::I32DivU, [a, b]) => ValueLang::I32DivU([*a, *b]),
        (InstKind::I32DivS, [a, b]) => ValueLang::I32DivS([*a, *b]),
        _ => panic!("unsupported value DAG op {kind:?} arity {}", args.len()),
    }
}

pub fn wasm_lang_from_kind(kind: InstKind, args: &[egg::Id]) -> crate::lang::WasmLang {
    use crate::lang::WasmLang;
    match (kind, args) {
        (InstKind::I32Add, [a, b]) => WasmLang::I32Add([*a, *b]),
        (InstKind::I32Mul, [a, b]) => WasmLang::I32Mul([*a, *b]),
        (InstKind::I32Shl, [a, b]) => WasmLang::I32Shl([*a, *b]),
        (InstKind::I32DivU, [a, b]) => WasmLang::I32DivU([*a, *b]),
        (InstKind::I32DivS, [a, b]) => WasmLang::I32DivS([*a, *b]),
        _ => panic!("unsupported wasm DAG op {kind:?} arity {}", args.len()),
    }
}

pub fn spec_for(op: &SemOp) -> InstSpec {
    match op {
        SemOp::I32Add => derive_rule_binop_spec(InstKind::I32Add),
        SemOp::I32Mul => derive_rule_binop_spec(InstKind::I32Mul),
        SemOp::I32Shl => derive_rule_binop_spec(InstKind::I32Shl),
        SemOp::I32DivU => derive_rule_binop_spec(InstKind::I32DivU),
        SemOp::I32DivS => derive_rule_binop_spec(InstKind::I32DivS),
        SemOp::LocalGet(x) => derive_rule_local_get_spec(*x),
        SemOp::LocalSet(x) => derive_rule_local_set_spec(*x),
        SemOp::LocalTee(x) => derive_rule_local_tee_spec(*x),
        _ => {
            let al = al_spec_for(op);
            derive_inst_spec(&al, &STRAIGHT_LINE_EMBED)
        }
    }
}

fn binop_wasm(op: &SemOp) -> Option<(NumType, WasmBinOp)> {
    match op {
        SemOp::I32Add => Some((NumType::I32, WasmBinOp::Add)),
        SemOp::I32Mul => Some((NumType::I32, WasmBinOp::Mul)),
        SemOp::I32Shl => Some((NumType::I32, WasmBinOp::Shl)),
        SemOp::I32DivU => Some((NumType::I32, WasmBinOp::Div(Sign::U))),
        SemOp::I32DivS => Some((NumType::I32, WasmBinOp::Div(Sign::S))),
        _ => None,
    }
}

pub fn concrete_ops() -> Vec<SemOp> {
    let mut ops = vec![
        SemOp::I32Add,
        SemOp::I32Mul,
        SemOp::I32DivU,
        SemOp::I32DivS,
        SemOp::I32Shl,
    ];
    for c in [0, 1, 2, 3, 4, 8, 16, -1, i32::MIN, i32::MAX] {
        ops.push(SemOp::I32Const(c));
    }
    for x in 0..3 {
        ops.push(SemOp::LocalGet(x));
        ops.push(SemOp::LocalSet(x));
        ops.push(SemOp::LocalTee(x));
    }
    ops
}

/// Pure arithmetic ops for value-level rule synthesis (no locals).
pub fn pure_arithmetic_ops() -> Vec<SemOp> {
    concrete_ops()
        .into_iter()
        .filter(|op| !op.is_effectful())
        .collect()
}

/// Reduced constant pool for exhaustive rule synthesis.
const SYNTHESIS_CONSTS: [i32; 6] = [0, 1, 2, -1, i32::MIN, i32::MAX];

pub fn synthesis_constants() -> &'static [i32] {
    &SYNTHESIS_CONSTS
}

/// Arithmetic ops used during rule synthesis (smaller constant pool than `concrete_ops`).
pub fn synthesis_arithmetic_ops() -> Vec<SemOp> {
    let mut ops = vec![
        SemOp::I32Add,
        SemOp::I32Mul,
        SemOp::I32DivU,
        SemOp::I32DivS,
        SemOp::I32Shl,
    ];
    for c in SYNTHESIS_CONSTS {
        ops.push(SemOp::I32Const(c));
    }
    ops
}

/// Both sequences must be type-valid on `input` and leave the same operand-stack shape.
pub fn same_stack_effect(input: &[StackTy], lhs: &[SemOp], rhs: &[SemOp]) -> bool {
    match (
        simulate_stack_effect(input, lhs),
        simulate_stack_effect(input, rhs),
    ) {
        (Some(a), Some(b)) => a == b,
        _ => false,
    }
}

/// Whether `ops` is type-valid when executed on `input` (no stack underflow).
pub fn is_type_valid(input: &[StackTy], ops: &[SemOp]) -> bool {
    simulate_stack_effect(input, ops).is_some()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum StackSlotOrigin {
    Initial,
    Computed,
}

/// How many operand-stack slots from the initial input this sequence actually pops.
pub fn initial_inputs_consumed(input: &[StackTy], ops: &[SemOp]) -> Option<usize> {
    let mut stack = vec![StackSlotOrigin::Initial; input.len()];
    let mut consumed = 0usize;
    for op in ops {
        let spec = spec_for(op);
        if spec.pops.len() > stack.len() {
            return None;
        }
        for _ in 0..spec.pops.len() {
            match stack.pop()? {
                StackSlotOrigin::Initial => consumed += 1,
                StackSlotOrigin::Computed => {}
            }
        }
        stack.extend(std::iter::repeat_n(
            StackSlotOrigin::Computed,
            spec.pushes.len(),
        ));
    }
    Some(consumed)
}

/// Sequence uses every symbolic input slot (no pass-through leftovers).
pub fn uses_all_input_slots(input: &[StackTy], ops: &[SemOp]) -> bool {
    initial_inputs_consumed(input, ops) == Some(input.len())
}

pub fn simulate_stack_effect(input: &[StackTy], ops: &[SemOp]) -> Option<Vec<StackTy>> {
    let mut stack = input.to_vec();
    for op in ops {
        if !apply_op_to_stack(&mut stack, op) {
            return None;
        }
    }
    Some(stack)
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct StackSig {
    pub stack: Vec<StackTy>,
}

/// Static operand-stack effect `(pop_n, push_n)` for indexing applicable ops.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct StackOpSig {
    pub pop_n: usize,
    pub push_n: usize,
}

impl StackOpSig {
    pub fn for_op(op: &SemOp) -> Self {
        let spec = spec_for(op);
        Self {
            pop_n: spec.pops.len(),
            push_n: spec.pushes.len(),
        }
    }
}

/// Concrete ops indexed by pop count for stack-height–aware enumeration.
pub struct OpCatalog {
    by_pop: Vec<Vec<SemOp>>,
    max_pop: usize,
}

impl OpCatalog {
    pub fn from_ops(ops: &[SemOp]) -> Self {
        let max_pop = ops
            .iter()
            .map(|op| StackOpSig::for_op(op).pop_n)
            .max()
            .unwrap_or(0);
        let mut by_pop = vec![Vec::new(); max_pop + 1];
        for op in ops {
            by_pop[StackOpSig::for_op(op).pop_n].push(op.clone());
        }
        Self { by_pop, max_pop }
    }

    /// Ops applicable when the operand stack has `height` slots (all `I32`).
    pub fn applicable(&self, stack_height: usize) -> impl Iterator<Item = &SemOp> {
        let limit = stack_height.min(self.max_pop);
        (0..=limit).flat_map(move |pop_n| self.by_pop[pop_n].iter())
    }
}

fn apply_op_to_stack(stack: &mut Vec<StackTy>, op: &SemOp) -> bool {
    let spec = spec_for(op);
    if spec.pops.len() > stack.len() {
        return false;
    }
    for _ in 0..spec.pops.len() {
        stack.pop();
    }
    stack.extend_from_slice(spec.pushes);
    true
}

pub fn enumerate_sequences_by_output(
    input: &[StackTy],
    catalog: &OpCatalog,
    max_len: usize,
) -> std::collections::HashMap<StackSig, Vec<Vec<SemOp>>> {
    use std::collections::HashMap;

    let mut by_output: HashMap<StackSig, Vec<Vec<SemOp>>> = HashMap::new();
    let mut work = vec![(input.to_vec(), Vec::new())];

    while let Some((stack, seq)) = work.pop() {
        let is_candidate =
            is_type_valid(input, &seq) && (seq.is_empty() || uses_all_input_slots(input, &seq));
        if is_candidate {
            by_output
                .entry(StackSig {
                    stack: stack.clone(),
                })
                .or_default()
                .push(seq.clone());
        }
        if seq.len() >= max_len {
            continue;
        }
        for op in catalog.applicable(stack.len()) {
            let mut next_stack = stack.clone();
            if !apply_op_to_stack(&mut next_stack, op) {
                continue;
            }
            let mut next_seq = seq.clone();
            next_seq.push(op.clone());
            work.push((next_stack, next_seq));
        }
    }

    by_output
}

pub fn exploration_inputs() -> Vec<Vec<StackTy>> {
    let mut inputs = vec![vec![]];
    for h in 1..=3 {
        inputs.push(vec![StackTy::I32; h]);
    }
    inputs
}

/// Input stacks for rule synthesis (symbolic inputs only; no constant-only stack).
pub fn synthesis_inputs() -> Vec<Vec<StackTy>> {
    (1..=3).map(|h| vec![StackTy::I32; h]).collect()
}

/// Human-readable summary of instruction semantics (for `--print-semantics`).
pub fn print_semantics_table() {
    println!("=== Wasm instruction semantics ===\n");
    for op in concrete_ops() {
        let spec = spec_for(&op);
        let trap = if spec.can_trap { "yes" } else { "no" };
        println!(
            "{}  pop={} push={} trap={}",
            op.name(),
            spec.pops.len(),
            spec.pushes.len(),
            trap,
        );
        for line in match binop_wasm(&op) {
            Some((nt, binop)) => format_rule_binop_pretty(nt, binop),
            None if op.is_effectful() => format_rule_local_pretty(&op),
            None => format_al_pretty(&al_spec_for(&op)),
        }
        .lines()
        {
            println!("  {line}");
        }
        println!();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::al::{ConcreteState, LOCAL_SLOTS, MEM_SLOTS, exec_sequence_concrete};

    #[test]
    fn synthesis_arithmetic_ops_has_minimal_constant_pool() {
        assert_eq!(synthesis_arithmetic_ops().len(), 11);
    }

    #[test]
    fn synthesis_inputs_has_no_empty_stack() {
        assert!(synthesis_inputs().iter().all(|input| !input.is_empty()));
    }

    #[test]
    fn enumerated_sequences_are_type_valid() {
        let input = vec![StackTy::I32];
        let catalog = OpCatalog::from_ops(&concrete_ops());
        let by_output = enumerate_sequences_by_output(&input, &catalog, 2);
        let state = ConcreteState::new([0; LOCAL_SLOTS], [0; MEM_SLOTS]);
        for (sig, seqs) in &by_output {
            for seq in seqs {
                assert!(is_type_valid(&input, seq), "invalid: {seq:?}");
                assert_eq!(
                    simulate_stack_effect(&input, seq).as_ref(),
                    Some(&sig.stack),
                    "seq={seq:?}"
                );
                if !seq.is_empty() {
                    exec_sequence_concrete(seq, vec![0], state.clone());
                }
            }
        }
    }

    #[test]
    fn enumerate_includes_empty_identity_sequence() {
        let input = vec![StackTy::I32];
        let catalog = OpCatalog::from_ops(&concrete_ops());
        let by_output = enumerate_sequences_by_output(&input, &catalog, 2);
        assert!(
            by_output
                .values()
                .any(|seqs| seqs.iter().any(|seq| seq.is_empty()))
        );
    }

    #[test]
    fn same_stack_effect_rejects_invalid_pairs() {
        let input = vec![StackTy::I32];
        let pushes = vec![SemOp::I32Const(0)];
        let underflow = vec![SemOp::I32Add];
        assert!(!same_stack_effect(&input, &pushes, &underflow));
        assert!(!same_stack_effect(&input, &underflow, &underflow));
    }

    #[test]
    fn uses_all_input_slots_filters_pass_through() {
        let input = vec![StackTy::I32, StackTy::I32];
        let seq = vec![SemOp::I32Const(1), SemOp::I32Mul];
        assert!(is_type_valid(&input, &seq));
        assert_eq!(initial_inputs_consumed(&input, &seq), Some(1));
        assert!(!uses_all_input_slots(&input, &seq));
    }
}
