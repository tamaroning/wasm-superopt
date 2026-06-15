//! Centralized Wasm instruction semantics: stack types, Z3 encoding, trap conditions.
//!
//! Operand stack holds i32 values only. Locals and linear memory are implicit machine
//! state threaded through effectful instructions (mirroring Wasm, not the egg DAG token).

use z3::ast::{Array, Ast, BV, Bool};
use z3::{Config, Context, Sort};

// ---------------------------------------------------------------------------
// Stack types (Wasm operand stack)
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize)]
pub enum StackTy {
    I32,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SemOp {
    I32Const(i32),
    I32Add,
    I32Mul,
    I32DivU,
    I32DivS,
    I32Shl,
    LocalGet(u32),
    LocalSet(u32),
    I32Load,
    I32Store,
    Drop,
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
            SemOp::LocalGet(_) => "local.get",
            SemOp::LocalSet(_) => "local.set",
            SemOp::I32Load => "i32.load",
            SemOp::I32Store => "i32.store",
            SemOp::Drop => "drop",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TrapCond {
    /// `i32.div_u` / `i32.div_s`: divisor == 0.
    DivByZero,
    /// `i32.div_s` only: `INT_MIN / -1`.
    DivSOverflow,
}

impl TrapCond {
    pub fn describe(self) -> &'static str {
        match self {
            TrapCond::DivByZero => "divisor==0",
            TrapCond::DivSOverflow => "INT_MIN/-1",
        }
    }
}

#[derive(Clone, Debug)]
pub struct InstSpec {
    pub pops: &'static [StackTy],
    pub pushes: &'static [StackTy],
    /// Reads or writes implicit machine state (locals / memory).
    pub touches_state: bool,
    /// Wasm trap conditions for this instruction.
    pub traps: &'static [TrapCond],
}

pub fn spec_for(op: &SemOp) -> InstSpec {
    match op {
        SemOp::I32Const(_) => InstSpec {
            pops: &[],
            pushes: &[StackTy::I32],
            touches_state: false,
            traps: &[],
        },
        SemOp::I32Add | SemOp::I32Mul | SemOp::I32Shl => InstSpec {
            pops: &[StackTy::I32, StackTy::I32],
            pushes: &[StackTy::I32],
            touches_state: false,
            traps: &[],
        },
        SemOp::I32DivU => InstSpec {
            pops: &[StackTy::I32, StackTy::I32],
            pushes: &[StackTy::I32],
            touches_state: false,
            traps: &[TrapCond::DivByZero],
        },
        SemOp::I32DivS => InstSpec {
            pops: &[StackTy::I32, StackTy::I32],
            pushes: &[StackTy::I32],
            touches_state: false,
            traps: &[TrapCond::DivByZero, TrapCond::DivSOverflow],
        },
        SemOp::LocalGet(_) => InstSpec {
            pops: &[],
            pushes: &[StackTy::I32],
            touches_state: true,
            traps: &[],
        },
        SemOp::LocalSet(_) => InstSpec {
            pops: &[StackTy::I32],
            pushes: &[],
            touches_state: true,
            traps: &[],
        },
        SemOp::I32Load => InstSpec {
            pops: &[StackTy::I32],
            pushes: &[StackTy::I32],
            touches_state: true,
            traps: &[],
        },
        SemOp::I32Store => InstSpec {
            pops: &[StackTy::I32, StackTy::I32],
            pushes: &[],
            touches_state: true,
            traps: &[],
        },
        SemOp::Drop => InstSpec {
            pops: &[StackTy::I32],
            pushes: &[],
            touches_state: false,
            traps: &[],
        },
    }
}

/// Evaluate Wasm trap conditions from popped operands `[a, b]` (b = divisor for div).
pub fn trap_concrete(op: &SemOp, a: i32, b: i32) -> bool {
    for cond in spec_for(op).traps {
        if trap_concrete_cond(*cond, a, b) {
            return true;
        }
    }
    false
}

fn trap_concrete_cond(cond: TrapCond, a: i32, b: i32) -> bool {
    match cond {
        TrapCond::DivByZero => b == 0,
        TrapCond::DivSOverflow => b == -1 && a == i32::MIN,
    }
}

/// Encode trap conditions as a Z3 boolean from operands `[a, b]`.
pub fn trap_z3<'ctx>(ctx: &'ctx Context, op: &SemOp, a: &BV<'ctx>, b: &BV<'ctx>) -> Bool<'ctx> {
    let mut trap = Bool::from_bool(ctx, false);
    for cond in spec_for(op).traps {
        trap = Bool::or(ctx, &[&trap, &trap_z3_cond(ctx, *cond, a, b)]);
    }
    trap
}

fn trap_z3_cond<'ctx>(ctx: &'ctx Context, cond: TrapCond, a: &BV<'ctx>, b: &BV<'ctx>) -> Bool<'ctx> {
    match cond {
        TrapCond::DivByZero => b._eq(&BV::from_i64(ctx, 0, I32_BITS)),
        TrapCond::DivSOverflow => Bool::and(
            ctx,
            &[
                &b._eq(&BV::from_i64(ctx, -1, I32_BITS)),
                &a._eq(&BV::from_i64(ctx, i32::MIN as i64, I32_BITS)),
            ],
        ),
    }
}

pub fn concrete_ops() -> Vec<SemOp> {
    let mut ops = vec![
        SemOp::I32Add,
        SemOp::I32Mul,
        SemOp::I32DivU,
        SemOp::I32DivS,
        SemOp::I32Shl,
        SemOp::I32Load,
        SemOp::I32Store,
        SemOp::Drop,
    ];
    for c in [0, 1, 2, 3, 4, 8, 16, -1, i32::MIN, i32::MAX] {
        ops.push(SemOp::I32Const(c));
    }
    for i in 0..3 {
        ops.push(SemOp::LocalGet(i));
        ops.push(SemOp::LocalSet(i));
    }
    ops
}

// ---------------------------------------------------------------------------
// Concrete machine (fast randomized equivalence filter)
// ---------------------------------------------------------------------------

const I32_BITS: u32 = 32;
const LOCAL_SLOTS: u32 = 8;
const MEM_SLOTS: u32 = 16;
/// Default number of randomized concrete tests before invoking Z3.
pub const DEFAULT_RANDOM_TESTS: usize = 100;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConcreteState {
    pub locals: [i32; LOCAL_SLOTS as usize],
    pub memory: [i32; MEM_SLOTS as usize],
}

impl ConcreteState {
    pub fn new(locals: [i32; LOCAL_SLOTS as usize], memory: [i32; MEM_SLOTS as usize]) -> Self {
        Self { locals, memory }
    }

    fn store_local(&self, idx: u32, val: i32) -> Self {
        let mut next = self.clone();
        if (idx as usize) < next.locals.len() {
            next.locals[idx as usize] = val;
        }
        next
    }

    fn load_local(&self, idx: u32) -> i32 {
        self.locals.get(idx as usize).copied().unwrap_or(0)
    }

    fn store_mem(&self, addr: i32, val: i32) -> Self {
        let mut next = self.clone();
        let slot = addr.rem_euclid(MEM_SLOTS as i32) as usize;
        next.memory[slot] = val;
        next
    }

    fn load_mem(&self, addr: i32) -> i32 {
        let slot = addr.rem_euclid(MEM_SLOTS as i32) as usize;
        self.memory[slot]
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConcreteResult {
    pub stack: Vec<i32>,
    pub state: ConcreteState,
    pub trap: bool,
}

pub fn exec_op_concrete(op: &SemOp, stack: &mut Vec<i32>, state: &mut ConcreteState) -> bool {
    let mut trap = false;

    match op {
        SemOp::I32Const(n) => stack.push(*n),
        SemOp::I32Add => {
            let b = stack.pop().unwrap();
            let a = stack.pop().unwrap();
            stack.push(a.wrapping_add(b));
        }
        SemOp::I32Mul => {
            let b = stack.pop().unwrap();
            let a = stack.pop().unwrap();
            stack.push(a.wrapping_mul(b));
        }
        SemOp::I32DivU => {
            let b = stack.pop().unwrap();
            let a = stack.pop().unwrap();
            trap = trap_concrete(op, a, b);
            stack.push(if trap {
                0
            } else {
                (a as u32).wrapping_div(b as u32) as i32
            });
        }
        SemOp::I32DivS => {
            let b = stack.pop().unwrap();
            let a = stack.pop().unwrap();
            trap = trap_concrete(op, a, b);
            stack.push(if trap { 0 } else { a.wrapping_div(b) });
        }
        SemOp::I32Shl => {
            let b = stack.pop().unwrap();
            let a = stack.pop().unwrap();
            stack.push(a.wrapping_shl(b as u32 & 31));
        }
        SemOp::LocalGet(idx) => stack.push(state.load_local(*idx)),
        SemOp::LocalSet(idx) => {
            let val = stack.pop().unwrap();
            *state = state.store_local(*idx, val);
        }
        SemOp::I32Load => {
            let addr = stack.pop().unwrap();
            stack.push(state.load_mem(addr));
        }
        SemOp::I32Store => {
            let val = stack.pop().unwrap();
            let addr = stack.pop().unwrap();
            *state = state.store_mem(addr, val);
        }
        SemOp::Drop => {
            stack.pop().unwrap();
        }
    }

    trap
}

pub fn exec_sequence_concrete(
    ops: &[SemOp],
    stack: Vec<i32>,
    state: ConcreteState,
) -> ConcreteResult {
    let mut stack = stack;
    let mut state = state;
    let mut trap = false;
    for op in ops {
        if trap {
            break;
        }
        trap = exec_op_concrete(op, &mut stack, &mut state);
    }
    ConcreteResult { stack, state, trap }
}

struct Lcg(u64);

impl Lcg {
    fn new(seed: u64) -> Self {
        Self(seed)
    }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1);
        self.0
    }

    fn next_i32(&mut self) -> i32 {
        self.next_u64() as i32
    }
}

fn concrete_inputs_for_test(
    input: &[StackTy],
    rng: &mut Lcg,
    case: usize,
) -> (Vec<i32>, ConcreteState) {
    let stack_in = if input.is_empty() {
        vec![]
    } else {
        match case % 8 {
            0 => vec![0; input.len()],
            1 => vec![1; input.len()],
            2 => vec![-1; input.len()],
            3 => (0..input.len()).map(|i| i as i32).collect(),
            4 => vec![i32::MAX; input.len()],
            5 => vec![i32::MIN; input.len()],
            6 => (0..input.len())
                .map(|i| if i % 2 == 0 { 0 } else { 1 })
                .collect(),
            _ => (0..input.len()).map(|_| rng.next_i32()).collect(),
        }
    };

    let locals = std::array::from_fn(|i| match case % 6 {
        0 => 0,
        1 => 1,
        2 => -1,
        3 => i as i32,
        4 => i32::MAX,
        _ => rng.next_i32(),
    });
    let memory = std::array::from_fn(|i| match case % 5 {
        0 => 0,
        1 => 42,
        2 => i as i32,
        3 => -1,
        _ => rng.next_i32(),
    });

    (stack_in, ConcreteState::new(locals, memory))
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
        stack.extend(std::iter::repeat_n(StackSlotOrigin::Computed, spec.pushes.len()));
    }
    Some(consumed)
}

/// Sequence uses every symbolic input slot (no pass-through leftovers).
pub fn uses_all_input_slots(input: &[StackTy], ops: &[SemOp]) -> bool {
    initial_inputs_consumed(input, ops) == Some(input.len())
}

fn concrete_results_match(lhs: &ConcreteResult, rhs: &ConcreteResult) -> bool {
    if lhs.trap != rhs.trap {
        return false;
    }
    lhs.stack == rhs.stack && lhs.state == rhs.state
}

/// Fast filter: returns `false` if a concrete counterexample is found.
pub fn sequences_equivalent_random(
    input: &[StackTy],
    lhs: &[SemOp],
    rhs: &[SemOp],
    num_tests: usize,
) -> bool {
    if !is_type_valid(input, lhs) || !is_type_valid(input, rhs) {
        return false;
    }
    if !same_stack_effect(input, lhs, rhs) {
        return false;
    }
    if num_tests == 0 {
        return true;
    }

    let mut rng = Lcg::new(0xE6A3_9A1B_CDE2_4701);
    for case in 0..num_tests {
        let (stack_in, state_in) = concrete_inputs_for_test(input, &mut rng, case);
        let lhs_r = exec_sequence_concrete(lhs, stack_in.clone(), state_in.clone());
        let rhs_r = exec_sequence_concrete(rhs, stack_in, state_in);
        if !concrete_results_match(&lhs_r, &rhs_r) {
            return false;
        }
    }
    true
}

// ---------------------------------------------------------------------------
// Z3 machine state
// ---------------------------------------------------------------------------

pub struct Z3State<'ctx> {
    pub locals: Array<'ctx>,
    pub memory: Array<'ctx>,
}

impl<'ctx> Clone for Z3State<'ctx> {
    fn clone(&self) -> Self {
        Self {
            locals: self.locals.clone(),
            memory: self.memory.clone(),
        }
    }
}

impl<'ctx> Z3State<'ctx> {
    pub fn fresh(ctx: &'ctx Context, prefix: &str) -> Self {
        let i32_sort = Sort::bitvector(ctx, I32_BITS);
        let idx_sort = Sort::bitvector(ctx, I32_BITS);
        let locals = Array::fresh_const(ctx, &format!("{prefix}_locals"), &idx_sort, &i32_sort);
        let memory = Array::fresh_const(ctx, &format!("{prefix}_mem"), &idx_sort, &i32_sort);
        Self { locals, memory }
    }

    pub fn store_local(&self, ctx: &'ctx Context, idx: u32, val: &BV<'ctx>) -> Self {
        let idx_bv = BV::from_u64(ctx, idx as u64, I32_BITS);
        Self {
            locals: self.locals.store(&idx_bv, val),
            memory: self.memory.clone(),
        }
    }

    pub fn load_local(&self, ctx: &'ctx Context, idx: u32) -> BV<'ctx> {
        let idx_bv = BV::from_u64(ctx, idx as u64, I32_BITS);
        self.locals.select(&idx_bv).as_bv().unwrap()
    }

    pub fn store_mem(&self, addr: &BV<'ctx>, val: &BV<'ctx>) -> Self {
        Self {
            locals: self.locals.clone(),
            memory: self.memory.store(addr, val),
        }
    }

    pub     fn load_mem(&self, addr: &BV<'ctx>) -> BV<'ctx> {
        self.memory.select(addr).as_bv().unwrap()
    }
}

/// Locals / memory slots written during execution (reads affect the stack only).
#[derive(Default)]
pub struct StateTouches<'ctx> {
    pub local_writes: std::collections::HashSet<u32>,
    pub mem_writes: Vec<BV<'ctx>>,
}

pub struct ExecResult<'ctx> {
    pub stack: Vec<BV<'ctx>>,
    pub state: Z3State<'ctx>,
    pub trap: Bool<'ctx>,
    pub touches: StateTouches<'ctx>,
}

pub fn exec_op<'ctx>(
    ctx: &'ctx Context,
    op: &SemOp,
    stack: &mut Vec<BV<'ctx>>,
    state: &mut Z3State<'ctx>,
    touches: &mut StateTouches<'ctx>,
) -> Bool<'ctx> {
    let mut trap = Bool::from_bool(ctx, false);

    match op {
        SemOp::I32Const(n) => stack.push(BV::from_i64(ctx, *n as i64, I32_BITS)),
        SemOp::I32Add => {
            let b = stack.pop().unwrap();
            let a = stack.pop().unwrap();
            stack.push(a.bvadd(&b));
        }
        SemOp::I32Mul => {
            let b = stack.pop().unwrap();
            let a = stack.pop().unwrap();
            stack.push(a.bvmul(&b));
        }
        SemOp::I32DivU => {
            let b = stack.pop().unwrap();
            let a = stack.pop().unwrap();
            trap = trap_z3(ctx, op, &a, &b);
            let zero = BV::from_i64(ctx, 0, I32_BITS);
            let result = trap.ite(&zero, &a.bvudiv(&b));
            stack.push(result);
        }
        SemOp::I32DivS => {
            let b = stack.pop().unwrap();
            let a = stack.pop().unwrap();
            trap = trap_z3(ctx, op, &a, &b);
            let zero = BV::from_i64(ctx, 0, I32_BITS);
            let result = trap.ite(&zero, &a.bvsdiv(&b));
            stack.push(result);
        }
        SemOp::I32Shl => {
            let b = stack.pop().unwrap();
            let a = stack.pop().unwrap();
            let mask = BV::from_u64(ctx, 31, I32_BITS);
            stack.push(a.bvshl(&b.bvand(&mask)));
        }
        SemOp::LocalGet(idx) => stack.push(state.load_local(ctx, *idx)),
        SemOp::LocalSet(idx) => {
            let val = stack.pop().unwrap();
            touches.local_writes.insert(*idx);
            *state = state.store_local(ctx, *idx, &val);
        }
        SemOp::I32Load => {
            let addr = stack.pop().unwrap();
            stack.push(state.load_mem(&addr));
        }
        SemOp::I32Store => {
            let val = stack.pop().unwrap();
            let addr = stack.pop().unwrap();
            touches.mem_writes.push(addr.clone());
            *state = state.store_mem(&addr, &val);
        }
        SemOp::Drop => {
            stack.pop().unwrap();
        }
    }

    trap
}

pub fn exec_sequence<'ctx>(
    ctx: &'ctx Context,
    ops: &[SemOp],
    mut stack: Vec<BV<'ctx>>,
    mut state: Z3State<'ctx>,
) -> ExecResult<'ctx> {
    let mut trap = Bool::from_bool(ctx, false);
    let mut touches = StateTouches::default();
    for op in ops {
        let t = exec_op(ctx, op, &mut stack, &mut state, &mut touches);
        trap = Bool::or(ctx, &[&trap, &t]);
    }
    ExecResult {
        stack,
        state,
        trap,
        touches,
    }
}

fn state_diff_z3<'ctx>(
    ctx: &'ctx Context,
    lhs: &ExecResult<'ctx>,
    rhs: &ExecResult<'ctx>,
) -> Bool<'ctx> {
    let mut diff = Bool::from_bool(ctx, false);
    if lhs.stack.len() != rhs.stack.len() {
        return Bool::from_bool(ctx, true);
    }
    for (l, r) in lhs.stack.iter().zip(rhs.stack.iter()) {
        diff = Bool::or(ctx, &[&diff, &l._eq(r).not()]);
    }

    let mut local_writes = lhs.touches.local_writes.clone();
    local_writes.extend(&rhs.touches.local_writes);
    for idx in local_writes {
        let idx_bv = BV::from_u64(ctx, idx as u64, I32_BITS);
        diff = Bool::or(
            ctx,
            &[&diff, &lhs.state.locals.select(&idx_bv)._eq(&rhs.state.locals.select(&idx_bv)).not()],
        );
    }

    for addr in lhs
        .touches
        .mem_writes
        .iter()
        .chain(rhs.touches.mem_writes.iter())
    {
        diff = Bool::or(
            ctx,
            &[&diff, &lhs.state.memory.select(addr)._eq(&rhs.state.memory.select(addr)).not()],
        );
    }

    diff
}

/// Prove equivalence under all inputs and initial machine states.
/// Runs randomized concrete tests first, then Z3.
pub fn sequences_equivalent(
    ctx: &Context,
    input: &[StackTy],
    lhs: &[SemOp],
    rhs: &[SemOp],
    random_tests: usize,
) -> bool {
    if !same_stack_effect(input, lhs, rhs) || lhs == rhs {
        return false;
    }

    if !sequences_equivalent_random(input, lhs, rhs, random_tests) {
        return false;
    }

    sequences_equivalent_z3(ctx, input, lhs, rhs)
}

/// Z3 proof only (call after `sequences_equivalent_random` passes).
pub fn sequences_equivalent_z3(
    ctx: &Context,
    input: &[StackTy],
    lhs: &[SemOp],
    rhs: &[SemOp],
) -> bool {
    if !same_stack_effect(input, lhs, rhs) {
        return false;
    }
    let stack_in: Vec<BV<'_>> = (0..input.len())
        .map(|i| BV::new_const(ctx, format!("in_{i}"), I32_BITS))
        .collect();

    let init = Z3State::fresh(ctx, "init");
    let lhs_r = exec_sequence(ctx, lhs, stack_in.clone(), init.clone());
    let rhs_r = exec_sequence(ctx, rhs, stack_in, init);

    let solver = z3::Solver::new(ctx);

    let trap_mismatch = lhs_r.trap.xor(&rhs_r.trap);
    let diff = state_diff_z3(ctx, &lhs_r, &rhs_r);

    solver.assert(&Bool::or(ctx, &[&trap_mismatch, &diff]));
    matches!(solver.check(), z3::SatResult::Unsat)
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
        if !seq.is_empty() && is_type_valid(input, &seq) && uses_all_input_slots(input, &seq) {
            by_output
                .entry(StackSig { stack: stack.clone() })
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

pub fn enumerate_sequences(
    input: &[StackTy],
    ops: &[SemOp],
    max_len: usize,
) -> Vec<Vec<SemOp>> {
    let catalog = OpCatalog::from_ops(ops);
    enumerate_sequences_by_output(input, &catalog, max_len)
        .into_values()
        .flatten()
        .collect()
}

pub fn exploration_inputs() -> Vec<Vec<StackTy>> {
    let mut inputs = vec![vec![]];
    for h in 1..=3 {
        inputs.push(vec![StackTy::I32; h]);
    }
    inputs
}

pub fn z3_context() -> Context {
    let mut cfg = Config::new();
    cfg.set_timeout_msec(5_000);
    Context::new(&cfg)
}

/// Human-readable summary of instruction semantics (for `--print-semantics`).
pub fn print_semantics_table() {
    println!("=== Wasm instruction semantics ===");
    println!(
        "{:<12} {:<6} {:<6} {:<6} {:<20} {}",
        "opcode", "pop", "push", "state?", "trap (Z3)", "Z3 op"
    );
    for op in concrete_ops() {
        let spec = spec_for(&op);
        let trap = if spec.traps.is_empty() {
            "-".to_string()
        } else {
            spec.traps
                .iter()
                .map(|c| c.describe())
                .collect::<Vec<_>>()
                .join(" | ")
        };
        let z3_op = match &op {
            SemOp::I32Const(n) => format!("BV const {n}"),
            SemOp::I32Add => "bvadd".into(),
            SemOp::I32Mul => "bvmul".into(),
            SemOp::I32DivU => "ite(trap,a,bvudiv(a,b))".into(),
            SemOp::I32DivS => "ite(trap,a,bvsdiv(a,b))".into(),
            SemOp::I32Shl => "bvshl (amt&31)".into(),
            SemOp::LocalGet(i) => format!("select locals[{i}]"),
            SemOp::LocalSet(i) => format!("store locals[{i}]"),
            SemOp::I32Load => "select memory[addr]".into(),
            SemOp::I32Store => "store memory[addr]".into(),
            SemOp::Drop => "pop".into(),
        };
        println!(
            "{:<12} {:<6} {:<6} {:<6} {:<20} {}",
            op.name(),
            spec.pops.len(),
            spec.pushes.len(),
            if spec.touches_state { "yes" } else { "no" },
            trap,
            z3_op,
        );
    }
    println!();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enumerated_sequences_are_type_valid() {
        let input = vec![StackTy::I32];
        let catalog = OpCatalog::from_ops(&concrete_ops());
        let by_output = enumerate_sequences_by_output(&input, &catalog, 2);
        let state = ConcreteState::new([0; LOCAL_SLOTS as usize], [0; MEM_SLOTS as usize]);
        for (sig, seqs) in &by_output {
            for seq in seqs {
                assert!(is_type_valid(&input, seq), "invalid: {seq:?}");
                assert_eq!(
                    simulate_stack_effect(&input, seq).as_ref(),
                    Some(&sig.stack),
                    "seq={seq:?}"
                );
                exec_sequence_concrete(seq, vec![0], state.clone());
            }
            for i in 0..seqs.len() {
                for j in (i + 1)..seqs.len() {
                    sequences_equivalent_random(&input, &seqs[i], &seqs[j], 100);
                }
            }
        }
    }

    #[test]
    fn same_stack_effect_rejects_invalid_pairs() {
        let input = vec![StackTy::I32];
        let valid = vec![SemOp::LocalSet(0)];
        let invalid = vec![SemOp::I32Add];
        assert!(!same_stack_effect(&input, &valid, &invalid));
        assert!(!same_stack_effect(&input, &invalid, &invalid));
    }

    #[test]
    fn mul_const2_equivalent_to_shl_const1_via_z3() {
        let ctx = z3_context();
        let input = vec![StackTy::I32];
        let mul_seq = vec![SemOp::I32Const(2), SemOp::I32Mul];
        let shl_seq = vec![SemOp::I32Const(1), SemOp::I32Shl];
        assert!(sequences_equivalent_z3(&ctx, &input, &mul_seq, &shl_seq));
    }

    #[test]
    fn div_s_not_equivalent_to_div_u_via_z3() {
        let ctx = z3_context();
        let input = vec![StackTy::I32, StackTy::I32];
        let div_s = vec![SemOp::I32DivS];
        let div_u = vec![SemOp::I32DivU];
        assert!(!sequences_equivalent_z3(&ctx, &input, &div_s, &div_u));
    }

    #[test]
    fn div_s_const1_not_equivalent_to_mul_const2_via_z3() {
        let ctx = z3_context();
        let input = vec![StackTy::I32];
        let div_s = vec![SemOp::I32Const(2), SemOp::I32DivS];
        let mul = vec![SemOp::I32Const(2), SemOp::I32Mul];
        assert!(!sequences_equivalent_z3(&ctx, &input, &div_s, &mul));
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
