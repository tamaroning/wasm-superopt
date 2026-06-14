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
    for c in [0, 1, 2, 3, 4, 16, 42] {
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

fn concrete_results_match(lhs: &ConcreteResult, rhs: &ConcreteResult) -> bool {
    if lhs.trap != rhs.trap {
        return false;
    }
    if lhs.trap {
        return true;
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

    pub fn load_mem(&self, addr: &BV<'ctx>) -> BV<'ctx> {
        self.memory.select(addr).as_bv().unwrap()
    }
}

pub struct ExecResult<'ctx> {
    pub stack: Vec<BV<'ctx>>,
    pub state: Z3State<'ctx>,
    pub trap: Bool<'ctx>,
}

pub fn exec_op<'ctx>(
    ctx: &'ctx Context,
    op: &SemOp,
    stack: &mut Vec<BV<'ctx>>,
    state: &mut Z3State<'ctx>,
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
            let result = trap.ite(&a, &a.bvudiv(&b));
            stack.push(result);
        }
        SemOp::I32DivS => {
            let b = stack.pop().unwrap();
            let a = stack.pop().unwrap();
            trap = trap_z3(ctx, op, &a, &b);
            let result = trap.ite(&a, &a.bvsdiv(&b));
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
            *state = state.store_local(ctx, *idx, &val);
        }
        SemOp::I32Load => {
            let addr = stack.pop().unwrap();
            stack.push(state.load_mem(&addr));
        }
        SemOp::I32Store => {
            let val = stack.pop().unwrap();
            let addr = stack.pop().unwrap();
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
    for op in ops {
        let t = exec_op(ctx, op, &mut stack, &mut state);
        trap = Bool::or(ctx, &[&trap, &t]);
    }
    ExecResult { stack, state, trap }
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
    let out_lhs = simulate_stack_effect(input, lhs);
    let out_rhs = simulate_stack_effect(input, rhs);
    if out_lhs != out_rhs {
        return false;
    }
    if lhs == rhs {
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
    let stack_in: Vec<BV<'_>> = (0..input.len())
        .map(|i| BV::new_const(ctx, format!("in_{i}"), I32_BITS))
        .collect();

    let st_lhs = Z3State::fresh(ctx, "lhs");
    let st_rhs = Z3State::fresh(ctx, "rhs");

    let lhs_r = exec_sequence(ctx, lhs, stack_in.clone(), st_lhs);
    let rhs_r = exec_sequence(ctx, rhs, stack_in, st_rhs);

    let solver = z3::Solver::new(ctx);

    let trap_mismatch = lhs_r.trap.xor(&rhs_r.trap);
    let no_trap = Bool::and(ctx, &[&lhs_r.trap.not(), &rhs_r.trap.not()]);

    let mut diff = Bool::from_bool(ctx, false);
    if lhs_r.stack.len() != rhs_r.stack.len() {
        return false;
    }
    for (l, r) in lhs_r.stack.iter().zip(rhs_r.stack.iter()) {
        diff = Bool::or(ctx, &[&diff, &l._eq(r).not()]);
    }
    for i in 0..LOCAL_SLOTS {
        let idx = BV::from_u64(ctx, i as u64, I32_BITS);
        diff = Bool::or(
            ctx,
            &[&diff, &lhs_r.state.locals.select(&idx)._eq(&rhs_r.state.locals.select(&idx)).not()],
        );
    }
    for a in 0..MEM_SLOTS {
        let addr = BV::from_u64(ctx, a as u64, I32_BITS);
        diff = Bool::or(
            ctx,
            &[&diff, &lhs_r.state.memory.select(&addr)._eq(&rhs_r.state.memory.select(&addr)).not()],
        );
    }

    solver.assert(&Bool::or(ctx, &[&trap_mismatch, &Bool::and(ctx, &[&no_trap, &diff])]));
    matches!(solver.check(), z3::SatResult::Unsat)
}

pub fn simulate_stack_effect(input: &[StackTy], ops: &[SemOp]) -> Option<Vec<StackTy>> {
    let mut stack = input.to_vec();
    for op in ops {
        let spec = spec_for(op);
        if spec.pops.len() > stack.len() {
            return None;
        }
        for _ in 0..spec.pops.len() {
            stack.pop();
        }
        stack.extend_from_slice(spec.pushes);
    }
    Some(stack)
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct StackSig {
    pub stack: Vec<StackTy>,
}

pub fn enumerate_sequences(
    input: &[StackTy],
    ops: &[SemOp],
    max_len: usize,
) -> Vec<Vec<SemOp>> {
    let mut results = Vec::new();
    let mut work = vec![(input.to_vec(), Vec::new())];

    while let Some((stack, seq)) = work.pop() {
        if !seq.is_empty() {
            results.push(seq.clone());
        }
        if seq.len() >= max_len {
            continue;
        }
        for op in ops {
            let spec = spec_for(op);
            if spec.pops.len() > stack.len() {
                continue;
            }
            let mut next_stack = stack.clone();
            for _ in 0..spec.pops.len() {
                next_stack.pop();
            }
            next_stack.extend_from_slice(spec.pushes);
            let mut next_seq = seq.clone();
            next_seq.push(op.clone());
            work.push((next_stack, next_seq));
        }
    }
    results
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
