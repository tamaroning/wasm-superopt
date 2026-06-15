//! Algorithmic-language (AL) IR for Wasm instruction semantics.
//!
//! Each `SemOp` is defined by an `AlSpec` (pop / if / trap / push steps). Concrete
//! execution, Z3 lowering, and `InstSpec` are derived from these definitions.

use super::{
    ConcreteState, InstSpec, SemOp, StackTy, StateTouches, Z3State, I32_BITS,
};
use std::borrow::Cow;
use std::collections::HashMap;
use z3::ast::{Ast, BV, Bool};
use z3::Context;

// ---------------------------------------------------------------------------
// AL IR
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AlSpec {
    pub steps: Vec<AlStep>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AlStep {
    Pop(&'static str),
    Push(AlExpr),
    SetLocal { idx: u32, var: &'static str },
    StoreMem { addr: &'static str, val: &'static str },
    If {
        cond: AlCond,
        then_steps: Vec<AlStep>,
        else_steps: Vec<AlStep>,
    },
    Trap,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AlExpr {
    ConstI32(i32),
    #[allow(dead_code)]
    Var(&'static str),
    BinOp(BinOpKind, &'static str, &'static str),
    LocalGet(u32),
    MemLoad(&'static str),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AlCond {
    BinOpEmpty(BinOpKind, &'static str, &'static str),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BinOpKind {
    Add,
    Mul,
    DivU,
    DivS,
    Shl,
}

impl BinOpKind {
    /// `binop(a, b) = ε` (Wasm partiality): may the operation trap?
    pub fn binop_empty_concrete(self, a: i32, b: i32) -> bool {
        match self {
            BinOpKind::DivU => b == 0,
            BinOpKind::DivS => b == 0 || (b == -1 && a == i32::MIN),
            BinOpKind::Add | BinOpKind::Mul | BinOpKind::Shl => false,
        }
    }

    pub fn binop_empty_z3<'ctx>(
        self,
        ctx: &'ctx Context,
        a: &BV<'ctx>,
        b: &BV<'ctx>,
    ) -> Bool<'ctx> {
        match self {
            BinOpKind::DivU => b._eq(&BV::from_i64(ctx, 0, I32_BITS)),
            BinOpKind::DivS => Bool::or(
                ctx,
                &[
                    &b._eq(&BV::from_i64(ctx, 0, I32_BITS)),
                    &Bool::and(
                        ctx,
                        &[
                            &b._eq(&BV::from_i64(ctx, -1, I32_BITS)),
                            &a._eq(&BV::from_i64(ctx, i32::MIN as i64, I32_BITS)),
                        ],
                    ),
                ],
            ),
            BinOpKind::Add | BinOpKind::Mul | BinOpKind::Shl => Bool::from_bool(ctx, false),
        }
    }
}

// ---------------------------------------------------------------------------
// Embedding policy
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EmbeddingPolicy {
    /// When lowering `if trap else push`, push a dummy value on the trap path.
    pub trap_dummy_push: bool,
}

pub const STRAIGHT_LINE_EMBED: EmbeddingPolicy = EmbeddingPolicy {
    trap_dummy_push: true,
};

// ---------------------------------------------------------------------------
// Static AL specs (shared instruction shapes)
// ---------------------------------------------------------------------------

fn steps_add() -> Vec<AlStep> {
    vec![
        AlStep::Pop("b"),
        AlStep::Pop("a"),
        AlStep::Push(AlExpr::BinOp(BinOpKind::Add, "a", "b")),
    ]
}

fn steps_mul() -> Vec<AlStep> {
    vec![
        AlStep::Pop("b"),
        AlStep::Pop("a"),
        AlStep::Push(AlExpr::BinOp(BinOpKind::Mul, "a", "b")),
    ]
}

fn steps_shl() -> Vec<AlStep> {
    vec![
        AlStep::Pop("b"),
        AlStep::Pop("a"),
        AlStep::Push(AlExpr::BinOp(BinOpKind::Shl, "a", "b")),
    ]
}

fn steps_div_u() -> Vec<AlStep> {
    vec![
        AlStep::Pop("c2"),
        AlStep::Pop("c1"),
        AlStep::If {
            cond: AlCond::BinOpEmpty(BinOpKind::DivU, "c1", "c2"),
            then_steps: vec![AlStep::Trap],
            else_steps: vec![AlStep::Push(AlExpr::BinOp(
                BinOpKind::DivU,
                "c1",
                "c2",
            ))],
        },
    ]
}

fn steps_div_s() -> Vec<AlStep> {
    vec![
        AlStep::Pop("c2"),
        AlStep::Pop("c1"),
        AlStep::If {
            cond: AlCond::BinOpEmpty(BinOpKind::DivS, "c1", "c2"),
            then_steps: vec![AlStep::Trap],
            else_steps: vec![AlStep::Push(AlExpr::BinOp(
                BinOpKind::DivS,
                "c1",
                "c2",
            ))],
        },
    ]
}

fn steps_load() -> Vec<AlStep> {
    vec![
        AlStep::Pop("addr"),
        AlStep::Push(AlExpr::MemLoad("addr")),
    ]
}

fn steps_store() -> Vec<AlStep> {
    vec![
        AlStep::Pop("val"),
        AlStep::Pop("addr"),
        AlStep::StoreMem {
            addr: "addr",
            val: "val",
        },
    ]
}

fn steps_drop() -> Vec<AlStep> {
    vec![AlStep::Pop("_")]
}

pub fn al_spec_for(op: &SemOp) -> Cow<'_, AlSpec> {
    match op {
        SemOp::I32Const(n) => Cow::Owned(AlSpec {
            steps: vec![AlStep::Push(AlExpr::ConstI32(*n))],
        }),
        SemOp::I32Add => Cow::Owned(AlSpec {
            steps: steps_add(),
        }),
        SemOp::I32Mul => Cow::Owned(AlSpec {
            steps: steps_mul(),
        }),
        SemOp::I32Shl => Cow::Owned(AlSpec {
            steps: steps_shl(),
        }),
        SemOp::I32DivU => Cow::Owned(AlSpec {
            steps: steps_div_u(),
        }),
        SemOp::I32DivS => Cow::Owned(AlSpec {
            steps: steps_div_s(),
        }),
        SemOp::LocalGet(i) => Cow::Owned(AlSpec {
            steps: vec![AlStep::Push(AlExpr::LocalGet(*i))],
        }),
        SemOp::LocalSet(i) => Cow::Owned(AlSpec {
            steps: vec![
                AlStep::Pop("v"),
                AlStep::SetLocal { idx: *i, var: "v" },
            ],
        }),
        SemOp::I32Load => Cow::Owned(AlSpec {
            steps: steps_load(),
        }),
        SemOp::I32Store => Cow::Owned(AlSpec {
            steps: steps_store(),
        }),
        SemOp::Drop => Cow::Owned(AlSpec {
            steps: steps_drop(),
        }),
    }
}

// ---------------------------------------------------------------------------
// InstSpec derivation
// ---------------------------------------------------------------------------

const I32: StackTy = StackTy::I32;
const POPS_0: &[StackTy] = &[];
const POPS_1: &[StackTy] = &[I32];
const POPS_2: &[StackTy] = &[I32, I32];
const PUSHES_0: &[StackTy] = &[];
const PUSHES_1: &[StackTy] = &[I32];

fn count_pops(steps: &[AlStep]) -> usize {
    let mut n = 0;
    for step in steps {
        match step {
            AlStep::Pop(_) => n += 1,
            AlStep::If {
                then_steps,
                else_steps,
                ..
            } => {
                n += count_pops(then_steps) + count_pops(else_steps);
            }
            AlStep::Push(_)
            | AlStep::SetLocal { .. }
            | AlStep::StoreMem { .. }
            | AlStep::Trap => {}
        }
    }
    n
}

fn count_pushes(steps: &[AlStep], policy: &EmbeddingPolicy) -> usize {
    let mut n = 0;
    for step in steps {
        match step {
            AlStep::Push(_) => n += 1,
            AlStep::If {
                then_steps,
                else_steps,
                ..
            } => {
                let then_p = count_pushes(then_steps, policy);
                let else_p = count_pushes(else_steps, policy);
                if is_trap_else_push(then_steps, else_steps) && policy.trap_dummy_push {
                    n += else_p.max(1);
                } else {
                    n += then_p + else_p;
                }
            }
            AlStep::Pop(_)
            | AlStep::SetLocal { .. }
            | AlStep::StoreMem { .. }
            | AlStep::Trap => {}
        }
    }
    n
}

fn is_trap_else_push(then_steps: &[AlStep], else_steps: &[AlStep]) -> bool {
    then_steps == [AlStep::Trap]
        && else_steps.len() == 1
        && matches!(else_steps[0], AlStep::Push(_))
}

fn touches_state(steps: &[AlStep]) -> bool {
    for step in steps {
        match step {
            AlStep::SetLocal { .. } | AlStep::StoreMem { .. } => return true,
            AlStep::Push(expr) => {
                if matches!(expr, AlExpr::LocalGet(_) | AlExpr::MemLoad(_)) {
                    return true;
                }
            }
            AlStep::If {
                then_steps,
                else_steps,
                ..
            } => {
                if touches_state(then_steps) || touches_state(else_steps) {
                    return true;
                }
            }
            AlStep::Pop(_) | AlStep::Trap => {}
        }
    }
    false
}

fn derive_can_trap(steps: &[AlStep]) -> bool {
    for step in steps {
        if let AlStep::If {
            cond: AlCond::BinOpEmpty(..),
            then_steps,
            ..
        } = step
        {
            if then_steps.as_slice() == [AlStep::Trap] {
                return true;
            }
        }
    }
    false
}

fn pops_slice(n: usize) -> &'static [StackTy] {
    match n {
        0 => POPS_0,
        1 => POPS_1,
        2 => POPS_2,
        _ => POPS_2, // unreachable for current ops
    }
}

fn pushes_slice(n: usize) -> &'static [StackTy] {
    match n {
        0 => PUSHES_0,
        1 => PUSHES_1,
        _ => PUSHES_1,
    }
}

pub fn derive_inst_spec(al: &AlSpec, policy: &EmbeddingPolicy) -> InstSpec {
    let pop_n = count_pops(&al.steps);
    let push_n = count_pushes(&al.steps, policy);
    InstSpec {
        pops: pops_slice(pop_n),
        pushes: pushes_slice(push_n),
        touches_state: touches_state(&al.steps),
        can_trap: derive_can_trap(&al.steps),
    }
}

// ---------------------------------------------------------------------------
// Condition / expression evaluation
// ---------------------------------------------------------------------------

struct AlEnv<V> {
    vars: HashMap<&'static str, V>,
}

impl<V: Clone> Clone for AlEnv<V> {
    fn clone(&self) -> Self {
        Self {
            vars: self.vars.clone(),
        }
    }
}

impl<V: Clone> AlEnv<V> {
    fn new() -> Self {
        Self {
            vars: HashMap::new(),
        }
    }

    fn bind(&mut self, name: &'static str, val: V) {
        self.vars.insert(name, val);
    }

    fn get(&self, name: &str) -> &V {
        self.vars.get(name).expect("unbound AL variable")
    }
}

fn eval_cond_concrete(cond: &AlCond, env: &AlEnv<i32>) -> bool {
    match cond {
        AlCond::BinOpEmpty(kind, lhs, rhs) => {
            let a = *env.get(lhs);
            let b = *env.get(rhs);
            kind.binop_empty_concrete(a, b)
        }
    }
}

fn eval_expr_concrete(expr: &AlExpr, env: &AlEnv<i32>) -> i32 {
    match expr {
        AlExpr::ConstI32(n) => *n,
        AlExpr::Var(name) => *env.get(name),
        AlExpr::BinOp(kind, lhs, rhs) => {
            let a = *env.get(lhs);
            let b = *env.get(rhs);
            eval_binop_concrete(*kind, a, b)
        }
        AlExpr::LocalGet(_idx) => panic!("LocalGet in eval_expr_concrete requires state"),
        AlExpr::MemLoad(_) => panic!("MemLoad in eval_expr_concrete requires state"),
    }
}

fn eval_binop_concrete(kind: BinOpKind, a: i32, b: i32) -> i32 {
    match kind {
        BinOpKind::Add => a.wrapping_add(b),
        BinOpKind::Mul => a.wrapping_mul(b),
        BinOpKind::DivU => (a as u32).wrapping_div(b as u32) as i32,
        BinOpKind::DivS => a.wrapping_div(b),
        BinOpKind::Shl => a.wrapping_shl(b as u32 & 31),
    }
}

fn eval_cond_z3<'ctx>(ctx: &'ctx Context, cond: &AlCond, env: &AlEnv<BV<'ctx>>) -> Bool<'ctx> {
    match cond {
        AlCond::BinOpEmpty(kind, lhs, rhs) => {
            let a = env.get(lhs).clone();
            let b = env.get(rhs).clone();
            kind.binop_empty_z3(ctx, &a, &b)
        }
    }
}

fn eval_expr_z3<'ctx>(
    ctx: &'ctx Context,
    expr: &AlExpr,
    env: &AlEnv<BV<'ctx>>,
    state: &Z3State<'ctx>,
) -> BV<'ctx> {
    match expr {
        AlExpr::ConstI32(n) => BV::from_i64(ctx, *n as i64, I32_BITS),
        AlExpr::Var(name) => env.get(name).clone(),
        AlExpr::BinOp(kind, lhs, rhs) => {
            let a = env.get(lhs).clone();
            let b = env.get(rhs).clone();
            eval_binop_z3(ctx, *kind, &a, &b)
        }
        AlExpr::LocalGet(idx) => state.load_local(ctx, *idx),
        AlExpr::MemLoad(addr) => state.load_mem(env.get(addr)),
    }
}

fn eval_binop_z3<'ctx>(ctx: &'ctx Context, kind: BinOpKind, a: &BV<'ctx>, b: &BV<'ctx>) -> BV<'ctx> {
    match kind {
        BinOpKind::Add => a.bvadd(b),
        BinOpKind::Mul => a.bvmul(b),
        BinOpKind::DivU => a.bvudiv(b),
        BinOpKind::DivS => a.bvsdiv(b),
        BinOpKind::Shl => {
            let mask = BV::from_u64(ctx, 31, I32_BITS);
            a.bvshl(&b.bvand(&mask))
        }
    }
}

// ---------------------------------------------------------------------------
// AL execution — concrete
// ---------------------------------------------------------------------------

fn exec_step_concrete(
    step: &AlStep,
    stack: &mut Vec<i32>,
    state: &mut ConcreteState,
    trap: &mut bool,
    env: &mut AlEnv<i32>,
    policy: &EmbeddingPolicy,
) {
    match step {
        AlStep::Pop(name) => {
            let val = stack.pop().expect("stack underflow");
            env.bind(name, val);
        }
        AlStep::Push(expr) => {
            let val = match expr {
                AlExpr::LocalGet(idx) => state.load_local(*idx),
                AlExpr::MemLoad(addr) => state.load_mem(*env.get(addr)),
                _ => eval_expr_concrete(expr, env),
            };
            stack.push(val);
        }
        AlStep::SetLocal { idx, var } => {
            let val = *env.get(var);
            *state = state.store_local(*idx, val);
        }
        AlStep::StoreMem { addr, val } => {
            let a = *env.get(addr);
            let v = *env.get(val);
            *state = state.store_mem(a, v);
        }
        AlStep::If {
            cond,
            then_steps,
            else_steps,
        } => {
            if is_trap_else_push(then_steps, else_steps) && policy.trap_dummy_push {
                let cond_val = eval_cond_concrete(cond, env);
                *trap = *trap || cond_val;
                let result = if cond_val {
                    0
                } else {
                    let push_expr = match &else_steps[0] {
                        AlStep::Push(e) => e,
                        _ => unreachable!(),
                    };
                    match push_expr {
                        AlExpr::LocalGet(idx) => state.load_local(*idx),
                        AlExpr::MemLoad(addr) => state.load_mem(*env.get(addr)),
                        _ => eval_expr_concrete(push_expr, env),
                    }
                };
                stack.push(result);
            } else if eval_cond_concrete(cond, env) {
                exec_al_steps_concrete(then_steps, stack, state, trap, env, policy);
            } else {
                exec_al_steps_concrete(else_steps, stack, state, trap, env, policy);
            }
        }
        AlStep::Trap => {
            *trap = true;
        }
    }
}

fn exec_al_steps_concrete(
    steps: &[AlStep],
    stack: &mut Vec<i32>,
    state: &mut ConcreteState,
    trap: &mut bool,
    env: &mut AlEnv<i32>,
    policy: &EmbeddingPolicy,
) {
    for step in steps {
        exec_step_concrete(step, stack, state, trap, env, policy);
    }
}

pub fn exec_al_concrete(
    al: &AlSpec,
    stack: &mut Vec<i32>,
    state: &mut ConcreteState,
    policy: &EmbeddingPolicy,
) -> bool {
    let mut trap = false;
    let mut env = AlEnv::new();
    exec_al_steps_concrete(&al.steps, stack, state, &mut trap, &mut env, policy);
    trap
}

// ---------------------------------------------------------------------------
// AL execution — Z3
// ---------------------------------------------------------------------------

fn exec_step_z3<'ctx>(
    ctx: &'ctx Context,
    step: &AlStep,
    stack: &mut Vec<BV<'ctx>>,
    state: &mut Z3State<'ctx>,
    trap: &mut Bool<'ctx>,
    env: &mut AlEnv<BV<'ctx>>,
    touches: &mut StateTouches<'ctx>,
    policy: &EmbeddingPolicy,
) {
    match step {
        AlStep::Pop(name) => {
            let val = stack.pop().expect("stack underflow");
            env.bind(name, val);
        }
        AlStep::Push(expr) => {
            stack.push(eval_expr_z3(ctx, expr, env, state));
        }
        AlStep::SetLocal { idx, var } => {
            let val = env.get(var).clone();
            touches.local_writes.insert(*idx);
            *state = state.store_local(ctx, *idx, &val);
        }
        AlStep::StoreMem { addr, val } => {
            let a = env.get(addr).clone();
            let v = env.get(val).clone();
            touches.mem_writes.push(a.clone());
            *state = state.store_mem(&a, &v);
        }
        AlStep::If {
            cond,
            then_steps,
            else_steps,
        } => {
            if is_trap_else_push(then_steps, else_steps) && policy.trap_dummy_push {
                let c = eval_cond_z3(ctx, cond, env);
                *trap = Bool::or(ctx, &[trap, &c]);
                let push_expr = match &else_steps[0] {
                    AlStep::Push(e) => e,
                    _ => unreachable!(),
                };
                let zero = BV::from_i64(ctx, 0, I32_BITS);
                let result = eval_expr_z3(ctx, push_expr, env, state);
                stack.push(c.ite(&zero, &result));
            } else {
                let c = eval_cond_z3(ctx, cond, env);
                // General merge (unused by current ops).
                let mut trap_t = trap.clone();
                let mut trap_e = trap.clone();
                let mut stack_t = stack.clone();
                let mut stack_e = stack.clone();
                let mut state_t = state.clone();
                let mut state_e = state.clone();
                let mut env_t = env.clone();
                let mut env_e = env.clone();
                let mut touches_t = StateTouches::default();
                let mut touches_e = StateTouches::default();
                exec_al_steps_z3(
                    ctx,
                    then_steps,
                    &mut stack_t,
                    &mut state_t,
                    &mut trap_t,
                    &mut env_t,
                    &mut touches_t,
                    policy,
                );
                exec_al_steps_z3(
                    ctx,
                    else_steps,
                    &mut stack_e,
                    &mut state_e,
                    &mut trap_e,
                    &mut env_e,
                    &mut touches_e,
                    policy,
                );
                *trap = Bool::or(
                    ctx,
                    &[
                        &Bool::and(ctx, &[&c, &trap_t]),
                        &Bool::and(ctx, &[&c.not(), &trap_e]),
                    ],
                );
                if stack_t.len() == stack_e.len() + (stack.len() - stack.len()) {
                    // merge stacks
                }
                let base_len = stack.len();
                let new_len = stack_t.len().max(stack_e.len());
                stack.truncate(base_len);
                for i in base_len..new_len {
                    let t = stack_t.get(i).cloned();
                    let e = stack_e.get(i).cloned();
                    match (t, e) {
                        (Some(tv), Some(ev)) => stack.push(c.ite(&tv, &ev)),
                        (Some(tv), None) => stack.push(tv),
                        (None, Some(ev)) => stack.push(ev),
                        (None, None) => {}
                    }
                }
                touches.local_writes.extend(touches_t.local_writes);
                touches.local_writes.extend(touches_e.local_writes);
                touches.mem_writes.extend(touches_t.mem_writes);
                touches.mem_writes.extend(touches_e.mem_writes);
                *state = state_t; // simplified: current ops don't use general if
                let _ = state_e;
            }
        }
        AlStep::Trap => {
            *trap = Bool::from_bool(ctx, true);
        }
    }
}

fn exec_al_steps_z3<'ctx>(
    ctx: &'ctx Context,
    steps: &[AlStep],
    stack: &mut Vec<BV<'ctx>>,
    state: &mut Z3State<'ctx>,
    trap: &mut Bool<'ctx>,
    env: &mut AlEnv<BV<'ctx>>,
    touches: &mut StateTouches<'ctx>,
    policy: &EmbeddingPolicy,
) {
    for step in steps {
        exec_step_z3(
            ctx, step, stack, state, trap, env, touches, policy,
        );
    }
}

pub fn exec_al_z3<'ctx>(
    ctx: &'ctx Context,
    al: &AlSpec,
    stack: &mut Vec<BV<'ctx>>,
    state: &mut Z3State<'ctx>,
    touches: &mut StateTouches<'ctx>,
    policy: &EmbeddingPolicy,
) -> Bool<'ctx> {
    let mut trap = Bool::from_bool(ctx, false);
    let mut env = AlEnv::new();
    exec_al_steps_z3(
        ctx,
        &al.steps,
        stack,
        state,
        &mut trap,
        &mut env,
        touches,
        policy,
    );
    trap
}

// ---------------------------------------------------------------------------
// Pretty-print (Z3 lowering summary)
// ---------------------------------------------------------------------------

pub fn format_al_z3(al: &AlSpec) -> String {
    let mut parts = Vec::new();
    for step in &al.steps {
        format_step_z3(step, &mut parts);
    }
    parts.join("; ")
}

fn format_step_z3(step: &AlStep, parts: &mut Vec<String>) {
    match step {
        AlStep::Pop(name) => parts.push(format!("pop {name}")),
        AlStep::Push(expr) => parts.push(format!("push {}", format_expr_z3(expr))),
        AlStep::SetLocal { idx, .. } => parts.push(format!("store locals[{idx}]")),
        AlStep::StoreMem { .. } => parts.push("store memory[addr]".into()),
        AlStep::If {
            cond,
            then_steps,
            else_steps,
        } => {
            if is_trap_else_push(then_steps, else_steps) {
                let push = match &else_steps[0] {
                    AlStep::Push(e) => format_expr_z3(e),
                    _ => "?".into(),
                };
                parts.push(format!(
                    "ite({},{},0)",
                    format_cond_z3(cond),
                    push
                ));
            } else {
                parts.push(format!(
                    "if {} {{ {} }} else {{ {} }}",
                    format_cond_z3(cond),
                    format_steps_z3(then_steps),
                    format_steps_z3(else_steps)
                ));
            }
        }
        AlStep::Trap => parts.push("trap".into()),
    }
}

fn format_steps_z3(steps: &[AlStep]) -> String {
    let mut parts = Vec::new();
    for s in steps {
        format_step_z3(s, &mut parts);
    }
    parts.join("; ")
}

fn format_cond_z3(cond: &AlCond) -> String {
    match cond {
        AlCond::BinOpEmpty(kind, lhs, rhs) => {
            format!("empty({kind:?},{lhs},{rhs})")
        }
    }
}

fn format_expr_z3(expr: &AlExpr) -> String {
    match expr {
        AlExpr::ConstI32(n) => format!("BV const {n}"),
        AlExpr::Var(name) => name.to_string(),
        AlExpr::BinOp(kind, lhs, rhs) => format!("{kind:?}({lhs},{rhs})"),
        AlExpr::LocalGet(i) => format!("select locals[{i}]"),
        AlExpr::MemLoad(addr) => format!("select memory[{addr}]"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::concrete_ops;

    #[test]
    fn derive_inst_spec_matches_expected() {
        let policy = STRAIGHT_LINE_EMBED;
        for op in concrete_ops() {
            let al = al_spec_for(&op);
            let derived = derive_inst_spec(&al, &policy);
            let expected = expected_inst_spec(&op);
            assert_eq!(derived.pops, expected.pops, "{op:?} pops");
            assert_eq!(derived.pushes, expected.pushes, "{op:?} pushes");
            assert_eq!(derived.touches_state, expected.touches_state, "{op:?} state");
            assert_eq!(derived.can_trap, expected.can_trap, "{op:?} can_trap");
        }
    }

    fn expected_inst_spec(op: &SemOp) -> InstSpec {
        match op {
            SemOp::I32Const(_) => InstSpec {
                pops: POPS_0,
                pushes: PUSHES_1,
                touches_state: false,
                can_trap: false,
            },
            SemOp::I32Add | SemOp::I32Mul | SemOp::I32Shl => InstSpec {
                pops: POPS_2,
                pushes: PUSHES_1,
                touches_state: false,
                can_trap: false,
            },
            SemOp::I32DivU | SemOp::I32DivS => InstSpec {
                pops: POPS_2,
                pushes: PUSHES_1,
                touches_state: false,
                can_trap: true,
            },
            SemOp::LocalGet(_) => InstSpec {
                pops: POPS_0,
                pushes: PUSHES_1,
                touches_state: true,
                can_trap: false,
            },
            SemOp::LocalSet(_) => InstSpec {
                pops: POPS_1,
                pushes: PUSHES_0,
                touches_state: true,
                can_trap: false,
            },
            SemOp::I32Load => InstSpec {
                pops: POPS_1,
                pushes: PUSHES_1,
                touches_state: true,
                can_trap: false,
            },
            SemOp::I32Store => InstSpec {
                pops: POPS_2,
                pushes: PUSHES_0,
                touches_state: true,
                can_trap: false,
            },
            SemOp::Drop => InstSpec {
                pops: POPS_1,
                pushes: PUSHES_0,
                touches_state: false,
                can_trap: false,
            },
        }
    }

    #[test]
    fn div_u_al_has_wasm_binop_shape() {
        let al = al_spec_for(&SemOp::I32DivU);
        assert!(matches!(
            al.steps.as_slice(),
            [
                AlStep::Pop("c2"),
                AlStep::Pop("c1"),
                AlStep::If { .. }
            ]
        ));
        if let AlStep::If {
            cond,
            then_steps,
            else_steps,
        } = &al.steps[2]
        {
            assert!(matches!(
                cond,
                AlCond::BinOpEmpty(BinOpKind::DivU, "c1", "c2")
            ));
            assert_eq!(then_steps.as_slice(), [AlStep::Trap]);
            assert!(matches!(else_steps.as_slice(), [AlStep::Push(_)]));
        } else {
            panic!("expected If");
        }
    }
}
