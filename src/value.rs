//! Pure i32 value DAG (no stack/local containers) for equality saturation.

use crate::al::I32_BITS;
use crate::al::z3_context;
use crate::lang::ValueLang;
use crate::semantics::{
    DagStackStep, SemOp, StackTy, dag_stack_step, simulate_stack_effect, spec_for,
    synthesis_constants, value_lang_from_kind,
};
use crate::stack::WasmOp;
use egg::{Id, Language, RecExpr};
use std::cmp::Ordering;
use z3::ast::{Ast, BV, Bool};
use z3::{Context, SatResult};

/// Pure i32 expression tree for rule synthesis (symbols `?a`, `?b`, …).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ValueAst {
    Symbol(usize),
    Const(i32),
    Add(Box<ValueAst>, Box<ValueAst>),
    Mul(Box<ValueAst>, Box<ValueAst>),
    DivU(Box<ValueAst>, Box<ValueAst>),
    DivS(Box<ValueAst>, Box<ValueAst>),
    Shl(Box<ValueAst>, Box<ValueAst>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ValueBinOp {
    Add,
    Mul,
    DivU,
    DivS,
    Shl,
}

impl ValueBinOp {
    fn all() -> [Self; 5] {
        [Self::Add, Self::Mul, Self::DivU, Self::DivS, Self::Shl]
    }
}

impl ValueAst {
    pub fn size(&self) -> usize {
        match self {
            Self::Symbol(_) | Self::Const(_) => 1,
            Self::Add(l, r)
            | Self::Mul(l, r)
            | Self::DivU(l, r)
            | Self::DivS(l, r)
            | Self::Shl(l, r) => 1 + l.size() + r.size(),
        }
    }

    pub fn uses_all_symbols(&self, num_inputs: usize) -> bool {
        let mut used = vec![false; num_inputs];
        self.collect_symbols(&mut used);
        used.iter().all(|&u| u)
    }

    /// Each input symbol appears exactly once (realizable from one stack read per slot).
    pub fn uses_each_symbol_once(&self, num_inputs: usize) -> bool {
        let mut counts = vec![0usize; num_inputs];
        self.collect_symbol_counts(&mut counts);
        counts.iter().all(|&c| c == 1)
    }

    fn collect_symbol_counts(&self, counts: &mut [usize]) {
        match self {
            Self::Symbol(i) => counts[*i] += 1,
            Self::Const(_) => {}
            Self::Add(l, r)
            | Self::Mul(l, r)
            | Self::DivU(l, r)
            | Self::DivS(l, r)
            | Self::Shl(l, r) => {
                l.collect_symbol_counts(counts);
                r.collect_symbol_counts(counts);
            }
        }
    }

    fn collect_symbols(&self, used: &mut [bool]) {
        match self {
            Self::Symbol(i) => used[*i] = true,
            Self::Const(_) => {}
            Self::Add(l, r)
            | Self::Mul(l, r)
            | Self::DivU(l, r)
            | Self::DivS(l, r)
            | Self::Shl(l, r) => {
                l.collect_symbols(used);
                r.collect_symbols(used);
            }
        }
    }

    pub fn to_pattern(&self) -> String {
        match self {
            Self::Symbol(i) => format!("?{}", (b'a' + *i as u8) as char),
            Self::Const(n) => n.to_string(),
            Self::Add(l, r) => format!("(i32.add {} {})", l.to_pattern(), r.to_pattern()),
            Self::Mul(l, r) => format!("(i32.mul {} {})", l.to_pattern(), r.to_pattern()),
            Self::DivU(l, r) => format!("(i32.div_u {} {})", l.to_pattern(), r.to_pattern()),
            Self::DivS(l, r) => format!("(i32.div_s {} {})", l.to_pattern(), r.to_pattern()),
            Self::Shl(l, r) => format!("(i32.shl {} {})", l.to_pattern(), r.to_pattern()),
        }
    }

    fn binop(op: ValueBinOp, left: ValueAst, right: ValueAst) -> Self {
        let l = Box::new(left);
        let r = Box::new(right);
        match op {
            ValueBinOp::Add => Self::Add(l, r),
            ValueBinOp::Mul => Self::Mul(l, r),
            ValueBinOp::DivU => Self::DivU(l, r),
            ValueBinOp::DivS => Self::DivS(l, r),
            ValueBinOp::Shl => Self::Shl(l, r),
        }
    }
}

/// Enumerate all pure-i32 expression trees with node count ≤ `max_size`.
pub fn enumerate_value_asts(max_size: usize, num_inputs: usize) -> Vec<ValueAst> {
    if max_size == 0 || num_inputs == 0 {
        return Vec::new();
    }

    let mut by_size: Vec<Vec<ValueAst>> = (0..max_size).map(|_| Vec::new()).collect();

    for i in 0..num_inputs {
        by_size[0].push(ValueAst::Symbol(i));
    }
    for &c in synthesis_constants() {
        by_size[0].push(ValueAst::Const(c));
    }

    for total in 2..=max_size {
        let idx = total - 1;
        let mut new_asts = Vec::new();
        for left_sz in 1..total {
            let right_sz = total - 1 - left_sz;
            if right_sz == 0 {
                continue;
            }
            for left in &by_size[left_sz - 1] {
                for right in &by_size[right_sz - 1] {
                    for op in ValueBinOp::all() {
                        new_asts.push(ValueAst::binop(op, left.clone(), right.clone()));
                    }
                }
            }
        }
        by_size[idx] = new_asts;
    }

    by_size.into_iter().flatten().collect()
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct AstEvalResult {
    value: i32,
    trap: bool,
}

fn eval_ast_concrete(ast: &ValueAst, inputs: &[i32]) -> AstEvalResult {
    match ast {
        ValueAst::Symbol(i) => AstEvalResult {
            value: inputs[*i],
            trap: false,
        },
        ValueAst::Const(n) => AstEvalResult {
            value: *n,
            trap: false,
        },
        ValueAst::Add(l, r) => {
            let l = eval_ast_concrete(l, inputs);
            if l.trap {
                return l;
            }
            let r = eval_ast_concrete(r, inputs);
            if r.trap {
                return r;
            }
            AstEvalResult {
                value: l.value.wrapping_add(r.value),
                trap: false,
            }
        }
        ValueAst::Mul(l, r) => {
            let l = eval_ast_concrete(l, inputs);
            if l.trap {
                return l;
            }
            let r = eval_ast_concrete(r, inputs);
            if r.trap {
                return r;
            }
            AstEvalResult {
                value: l.value.wrapping_mul(r.value),
                trap: false,
            }
        }
        ValueAst::DivU(l, r) => {
            let l = eval_ast_concrete(l, inputs);
            if l.trap {
                return l;
            }
            let r = eval_ast_concrete(r, inputs);
            if r.trap {
                return r;
            }
            if r.value == 0 {
                return AstEvalResult {
                    value: 0,
                    trap: true,
                };
            }
            AstEvalResult {
                value: (l.value as u32).wrapping_div(r.value as u32) as i32,
                trap: false,
            }
        }
        ValueAst::DivS(l, r) => {
            let l = eval_ast_concrete(l, inputs);
            if l.trap {
                return l;
            }
            let r = eval_ast_concrete(r, inputs);
            if r.trap {
                return r;
            }
            if r.value == 0 {
                return AstEvalResult {
                    value: 0,
                    trap: true,
                };
            }
            AstEvalResult {
                value: l.value.wrapping_div(r.value),
                trap: false,
            }
        }
        ValueAst::Shl(l, r) => {
            let l = eval_ast_concrete(l, inputs);
            if l.trap {
                return l;
            }
            let r = eval_ast_concrete(r, inputs);
            if r.trap {
                return r;
            }
            AstEvalResult {
                value: l.value.wrapping_shl((r.value as u32) & 31),
                trap: false,
            }
        }
    }
}

fn concrete_valid_ast_rewrite(lhs: &AstEvalResult, rhs: &AstEvalResult) -> bool {
    if lhs.trap != rhs.trap {
        return false;
    }
    if lhs.trap {
        return true;
    }
    lhs.value == rhs.value
}

/// Fast filter: returns `false` if a concrete counterexample is found.
pub fn asts_valid_rewrite_random(
    num_inputs: usize,
    lhs: &ValueAst,
    rhs: &ValueAst,
    num_tests: usize,
) -> bool {
    if num_tests == 0 {
        return true;
    }

    let mut rng = AstLcg::new(0xE6A3_9A1B_CDE2_4701);
    for case in 0..num_tests {
        let inputs: Vec<i32> = (0..num_inputs)
            .map(|i| ast_concrete_input(&mut rng, case, i))
            .collect();
        let lhs_r = eval_ast_concrete(lhs, &inputs);
        let rhs_r = eval_ast_concrete(rhs, &inputs);
        if !concrete_valid_ast_rewrite(&lhs_r, &rhs_r) {
            return false;
        }
    }
    true
}

struct AstLcg(u64);

impl AstLcg {
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

fn ast_concrete_input(rng: &mut AstLcg, case: usize, slot: usize) -> i32 {
    match (case + slot) % 7 {
        0 => 0,
        1 => 1,
        2 => -1,
        3 => 2,
        4 => i32::MIN,
        5 => i32::MAX,
        _ => rng.next_i32(),
    }
}

fn eval_ast_z3<'ctx>(
    ctx: &'ctx Context,
    ast: &ValueAst,
    vars: &[BV<'ctx>],
) -> (BV<'ctx>, Bool<'ctx>) {
    match ast {
        ValueAst::Symbol(i) => (vars[*i].clone(), Bool::from_bool(ctx, false)),
        ValueAst::Const(n) => (
            BV::from_i64(ctx, *n as i64, I32_BITS),
            Bool::from_bool(ctx, false),
        ),
        ValueAst::Add(l, r) => {
            let (lv, lt) = eval_ast_z3(ctx, l, vars);
            let (rv, rt) = eval_ast_z3(ctx, r, vars);
            (lv.bvadd(&rv), Bool::or(ctx, &[&lt, &rt]))
        }
        ValueAst::Mul(l, r) => {
            let (lv, lt) = eval_ast_z3(ctx, l, vars);
            let (rv, rt) = eval_ast_z3(ctx, r, vars);
            (lv.bvmul(&rv), Bool::or(ctx, &[&lt, &rt]))
        }
        ValueAst::DivU(l, r) => {
            let (lv, lt) = eval_ast_z3(ctx, l, vars);
            let (rv, rt) = eval_ast_z3(ctx, r, vars);
            let zero = BV::from_u64(ctx, 0, I32_BITS);
            let div_trap = rv._eq(&zero);
            let trap = Bool::or(ctx, &[&lt, &rt, &div_trap]);
            let result = lv.bvudiv(&rv);
            (result, trap)
        }
        ValueAst::DivS(l, r) => {
            let (lv, lt) = eval_ast_z3(ctx, l, vars);
            let (rv, rt) = eval_ast_z3(ctx, r, vars);
            let zero = BV::from_u64(ctx, 0, I32_BITS);
            let div_trap = rv._eq(&zero);
            let trap = Bool::or(ctx, &[&lt, &rt, &div_trap]);
            let result = lv.bvsdiv(&rv);
            (result, trap)
        }
        ValueAst::Shl(l, r) => {
            let (lv, lt) = eval_ast_z3(ctx, l, vars);
            let (rv, rt) = eval_ast_z3(ctx, r, vars);
            let mask = BV::from_u64(ctx, 31, I32_BITS);
            let shift = rv.bvand(&mask);
            (lv.bvshl(&shift), Bool::or(ctx, &[&lt, &rt]))
        }
    }
}

/// Z3 proof only (call after `asts_valid_rewrite_random` passes).
pub fn asts_valid_rewrite_z3(
    ctx: &Context,
    num_inputs: usize,
    lhs: &ValueAst,
    rhs: &ValueAst,
) -> bool {
    let vars: Vec<BV<'_>> = (0..num_inputs)
        .map(|i| BV::new_const(ctx, format!("in_{i}"), I32_BITS))
        .collect();

    let (lv, lt) = eval_ast_z3(ctx, lhs, &vars);
    let (rv, rt) = eval_ast_z3(ctx, rhs, &vars);

    let solver = z3::Solver::new(ctx);
    let trap_violation = lt.xor(&rt);
    let defined_both = Bool::and(ctx, &[&lt.not(), &rt.not()]);
    let value_violation = Bool::and(ctx, &[&defined_both, &lv._eq(&rv).not()]);
    solver.assert(&Bool::or(ctx, &[&trap_violation, &value_violation]));
    matches!(solver.check(), SatResult::Unsat)
}

pub fn asts_valid_rewrite_z3_default(num_inputs: usize, lhs: &ValueAst, rhs: &ValueAst) -> bool {
    let ctx = z3_context();
    asts_valid_rewrite_z3(&ctx, num_inputs, lhs, rhs)
}

pub fn is_directed_ast_pair(lhs: &ValueAst, rhs: &ValueAst) -> bool {
    match lhs.size().cmp(&rhs.size()) {
        Ordering::Greater => true,
        Ordering::Less => false,
        // Match legacy sequence ordering: for equal-length sequences, `lhs > rhs`
        // on `SemOp` vectors chose `(i32.mul ?a 2) => (i32.shl ?a 1)` over the reverse.
        Ordering::Equal => lhs.to_pattern() < rhs.to_pattern(),
    }
}

pub fn is_ast_rewrite_pair(num_inputs: usize, lhs: &ValueAst, rhs: &ValueAst) -> bool {
    if lhs == rhs {
        return false;
    }
    if is_commutative_swap(lhs, rhs) {
        return false;
    }
    lhs.uses_each_symbol_once(num_inputs) && rhs.uses_each_symbol_once(num_inputs)
}

fn is_commutative_swap(lhs: &ValueAst, rhs: &ValueAst) -> bool {
    match (lhs, rhs) {
        (ValueAst::Add(l1, r1), ValueAst::Add(l2, r2)) if **l1 == **r2 && **r1 == **l2 => true,
        (ValueAst::Mul(l1, r1), ValueAst::Mul(l2, r2)) if **l1 == **r2 && **r1 == **l2 => true,
        _ => false,
    }
}

/// Stack emulator building a `ValueLang` DAG; the final root is the stack top.
pub struct ValueToDag {
    expr: RecExpr<ValueLang>,
    stack: Vec<Id>,
}

impl ValueToDag {
    pub fn new() -> Self {
        Self {
            expr: RecExpr::default(),
            stack: Vec::new(),
        }
    }

    pub fn apply(&mut self, op: &WasmOp) {
        match op {
            WasmOp::I32Const(n) => self.apply_sem(&SemOp::I32Const(*n)),
            WasmOp::I32Add => self.apply_sem(&SemOp::I32Add),
            WasmOp::I32Mul => self.apply_sem(&SemOp::I32Mul),
            WasmOp::I32DivU => self.apply_sem(&SemOp::I32DivU),
            WasmOp::I32DivS => self.apply_sem(&SemOp::I32DivS),
            WasmOp::I32Shl => self.apply_sem(&SemOp::I32Shl),
        }
    }

    pub fn apply_sem(&mut self, op: &SemOp) {
        let spec = spec_for(op);
        let step = dag_stack_step(op, &spec, &mut self.stack).unwrap_or_else(|| {
            panic!("effectful or unsupported op in value DAG conversion: {op:?}")
        });
        match step {
            DagStackStep::PushConst(n) => {
                self.stack.push(self.expr.add(ValueLang::I32Const(n)));
            }
            DagStackStep::Push { kind, args } => {
                self.stack
                    .push(self.expr.add(value_lang_from_kind(kind, &args)));
            }
        }
    }

    /// Seed the stack with pattern variables `?a`, `?b`, … for synthesis.
    pub fn seed_symbolic_i32(&mut self, count: usize) -> Vec<String> {
        (0..count)
            .map(|i| {
                let name = format!("?{}", (b'a' + i as u8) as char);
                let id = self.expr.add(ValueLang::Symbol(name.parse().unwrap()));
                self.stack.push(id);
                name
            })
            .collect()
    }

    /// S-expression pattern for the stack top (single value root).
    pub fn top_pattern(&self) -> Option<String> {
        let top = self.stack.last()?;
        Some(enode_to_pattern(&self.expr, *top))
    }

    pub fn finish(self) -> RecExpr<ValueLang> {
        assert_eq!(
            self.stack.len(),
            1,
            "value DAG expects exactly one stack slot at finish, got {}",
            self.stack.len()
        );
        self.expr
    }

    pub fn build(mut self, ops: &[WasmOp]) -> RecExpr<ValueLang> {
        for op in ops {
            self.apply(op);
        }
        self.finish()
    }
}

pub fn ops_to_value_expr(ops: &[WasmOp]) -> RecExpr<ValueLang> {
    ValueToDag::new().build(ops)
}

pub fn sem_sequence_to_value_pattern(input: &[StackTy], ops: &[SemOp]) -> Option<String> {
    if ops.iter().any(|op| op.is_effectful()) {
        return None;
    }
    let output = simulate_stack_effect(input, ops)?;
    if output.len() != 1 {
        return None;
    }
    let mut dag = ValueToDag::new();
    for _ in input {
        dag.seed_symbolic_i32(1);
    }
    for op in ops {
        dag.apply_sem(op);
    }
    dag.top_pattern()
}

pub fn parse_value_expr(s: &str) -> RecExpr<ValueLang> {
    s.parse().expect("invalid ValueLang RecExpr")
}

fn enode_to_pattern(expr: &RecExpr<ValueLang>, id: Id) -> String {
    let node = &expr[id];
    if node.is_leaf() {
        node.to_string()
    } else {
        let children = node
            .children()
            .iter()
            .map(|&child| enode_to_pattern(expr, child))
            .collect::<Vec<_>>()
            .join(" ");
        format!("({node} {children})")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ops_to_value_expr_builds_single_root() {
        let ops = [WasmOp::I32Const(42), WasmOp::I32Const(0), WasmOp::I32Add];
        let expr = ops_to_value_expr(&ops);
        assert_eq!(expr.to_string(), "(i32.add 42 0)");
        assert!(!expr.to_string().contains("stack.slot"));
    }

    #[test]
    fn top_pattern_has_no_stack_nodes() {
        let input = [StackTy::I32];
        let ops = [SemOp::I32Const(2), SemOp::I32Mul];
        let pat = sem_sequence_to_value_pattern(&input, &ops).expect("pattern");
        assert_eq!(pat, "(i32.mul ?a 2)");
        assert!(!pat.contains("stack"));
    }

    #[test]
    fn sem_sequence_to_value_pattern_rejects_multi_output_stack() {
        let input = [StackTy::I32];
        let ops = [SemOp::I32Const(0)];
        assert!(sem_sequence_to_value_pattern(&input, &ops).is_none());

        let input2 = [StackTy::I32, StackTy::I32];
        let ops2 = [];
        assert!(sem_sequence_to_value_pattern(&input2, &ops2).is_none());

        let input3 = [StackTy::I32];
        let ops3 = [SemOp::I32Const(2), SemOp::I32Mul];
        assert!(sem_sequence_to_value_pattern(&input3, &ops3).is_some());
    }

    #[test]
    fn enumerate_value_asts_includes_mul_const2() {
        let asts = enumerate_value_asts(3, 1);
        let mul = ValueAst::Mul(Box::new(ValueAst::Symbol(0)), Box::new(ValueAst::Const(2)));
        assert!(asts.contains(&mul));
        assert_eq!(mul.to_pattern(), "(i32.mul ?a 2)");
        assert_eq!(mul.size(), 3);
    }

    #[test]
    fn ast_mul_const2_equiv_add_self() {
        let lhs = ValueAst::Mul(Box::new(ValueAst::Symbol(0)), Box::new(ValueAst::Const(2)));
        let rhs = ValueAst::Add(Box::new(ValueAst::Symbol(0)), Box::new(ValueAst::Symbol(0)));
        assert!(asts_valid_rewrite_random(1, &lhs, &rhs, 100));
        assert!(asts_valid_rewrite_z3_default(1, &lhs, &rhs));
    }

    #[test]
    fn uses_each_symbol_once_rejects_duplicated_input() {
        let dup = ValueAst::Add(Box::new(ValueAst::Symbol(0)), Box::new(ValueAst::Symbol(0)));
        assert!(!dup.uses_each_symbol_once(1));
        let mul = ValueAst::Mul(Box::new(ValueAst::Symbol(0)), Box::new(ValueAst::Const(2)));
        assert!(mul.uses_each_symbol_once(1));
    }

    #[test]
    fn directed_ast_pair_prefers_mul_as_lhs_for_shl_equiv() {
        let mul = ValueAst::Mul(Box::new(ValueAst::Symbol(0)), Box::new(ValueAst::Const(2)));
        let shl = ValueAst::Shl(Box::new(ValueAst::Symbol(0)), Box::new(ValueAst::Const(1)));
        assert!(is_directed_ast_pair(&mul, &shl));
        assert!(!is_directed_ast_pair(&shl, &mul));
    }

    #[test]
    fn directed_ast_pair_prefers_larger_lhs() {
        let small = ValueAst::Mul(Box::new(ValueAst::Symbol(0)), Box::new(ValueAst::Const(2)));
        let large = ValueAst::Add(Box::new(small.clone()), Box::new(ValueAst::Const(1)));
        assert!(!is_directed_ast_pair(&small, &large));
        assert!(is_directed_ast_pair(&large, &small));
    }
}
