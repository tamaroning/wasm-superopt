//! Pure i32 value DAG (no stack/local containers) for equality saturation.

use crate::al::I32_BITS;
use crate::lang::ValueLang;
use crate::semantics::synthesis_constants;
use egg::RecExpr;
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

pub fn is_directed_ast_pair(lhs: &ValueAst, rhs: &ValueAst) -> bool {
    use std::cmp::Ordering;
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

/// Parse a s-expression into a [`ValueLang`] DAG (used by symbolic forward execution).
pub fn parse_value_expr(s: &str) -> RecExpr<ValueLang> {
    s.parse().expect("invalid ValueLang RecExpr")
}
