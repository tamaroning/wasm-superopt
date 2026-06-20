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
    Eq(Box<ValueAst>, Box<ValueAst>),
    Ne(Box<ValueAst>, Box<ValueAst>),
    LtS(Box<ValueAst>, Box<ValueAst>),
    LeS(Box<ValueAst>, Box<ValueAst>),
    GtS(Box<ValueAst>, Box<ValueAst>),
    Eqz(Box<ValueAst>),
    Clz(Box<ValueAst>),
    Ctz(Box<ValueAst>),
    Popcnt(Box<ValueAst>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ValueBinOp {
    Add,
    Mul,
    DivU,
    DivS,
    Shl,
    Eq,
    Ne,
    LtS,
    LeS,
    GtS,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ValueUnOp {
    Eqz,
    Clz,
    Ctz,
    Popcnt,
}

impl ValueBinOp {
    fn all() -> [Self; 10] {
        [
            Self::Add,
            Self::Mul,
            Self::DivU,
            Self::DivS,
            Self::Shl,
            Self::Eq,
            Self::Ne,
            Self::LtS,
            Self::LeS,
            Self::GtS,
        ]
    }
}

impl ValueUnOp {
    fn all() -> [Self; 4] {
        [Self::Eqz, Self::Clz, Self::Ctz, Self::Popcnt]
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
            | Self::Shl(l, r)
            | Self::Eq(l, r)
            | Self::Ne(l, r)
            | Self::LtS(l, r)
            | Self::LeS(l, r)
            | Self::GtS(l, r) => 1 + l.size() + r.size(),
            Self::Eqz(c) | Self::Clz(c) | Self::Ctz(c) | Self::Popcnt(c) => 1 + c.size(),
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
            | Self::Shl(l, r)
            | Self::Eq(l, r)
            | Self::Ne(l, r)
            | Self::LtS(l, r)
            | Self::LeS(l, r)
            | Self::GtS(l, r) => {
                l.collect_symbol_counts(counts);
                r.collect_symbol_counts(counts);
            }
            Self::Eqz(c) | Self::Clz(c) | Self::Ctz(c) | Self::Popcnt(c) => {
                c.collect_symbol_counts(counts);
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
            Self::Eq(l, r) => format!("(i32.eq {} {})", l.to_pattern(), r.to_pattern()),
            Self::Ne(l, r) => format!("(i32.ne {} {})", l.to_pattern(), r.to_pattern()),
            Self::LtS(l, r) => format!("(i32.lt_s {} {})", l.to_pattern(), r.to_pattern()),
            Self::LeS(l, r) => format!("(i32.le_s {} {})", l.to_pattern(), r.to_pattern()),
            Self::GtS(l, r) => format!("(i32.gt_s {} {})", l.to_pattern(), r.to_pattern()),
            Self::Eqz(c) => format!("(i32.eqz {})", c.to_pattern()),
            Self::Clz(c) => format!("(i32.clz {})", c.to_pattern()),
            Self::Ctz(c) => format!("(i32.ctz {})", c.to_pattern()),
            Self::Popcnt(c) => format!("(i32.popcnt {})", c.to_pattern()),
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
            ValueBinOp::Eq => Self::Eq(l, r),
            ValueBinOp::Ne => Self::Ne(l, r),
            ValueBinOp::LtS => Self::LtS(l, r),
            ValueBinOp::LeS => Self::LeS(l, r),
            ValueBinOp::GtS => Self::GtS(l, r),
        }
    }

    fn unop(op: ValueUnOp, child: ValueAst) -> Self {
        let c = Box::new(child);
        match op {
            ValueUnOp::Eqz => Self::Eqz(c),
            ValueUnOp::Clz => Self::Clz(c),
            ValueUnOp::Ctz => Self::Ctz(c),
            ValueUnOp::Popcnt => Self::Popcnt(c),
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
        for child_sz in 1..total {
            for child in &by_size[child_sz - 1] {
                for op in ValueUnOp::all() {
                    new_asts.push(ValueAst::unop(op, child.clone()));
                }
            }
        }
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

fn i32_bool(b: bool) -> i32 {
    i32::from(b)
}

fn eval_children(
    l: &ValueAst,
    r: &ValueAst,
    inputs: &[i32],
    f: fn(i32, i32) -> i32,
) -> AstEvalResult {
    let l = eval_ast_concrete(l, inputs);
    if l.trap {
        return l;
    }
    let r = eval_ast_concrete(r, inputs);
    if r.trap {
        return r;
    }
    AstEvalResult {
        value: f(l.value, r.value),
        trap: false,
    }
}

fn eval_unary_child(
    c: &ValueAst,
    inputs: &[i32],
    f: fn(i32) -> i32,
) -> AstEvalResult {
    let c = eval_ast_concrete(c, inputs);
    if c.trap {
        return c;
    }
    AstEvalResult {
        value: f(c.value),
        trap: false,
    }
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
        ValueAst::Eq(l, r) => eval_children(l, r, inputs, |a, b| i32_bool(a == b)),
        ValueAst::Ne(l, r) => eval_children(l, r, inputs, |a, b| i32_bool(a != b)),
        ValueAst::LtS(l, r) => eval_children(l, r, inputs, |a, b| i32_bool(a < b)),
        ValueAst::LeS(l, r) => eval_children(l, r, inputs, |a, b| i32_bool(a <= b)),
        ValueAst::GtS(l, r) => eval_children(l, r, inputs, |a, b| i32_bool(a > b)),
        ValueAst::Eqz(c) => eval_unary_child(c, inputs, |a| i32_bool(a == 0)),
        ValueAst::Clz(c) => eval_unary_child(c, inputs, |a| (a as u32).leading_zeros() as i32),
        ValueAst::Ctz(c) => eval_unary_child(c, inputs, |a| (a as u32).trailing_zeros() as i32),
        ValueAst::Popcnt(c) => eval_unary_child(c, inputs, |a| (a as u32).count_ones() as i32),
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

fn bool32<'ctx>(ctx: &'ctx Context, b: &Bool<'ctx>) -> BV<'ctx> {
    b.ite(
        &BV::from_i64(ctx, 1, I32_BITS),
        &BV::from_i64(ctx, 0, I32_BITS),
    )
}

fn bv_bit_is_set<'ctx>(ctx: &'ctx Context, v: &BV<'ctx>, i: u32) -> Bool<'ctx> {
    v.extract(i, i)._eq(&BV::from_u64(ctx, 1, 1))
}

fn i32_clz_z3<'ctx>(ctx: &'ctx Context, v: &BV<'ctx>) -> BV<'ctx> {
    let mut out = BV::from_i64(ctx, 32, I32_BITS);
    for i in (0..32).rev() {
        let bit = bv_bit_is_set(ctx, v, i);
        let val = BV::from_i64(ctx, (31 - i) as i64, I32_BITS);
        out = bit.ite(&val, &out);
    }
    out
}

fn i32_ctz_z3<'ctx>(ctx: &'ctx Context, v: &BV<'ctx>) -> BV<'ctx> {
    let mut out = BV::from_i64(ctx, 32, I32_BITS);
    for i in 0..32 {
        let bit = bv_bit_is_set(ctx, v, i);
        let val = BV::from_i64(ctx, i as i64, I32_BITS);
        out = bit.ite(&val, &out);
    }
    out
}

fn i32_popcnt_z3<'ctx>(ctx: &'ctx Context, v: &BV<'ctx>) -> BV<'ctx> {
    let mut sum = BV::from_i64(ctx, 0, I32_BITS);
    for i in 0..32 {
        let bit = bool32(ctx, &bv_bit_is_set(ctx, v, i));
        sum = sum.bvadd(&bit);
    }
    sum
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
        ValueAst::Eq(l, r) => {
            let (lv, lt) = eval_ast_z3(ctx, l, vars);
            let (rv, rt) = eval_ast_z3(ctx, r, vars);
            (bool32(ctx, &lv._eq(&rv)), Bool::or(ctx, &[&lt, &rt]))
        }
        ValueAst::Ne(l, r) => {
            let (lv, lt) = eval_ast_z3(ctx, l, vars);
            let (rv, rt) = eval_ast_z3(ctx, r, vars);
            (bool32(ctx, &lv._eq(&rv).not()), Bool::or(ctx, &[&lt, &rt]))
        }
        ValueAst::LtS(l, r) => {
            let (lv, lt) = eval_ast_z3(ctx, l, vars);
            let (rv, rt) = eval_ast_z3(ctx, r, vars);
            (bool32(ctx, &lv.bvslt(&rv)), Bool::or(ctx, &[&lt, &rt]))
        }
        ValueAst::LeS(l, r) => {
            let (lv, lt) = eval_ast_z3(ctx, l, vars);
            let (rv, rt) = eval_ast_z3(ctx, r, vars);
            (bool32(ctx, &lv.bvsle(&rv)), Bool::or(ctx, &[&lt, &rt]))
        }
        ValueAst::GtS(l, r) => {
            let (lv, lt) = eval_ast_z3(ctx, l, vars);
            let (rv, rt) = eval_ast_z3(ctx, r, vars);
            (bool32(ctx, &lv.bvsgt(&rv)), Bool::or(ctx, &[&lt, &rt]))
        }
        ValueAst::Eqz(c) => {
            let (cv, ct) = eval_ast_z3(ctx, c, vars);
            let zero = BV::from_i64(ctx, 0, I32_BITS);
            (bool32(ctx, &cv._eq(&zero)), ct)
        }
        ValueAst::Clz(c) => {
            let (cv, ct) = eval_ast_z3(ctx, c, vars);
            (i32_clz_z3(ctx, &cv), ct)
        }
        ValueAst::Ctz(c) => {
            let (cv, ct) = eval_ast_z3(ctx, c, vars);
            (i32_ctz_z3(ctx, &cv), ct)
        }
        ValueAst::Popcnt(c) => {
            let (cv, ct) = eval_ast_z3(ctx, c, vars);
            (i32_popcnt_z3(ctx, &cv), ct)
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
        (ValueAst::Eq(l1, r1), ValueAst::Eq(l2, r2)) if **l1 == **r2 && **r1 == **l2 => true,
        (ValueAst::Ne(l1, r1), ValueAst::Ne(l2, r2)) if **l1 == **r2 && **r1 == **l2 => true,
        _ => false,
    }
}

/// Parse a s-expression into a [`ValueLang`] DAG (used by symbolic forward execution).
pub fn parse_value_expr(s: &str) -> RecExpr<ValueLang> {
    s.parse().expect("invalid ValueLang RecExpr")
}
