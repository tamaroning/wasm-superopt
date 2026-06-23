//! Pure i32 value DAG (no stack/local containers) for equality saturation.

use crate::al::{asts_valid_rewrite_z3 as al_asts_valid_rewrite_z3, eval_value_ast_concrete};
use crate::lang::ValueLang;
use crate::semantics::synthesis_constants;
use egg::{Id, RecExpr, Symbol};

/// Pure i32 expression tree for rule synthesis (symbols `?a`, `?b`, …).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ValueAst {
    Symbol(usize),
    Const(i32),
    Add(Box<ValueAst>, Box<ValueAst>),
    Sub(Box<ValueAst>, Box<ValueAst>),
    Mul(Box<ValueAst>, Box<ValueAst>),
    DivU(Box<ValueAst>, Box<ValueAst>),
    DivS(Box<ValueAst>, Box<ValueAst>),
    RemU(Box<ValueAst>, Box<ValueAst>),
    RemS(Box<ValueAst>, Box<ValueAst>),
    Shl(Box<ValueAst>, Box<ValueAst>),
    And(Box<ValueAst>, Box<ValueAst>),
    Or(Box<ValueAst>, Box<ValueAst>),
    Xor(Box<ValueAst>, Box<ValueAst>),
    ShrU(Box<ValueAst>, Box<ValueAst>),
    ShrS(Box<ValueAst>, Box<ValueAst>),
    Rotl(Box<ValueAst>, Box<ValueAst>),
    Rotr(Box<ValueAst>, Box<ValueAst>),
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
pub(crate) enum ValueBinOp {
    Add,
    Sub,
    Mul,
    DivU,
    DivS,
    RemU,
    RemS,
    Shl,
    And,
    Or,
    Xor,
    ShrU,
    ShrS,
    Rotl,
    Rotr,
    Eq,
    Ne,
    LtS,
    LeS,
    GtS,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ValueUnOp {
    Eqz,
    Clz,
    Ctz,
    Popcnt,
}

impl ValueBinOp {
    pub(crate) fn all() -> [Self; 20] {
        [
            Self::Add,
            Self::Sub,
            Self::Mul,
            Self::DivU,
            Self::DivS,
            Self::RemU,
            Self::RemS,
            Self::Shl,
            Self::And,
            Self::Or,
            Self::Xor,
            Self::ShrU,
            Self::ShrS,
            Self::Rotl,
            Self::Rotr,
            Self::Eq,
            Self::Ne,
            Self::LtS,
            Self::LeS,
            Self::GtS,
        ]
    }
}

impl ValueUnOp {
    pub(crate) fn all() -> [Self; 4] {
        [Self::Eqz, Self::Clz, Self::Ctz, Self::Popcnt]
    }
}

impl ValueAst {
    pub fn size(&self) -> usize {
        match self {
            Self::Symbol(_) | Self::Const(_) => 1,
            Self::Add(l, r)
            | Self::Sub(l, r)
            | Self::Mul(l, r)
            | Self::DivU(l, r)
            | Self::DivS(l, r)
            | Self::RemU(l, r)
            | Self::RemS(l, r)
            | Self::Shl(l, r)
            | Self::And(l, r)
            | Self::Or(l, r)
            | Self::Xor(l, r)
            | Self::ShrU(l, r)
            | Self::ShrS(l, r)
            | Self::Rotl(l, r)
            | Self::Rotr(l, r)
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
            | Self::Sub(l, r)
            | Self::Mul(l, r)
            | Self::DivU(l, r)
            | Self::DivS(l, r)
            | Self::RemU(l, r)
            | Self::RemS(l, r)
            | Self::Shl(l, r)
            | Self::And(l, r)
            | Self::Or(l, r)
            | Self::Xor(l, r)
            | Self::ShrU(l, r)
            | Self::ShrS(l, r)
            | Self::Rotl(l, r)
            | Self::Rotr(l, r)
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
            Self::Sub(l, r) => format!("(i32.sub {} {})", l.to_pattern(), r.to_pattern()),
            Self::Mul(l, r) => format!("(i32.mul {} {})", l.to_pattern(), r.to_pattern()),
            Self::DivU(l, r) => format!("(i32.div_u {} {})", l.to_pattern(), r.to_pattern()),
            Self::DivS(l, r) => format!("(i32.div_s {} {})", l.to_pattern(), r.to_pattern()),
            Self::RemU(l, r) => format!("(i32.rem_u {} {})", l.to_pattern(), r.to_pattern()),
            Self::RemS(l, r) => format!("(i32.rem_s {} {})", l.to_pattern(), r.to_pattern()),
            Self::Shl(l, r) => format!("(i32.shl {} {})", l.to_pattern(), r.to_pattern()),
            Self::And(l, r) => format!("(i32.and {} {})", l.to_pattern(), r.to_pattern()),
            Self::Or(l, r) => format!("(i32.or {} {})", l.to_pattern(), r.to_pattern()),
            Self::Xor(l, r) => format!("(i32.xor {} {})", l.to_pattern(), r.to_pattern()),
            Self::ShrU(l, r) => format!("(i32.shr_u {} {})", l.to_pattern(), r.to_pattern()),
            Self::ShrS(l, r) => format!("(i32.shr_s {} {})", l.to_pattern(), r.to_pattern()),
            Self::Rotl(l, r) => format!("(i32.rotl {} {})", l.to_pattern(), r.to_pattern()),
            Self::Rotr(l, r) => format!("(i32.rotr {} {})", l.to_pattern(), r.to_pattern()),
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
            ValueBinOp::Sub => Self::Sub(l, r),
            ValueBinOp::Mul => Self::Mul(l, r),
            ValueBinOp::DivU => Self::DivU(l, r),
            ValueBinOp::DivS => Self::DivS(l, r),
            ValueBinOp::RemU => Self::RemU(l, r),
            ValueBinOp::RemS => Self::RemS(l, r),
            ValueBinOp::Shl => Self::Shl(l, r),
            ValueBinOp::And => Self::And(l, r),
            ValueBinOp::Or => Self::Or(l, r),
            ValueBinOp::Xor => Self::Xor(l, r),
            ValueBinOp::ShrU => Self::ShrU(l, r),
            ValueBinOp::ShrS => Self::ShrS(l, r),
            ValueBinOp::Rotl => Self::Rotl(l, r),
            ValueBinOp::Rotr => Self::Rotr(l, r),
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

fn eval_ast_concrete(ast: &ValueAst, inputs: &[i32]) -> AstEvalResult {
    let r = eval_value_ast_concrete(ast, inputs);
    AstEvalResult {
        value: r.value,
        trap: r.trap,
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

const AST_CORNER_INPUTS: [i32; 6] = [0, 1, -1, 2, i32::MIN, i32::MAX];

fn asts_match_on_inputs(lhs: &ValueAst, rhs: &ValueAst, inputs: &[i32]) -> bool {
    let lhs_r = eval_ast_concrete(lhs, inputs);
    let rhs_r = eval_ast_concrete(rhs, inputs);
    concrete_valid_ast_rewrite(&lhs_r, &rhs_r)
}

/// Fast filter: returns `false` if a concrete counterexample is found.
pub fn asts_valid_rewrite_random(
    num_inputs: usize,
    lhs: &ValueAst,
    rhs: &ValueAst,
    num_tests: usize,
) -> bool {
    for &v in &AST_CORNER_INPUTS {
        let inputs = vec![v; num_inputs];
        if !asts_match_on_inputs(lhs, rhs, &inputs) {
            return false;
        }
    }

    let mut rng = AstLcg::new(0xE6A3_9A1B_CDE2_4701);
    for _ in 0..num_tests {
        let inputs: Vec<i32> = (0..num_inputs).map(|_| rng.next_i32()).collect();
        if !asts_match_on_inputs(lhs, rhs, &inputs) {
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

/// Z3 proof only (call after `asts_valid_rewrite_random` passes).
pub fn asts_valid_rewrite_z3(
    ctx: &z3::Context,
    num_inputs: usize,
    lhs: &ValueAst,
    rhs: &ValueAst,
) -> bool {
    al_asts_valid_rewrite_z3(ctx, num_inputs, lhs, rhs)
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
        (ValueAst::And(l1, r1), ValueAst::And(l2, r2)) if **l1 == **r2 && **r1 == **l2 => true,
        (ValueAst::Or(l1, r1), ValueAst::Or(l2, r2)) if **l1 == **r2 && **r1 == **l2 => true,
        (ValueAst::Xor(l1, r1), ValueAst::Xor(l2, r2)) if **l1 == **r2 && **r1 == **l2 => true,
        (ValueAst::Eq(l1, r1), ValueAst::Eq(l2, r2)) if **l1 == **r2 && **r1 == **l2 => true,
        (ValueAst::Ne(l1, r1), ValueAst::Ne(l2, r2)) if **l1 == **r2 && **r1 == **l2 => true,
        _ => false,
    }
}

/// Variable symbol for synthesis (`?a`, `?b`, …).
pub fn synthesis_symbol(i: usize) -> Symbol {
    assert!(i < 26, "synthesis supports at most 26 inputs");
    format!("?{}", (b'a' + i as u8) as char)
        .parse()
        .expect("valid synthesis symbol")
}

/// Build an egg enode for a binary operator with e-class children.
pub fn binop_enode(op: ValueBinOp, left: Id, right: Id) -> ValueLang {
    match op {
        ValueBinOp::Add => ValueLang::I32Add([left, right]),
        ValueBinOp::Sub => ValueLang::I32Sub([left, right]),
        ValueBinOp::Mul => ValueLang::I32Mul([left, right]),
        ValueBinOp::DivU => ValueLang::I32DivU([left, right]),
        ValueBinOp::DivS => ValueLang::I32DivS([left, right]),
        ValueBinOp::RemU => ValueLang::I32RemU([left, right]),
        ValueBinOp::RemS => ValueLang::I32RemS([left, right]),
        ValueBinOp::Shl => ValueLang::I32Shl([left, right]),
        ValueBinOp::And => ValueLang::I32And([left, right]),
        ValueBinOp::Or => ValueLang::I32Or([left, right]),
        ValueBinOp::Xor => ValueLang::I32Xor([left, right]),
        ValueBinOp::ShrU => ValueLang::I32ShrU([left, right]),
        ValueBinOp::ShrS => ValueLang::I32ShrS([left, right]),
        ValueBinOp::Rotl => ValueLang::I32Rotl([left, right]),
        ValueBinOp::Rotr => ValueLang::I32Rotr([left, right]),
        ValueBinOp::Eq => ValueLang::I32Eq([left, right]),
        ValueBinOp::Ne => ValueLang::I32Ne([left, right]),
        ValueBinOp::LtS => ValueLang::I32LtS([left, right]),
        ValueBinOp::LeS => ValueLang::I32LeS([left, right]),
        ValueBinOp::GtS => ValueLang::I32GtS([left, right]),
    }
}

/// Build an egg enode for a unary operator with an e-class child.
pub fn unop_enode(op: ValueUnOp, child: Id) -> ValueLang {
    match op {
        ValueUnOp::Eqz => ValueLang::I32Eqz([child]),
        ValueUnOp::Clz => ValueLang::I32Clz([child]),
        ValueUnOp::Ctz => ValueLang::I32Ctz([child]),
        ValueUnOp::Popcnt => ValueLang::I32Popcnt([child]),
    }
}

/// Convert a synthesis AST into a [`RecExpr`] for the e-graph.
pub fn value_ast_to_expr(ast: &ValueAst) -> RecExpr<ValueLang> {
    let mut expr = RecExpr::default();
    fn go(ast: &ValueAst, expr: &mut RecExpr<ValueLang>) -> Id {
        match ast {
            ValueAst::Symbol(i) => expr.add(ValueLang::Symbol(synthesis_symbol(*i))),
            ValueAst::Const(n) => expr.add(ValueLang::I32Const(*n)),
            ValueAst::Add(l, r) => {
                let l = go(l, expr);
                let r = go(r, expr);
                expr.add(ValueLang::I32Add([l, r]))
            }
            ValueAst::Sub(l, r) => {
                let l = go(l, expr);
                let r = go(r, expr);
                expr.add(ValueLang::I32Sub([l, r]))
            }
            ValueAst::Mul(l, r) => {
                let l = go(l, expr);
                let r = go(r, expr);
                expr.add(ValueLang::I32Mul([l, r]))
            }
            ValueAst::DivU(l, r) => {
                let l = go(l, expr);
                let r = go(r, expr);
                expr.add(ValueLang::I32DivU([l, r]))
            }
            ValueAst::DivS(l, r) => {
                let l = go(l, expr);
                let r = go(r, expr);
                expr.add(ValueLang::I32DivS([l, r]))
            }
            ValueAst::RemU(l, r) => {
                let l = go(l, expr);
                let r = go(r, expr);
                expr.add(ValueLang::I32RemU([l, r]))
            }
            ValueAst::RemS(l, r) => {
                let l = go(l, expr);
                let r = go(r, expr);
                expr.add(ValueLang::I32RemS([l, r]))
            }
            ValueAst::Shl(l, r) => {
                let l = go(l, expr);
                let r = go(r, expr);
                expr.add(ValueLang::I32Shl([l, r]))
            }
            ValueAst::And(l, r) => {
                let l = go(l, expr);
                let r = go(r, expr);
                expr.add(ValueLang::I32And([l, r]))
            }
            ValueAst::Or(l, r) => {
                let l = go(l, expr);
                let r = go(r, expr);
                expr.add(ValueLang::I32Or([l, r]))
            }
            ValueAst::Xor(l, r) => {
                let l = go(l, expr);
                let r = go(r, expr);
                expr.add(ValueLang::I32Xor([l, r]))
            }
            ValueAst::ShrU(l, r) => {
                let l = go(l, expr);
                let r = go(r, expr);
                expr.add(ValueLang::I32ShrU([l, r]))
            }
            ValueAst::ShrS(l, r) => {
                let l = go(l, expr);
                let r = go(r, expr);
                expr.add(ValueLang::I32ShrS([l, r]))
            }
            ValueAst::Rotl(l, r) => {
                let l = go(l, expr);
                let r = go(r, expr);
                expr.add(ValueLang::I32Rotl([l, r]))
            }
            ValueAst::Rotr(l, r) => {
                let l = go(l, expr);
                let r = go(r, expr);
                expr.add(ValueLang::I32Rotr([l, r]))
            }
            ValueAst::Eq(l, r) => {
                let l = go(l, expr);
                let r = go(r, expr);
                expr.add(ValueLang::I32Eq([l, r]))
            }
            ValueAst::Ne(l, r) => {
                let l = go(l, expr);
                let r = go(r, expr);
                expr.add(ValueLang::I32Ne([l, r]))
            }
            ValueAst::LtS(l, r) => {
                let l = go(l, expr);
                let r = go(r, expr);
                expr.add(ValueLang::I32LtS([l, r]))
            }
            ValueAst::LeS(l, r) => {
                let l = go(l, expr);
                let r = go(r, expr);
                expr.add(ValueLang::I32LeS([l, r]))
            }
            ValueAst::GtS(l, r) => {
                let l = go(l, expr);
                let r = go(r, expr);
                expr.add(ValueLang::I32GtS([l, r]))
            }
            ValueAst::Eqz(c) => {
                let c = go(c, expr);
                expr.add(ValueLang::I32Eqz([c]))
            }
            ValueAst::Clz(c) => {
                let c = go(c, expr);
                expr.add(ValueLang::I32Clz([c]))
            }
            ValueAst::Ctz(c) => {
                let c = go(c, expr);
                expr.add(ValueLang::I32Ctz([c]))
            }
            ValueAst::Popcnt(c) => {
                let c = go(c, expr);
                expr.add(ValueLang::I32Popcnt([c]))
            }
        }
    }
    go(ast, &mut expr);
    expr
}

fn synthesis_symbol_index(sym: &Symbol) -> Option<usize> {
    let name = sym.as_str();
    let mut chars = name.chars();
    if chars.next()? != '?' {
        return None;
    }
    let ch = chars.next()?;
    if chars.next().is_some() {
        return None;
    }
    let i = ch as u8;
    if !(b'a'..=b'z').contains(&i) {
        return None;
    }
    Some((i - b'a') as usize)
}

/// Recover a synthesis AST from a [`RecExpr`] (synthesis symbols only).
pub fn value_ast_from_expr(expr: &RecExpr<ValueLang>) -> Option<ValueAst> {
    fn go(id: Id, expr: &RecExpr<ValueLang>) -> Option<ValueAst> {
        match &expr[id] {
            ValueLang::Symbol(s) => Some(ValueAst::Symbol(synthesis_symbol_index(s)?)),
            ValueLang::I32Const(n) => Some(ValueAst::Const(*n)),
            ValueLang::I32Add([l, r]) => Some(ValueAst::Add(Box::new(go(*l, expr)?), Box::new(go(*r, expr)?))),
            ValueLang::I32Sub([l, r]) => Some(ValueAst::Sub(Box::new(go(*l, expr)?), Box::new(go(*r, expr)?))),
            ValueLang::I32Mul([l, r]) => Some(ValueAst::Mul(Box::new(go(*l, expr)?), Box::new(go(*r, expr)?))),
            ValueLang::I32DivU([l, r]) => Some(ValueAst::DivU(Box::new(go(*l, expr)?), Box::new(go(*r, expr)?))),
            ValueLang::I32DivS([l, r]) => Some(ValueAst::DivS(Box::new(go(*l, expr)?), Box::new(go(*r, expr)?))),
            ValueLang::I32RemU([l, r]) => Some(ValueAst::RemU(Box::new(go(*l, expr)?), Box::new(go(*r, expr)?))),
            ValueLang::I32RemS([l, r]) => Some(ValueAst::RemS(Box::new(go(*l, expr)?), Box::new(go(*r, expr)?))),
            ValueLang::I32Shl([l, r]) => Some(ValueAst::Shl(Box::new(go(*l, expr)?), Box::new(go(*r, expr)?))),
            ValueLang::I32And([l, r]) => Some(ValueAst::And(Box::new(go(*l, expr)?), Box::new(go(*r, expr)?))),
            ValueLang::I32Or([l, r]) => Some(ValueAst::Or(Box::new(go(*l, expr)?), Box::new(go(*r, expr)?))),
            ValueLang::I32Xor([l, r]) => Some(ValueAst::Xor(Box::new(go(*l, expr)?), Box::new(go(*r, expr)?))),
            ValueLang::I32ShrU([l, r]) => Some(ValueAst::ShrU(Box::new(go(*l, expr)?), Box::new(go(*r, expr)?))),
            ValueLang::I32ShrS([l, r]) => Some(ValueAst::ShrS(Box::new(go(*l, expr)?), Box::new(go(*r, expr)?))),
            ValueLang::I32Rotl([l, r]) => Some(ValueAst::Rotl(Box::new(go(*l, expr)?), Box::new(go(*r, expr)?))),
            ValueLang::I32Rotr([l, r]) => Some(ValueAst::Rotr(Box::new(go(*l, expr)?), Box::new(go(*r, expr)?))),
            ValueLang::I32Eq([l, r]) => Some(ValueAst::Eq(Box::new(go(*l, expr)?), Box::new(go(*r, expr)?))),
            ValueLang::I32Ne([l, r]) => Some(ValueAst::Ne(Box::new(go(*l, expr)?), Box::new(go(*r, expr)?))),
            ValueLang::I32LtS([l, r]) => Some(ValueAst::LtS(Box::new(go(*l, expr)?), Box::new(go(*r, expr)?))),
            ValueLang::I32LeS([l, r]) => Some(ValueAst::LeS(Box::new(go(*l, expr)?), Box::new(go(*r, expr)?))),
            ValueLang::I32GtS([l, r]) => Some(ValueAst::GtS(Box::new(go(*l, expr)?), Box::new(go(*r, expr)?))),
            ValueLang::I32Eqz([c]) => Some(ValueAst::Eqz(Box::new(go(*c, expr)?))),
            ValueLang::I32Clz([c]) => Some(ValueAst::Clz(Box::new(go(*c, expr)?))),
            ValueLang::I32Ctz([c]) => Some(ValueAst::Ctz(Box::new(go(*c, expr)?))),
            ValueLang::I32Popcnt([c]) => Some(ValueAst::Popcnt(Box::new(go(*c, expr)?))),
        }
    }
    go(expr.root(), expr)
}

/// Fixed concrete inputs for characteristic-vector matching (Ruler-style cvecs).
pub fn cvec_test_inputs(num_inputs: usize) -> Vec<Vec<i32>> {
    let mut out: Vec<Vec<i32>> = AST_CORNER_INPUTS
        .iter()
        .map(|&v| vec![v; num_inputs])
        .collect();
    let mut rng = AstLcg::new(0xC0FF_EE42);
    for _ in 0..32 {
        let inputs: Vec<i32> = (0..num_inputs).map(|_| rng.next_i32()).collect();
        out.push(inputs);
    }
    out
}

/// Characteristic vector: concrete evaluation on a fixed input suite.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct AstEvalSignature {
    samples: Vec<(bool, i32)>,
}

impl AstEvalSignature {
    pub fn of(ast: &ValueAst, test_inputs: &[Vec<i32>]) -> Self {
        let samples = test_inputs
            .iter()
            .map(|inputs| {
                let r = eval_ast_concrete(ast, inputs);
                (r.trap, r.value)
            })
            .collect();
        Self { samples }
    }
}

/// Parse a s-expression into a [`ValueLang`] DAG (used by symbolic forward execution).
pub fn parse_value_expr(s: &str) -> RecExpr<ValueLang> {
    s.parse().expect("invalid ValueLang RecExpr")
}
