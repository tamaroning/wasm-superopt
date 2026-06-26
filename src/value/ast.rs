//! Typed expression trees for rule synthesis.

use super::ops::{RuleSignature, ValueOp};
use crate::lang::ValueLang;
use crate::semantics::{StackTy, synthesis_constants};
use egg::{Id, RecExpr, Symbol};

/// Pure expression tree for rule synthesis (symbols `?a`, `?b`, …).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ValueAst {
    Symbol(usize),
    Const { ty: StackTy, value: i64 },
    App { op: ValueOp, args: Vec<ValueAst> },
}

impl ValueAst {
    pub fn symbol(i: usize) -> Self {
        Self::Symbol(i)
    }

    pub fn const_ty(ty: StackTy, value: i64) -> Self {
        Self::Const { ty, value }
    }

    pub fn app(op: ValueOp, args: Vec<ValueAst>) -> Self {
        Self::App { op, args }
    }

    pub fn size(&self) -> usize {
        match self {
            Self::Symbol(_) | Self::Const { .. } => 1,
            Self::App { args, .. } => 1 + args.iter().map(ValueAst::size).sum::<usize>(),
        }
    }

    pub fn type_of(&self, sig: &RuleSignature) -> Option<StackTy> {
        match self {
            Self::Symbol(i) => sig.inputs.get(*i).copied(),
            Self::Const { ty, .. } => Some(*ty),
            Self::App { op, args } => {
                if args.len() != op.pops().len() {
                    return None;
                }
                for (arg, &expected) in args.iter().zip(op.pops()) {
                    if arg.type_of(sig)? != expected {
                        return None;
                    }
                }
                Some(op.push())
            }
        }
    }

    pub fn uses_each_symbol_once(&self, sig: &RuleSignature) -> bool {
        let mut counts = vec![0usize; sig.inputs.len()];
        self.collect_symbol_counts(&mut counts);
        if !counts.iter().all(|&c| c == 1) {
            return false;
        }
        self.type_of(sig) == Some(sig.output)
    }

    fn collect_symbol_counts(&self, counts: &mut [usize]) {
        match self {
            Self::Symbol(i) => counts[*i] += 1,
            Self::Const { .. } => {}
            Self::App { args, .. } => {
                for arg in args {
                    arg.collect_symbol_counts(counts);
                }
            }
        }
    }

    pub fn to_pattern(&self) -> String {
        match self {
            Self::Symbol(i) => format!("?{}", (b'a' + *i as u8) as char),
            Self::Const { value, .. } => value.to_string(),
            Self::App { op, args } => {
                let name = op.pattern_name();
                let parts: Vec<String> = args.iter().map(ValueAst::to_pattern).collect();
                if parts.is_empty() {
                    format!("({name})")
                } else {
                    format!("({name} {})", parts.join(" "))
                }
            }
        }
    }
}

pub fn is_directed_ast_pair(lhs: &ValueAst, rhs: &ValueAst) -> bool {
    use std::cmp::Ordering;
    match lhs.size().cmp(&rhs.size()) {
        Ordering::Greater => true,
        Ordering::Less => false,
        Ordering::Equal => lhs.to_pattern() < rhs.to_pattern(),
    }
}

pub fn is_ast_rewrite_pair(sig: &RuleSignature, lhs: &ValueAst, rhs: &ValueAst) -> bool {
    if lhs == rhs {
        return false;
    }
    if is_commutative_swap(lhs, rhs) {
        return false;
    }
    lhs.uses_each_symbol_once(sig) && rhs.uses_each_symbol_once(sig)
}

fn is_commutative_swap(lhs: &ValueAst, rhs: &ValueAst) -> bool {
    match (lhs, rhs) {
        (
            ValueAst::App {
                op: lop,
                args: largs,
            },
            ValueAst::App {
                op: rop,
                args: rargs,
            },
        ) if lop.is_commutative() && lop == rop && largs.len() == 2 && rargs.len() == 2 => {
            largs[0] == rargs[1] && largs[1] == rargs[0]
        }
        _ => false,
    }
}

pub fn synthesis_symbol(i: usize) -> Symbol {
    assert!(i < 26, "synthesis supports at most 26 inputs");
    format!("?{}", (b'a' + i as u8) as char)
        .parse()
        .expect("valid synthesis symbol")
}

pub fn value_ast_to_expr(ast: &ValueAst) -> RecExpr<ValueLang> {
    let mut expr = RecExpr::default();
    fn go(ast: &ValueAst, expr: &mut RecExpr<ValueLang>) -> Id {
        match ast {
            ValueAst::Symbol(i) => expr.add(ValueLang::Symbol(synthesis_symbol(*i))),
            ValueAst::Const { ty, value } => match ty {
                StackTy::I32 => expr.add(ValueLang::I32Const(*value as i32)),
                StackTy::I64 => expr.add(ValueLang::I64Const(*value)),
            },
            ValueAst::App { op, args } => {
                let child_ids: Vec<Id> = args.iter().map(|a| go(a, expr)).collect();
                expr.add(op.to_enode(&child_ids))
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

pub fn value_ast_from_expr(expr: &RecExpr<ValueLang>) -> Option<ValueAst> {
    fn go(id: Id, expr: &RecExpr<ValueLang>) -> Option<ValueAst> {
        match &expr[id] {
            ValueLang::Symbol(s) => Some(ValueAst::Symbol(synthesis_symbol_index(s)?)),
            ValueLang::I32Const(n) => Some(ValueAst::const_ty(StackTy::I32, *n as i64)),
            ValueLang::I64Const(n) => Some(ValueAst::const_ty(StackTy::I64, *n)),
            node => {
                let (op, child_ids) = ValueOp::from_lang(node)?;
                let args: Option<Vec<ValueAst>> = child_ids.iter().map(|&c| go(c, expr)).collect();
                Some(ValueAst::app(op, args?))
            }
        }
    }
    go(expr.root(), expr)
}

/// Enumerate all well-typed expression trees with node count ≤ `max_size`.
pub fn enumerate_value_asts(sig: &RuleSignature, max_size: usize) -> Vec<ValueAst> {
    if max_size == 0 || sig.inputs.is_empty() {
        return Vec::new();
    }
    let mut by_sort_size: std::collections::HashMap<StackTy, Vec<Vec<ValueAst>>> =
        std::collections::HashMap::new();
    for &sort in &[StackTy::I32, StackTy::I64] {
        by_sort_size.insert(sort, (0..max_size).map(|_| Vec::new()).collect());
    }

    for (i, &ty) in sig.inputs.iter().enumerate() {
        by_sort_size.get_mut(&ty).unwrap()[0].push(ValueAst::symbol(i));
    }
    for &c in synthesis_constants() {
        by_sort_size
            .get_mut(&StackTy::I32)
            .unwrap()[0]
            .push(ValueAst::const_ty(StackTy::I32, c as i64));
        by_sort_size
            .get_mut(&StackTy::I64)
            .unwrap()[0]
            .push(ValueAst::const_ty(StackTy::I64, c as i64));
    }

    for total in 2..=max_size {
        let idx = total - 1;
        for &sort in &[StackTy::I32, StackTy::I64] {
            let mut new_asts = Vec::new();
            for op in ValueOp::ops_with_result(sort) {
                let pops = op.pops();
                let k = pops.len();
                if k == 0 || total < 1 + k {
                    continue;
                }
                let inner = total - 1;
                for part in partitions(inner, k) {
                    if part.iter().all(|&s| s >= 1) {
                        let mut ok = true;
                        for (&pop_ty, &sz) in pops.iter().zip(part.iter()) {
                            let bucket = &by_sort_size.get(&pop_ty).unwrap()[sz - 1];
                            if bucket.is_empty() {
                                ok = false;
                                break;
                            }
                        }
                        if !ok {
                            continue;
                        }
                        // Cartesian product of child choices at each partition size
                        enumerate_child_combos(pops, &part, &by_sort_size, 0, &mut vec![], &mut |combo| {
                            new_asts.push(ValueAst::app(op, combo.to_vec()));
                        });
                    }
                }
            }
            by_sort_size.get_mut(&sort).unwrap()[idx] = new_asts;
        }
    }

    by_sort_size
        .get(&sig.output)
        .unwrap()
        .iter()
        .flatten()
        .cloned()
        .filter(|ast| ast.type_of(sig) == Some(sig.output))
        .collect()
}

fn partitions(sum: usize, k: usize) -> Vec<Vec<usize>> {
    let mut out = Vec::new();
    if k == 1 {
        if sum >= 1 {
            out.push(vec![sum]);
        }
        return out;
    }
    for first in 1..=sum.saturating_sub(k - 1) {
        for rest in partitions(sum - first, k - 1) {
            let mut p = vec![first];
            p.extend(rest);
            out.push(p);
        }
    }
    out
}

fn enumerate_child_combos(
    pops: &[StackTy],
    part: &[usize],
    by_sort_size: &std::collections::HashMap<StackTy, Vec<Vec<ValueAst>>>,
    depth: usize,
    acc: &mut Vec<ValueAst>,
    emit: &mut dyn FnMut(&[ValueAst]),
) {
    if depth == pops.len() {
        emit(acc);
        return;
    }
    let ty = pops[depth];
    let sz = part[depth];
    for ast in &by_sort_size.get(&ty).unwrap()[sz - 1] {
        acc.push(ast.clone());
        enumerate_child_combos(pops, part, by_sort_size, depth + 1, acc, emit);
        acc.pop();
    }
}
