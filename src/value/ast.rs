//! Typed expression trees for rule synthesis.

use super::ops::{RuleSignature, ValueOp};
use crate::lang::{F32Bits, F64Bits, ValueLang};
use crate::semantics::StackTy;
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
            Self::Const { ty, value } => match ty {
                StackTy::F32 => format!("{}", F32Bits::from_i64_carrier(*value)),
                StackTy::F64 => format!("{}", F64Bits::from_i64_carrier(*value)),
                _ => value.to_string(),
            },
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
    lhs.uses_each_symbol_once(sig) && valid_rewrite_rhs(sig, rhs)
}

/// RHS of a rewrite: well-typed, correct output sort, each symbol used at most once.
/// Unlike the LHS, constants and folds (e.g. `?a * 0 → 0`) need not mention every symbol.
fn valid_rewrite_rhs(sig: &RuleSignature, rhs: &ValueAst) -> bool {
    if rhs.type_of(sig) != Some(sig.output) {
        return false;
    }
    let mut counts = vec![0usize; sig.inputs.len()];
    rhs.collect_symbol_counts(&mut counts);
    counts.iter().all(|&c| c <= 1)
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
                StackTy::F32 => expr.add(ValueLang::F32Const(F32Bits::from_i64_carrier(*value))),
                StackTy::F64 => expr.add(ValueLang::F64Const(F64Bits::from_i64_carrier(*value))),
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
            ValueLang::F32Const(n) => Some(ValueAst::const_ty(StackTy::F32, n.to_i64_carrier())),
            ValueLang::F64Const(n) => Some(ValueAst::const_ty(StackTy::F64, n.to_i64_carrier())),
            node => {
                let (op, child_ids) = ValueOp::from_lang(node)?;
                let args: Option<Vec<ValueAst>> = child_ids.iter().map(|&c| go(c, expr)).collect();
                Some(ValueAst::app(op, args?))
            }
        }
    }
    go(expr.root(), expr)
}
