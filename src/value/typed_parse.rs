//! Typed s-expression parser for [`ValueLang`] DAGs.
//!
//! Ruler patterns use explicit `(i32.const N)` / `(i64.const N)` forms. Legacy
//! bare integers default to `i32.const`, with parent-op sort coercion for `i64`
//! operands.

use crate::lang::{F32Bits, F64Bits, ValueLang};
use crate::semantics::StackTy;
use crate::value::ValueOp;
use egg::{ENodeOrVar, Id, Pattern, PatternAst, RecExpr, Symbol, Var};

#[derive(Clone, Debug, PartialEq, Eq)]
enum Tok<'a> {
    LParen,
    RParen,
    Atom(&'a str),
}

pub fn parse_typed_sexpr(input: &str) -> Result<RecExpr<ValueLang>, String> {
  let tokens = tokenize(input)?;
  let mut pos = 0;
  let mut expr = RecExpr::default();
  parse_expr(&tokens, &mut pos, &mut expr, None)?;
  if pos != tokens.len() {
    return Err(format!("trailing tokens after parse: {input}"));
  }
  Ok(expr)
}

/// Build an egg [`Pattern`] from a typed s-expression.
///
/// Unlike [`Pattern::from`] on a [`RecExpr`], `?`-prefixed symbols become
/// pattern variables so rewrites match arbitrary locals.
pub fn pattern_from_typed_sexpr(input: &str) -> Result<Pattern<ValueLang>, String> {
  let expr = parse_typed_sexpr(input)?;
  Ok(pattern_from_value_expr(&expr))
}

pub fn pattern_from_value_expr(expr: &RecExpr<ValueLang>) -> Pattern<ValueLang> {
  let ast: PatternAst<ValueLang> = expr
    .as_ref()
    .iter()
    .map(|node| match node {
      ValueLang::Symbol(sym) => {
        let var: Var = sym
          .to_string()
          .parse()
          .expect("pattern symbol should parse as Var");
        ENodeOrVar::Var(var)
      }
      other => ENodeOrVar::ENode(other.clone()),
    })
    .collect();
  Pattern::from(ast)
}

fn tokenize(input: &str) -> Result<Vec<Tok<'_>>, String> {
  let mut out = Vec::new();
  let bytes = input.as_bytes();
  let mut i = 0;
  while i < bytes.len() {
    let c = bytes[i] as char;
    if c.is_whitespace() {
      i += 1;
      continue;
    }
    match c {
      '(' => {
        out.push(Tok::LParen);
        i += 1;
      }
      ')' => {
        out.push(Tok::RParen);
        i += 1;
      }
      _ => {
        let start = i;
        i += 1;
        while i < bytes.len() {
          let ch = bytes[i] as char;
          if ch.is_whitespace() || ch == '(' || ch == ')' {
            break;
          }
          i += 1;
        }
        out.push(Tok::Atom(&input[start..i]));
      }
    }
  }
  Ok(out)
}

fn parse_expr(
  tokens: &[Tok<'_>],
  pos: &mut usize,
  expr: &mut RecExpr<ValueLang>,
  expected: Option<StackTy>,
) -> Result<Id, String> {
  match tokens.get(*pos) {
    Some(Tok::LParen) => {
      *pos += 1;
      let head = match tokens.get(*pos) {
        Some(Tok::Atom(s)) => *s,
        _ => return Err("expected head symbol".to_string()),
      };
      *pos += 1;
      if head == "i32.const" {
        let v = parse_const_atom(tokens, pos, StackTy::I32)?;
        expect(tokens, pos, Tok::RParen)?;
        return Ok(expr.add(ValueLang::I32Const(v as i32)));
      }
      if head == "i64.const" {
        let v = parse_const_atom(tokens, pos, StackTy::I64)?;
        expect(tokens, pos, Tok::RParen)?;
        return Ok(expr.add(ValueLang::I64Const(v)));
      }
      let (op, _) = ValueOp::all()
        .iter()
        .copied()
        .find(|op| op.pattern_name() == head)
        .map(|op| (op, ()))
        .ok_or_else(|| format!("unknown operator head: {head}"))?;
      let pops = op.pops();
      let mut kids = Vec::with_capacity(pops.len());
      for &ty in pops {
        kids.push(parse_expr(tokens, pos, expr, Some(ty))?);
      }
      expect(tokens, pos, Tok::RParen)?;
      Ok(expr.add(op.to_enode(&kids)))
    }
    Some(Tok::Atom(s)) => {
      *pos += 1;
      parse_atom(expr, s, expected)
    }
    _ => Err("expected atom or list".to_string()),
  }
}

fn parse_atom(expr: &mut RecExpr<ValueLang>, s: &str, expected: Option<StackTy>) -> Result<Id, String> {
  if s.starts_with('?') {
    return Ok(expr.add(ValueLang::Symbol(
      s.parse::<Symbol>().map_err(|e| e.to_string())?,
    )));
  }
  if let Ok(v) = parse_integer(s) {
    return Ok(match expected {
      Some(StackTy::I64) => expr.add(ValueLang::I64Const(v)),
      Some(StackTy::I32) => expr.add(ValueLang::I32Const(v as i32)),
      Some(StackTy::F32) => {
        expr.add(ValueLang::F32Const(F32Bits(f32::to_bits(parse_float(s)? as f32))))
      }
      Some(StackTy::F64) => {
        expr.add(ValueLang::F64Const(F64Bits(f64::to_bits(parse_float(s)?))))
      }
      None => expr.add(ValueLang::I32Const(v as i32)),
    });
  }
  if let Ok(v) = parse_float(s) {
    return Ok(match expected {
      Some(StackTy::F64) => expr.add(ValueLang::F64Const(F64Bits(f64::to_bits(v)))),
      Some(StackTy::F32) => expr.add(ValueLang::F32Const(F32Bits(f32::to_bits(v as f32)))),
      _ => return Err(format!("float literal {s} in non-float context")),
    });
  }
  Err(format!("invalid atom: {s}"))
}

fn parse_const_atom(tokens: &[Tok<'_>], pos: &mut usize, ty: StackTy) -> Result<i64, String> {
  let s = match tokens.get(*pos) {
    Some(Tok::Atom(s)) => *s,
    _ => return Err("expected constant literal".to_string()),
  };
  *pos += 1;
  match ty {
    StackTy::I32 | StackTy::I64 => parse_integer(s),
    StackTy::F32 => Ok(f32::to_bits(parse_float(s)? as f32) as i32 as i64),
    StackTy::F64 => Ok(f64::to_bits(parse_float(s)?) as i64),
  }
}

fn parse_integer(s: &str) -> Result<i64, String> {
  s.parse::<i64>().map_err(|e| e.to_string())
}

fn parse_float(s: &str) -> Result<f64, String> {
  s.parse::<f64>().map_err(|e| e.to_string())
}

fn expect(tokens: &[Tok<'_>], pos: &mut usize, want: Tok<'_>) -> Result<(), String> {
  match tokens.get(*pos) {
    Some(tok) if *tok == want => {
      *pos += 1;
      Ok(())
    }
    _ => Err(format!("expected {want:?}")),
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::lang::ValueLang;

  #[test]
  fn typed_i64_const_in_add() {
    let e = parse_typed_sexpr("(i64.add (i64.const 0) (i64.mul ?L7 ?L13))").expect("parse");
    assert!(matches!(&e[e.root()], ValueLang::I64Add(_)));
    let left = match &e[e.root()] {
      ValueLang::I64Add([l, _]) => e[*l].clone(),
      _ => panic!("not add"),
    };
    assert!(matches!(left, ValueLang::I64Const(0)));
  }

  #[test]
  fn bare_zero_in_i64_add_becomes_i64_const() {
    let e = parse_typed_sexpr("(i64.add 0 (i64.mul ?L7 ?L13))").expect("parse");
    let left = match &e[e.root()] {
      ValueLang::I64Add([l, _]) => e[*l].clone(),
      _ => panic!("not add"),
    };
    assert!(matches!(left, ValueLang::I64Const(0)));
  }
}
