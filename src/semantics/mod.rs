//! Centralized Wasm instruction semantics: stack types, specs, and synthesis config.

mod types;
mod pure_ops;

pub use types::{InstKind, InstSpec, SemOp, StackTy};
pub use pure_ops::{
    classify_pure_operator, const_stack_ty, inst_kind_from_sem, inst_kind_from_value_op, sat_pure_ops, sem_from_inst_kind, sem_to_value_op, value_op_from_inst_kind, value_op_is_binop, value_op_is_unop,
    value_op_to_sem,
};

use crate::al::{
    NumType, STRAIGHT_LINE_EMBED, Sign, WasmBinOp, WasmRelOp, WasmTestOp, WasmUnOp, al_spec_for,
    derive_inst_spec, derive_rule_binop_spec, derive_rule_local_get_spec,
    derive_rule_local_set_spec, derive_rule_local_tee_spec, derive_rule_relop_spec,
    derive_rule_testop_spec, derive_rule_unop_spec, format_al_pretty, format_rule_binop_pretty,
    format_rule_local_pretty, format_rule_relop_pretty, format_rule_testop_pretty,
    format_rule_unop_pretty,
};
use crate::value::ValueOp;

fn spec_for_pure(v: ValueOp) -> InstSpec {
    let kind = inst_kind_from_value_op(v);
    match v.pops().len() {
        2 => {
            if matches!(
                v,
                ValueOp::I32Eq
                    | ValueOp::I32Ne
                    | ValueOp::I32LtS
                    | ValueOp::I32LeS
                    | ValueOp::I32GtS
                    | ValueOp::I64Eq
                    | ValueOp::I64Ne
                    | ValueOp::I64LtS
                    | ValueOp::I64LeS
                    | ValueOp::I64GtS
                    | ValueOp::F32Eq
                    | ValueOp::F32Ne
                    | ValueOp::F32Lt
                    | ValueOp::F32Le
                    | ValueOp::F32Gt
                    | ValueOp::F32Ge
                    | ValueOp::F64Eq
                    | ValueOp::F64Ne
                    | ValueOp::F64Lt
                    | ValueOp::F64Le
                    | ValueOp::F64Gt
                    | ValueOp::F64Ge
            ) {
                derive_rule_relop_spec(kind)
            } else {
                derive_rule_binop_spec(kind)
            }
        }
        1 => {
            if matches!(v, ValueOp::I32Eqz | ValueOp::I64Eqz) {
                derive_rule_testop_spec(kind)
            } else {
                derive_rule_unop_spec(kind)
            }
        }
        _ => panic!("unexpected pure op arity: {v:?}"),
    }
}

pub fn spec_for(op: &SemOp) -> InstSpec {
    if let Some(v) = sem_to_value_op(op) {
        return spec_for_pure(v);
    }
    match op {
        SemOp::I32Const(_)
        | SemOp::I64Const(_)
        | SemOp::F32Const(_)
        | SemOp::F64Const(_) => {
            let al = al_spec_for(op);
            derive_inst_spec(&al, &STRAIGHT_LINE_EMBED)
        }
        SemOp::LocalGet(x) => derive_rule_local_get_spec(*x),
        SemOp::LocalSet(x) => derive_rule_local_set_spec(*x),
        SemOp::LocalTee(x) => derive_rule_local_tee_spec(*x),
        _ => {
            let al = al_spec_for(op);
            derive_inst_spec(&al, &STRAIGHT_LINE_EMBED)
        }
    }
}

fn binop_wasm(op: &SemOp) -> Option<(NumType, WasmBinOp)> {
    match op {
        SemOp::I32Add => Some((NumType::I32, WasmBinOp::Add)),
        SemOp::I32Sub => Some((NumType::I32, WasmBinOp::Sub)),
        SemOp::I32Mul => Some((NumType::I32, WasmBinOp::Mul)),
        SemOp::I32Shl => Some((NumType::I32, WasmBinOp::Shl)),
        SemOp::I32DivU => Some((NumType::I32, WasmBinOp::Div(Sign::U))),
        SemOp::I32DivS => Some((NumType::I32, WasmBinOp::Div(Sign::S))),
        SemOp::I32RemU => Some((NumType::I32, WasmBinOp::Rem(Sign::U))),
        SemOp::I32RemS => Some((NumType::I32, WasmBinOp::Rem(Sign::S))),
        SemOp::I32And => Some((NumType::I32, WasmBinOp::And)),
        SemOp::I32Or => Some((NumType::I32, WasmBinOp::Or)),
        SemOp::I32Xor => Some((NumType::I32, WasmBinOp::Xor)),
        SemOp::I32ShrU => Some((NumType::I32, WasmBinOp::Shr(Sign::U))),
        SemOp::I32ShrS => Some((NumType::I32, WasmBinOp::Shr(Sign::S))),
        SemOp::I32Rotl => Some((NumType::I32, WasmBinOp::Rotl)),
        SemOp::I32Rotr => Some((NumType::I32, WasmBinOp::Rotr)),
        _ => None,
    }
}

fn relop_wasm(op: &SemOp) -> Option<(NumType, WasmRelOp)> {
    match op {
        SemOp::I32Eq => Some((NumType::I32, WasmRelOp::Eq)),
        SemOp::I32Ne => Some((NumType::I32, WasmRelOp::Ne)),
        SemOp::I32LtS => Some((NumType::I32, WasmRelOp::Lt(Sign::S))),
        SemOp::I32LeS => Some((NumType::I32, WasmRelOp::Le(Sign::S))),
        SemOp::I32GtS => Some((NumType::I32, WasmRelOp::Gt(Sign::S))),
        _ => None,
    }
}

fn testop_wasm(op: &SemOp) -> Option<(NumType, WasmTestOp)> {
    match op {
        SemOp::I32Eqz => Some((NumType::I32, WasmTestOp::Eqz)),
        _ => None,
    }
}

fn unop_wasm(op: &SemOp) -> Option<(NumType, WasmUnOp)> {
    match op {
        SemOp::I32Clz => Some((NumType::I32, WasmUnOp::Clz)),
        SemOp::I32Ctz => Some((NumType::I32, WasmUnOp::Ctz)),
        SemOp::I32Popcnt => Some((NumType::I32, WasmUnOp::Popcnt)),
        _ => None,
    }
}

pub fn concrete_ops() -> Vec<SemOp> {
    let mut ops = vec![
        SemOp::I32Add,
        SemOp::I32Sub,
        SemOp::I32Mul,
        SemOp::I32DivU,
        SemOp::I32DivS,
        SemOp::I32RemU,
        SemOp::I32RemS,
        SemOp::I32Shl,
        SemOp::I32And,
        SemOp::I32Or,
        SemOp::I32Xor,
        SemOp::I32ShrU,
        SemOp::I32ShrS,
        SemOp::I32Rotl,
        SemOp::I32Rotr,
        SemOp::I32Eqz,
        SemOp::I32Clz,
        SemOp::I32Ctz,
        SemOp::I32Popcnt,
    ];
    ops.push(SemOp::I32Const(42));
    ops.push(SemOp::LocalGet(42));
    ops
}

const SYNTHESIS_CONSTS: [i32; 4] = [0, 1, 2, -1];

const SYNTHESIS_I32: [i64; 4] = [0, 1, 2, -1];
const SYNTHESIS_I64: [i64; 4] = [0, 1, 2, -1];

const fn f32_bits_carrier(bits: u32) -> i64 {
    bits as i32 as i64
}

const fn f64_bits_carrier(bits: u64) -> i64 {
    bits as i64
}

const SYNTHESIS_F32: [i64; 4] = [
    f32_bits_carrier(0),
    f32_bits_carrier(f32::to_bits(1.0)),
    f32_bits_carrier(f32::to_bits(-1.0)),
    f32_bits_carrier(f32::to_bits(2.0)),
];
const SYNTHESIS_F64: [i64; 4] = [
    f64_bits_carrier(0),
    f64_bits_carrier(f64::to_bits(1.0)),
    f64_bits_carrier(f64::to_bits(-1.0)),
    f64_bits_carrier(f64::to_bits(2.0)),
];

pub fn synthesis_constants() -> &'static [i32] {
    &SYNTHESIS_CONSTS
}

/// Synthesis leaf constants as [`ValueExpr`] trees (all four stack types).
pub fn synthesis_const_exprs() -> Vec<crate::sym::ValueExpr> {
    use crate::lang::{F32Bits, F64Bits, ValueLang};
    use crate::value::parse_value_expr;
    use egg::RecExpr;

    let mut out = Vec::new();
    for &c in synthesis_constants() {
        out.push(parse_value_expr(&c.to_string()));
    }
    for ty in [
        StackTy::I32,
        StackTy::I64,
        StackTy::F32,
        StackTy::F64,
    ] {
        for &v in synthesis_const_values(ty) {
            match ty {
                StackTy::I32 => out.push(parse_value_expr(&v.to_string())),
                StackTy::I64 => {
                    let mut e = RecExpr::default();
                    e.add(ValueLang::I64Const(v));
                    out.push(e);
                }
                StackTy::F32 => {
                    let mut e = RecExpr::default();
                    e.add(ValueLang::F32Const(F32Bits(v as u32)));
                    out.push(e);
                }
                StackTy::F64 => {
                    let mut e = RecExpr::default();
                    e.add(ValueLang::F64Const(F64Bits(v as u64)));
                    out.push(e);
                }
            }
        }
    }
    out
}

/// Synthesis leaf constants for `ty`, as the `i64` carrier stored in [`ValueAst::Const`].
pub fn synthesis_const_values(ty: StackTy) -> &'static [i64] {
    match ty {
        StackTy::I32 => &SYNTHESIS_I32,
        StackTy::I64 => &SYNTHESIS_I64,
        StackTy::F32 => &SYNTHESIS_F32,
        StackTy::F64 => &SYNTHESIS_F64,
    }
}

pub fn print_semantics_table() {
    println!("=== Wasm instruction semantics ===\n");
    for op in concrete_ops() {
        let spec = spec_for(&op);
        let trap = if spec.can_trap { "yes" } else { "no" };
        println!(
            "{}  pop={} push={} trap={}",
            op.name(),
            spec.pops.len(),
            spec.pushes.len(),
            trap,
        );
        for line in match binop_wasm(&op) {
            Some((nt, binop)) => format_rule_binop_pretty(nt, binop),
            None if relop_wasm(&op).is_some() => {
                let (nt, relop) = relop_wasm(&op).expect("relop");
                format_rule_relop_pretty(nt, relop)
            }
            None if testop_wasm(&op).is_some() => {
                let (nt, testop) = testop_wasm(&op).expect("testop");
                format_rule_testop_pretty(nt, testop)
            }
            None if unop_wasm(&op).is_some() => {
                let (nt, unop) = unop_wasm(&op).expect("unop");
                format_rule_unop_pretty(nt, unop)
            }
            None if op.is_effectful() => format_rule_local_pretty(&op),
            None => format_al_pretty(&al_spec_for(&op)),
        }
        .lines()
        {
            println!("  {line}");
        }
        println!();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn synthesis_inputs_has_no_empty_stack() {
        let inputs: Vec<Vec<StackTy>> = crate::value::enumerate_signatures(3)
            .into_iter()
            .filter(|sig| crate::value::is_reachable(sig))
            .map(|sig| sig.inputs)
            .collect();
        assert!(inputs.iter().all(|input| !input.is_empty()));
    }

    #[test]
    fn synthesis_const_values_per_type() {
        assert_eq!(synthesis_const_values(StackTy::I32), &[0, 1, 2, -1]);
        assert_eq!(
            synthesis_const_values(StackTy::F32)[1],
            f32::to_bits(1.0) as i32 as i64
        );
        assert_eq!(
            synthesis_const_values(StackTy::F64)[2],
            f64::to_bits(-1.0) as i64
        );
    }
}
