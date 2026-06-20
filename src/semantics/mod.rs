//! Centralized Wasm instruction semantics: stack types, specs, and synthesis config.

mod types;

pub use types::{InstKind, InstSpec, SemOp, StackTy};

use crate::al::{
    NumType, STRAIGHT_LINE_EMBED, Sign, WasmBinOp, WasmRelOp, WasmTestOp, WasmUnOp, al_spec_for,
    derive_inst_spec, derive_rule_binop_spec, derive_rule_local_get_spec,
    derive_rule_local_set_spec, derive_rule_local_tee_spec, derive_rule_relop_spec,
    derive_rule_testop_spec, derive_rule_unop_spec, format_al_pretty, format_rule_binop_pretty,
    format_rule_local_pretty, format_rule_relop_pretty, format_rule_testop_pretty,
    format_rule_unop_pretty,
};

pub fn spec_for(op: &SemOp) -> InstSpec {
    match op {
        SemOp::I32Add => derive_rule_binop_spec(InstKind::I32Add),
        SemOp::I32Sub => derive_rule_binop_spec(InstKind::I32Sub),
        SemOp::I32Mul => derive_rule_binop_spec(InstKind::I32Mul),
        SemOp::I32Shl => derive_rule_binop_spec(InstKind::I32Shl),
        SemOp::I32DivU => derive_rule_binop_spec(InstKind::I32DivU),
        SemOp::I32DivS => derive_rule_binop_spec(InstKind::I32DivS),
        SemOp::I32Eq => derive_rule_relop_spec(InstKind::I32Eq),
        SemOp::I32Ne => derive_rule_relop_spec(InstKind::I32Ne),
        SemOp::I32LtS => derive_rule_relop_spec(InstKind::I32LtS),
        SemOp::I32LeS => derive_rule_relop_spec(InstKind::I32LeS),
        SemOp::I32GtS => derive_rule_relop_spec(InstKind::I32GtS),
        SemOp::I32Eqz => derive_rule_testop_spec(InstKind::I32Eqz),
        SemOp::I32Clz => derive_rule_unop_spec(InstKind::I32Clz),
        SemOp::I32Ctz => derive_rule_unop_spec(InstKind::I32Ctz),
        SemOp::I32Popcnt => derive_rule_unop_spec(InstKind::I32Popcnt),
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
        SemOp::I32Mul,
        SemOp::I32DivU,
        SemOp::I32DivS,
        SemOp::I32Shl,
        SemOp::I32Eqz,
        SemOp::I32Clz,
        SemOp::I32Ctz,
        SemOp::I32Popcnt,
    ];
    for c in [0, 1, 2, 3, 4, 8, 16, -1, i32::MIN, i32::MAX] {
        ops.push(SemOp::I32Const(c));
    }
    for x in 0..3 {
        ops.push(SemOp::LocalGet(x));
        ops.push(SemOp::LocalSet(x));
        ops.push(SemOp::LocalTee(x));
    }
    ops
}

const SYNTHESIS_CONSTS: [i32; 6] = [0, 1, 2, -1, i32::MIN, i32::MAX];

pub fn synthesis_constants() -> &'static [i32] {
    &SYNTHESIS_CONSTS
}

pub fn synthesis_inputs() -> Vec<Vec<StackTy>> {
    (1..=3).map(|h| vec![StackTy::I32; h]).collect()
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
        assert!(synthesis_inputs().iter().all(|input| !input.is_empty()));
    }
}
