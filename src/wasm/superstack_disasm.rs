//! SuperStack-compatible instruction disassembly for benchmark CSV rows.

use crate::semantics::SemOp;
use std::collections::HashMap;
use wasmparser::Operator;

fn memarg_args(m: &wasmparser::MemArg) -> String {
    format!("{},{}", m.align, m.offset)
}

/// SuperStack `str(Instruction)` / CSV token for a wasm operator.
pub fn operator_disasm(op: &Operator<'_>) -> String {
    match op {
        Operator::Drop => "drop".to_string(),
        Operator::I32Const { value } => format!("i32.const[{value}]"),
        Operator::I64Const { value } => format!("i64.const[{value}]"),
        Operator::F32Const { value } => format!("f32.const[{}]", value.bits()),
        Operator::F64Const { value } => format!("f64.const[{}]", value.bits()),
        Operator::LocalGet { local_index } => format!("local.get[local_index({local_index})]"),
        Operator::LocalSet { local_index } => format!("local.set[local_index({local_index})]"),
        Operator::LocalTee { local_index } => format!("local.tee[local_index({local_index})]"),
        Operator::GlobalGet { global_index } => {
            format!("global.get[global_index({global_index})]")
        }
        Operator::GlobalSet { global_index } => {
            format!("global.set[global_index({global_index})]")
        }
        Operator::Call { function_index } => format!("call[function_index({function_index})]"),
        Operator::I32Load { memarg, .. } => format!("i32.load[{}]", memarg_args(memarg)),
        Operator::I64Load { memarg, .. } => format!("i64.load[{}]", memarg_args(memarg)),
        Operator::F32Load { memarg, .. } => format!("f32.load[{}]", memarg_args(memarg)),
        Operator::F64Load { memarg, .. } => format!("f64.load[{}]", memarg_args(memarg)),
        Operator::I32Load8S { memarg, .. } => format!("i32.load8_s[{}]", memarg_args(memarg)),
        Operator::I32Load8U { memarg, .. } => format!("i32.load8_u[{}]", memarg_args(memarg)),
        Operator::I32Load16S { memarg, .. } => format!("i32.load16_s[{}]", memarg_args(memarg)),
        Operator::I32Load16U { memarg, .. } => format!("i32.load16_u[{}]", memarg_args(memarg)),
        Operator::I64Load8S { memarg, .. } => format!("i64.load8_s[{}]", memarg_args(memarg)),
        Operator::I64Load8U { memarg, .. } => format!("i64.load8_u[{}]", memarg_args(memarg)),
        Operator::I64Load16S { memarg, .. } => format!("i64.load16_s[{}]", memarg_args(memarg)),
        Operator::I64Load16U { memarg, .. } => format!("i64.load16_u[{}]", memarg_args(memarg)),
        Operator::I64Load32S { memarg, .. } => format!("i64.load32_s[{}]", memarg_args(memarg)),
        Operator::I64Load32U { memarg, .. } => format!("i64.load32_u[{}]", memarg_args(memarg)),
        Operator::I32Store { memarg, .. } => format!("i32.store[{}]", memarg_args(memarg)),
        Operator::I64Store { memarg, .. } => format!("i64.store[{}]", memarg_args(memarg)),
        Operator::F32Store { memarg, .. } => format!("f32.store[{}]", memarg_args(memarg)),
        Operator::F64Store { memarg, .. } => format!("f64.store[{}]", memarg_args(memarg)),
        Operator::I32Store8 { memarg, .. } => format!("i32.store8[{}]", memarg_args(memarg)),
        Operator::I32Store16 { memarg, .. } => format!("i32.store16[{}]", memarg_args(memarg)),
        Operator::I64Store8 { memarg, .. } => format!("i64.store8[{}]", memarg_args(memarg)),
        Operator::I64Store16 { memarg, .. } => format!("i64.store16[{}]", memarg_args(memarg)),
        Operator::I64Store32 { memarg, .. } => format!("i64.store32[{}]", memarg_args(memarg)),
        Operator::MemorySize { mem } => format!("memory.size[{mem}]"),
        Operator::MemoryGrow { mem } => format!("memory.grow[{mem}]"),
        Operator::I32Add => "i32.add".to_string(),
        Operator::I32Sub => "i32.sub".to_string(),
        Operator::I32Mul => "i32.mul".to_string(),
        Operator::I32DivU => "i32.div_u".to_string(),
        Operator::I32DivS => "i32.div_s".to_string(),
        Operator::I32RemU => "i32.rem_u".to_string(),
        Operator::I32RemS => "i32.rem_s".to_string(),
        Operator::I32And => "i32.and".to_string(),
        Operator::I32Or => "i32.or".to_string(),
        Operator::I32Xor => "i32.xor".to_string(),
        Operator::I32Shl => "i32.shl".to_string(),
        Operator::I32ShrU => "i32.shr_u".to_string(),
        Operator::I32ShrS => "i32.shr_s".to_string(),
        Operator::I32Rotl => "i32.rotl".to_string(),
        Operator::I32Rotr => "i32.rotr".to_string(),
        Operator::I32Eq => "i32.eq".to_string(),
        Operator::I32Ne => "i32.ne".to_string(),
        Operator::I32LtS => "i32.lt_s".to_string(),
        Operator::I32LtU => "i32.lt_u".to_string(),
        Operator::I32LeS => "i32.le_s".to_string(),
        Operator::I32LeU => "i32.le_u".to_string(),
        Operator::I32GtS => "i32.gt_s".to_string(),
        Operator::I32GtU => "i32.gt_u".to_string(),
        Operator::I32GeS => "i32.ge_s".to_string(),
        Operator::I32GeU => "i32.ge_u".to_string(),
        Operator::I32Eqz => "i32.eqz".to_string(),
        Operator::I32Clz => "i32.clz".to_string(),
        Operator::I32Ctz => "i32.ctz".to_string(),
        Operator::I32Popcnt => "i32.popcnt".to_string(),
        Operator::I32WrapI64 => "i32.wrap_i64".to_string(),
        Operator::I64ExtendI32S => "i64.extend_i32_s".to_string(),
        Operator::I64ExtendI32U => "i64.extend_i32_u".to_string(),
        Operator::I64Add => "i64.add".to_string(),
        Operator::I64Sub => "i64.sub".to_string(),
        Operator::I64Mul => "i64.mul".to_string(),
        Operator::I64And => "i64.and".to_string(),
        Operator::I64Or => "i64.or".to_string(),
        Operator::I64Xor => "i64.xor".to_string(),
        Operator::I64Shl => "i64.shl".to_string(),
        Operator::I64ShrU => "i64.shr_u".to_string(),
        Operator::I64ShrS => "i64.shr_s".to_string(),
        Operator::I64Eq => "i64.eq".to_string(),
        Operator::I64Ne => "i64.ne".to_string(),
        Operator::I64LtS => "i64.lt_s".to_string(),
        Operator::I64LtU => "i64.lt_u".to_string(),
        Operator::I64LeS => "i64.le_s".to_string(),
        Operator::I64LeU => "i64.le_u".to_string(),
        Operator::I64GtS => "i64.gt_s".to_string(),
        Operator::I64GtU => "i64.gt_u".to_string(),
        Operator::I64GeS => "i64.ge_s".to_string(),
        Operator::I64GeU => "i64.ge_u".to_string(),
        Operator::I64Eqz => "i64.eqz".to_string(),
        other => format!("{other:?}"),
    }
}

/// One SuperStack-style instruction token from a `SemOp` and optional captured disasm.
pub fn format_op_superstack(op: &SemOp, disasm_by_id: &HashMap<u32, String>) -> String {
    if let Some(id) = op.opaque_id() {
        if let Some(d) = disasm_by_id.get(&id) {
            return d.clone();
        }
    }
    match op {
        SemOp::Drop => "drop".to_string(),
        SemOp::I32Const(n) => format!("i32.const[{n}]"),
        SemOp::I32Add => "i32.add".to_string(),
        SemOp::I32Sub => "i32.sub".to_string(),
        SemOp::I32Mul => "i32.mul".to_string(),
        SemOp::I32DivU => "i32.div_u".to_string(),
        SemOp::I32DivS => "i32.div_s".to_string(),
        SemOp::I32RemU => "i32.rem_u".to_string(),
        SemOp::I32RemS => "i32.rem_s".to_string(),
        SemOp::I32Shl => "i32.shl".to_string(),
        SemOp::I32And => "i32.and".to_string(),
        SemOp::I32Or => "i32.or".to_string(),
        SemOp::I32Xor => "i32.xor".to_string(),
        SemOp::I32ShrU => "i32.shr_u".to_string(),
        SemOp::I32ShrS => "i32.shr_s".to_string(),
        SemOp::I32Rotl => "i32.rotl".to_string(),
        SemOp::I32Rotr => "i32.rotr".to_string(),
        SemOp::I32Eq => "i32.eq".to_string(),
        SemOp::I32Ne => "i32.ne".to_string(),
        SemOp::I32LtS => "i32.lt_s".to_string(),
        SemOp::I32LeS => "i32.le_s".to_string(),
        SemOp::I32GtS => "i32.gt_s".to_string(),
        SemOp::I32Eqz => "i32.eqz".to_string(),
        SemOp::I32Clz => "i32.clz".to_string(),
        SemOp::I32Ctz => "i32.ctz".to_string(),
        SemOp::I32Popcnt => "i32.popcnt".to_string(),
        SemOp::LocalGet(x) => format!("local.get[local_index({x})]"),
        SemOp::LocalSet(x) => format!("local.set[local_index({x})]"),
        SemOp::LocalTee(x) => format!("local.tee[local_index({x})]"),
        SemOp::Call { func_index, .. } => format!("call[function_index({func_index})]"),
        SemOp::GlobalGet { global_index, .. } => {
            format!("global.get[global_index({global_index})]")
        }
        SemOp::GlobalSet { global_index, .. } => {
            format!("global.set[global_index({global_index})]")
        }
        SemOp::I32Load { mem, offset, .. } => format!("i32.load[{mem},{offset}]"),
        SemOp::I32Store { mem, offset, .. } => format!("i32.store[{mem},{offset}]"),
        SemOp::Opaque { id, .. } => format!("opaque {id}"),
    }
}

/// Space-separated SuperStack `statistics.csv` instruction list.
pub fn format_ops_superstack_csv(ops: &[SemOp], disasm_by_id: &HashMap<u32, String>) -> String {
    ops.iter()
        .map(|op| format_op_superstack(op, disasm_by_id))
        .collect::<Vec<_>>()
        .join(" ")
}
