//! Static stack-depth analysis for Wasm operators and SemOps.

use crate::semantics::SemOp;
use wasmparser::{FuncType, Operator};

/// Module-level type context for resolving `call` / `call_indirect` stack effects.
#[derive(Clone, Copy, Debug)]
pub struct ModuleStackTypes<'a> {
    /// Function index → type (imports + defined functions).
    pub module_func_types: &'a [FuncType],
    /// Type section entries (used by `call_indirect`'s type index).
    pub type_section: &'a [FuncType],
}

/// `(init_stack_depth, max_stack_depth)` for a straight-line sequence.
pub fn stack_bounds_ops(ops: &[SemOp]) -> (usize, usize) {
    let mut current = 0usize;
    let mut init = 0usize;
    let mut max = 0usize;
    for op in ops {
        let (pop, push) = semop_stack_effect(op);
        if pop > current {
            let diff = pop - current;
            init += diff;
            current = current + diff - pop + push;
        } else {
            current = current - pop + push;
        }
        max = max.max(current);
    }
    max = max.max(init);
    (init, max)
}

pub fn stack_bounds_operators(
    ops: &[Operator<'_>],
    types: ModuleStackTypes<'_>,
) -> (usize, usize) {
    let mut current = 0usize;
    let mut init = 0usize;
    let mut max = 0usize;
    for op in ops {
        if let Some((pop, push)) = operator_stack_effect_with_types(op, types) {
            if pop > current {
                let diff = pop - current;
                init += diff;
                current = current + diff - pop + push;
            } else {
                current = current - pop + push;
            }
            max = max.max(current);
        }
    }
    max = max.max(init);
    (init, max)
}

pub fn semop_stack_effect(op: &SemOp) -> (usize, usize) {
    match op {
        SemOp::I32Const(_) => (0, 1),
        SemOp::I32Add
        | SemOp::I32Sub
        | SemOp::I32Mul
        |         SemOp::I32DivU
        | SemOp::I32DivS
        | SemOp::I32RemU
        | SemOp::I32RemS
        | SemOp::I32Shl
        | SemOp::I32And
        | SemOp::I32Or
        | SemOp::I32Xor
        | SemOp::I32ShrU
        | SemOp::I32ShrS
        | SemOp::I32Rotl
        | SemOp::I32Rotr
        | SemOp::I32Eq
        | SemOp::I32Ne
        | SemOp::I32LtS
        | SemOp::I32LeS
        | SemOp::I32GtS => (2, 1),
        SemOp::I32Eqz => (1, 1),
        SemOp::I32Clz | SemOp::I32Ctz | SemOp::I32Popcnt => (1, 1),
        SemOp::LocalGet(_) => (0, 1),
        SemOp::LocalSet(_) => (1, 0),
        SemOp::LocalTee(_) => (1, 1),
        SemOp::I32Load { .. } => (1, 1),
        SemOp::I32Store { .. } => (2, 0),
        SemOp::Call { pops, pushes, .. } => (*pops as usize, *pushes as usize),
        SemOp::GlobalGet { .. } => (0, 1),
        SemOp::GlobalSet { .. } => (1, 0),
        SemOp::Opaque { pops, pushes, .. } => (*pops as usize, *pushes as usize),
    }
}

/// Whether a wasm operator writes memory/globals (storage boundary), excluding `call`.
pub fn operator_is_storage(op: &Operator<'_>) -> bool {
    matches!(
        op,
        Operator::I32Store { .. }
            | Operator::I32Store8 { .. }
            | Operator::I32Store16 { .. }
            | Operator::I64Store { .. }
            | Operator::I64Store8 { .. }
            | Operator::I64Store16 { .. }
            | Operator::I64Store32 { .. }
            | Operator::F32Store { .. }
            | Operator::F64Store { .. }
            | Operator::GlobalSet { .. }
    )
}

pub fn operator_stack_effect_with_types(
    op: &Operator<'_>,
    types: ModuleStackTypes<'_>,
) -> Option<(usize, usize)> {
    if let Operator::Call { function_index } = op {
        let ft = types.module_func_types.get(*function_index as usize)?;
        return Some((ft.params().len(), ft.results().len()));
    }
    if let Operator::CallIndirect { type_index, .. } = op {
        let ft = types.type_section.get(*type_index as usize)?;
        return Some((1 + ft.params().len(), ft.results().len()));
    }
    operator_stack_effect(op)
}

pub fn operator_stack_effect(op: &Operator<'_>) -> Option<(usize, usize)> {
    Some(match op {
        Operator::I32Const { .. }
        | Operator::I64Const { .. }
        | Operator::F32Const { .. }
        | Operator::F64Const { .. } => (0, 1),
        Operator::I32Add
        | Operator::I32Sub
        | Operator::I32Mul
        | Operator::I32DivU
        | Operator::I32DivS
        | Operator::I32RemU
        | Operator::I32RemS
        | Operator::I32Shl
        | Operator::I32And
        | Operator::I32Or
        | Operator::I32Xor
        | Operator::I32ShrU
        | Operator::I32ShrS
        | Operator::I32Rotl
        | Operator::I32Rotr
        | Operator::I32Eq
        | Operator::I32Ne
        |         Operator::I32LtS
        | Operator::I32LtU
        | Operator::I32LeS
        | Operator::I32LeU
        | Operator::I32GtS
        | Operator::I32GtU
        | Operator::I32GeS
        | Operator::I32GeU
        | Operator::I64Add
        | Operator::I64Sub
        | Operator::I64Mul
        | Operator::I64DivU
        | Operator::I64DivS
        | Operator::I64RemU
        | Operator::I64RemS
        | Operator::I64And
        | Operator::I64Or
        | Operator::I64Xor
        | Operator::I64Shl
        | Operator::I64ShrU
        | Operator::I64ShrS
        | Operator::I64Rotl
        | Operator::I64Rotr
        | Operator::I64Eq
        | Operator::I64Ne
        | Operator::I64LtS
        | Operator::I64LtU
        | Operator::I64LeS
        | Operator::I64LeU
        | Operator::I64GtS
        | Operator::I64GtU
        | Operator::I64GeS
        | Operator::I64GeU
        | Operator::F32Add
        | Operator::F32Sub
        | Operator::F32Mul
        | Operator::F32Div
        | Operator::F32Min
        | Operator::F32Max
        | Operator::F32Copysign
        | Operator::F32Eq
        | Operator::F32Ne
        | Operator::F32Lt
        | Operator::F32Le
        | Operator::F32Gt
        | Operator::F32Ge
        | Operator::F64Add
        | Operator::F64Sub
        | Operator::F64Mul
        | Operator::F64Div
        | Operator::F64Min
        | Operator::F64Max
        | Operator::F64Copysign
        | Operator::F64Eq
        | Operator::F64Ne
        | Operator::F64Lt
        | Operator::F64Le
        | Operator::F64Gt
        | Operator::F64Ge => (2, 1),
        Operator::I32Eqz
        | Operator::I32Clz
        | Operator::I32Ctz
        | Operator::I32Popcnt
        | Operator::I64Eqz
        | Operator::I64Clz
        | Operator::I64Ctz
        | Operator::I64Popcnt
        | Operator::F32Abs
        | Operator::F32Neg
        | Operator::F32Ceil
        | Operator::F32Floor
        | Operator::F32Trunc
        | Operator::F32Nearest
        | Operator::F32Sqrt
        | Operator::F64Abs
        | Operator::F64Neg
        | Operator::F64Ceil
        | Operator::F64Floor
        | Operator::F64Trunc
        | Operator::F64Nearest
        | Operator::F64Sqrt
        | Operator::I32WrapI64
        | Operator::I64ExtendI32S
        | Operator::I64ExtendI32U
        | Operator::I32Extend8S
        | Operator::I32Extend16S
        | Operator::I64Extend8S
        | Operator::I64Extend16S
        | Operator::I64Extend32S
        | Operator::F32ConvertI32S
        | Operator::F32ConvertI32U
        | Operator::F32ConvertI64S
        | Operator::F32ConvertI64U
        | Operator::F64ConvertI32S
        | Operator::F64ConvertI32U
        | Operator::F64ConvertI64S
        | Operator::F64ConvertI64U
        | Operator::I32TruncF32S
        | Operator::I32TruncF32U
        | Operator::I32TruncF64S
        | Operator::I32TruncF64U
        | Operator::I64TruncF32S
        | Operator::I64TruncF32U
        | Operator::I64TruncF64S
        | Operator::I64TruncF64U
        | Operator::F32DemoteF64
        | Operator::F64PromoteF32
        | Operator::I32ReinterpretF32
        | Operator::I64ReinterpretF64
        | Operator::F32ReinterpretI32
        | Operator::F64ReinterpretI64 => (1, 1),
        Operator::LocalGet { .. } => (0, 1),
        Operator::LocalSet { .. } => (1, 0),
        Operator::LocalTee { .. } => (1, 1),
        Operator::Drop => (1, 0),
        Operator::Select => (3, 1),
        Operator::MemorySize { .. } => (0, 1),
        Operator::MemoryGrow { .. } => (1, 1),
        Operator::I32Load { .. }
        | Operator::I32Load8S { .. }
        | Operator::I32Load8U { .. }
        | Operator::I32Load16S { .. }
        | Operator::I32Load16U { .. }
        | Operator::I64Load { .. }
        | Operator::I64Load8S { .. }
        | Operator::I64Load8U { .. }
        | Operator::I64Load16S { .. }
        | Operator::I64Load16U { .. }
        | Operator::I64Load32S { .. }
        | Operator::I64Load32U { .. }
        | Operator::F32Load { .. }
        | Operator::F64Load { .. } => (1, 1),
        Operator::I32Store { .. }
        | Operator::I32Store8 { .. }
        | Operator::I32Store16 { .. }
        | Operator::I64Store { .. }
        | Operator::I64Store8 { .. }
        | Operator::I64Store16 { .. }
        | Operator::I64Store32 { .. }
        | Operator::F32Store { .. }
        | Operator::F64Store { .. } => (2, 0),
        Operator::GlobalGet { .. } => (0, 1),
        Operator::GlobalSet { .. } => (1, 0),
        Operator::Return => (0, 0),
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use wasmparser::ValType;

    fn func_type(params: &[ValType], results: &[ValType]) -> FuncType {
        FuncType::new(params.iter().copied(), results.iter().copied())
    }

    #[test]
    fn call_stack_effect_uses_function_type() {
        let module_func_types = vec![func_type(&[ValType::I32; 5], &[])];
        let types = ModuleStackTypes {
            module_func_types: &module_func_types,
            type_section: &module_func_types,
        };
        let op = Operator::Call { function_index: 0 };
        assert_eq!(
            operator_stack_effect_with_types(&op, types),
            Some((5, 0))
        );
    }

    #[test]
    fn call_indirect_includes_table_index_on_stack() {
        let type_section = vec![func_type(&[ValType::I32, ValType::I64], &[ValType::F32])];
        let types = ModuleStackTypes {
            module_func_types: &[],
            type_section: &type_section,
        };
        let op = Operator::CallIndirect {
            type_index: 0,
            table_index: 0,
        };
        assert_eq!(
            operator_stack_effect_with_types(&op, types),
            Some((3, 1))
        );
    }

    #[test]
    fn unsigned_comparisons_count_toward_stack_bounds() {
        let types = ModuleStackTypes {
            module_func_types: &[],
            type_section: &[],
        };
        let ops = [
            Operator::I32Const { value: 0 },
            Operator::I32Const { value: 1 },
            Operator::I32LtU,
        ];
        let (init, max) = stack_bounds_operators(&ops, types);
        assert_eq!(init, 0);
        assert_eq!(max, 2);
    }
}
