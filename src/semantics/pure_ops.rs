//! Pure (side-effect-free) Wasm arithmetic: `ValueOp` ↔ `SemOp` ↔ `wasmparser::Operator`.

use crate::semantics::{InstKind, SemOp, StackTy};
use crate::value::ValueOp;
use wasmparser::Operator;

/// Map a synthesis [`ValueOp`] to [`SemOp`].
pub fn value_op_to_sem(op: ValueOp) -> SemOp {
    SemOp::Pure(op)
}

/// Recover a [`ValueOp`] from a pure [`SemOp`], including legacy i32 variants.
pub fn sem_to_value_op(op: &SemOp) -> Option<ValueOp> {
    match op {
        SemOp::Pure(v) => Some(*v),
        SemOp::I32Add => Some(ValueOp::I32Add),
        SemOp::I32Sub => Some(ValueOp::I32Sub),
        SemOp::I32Mul => Some(ValueOp::I32Mul),
        SemOp::I32DivU => Some(ValueOp::I32DivU),
        SemOp::I32DivS => Some(ValueOp::I32DivS),
        SemOp::I32RemU => Some(ValueOp::I32RemU),
        SemOp::I32RemS => Some(ValueOp::I32RemS),
        SemOp::I32Shl => Some(ValueOp::I32Shl),
        SemOp::I32And => Some(ValueOp::I32And),
        SemOp::I32Or => Some(ValueOp::I32Or),
        SemOp::I32Xor => Some(ValueOp::I32Xor),
        SemOp::I32ShrU => Some(ValueOp::I32ShrU),
        SemOp::I32ShrS => Some(ValueOp::I32ShrS),
        SemOp::I32Rotl => Some(ValueOp::I32Rotl),
        SemOp::I32Rotr => Some(ValueOp::I32Rotr),
        SemOp::I32Eq => Some(ValueOp::I32Eq),
        SemOp::I32Ne => Some(ValueOp::I32Ne),
        SemOp::I32LtS => Some(ValueOp::I32LtS),
        SemOp::I32LeS => Some(ValueOp::I32LeS),
        SemOp::I32GtS => Some(ValueOp::I32GtS),
        SemOp::I32Eqz => Some(ValueOp::I32Eqz),
        SemOp::I32Clz => Some(ValueOp::I32Clz),
        SemOp::I32Ctz => Some(ValueOp::I32Ctz),
        SemOp::I32Popcnt => Some(ValueOp::I32Popcnt),
        _ => None,
    }
}

pub fn inst_kind_from_value_op(op: ValueOp) -> InstKind {
    InstKind::Pure(op)
}

pub fn value_op_from_inst_kind(kind: InstKind) -> Option<ValueOp> {
    match kind {
        InstKind::Pure(v) => Some(v),
        _ => None,
    }
}

pub fn inst_kind_from_sem(op: &SemOp) -> Option<InstKind> {
    sem_to_value_op(op).map(inst_kind_from_value_op)
}

pub fn sem_from_inst_kind(kind: InstKind) -> Option<SemOp> {
    value_op_from_inst_kind(kind).map(value_op_to_sem)
}

/// Classify a Wasm operator as a supported pure instruction.
pub fn classify_pure_operator(op: &Operator<'_>) -> Option<SemOp> {
    use Operator::*;
    let v = match op {
        I32Add => ValueOp::I32Add,
        I32Sub => ValueOp::I32Sub,
        I32Mul => ValueOp::I32Mul,
        I32DivU => ValueOp::I32DivU,
        I32DivS => ValueOp::I32DivS,
        I32RemU => ValueOp::I32RemU,
        I32RemS => ValueOp::I32RemS,
        I32Shl => ValueOp::I32Shl,
        I32And => ValueOp::I32And,
        I32Or => ValueOp::I32Or,
        I32Xor => ValueOp::I32Xor,
        I32ShrU => ValueOp::I32ShrU,
        I32ShrS => ValueOp::I32ShrS,
        I32Rotl => ValueOp::I32Rotl,
        I32Rotr => ValueOp::I32Rotr,
        I32Eq => ValueOp::I32Eq,
        I32Ne => ValueOp::I32Ne,
        I32LtS => ValueOp::I32LtS,
        I32LeS => ValueOp::I32LeS,
        I32GtS => ValueOp::I32GtS,
        I32Eqz => ValueOp::I32Eqz,
        I32Clz => ValueOp::I32Clz,
        I32Ctz => ValueOp::I32Ctz,
        I32Popcnt => ValueOp::I32Popcnt,
        I64Add => ValueOp::I64Add,
        I64Sub => ValueOp::I64Sub,
        I64Mul => ValueOp::I64Mul,
        I64DivU => ValueOp::I64DivU,
        I64DivS => ValueOp::I64DivS,
        I64RemU => ValueOp::I64RemU,
        I64RemS => ValueOp::I64RemS,
        I64Shl => ValueOp::I64Shl,
        I64And => ValueOp::I64And,
        I64Or => ValueOp::I64Or,
        I64Xor => ValueOp::I64Xor,
        I64ShrU => ValueOp::I64ShrU,
        I64ShrS => ValueOp::I64ShrS,
        I64Rotl => ValueOp::I64Rotl,
        I64Rotr => ValueOp::I64Rotr,
        I64Eq => ValueOp::I64Eq,
        I64Ne => ValueOp::I64Ne,
        I64LtS => ValueOp::I64LtS,
        I64LeS => ValueOp::I64LeS,
        I64GtS => ValueOp::I64GtS,
        I64Eqz => ValueOp::I64Eqz,
        I64Clz => ValueOp::I64Clz,
        I64Ctz => ValueOp::I64Ctz,
        I64Popcnt => ValueOp::I64Popcnt,
        I64ExtendI32S => ValueOp::I64ExtendI32S,
        I64ExtendI32U => ValueOp::I64ExtendI32U,
        I32WrapI64 => ValueOp::I32WrapI64,
        F32Add => ValueOp::F32Add,
        F32Sub => ValueOp::F32Sub,
        F32Mul => ValueOp::F32Mul,
        F32Div => ValueOp::F32Div,
        F32Min => ValueOp::F32Min,
        F32Max => ValueOp::F32Max,
        F32Copysign => ValueOp::F32Copysign,
        F32Eq => ValueOp::F32Eq,
        F32Ne => ValueOp::F32Ne,
        F32Lt => ValueOp::F32Lt,
        F32Le => ValueOp::F32Le,
        F32Gt => ValueOp::F32Gt,
        F32Ge => ValueOp::F32Ge,
        F32Abs => ValueOp::F32Abs,
        F32Neg => ValueOp::F32Neg,
        F32Sqrt => ValueOp::F32Sqrt,
        F32Ceil => ValueOp::F32Ceil,
        F32Floor => ValueOp::F32Floor,
        F32Trunc => ValueOp::F32Trunc,
        F32Nearest => ValueOp::F32Nearest,
        F64Add => ValueOp::F64Add,
        F64Sub => ValueOp::F64Sub,
        F64Mul => ValueOp::F64Mul,
        F64Div => ValueOp::F64Div,
        F64Min => ValueOp::F64Min,
        F64Max => ValueOp::F64Max,
        F64Copysign => ValueOp::F64Copysign,
        F64Eq => ValueOp::F64Eq,
        F64Ne => ValueOp::F64Ne,
        F64Lt => ValueOp::F64Lt,
        F64Le => ValueOp::F64Le,
        F64Gt => ValueOp::F64Gt,
        F64Ge => ValueOp::F64Ge,
        F64Abs => ValueOp::F64Abs,
        F64Neg => ValueOp::F64Neg,
        F64Sqrt => ValueOp::F64Sqrt,
        F64Ceil => ValueOp::F64Ceil,
        F64Floor => ValueOp::F64Floor,
        F64Trunc => ValueOp::F64Trunc,
        F64Nearest => ValueOp::F64Nearest,
        I32Const { value } => return Some(SemOp::I32Const(*value)),
        I64Const { value } => return Some(SemOp::I64Const(*value)),
        F32Const { value } => return Some(SemOp::F32Const(value.bits())),
        F64Const { value } => return Some(SemOp::F64Const(value.bits())),
        _ => return None,
    };
    Some(SemOp::Pure(v))
}

/// Stack type pushed by a const [`SemOp`].
pub fn const_stack_ty(op: &SemOp) -> Option<StackTy> {
    match op {
        SemOp::I32Const(_) => Some(StackTy::I32),
        SemOp::I64Const(_) => Some(StackTy::I64),
        SemOp::F32Const(_) => Some(StackTy::F32),
        SemOp::F64Const(_) => Some(StackTy::F64),
        _ => None,
    }
}

/// All SAT-eligible pure ops (binops and unops, excluding legacy duplication).
pub fn sat_pure_ops() -> Vec<ValueOp> {
    ValueOp::all().to_vec()
}

pub fn value_op_is_binop(op: ValueOp) -> bool {
    op.pops().len() == 2
}

pub fn value_op_is_unop(op: ValueOp) -> bool {
    op.pops().len() == 1
}

/// Wasm binops whose stack operand order is semantically irrelevant.
pub fn value_op_is_commutative_binop(op: ValueOp) -> bool {
    matches!(
        op,
        ValueOp::I32Add
            | ValueOp::I64Add
            | ValueOp::I32Mul
            | ValueOp::I64Mul
            | ValueOp::I32And
            | ValueOp::I64And
            | ValueOp::I32Or
            | ValueOp::I64Or
            | ValueOp::I32Xor
            | ValueOp::I64Xor
            | ValueOp::F32Add
            | ValueOp::F64Add
            | ValueOp::F32Mul
            | ValueOp::F64Mul
    )
}

pub fn inst_kind_is_commutative_binop(kind: InstKind) -> bool {
    matches!(kind, InstKind::Pure(op) if value_op_is_commutative_binop(op))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn commutative_binop_i64_add() {
        use crate::semantics::{inst_kind_is_commutative_binop, value_op_is_commutative_binop};
        use crate::value::ValueOp;

        assert!(value_op_is_commutative_binop(ValueOp::I64Add));
        assert!(!value_op_is_commutative_binop(ValueOp::I64ShrU));
        assert!(inst_kind_is_commutative_binop(InstKind::Pure(ValueOp::I64Add)));
    }

    #[test]
    fn i64_shr_s_not_opaque() {
        let sem = classify_pure_operator(&Operator::I64ShrS).expect("i64.shr_s");
        assert!(matches!(sem, SemOp::Pure(ValueOp::I64ShrS)));
    }

    #[test]
    fn f32_add_pure() {
        let sem = classify_pure_operator(&Operator::F32Add).expect("f32.add");
        assert!(matches!(sem, SemOp::Pure(ValueOp::F32Add)));
    }

    #[test]
    fn wrap_i64_pure() {
        let sem = classify_pure_operator(&Operator::I32WrapI64).expect("wrap");
        assert!(matches!(sem, SemOp::Pure(ValueOp::I32WrapI64)));
    }

    #[test]
    fn legacy_i32_maps_to_value_op() {
        assert_eq!(sem_to_value_op(&SemOp::I32Add), Some(ValueOp::I32Add));
    }
}
