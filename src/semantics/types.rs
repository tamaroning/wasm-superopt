//! Core Wasm instruction and stack types (no AL dependency).

use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum StackTy {
    I32,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SemOp {
    I32Const(i32),
    I32Add,
    I32Mul,
    I32DivU,
    I32DivS,
    I32Shl,
    LocalGet(u32),
    LocalSet(u32),
    LocalTee(u32),
}

impl SemOp {
    pub fn name(&self) -> &'static str {
        match self {
            SemOp::I32Const(_) => "i32.const",
            SemOp::I32Add => "i32.add",
            SemOp::I32Mul => "i32.mul",
            SemOp::I32DivU => "i32.div_u",
            SemOp::I32DivS => "i32.div_s",
            SemOp::I32Shl => "i32.shl",
            SemOp::LocalGet(x) => local_op_name("local.get", *x),
            SemOp::LocalSet(x) => local_op_name("local.set", *x),
            SemOp::LocalTee(x) => local_op_name("local.tee", *x),
        }
    }

    /// Whether this op reads or writes implicit machine state (not representable in the egg DAG).
    pub fn is_effectful(&self) -> bool {
        matches!(
            self,
            SemOp::LocalGet(_) | SemOp::LocalSet(_) | SemOp::LocalTee(_)
        )
    }
}

impl fmt::Display for SemOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SemOp::I32Const(n) => write!(f, "i32.const {n}"),
            SemOp::I32Add => write!(f, "i32.add"),
            SemOp::I32Mul => write!(f, "i32.mul"),
            SemOp::I32DivU => write!(f, "i32.div_u"),
            SemOp::I32DivS => write!(f, "i32.div_s"),
            SemOp::I32Shl => write!(f, "i32.shl"),
            SemOp::LocalGet(x) => write!(f, "local.get {x}"),
            SemOp::LocalSet(x) => write!(f, "local.set {x}"),
            SemOp::LocalTee(x) => write!(f, "local.tee {x}"),
        }
    }
}

fn local_op_name(kind: &'static str, x: u32) -> &'static str {
    match (kind, x) {
        ("local.get", 0) => "local.get 0",
        ("local.get", 1) => "local.get 1",
        ("local.get", 2) => "local.get 2",
        ("local.set", 0) => "local.set 0",
        ("local.set", 1) => "local.set 1",
        ("local.set", 2) => "local.set 2",
        ("local.tee", 0) => "local.tee 0",
        ("local.tee", 1) => "local.tee 1",
        ("local.tee", 2) => "local.tee 2",
        _ => panic!("local op name only defined for indices 0..2"),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum InstKind {
    I32Const,
    I32Add,
    I32Mul,
    I32DivU,
    I32DivS,
    I32Shl,
    LocalGet(u32),
    LocalSet(u32),
    LocalTee(u32),
}

impl InstKind {
    pub fn is_i32_binop(self) -> bool {
        matches!(
            self,
            InstKind::I32Add
                | InstKind::I32Mul
                | InstKind::I32DivU
                | InstKind::I32DivS
                | InstKind::I32Shl
        )
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct InstSpec {
    pub kind: InstKind,
    pub pops: &'static [StackTy],
    pub pushes: &'static [StackTy],
    /// Whether this instruction may trap (trap kind is not distinguished).
    pub can_trap: bool,
}
