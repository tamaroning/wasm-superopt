//! Core Wasm instruction and stack types (no AL dependency).

use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum StackTy {
    I32,
    I64,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SemOp {
    I32Const(i32),
    I32Add,
    I32Sub,
    I32Mul,
    I32DivU,
    I32DivS,
    I32RemU,
    I32RemS,
    I32Shl,
    I32And,
    I32Or,
    I32Xor,
    I32ShrU,
    I32ShrS,
    I32Rotl,
    I32Rotr,
    I32Eq,
    I32Ne,
    I32LtS,
    I32LeS,
    I32GtS,
    I32Eqz,
    I32Clz,
    I32Ctz,
    I32Popcnt,
    LocalGet(u32),
    LocalSet(u32),
    LocalTee(u32),
    I32Load {
        id: u32,
        mem: u32,
        offset: u32,
    },
    I32Store {
        id: u32,
        mem: u32,
        offset: u32,
    },
    Call {
        id: u32,
        func_index: u32,
        pops: u8,
        pushes: u8,
    },
    GlobalGet {
        id: u32,
        global_index: u32,
    },
    GlobalSet {
        id: u32,
        global_index: u32,
    },
    /// Non-i32 wasm instruction tracked symbolically (SuperStack-style), not optimized.
    Opaque {
        id: u32,
        pops: u8,
        pushes: u8,
        storage: bool,
    },
}

impl SemOp {
    pub fn name(&self) -> &'static str {
        match self {
            SemOp::I32Const(_) => "i32.const",
            SemOp::I32Add => "i32.add",
            SemOp::I32Sub => "i32.sub",
            SemOp::I32Mul => "i32.mul",
            SemOp::I32DivU => "i32.div_u",
            SemOp::I32DivS => "i32.div_s",
            SemOp::I32RemU => "i32.rem_u",
            SemOp::I32RemS => "i32.rem_s",
            SemOp::I32Shl => "i32.shl",
            SemOp::I32And => "i32.and",
            SemOp::I32Or => "i32.or",
            SemOp::I32Xor => "i32.xor",
            SemOp::I32ShrU => "i32.shr_u",
            SemOp::I32ShrS => "i32.shr_s",
            SemOp::I32Rotl => "i32.rotl",
            SemOp::I32Rotr => "i32.rotr",
            SemOp::I32Eq => "i32.eq",
            SemOp::I32Ne => "i32.ne",
            SemOp::I32LtS => "i32.lt_s",
            SemOp::I32LeS => "i32.le_s",
            SemOp::I32GtS => "i32.gt_s",
            SemOp::I32Eqz => "i32.eqz",
            SemOp::I32Clz => "i32.clz",
            SemOp::I32Ctz => "i32.ctz",
            SemOp::I32Popcnt => "i32.popcnt",
            SemOp::LocalGet(x) => local_op_name("local.get", *x),
            SemOp::LocalSet(x) => local_op_name("local.set", *x),
            SemOp::LocalTee(x) => local_op_name("local.tee", *x),
            SemOp::I32Load { .. } => "i32.load",
            SemOp::I32Store { .. } => "i32.store",
            SemOp::Call { .. } => "call",
            SemOp::GlobalGet { .. } => "global.get",
            SemOp::GlobalSet { .. } => "global.set",
            SemOp::Opaque { .. } => "opaque",
        }
    }

    pub fn opaque_id(&self) -> Option<u32> {
        match self {
            SemOp::I32Load { id, .. }
            | SemOp::I32Store { id, .. }
            | SemOp::Call { id, .. }
            | SemOp::GlobalGet { id, .. }
            | SemOp::GlobalSet { id, .. }
            | SemOp::Opaque { id, .. } => Some(*id),
            _ => None,
        }
    }

    /// Side-effect ops that must appear exactly once in optimized output (SuperStack `storage`).
    pub fn is_storage_boundary(&self) -> bool {
        matches!(
            self,
            SemOp::I32Store { .. }
                | SemOp::Call { .. }
                | SemOp::GlobalSet { .. }
                | SemOp::Opaque {
                    storage: true,
                    ..
                }
        )
    }

    /// Whether this op reads or writes implicit machine state (not representable in the egg DAG).
    pub fn is_effectful(&self) -> bool {
        matches!(
            self,
            SemOp::LocalGet(_)
                | SemOp::LocalSet(_)
                | SemOp::LocalTee(_)
                | SemOp::I32Load { .. }
                | SemOp::I32Store { .. }
                | SemOp::Call { .. }
                | SemOp::GlobalGet { .. }
                | SemOp::GlobalSet { .. }
                | SemOp::Opaque { storage: true, .. }
        )
    }

}

impl fmt::Display for SemOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SemOp::I32Const(n) => write!(f, "i32.const {n}"),
            SemOp::I32Add => write!(f, "i32.add"),
            SemOp::I32Sub => write!(f, "i32.sub"),
            SemOp::I32Mul => write!(f, "i32.mul"),
            SemOp::I32DivU => write!(f, "i32.div_u"),
            SemOp::I32DivS => write!(f, "i32.div_s"),
            SemOp::I32RemU => write!(f, "i32.rem_u"),
            SemOp::I32RemS => write!(f, "i32.rem_s"),
            SemOp::I32Shl => write!(f, "i32.shl"),
            SemOp::I32And => write!(f, "i32.and"),
            SemOp::I32Or => write!(f, "i32.or"),
            SemOp::I32Xor => write!(f, "i32.xor"),
            SemOp::I32ShrU => write!(f, "i32.shr_u"),
            SemOp::I32ShrS => write!(f, "i32.shr_s"),
            SemOp::I32Rotl => write!(f, "i32.rotl"),
            SemOp::I32Rotr => write!(f, "i32.rotr"),
            SemOp::I32Eq => write!(f, "i32.eq"),
            SemOp::I32Ne => write!(f, "i32.ne"),
            SemOp::I32LtS => write!(f, "i32.lt_s"),
            SemOp::I32LeS => write!(f, "i32.le_s"),
            SemOp::I32GtS => write!(f, "i32.gt_s"),
            SemOp::I32Eqz => write!(f, "i32.eqz"),
            SemOp::I32Clz => write!(f, "i32.clz"),
            SemOp::I32Ctz => write!(f, "i32.ctz"),
            SemOp::I32Popcnt => write!(f, "i32.popcnt"),
            SemOp::LocalGet(x) => write!(f, "local.get {x}"),
            SemOp::LocalSet(x) => write!(f, "local.set {x}"),
            SemOp::LocalTee(x) => write!(f, "local.tee {x}"),
            SemOp::I32Load {
                id,
                mem,
                offset,
            } => write!(f, "i32.load {id} mem={mem} off={offset}"),
            SemOp::I32Store {
                id,
                mem,
                offset,
            } => write!(f, "i32.store {id} mem={mem} off={offset}"),
            SemOp::Call {
                id,
                func_index,
                pops,
                pushes,
            } => write!(f, "call {id} fn={func_index} pops={pops} pushes={pushes}"),
            SemOp::GlobalGet {
                id,
                global_index,
            } => write!(f, "global.get {id} g={global_index}"),
            SemOp::GlobalSet {
                id,
                global_index,
            } => write!(f, "global.set {id} g={global_index}"),
            SemOp::Opaque {
                id,
                pops,
                pushes,
                storage,
            } => write!(f, "opaque {id} pops={pops} pushes={pushes} storage={storage}"),
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
        _ => kind,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum InstKind {
    I32Const,
    I32Add,
    I32Sub,
    I32Mul,
    I32DivU,
    I32DivS,
    I32RemU,
    I32RemS,
    I32Shl,
    I32And,
    I32Or,
    I32Xor,
    I32ShrU,
    I32ShrS,
    I32Rotl,
    I32Rotr,
    I32Eq,
    I32Ne,
    I32LtS,
    I32LeS,
    I32GtS,
    I32Eqz,
    I32Clz,
    I32Ctz,
    I32Popcnt,
    LocalGet(u32),
    LocalSet(u32),
    LocalTee(u32),
}

impl InstKind {
    pub fn is_i32_binop(self) -> bool {
        matches!(
            self,
            InstKind::I32Add
                | InstKind::I32Sub
                | InstKind::I32Mul
                | InstKind::I32DivU
                | InstKind::I32DivS
                | InstKind::I32RemU
                | InstKind::I32RemS
                | InstKind::I32Shl
                | InstKind::I32And
                | InstKind::I32Or
                | InstKind::I32Xor
                | InstKind::I32ShrU
                | InstKind::I32ShrS
                | InstKind::I32Rotl
                | InstKind::I32Rotr
        )
    }

    pub fn is_i32_relop(self) -> bool {
        matches!(
            self,
            InstKind::I32Eq
                | InstKind::I32Ne
                | InstKind::I32LtS
                | InstKind::I32LeS
                | InstKind::I32GtS
        )
    }

    pub fn is_i32_testop(self) -> bool {
        matches!(self, InstKind::I32Eqz)
    }

    pub fn is_i32_unop(self) -> bool {
        matches!(
            self,
            InstKind::I32Clz | InstKind::I32Ctz | InstKind::I32Popcnt
        )
    }

    pub fn may_trap_as_unop(self) -> bool {
        false
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
