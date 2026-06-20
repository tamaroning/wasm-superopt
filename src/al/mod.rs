//! Algorithmic-language (AL) IR for Wasm instruction semantics.
//!
//! Each `SemOp` is defined by an `AlSpec` (pop / if / trap / push steps). Concrete
//! execution, Z3 lowering, and `InstSpec` are derived from these definitions.
//!
//! Executor layout:
//! - [`eval::func`](eval/func.rs) / [`symbolic::func`](symbolic/func.rs) — `$fn` definitions
//! - [`eval::instr`](eval/instr.rs) / [`symbolic::instr`](symbolic/instr.rs) — `Instr` templates
//! - [`eval::alspec`](eval/alspec.rs) / [`symbolic::alspec`](symbolic/alspec.rs) — flat [`AlSpec`](ir::AlSpec)

mod ast;
mod defs;
mod derive;
mod env;
mod eval;
mod ir;
mod policy;
mod specs;
mod symbolic;
mod util;

pub use ast::format_rule_binop_pretty;
pub use defs::format_rule_local_pretty;
pub use defs::{NumType, Sign, WasmBinOp};
pub use derive::{
    derive_inst_spec, derive_rule_binop_spec, derive_rule_local_get_spec,
    derive_rule_local_set_spec, derive_rule_local_tee_spec,
};
pub use eval::alspec::exec_al_concrete;
pub use eval::instr::exec_instrs_concrete;
pub use eval::sequence::{
    DEFAULT_RANDOM_TESTS, exec_op_concrete, exec_sequence_concrete, sequences_valid_rewrite_random,
};
pub use eval::state::{ConcreteResult, ConcreteState, LOCAL_SLOTS, MEM_SLOTS};
pub use ir::format_al_pretty;
pub use policy::STRAIGHT_LINE_EMBED;
pub use specs::{al_spec_for, rule_instrs_for};
pub use symbolic::alspec::exec_al_z3;
pub use symbolic::context::z3_context;
pub use symbolic::instr::exec_instrs_z3;
pub use symbolic::sequence::{exec_op, exec_sequence, sequences_valid_rewrite_z3};
pub use symbolic::state::{ExecResult, StateTouches, Z3State};

/// Bit width of Wasm `i32` in AL / Z3 lowering.
pub const I32_BITS: u32 = 32;
