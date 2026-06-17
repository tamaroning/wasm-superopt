//! Algorithmic-language (AL) IR for Wasm instruction semantics.
//!
//! Each `SemOp` is defined by an `AlSpec` (pop / if / trap / push steps). Concrete
//! execution, Z3 lowering, and `InstSpec` are derived from these definitions.
//!
//! Executor layout:
//! - [`eval::func`](eval/func.rs) / [`symbolic::func`](symbolic/func.rs) — `$fn` definitions
//! - [`eval::instr`](eval/instr.rs) / [`symbolic::instr`](symbolic/instr.rs) — `Instr` templates
//! - [`eval::alspec`](eval/alspec.rs) / [`symbolic::alspec`](symbolic/alspec.rs) — flat [`AlSpec`](ir::AlSpec)

mod defs;
mod derive;
mod env;
mod eval;
mod ir;
mod ast;
mod policy;
mod specs;
mod symbolic;
mod util;

#[cfg(test)]
mod tests;

pub use derive::{derive_inst_spec, derive_rule_binop_spec};
pub use eval::alspec::exec_al_concrete;
pub use eval::instr::exec_instrs_concrete;
pub use symbolic::alspec::exec_al_z3;
pub use symbolic::instr::exec_instrs_z3;
pub use policy::STRAIGHT_LINE_EMBED;
pub use specs::{al_spec_for, rule_instrs_for};
pub use defs::{NumType, Sign, WasmBinOp};
pub use ir::format_al_pretty;
pub use ast::format_rule_binop_pretty;
