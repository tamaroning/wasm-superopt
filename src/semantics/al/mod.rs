//! Algorithmic-language (AL) IR for Wasm instruction semantics.
//!
//! Each `SemOp` is defined by an `AlSpec` (pop / if / trap / push steps). Concrete
//! execution, Z3 lowering, and `InstSpec` are derived from these definitions.
//!
//! Executor layout:
//! - [`eval`](eval.rs) / [`encode_sym`](encode_sym.rs) — `$fn` definitions
//! - [`exec_step_concrete`](exec_step_concrete.rs) / [`exec_step_z3`](exec_step_z3.rs) — `AlMetaStep` templates
//! - [`exec_alspec_concrete`](exec_alspec_concrete.rs) / [`exec_alspec_z3`](exec_alspec_z3.rs) — flat [`AlSpec`](ir::AlSpec)

mod al_defs;
mod encode_sym;
mod eval;
mod derive;
mod env;
mod exec_alspec_concrete;
mod exec_alspec_z3;
mod exec_step_concrete;
mod exec_step_z3;
mod ir;
mod meta;
mod policy;
mod specs;
mod util;

#[cfg(test)]
mod tests;

pub use encode_sym::encode_binop_stack;
pub use derive::{derive_inst_spec, derive_meta_binop_spec};
pub use exec_alspec_concrete::exec_al_concrete;
pub use exec_alspec_z3::exec_al_z3;
pub use exec_step_concrete::exec_meta_binop_concrete;
pub use exec_step_z3::exec_meta_binop_z3;
pub use policy::STRAIGHT_LINE_EMBED;
pub use specs::al_spec_for;
pub use ir::{format_al_pretty, NumType, Sign, WasmBinOp};
pub use meta::format_meta_binop_pretty;
