//! Algorithmic-language (AL) IR for Wasm instruction semantics.
//!
//! Each `SemOp` is defined by an `AlSpec` (pop / if / trap / push steps). Concrete
//! execution, Z3 lowering, and `InstSpec` are derived from these definitions.
//!
//! Executor layout:
//! - [`eval::meta_fn`](eval/meta_fn.rs) / [`symbolic::meta_fn`](symbolic/meta_fn.rs) — `$fn` definitions
//! - [`eval::meta_step`](eval/meta_step.rs) / [`symbolic::meta_step`](symbolic/meta_step.rs) — `AlMetaStep` templates
//! - [`eval::alspec`](eval/alspec.rs) / [`symbolic::alspec`](symbolic/alspec.rs) — flat [`AlSpec`](ir::AlSpec)

mod defs;
mod derive;
mod env;
mod eval;
mod ir;
mod meta;
mod policy;
mod specs;
mod symbolic;
mod util;

#[cfg(test)]
mod tests;

pub use derive::{derive_inst_spec, derive_meta_binop_spec};
pub use eval::alspec::exec_al_concrete;
pub use eval::meta_step::exec_meta_steps_concrete;
pub use symbolic::alspec::exec_al_z3;
pub use symbolic::meta_step::exec_meta_steps_z3;
pub use policy::STRAIGHT_LINE_EMBED;
pub use specs::{al_spec_for, meta_steps_for};
pub use defs::{NumType, Sign, WasmBinOp};
pub use ir::format_al_pretty;
pub use meta::format_meta_binop_pretty;
