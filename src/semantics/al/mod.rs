//! Algorithmic-language (AL) IR for Wasm instruction semantics.
//!
//! Each `SemOp` is defined by an `AlSpec` (pop / if / trap / push steps). Concrete
//! execution, Z3 lowering, and `InstSpec` are derived from these definitions.

mod al_defs;
mod concrete;
mod eval;
mod derive;
mod env;
mod ir;
mod meta;
mod meta_z3;
mod policy;
mod specs;
mod sym;
mod util;
mod z3;

#[cfg(test)]
mod tests;

pub use concrete::exec_al_concrete;
pub use derive::{derive_inst_spec, derive_meta_binop_spec};
pub use meta_z3::{exec_meta_binop_concrete, exec_meta_binop_z3};
pub use policy::STRAIGHT_LINE_EMBED;
pub use specs::al_spec_for;
pub use ir::{format_al_pretty, NumType, Sign, WasmBinOp};
pub use meta::format_meta_binop_pretty;
pub use z3::exec_al_z3;
