//! Algorithmic-language (AL) IR for Wasm instruction semantics.
//!
//! Each `SemOp` is defined by an `AlSpec` (pop / if / trap / push steps). Concrete
//! execution, Z3 lowering, and `InstSpec` are derived from these definitions.

mod al_defs;
mod concrete;
mod eval;
mod derive;
mod env;
mod instantiate;
mod ir;
mod meta;
mod policy;
mod specs;
mod util;
mod z3;

#[cfg(test)]
mod tests;

pub use concrete::exec_al_concrete;
pub use derive::derive_inst_spec;
pub use instantiate::step_pure_binop;
pub use policy::STRAIGHT_LINE_EMBED;
pub use specs::al_spec_for;
pub use z3::{exec_al_z3, format_al_z3};
