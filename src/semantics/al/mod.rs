//! Algorithmic-language (AL) IR for Wasm instruction semantics.
//!
//! Each `SemOp` is defined by an `AlSpec` (pop / if / trap / push steps). Concrete
//! execution, Z3 lowering, and `InstSpec` are derived from these definitions.

mod concrete;
mod derive;
mod env;
mod format;
mod ir;
mod policy;
mod specs;
mod util;
mod z3;

#[cfg(test)]
mod tests;

pub use concrete::exec_al_concrete;
pub use derive::derive_inst_spec;
pub use format::format_al_z3;
pub use policy::STRAIGHT_LINE_EMBED;
pub use specs::al_spec_for;
pub use z3::exec_al_z3;
