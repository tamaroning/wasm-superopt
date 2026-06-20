//! Algorithmic-language (AL) IR for Wasm instruction semantics.
//!
//! Each `SemOp` is defined by an `AlSpec` (pop / if / trap / push steps). Static
//! `InstSpec` values are derived from these definitions.

mod ast;
mod defs;
mod derive;
mod ir;
mod policy;
mod specs;
mod symbolic;
mod util;

pub use ast::{
    format_rule_binop_pretty, format_rule_relop_pretty, format_rule_testop_pretty,
    format_rule_unop_pretty,
};
pub use defs::format_rule_local_pretty;
pub use defs::{
    NumType, Sign, WasmBinOp, WasmRelOp, WasmTestOp, WasmUnOp,
};
pub use derive::{
    derive_inst_spec, derive_rule_binop_spec, derive_rule_local_get_spec,
    derive_rule_local_set_spec, derive_rule_local_tee_spec, derive_rule_relop_spec,
    derive_rule_testop_spec, derive_rule_unop_spec,
};
pub use ir::format_al_pretty;
pub use policy::STRAIGHT_LINE_EMBED;
pub use specs::al_spec_for;
pub use symbolic::context::z3_context;

/// Default number of randomized concrete tests before invoking Z3.
pub const DEFAULT_RANDOM_TESTS: usize = 100;

/// Bit width of Wasm `i32` in AL / Z3 lowering.
pub const I32_BITS: u32 = 32;
