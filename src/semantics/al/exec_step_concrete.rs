//! Concrete executor for meta-level `AlMetaStep` templates (e.g. `Step_pure/binop`).

use super::eval::eval_binop_;
use super::ir::{NumType, WasmBinOp};

/// Concrete execution of `Step_pure/binop` via meta AL (`eval_binop_`).
pub fn exec_meta_binop_concrete(
    nt: NumType,
    binop: WasmBinOp,
    stack: &mut Vec<i32>,
) -> bool {
    let c2 = stack.pop().expect("stack underflow") as u32;
    let c1 = stack.pop().expect("stack underflow") as u32;
    match eval_binop_(nt, binop, c1, c2) {
        None => true,
        Some(n) => {
            stack.push(n as i32);
            false
        }
    }
}
