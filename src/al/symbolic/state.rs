//! Symbolic (Z3) machine state.

use crate::al::I32_BITS;
use z3::ast::{Array, BV};
use z3::{Context, Sort};

pub struct Z3State<'ctx> {
    pub locals: Array<'ctx>,
    pub memory: Array<'ctx>,
}

impl<'ctx> Clone for Z3State<'ctx> {
    fn clone(&self) -> Self {
        Self {
            locals: self.locals.clone(),
            memory: self.memory.clone(),
        }
    }
}

impl<'ctx> Z3State<'ctx> {
    pub fn fresh(ctx: &'ctx Context, prefix: &str) -> Self {
        let i32_sort = Sort::bitvector(ctx, I32_BITS);
        let idx_sort = Sort::bitvector(ctx, I32_BITS);
        let locals = Array::fresh_const(ctx, &format!("{prefix}_locals"), &idx_sort, &i32_sort);
        let memory = Array::fresh_const(ctx, &format!("{prefix}_mem"), &idx_sort, &i32_sort);
        Self { locals, memory }
    }
}

/// Locals / memory slots written during execution (reads affect the stack only).
#[derive(Default)]
pub struct StateTouches<'ctx> {
    pub local_writes: std::collections::HashSet<u32>,
    pub mem_writes: Vec<BV<'ctx>>,
}

pub struct ExecResult<'ctx> {
    pub stack: Vec<BV<'ctx>>,
    pub state: Z3State<'ctx>,
    pub trap: z3::ast::Bool<'ctx>,
    pub touches: StateTouches<'ctx>,
}
