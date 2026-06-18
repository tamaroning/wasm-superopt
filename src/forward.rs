//! Forward symbolic execution: build residual goals from instruction sequences.

use crate::goal::{LocalReq, MachineState, MAX_LOCAL_SLOT, MAX_STACK_HEIGHT};
use crate::lang::ValueLang;
use crate::semantics::SemOp;
use crate::value::parse_value_expr;
use egg::RecExpr;
use std::collections::BTreeMap;

pub type ValueExpr = RecExpr<ValueLang>;

#[derive(Debug, Clone)]
pub struct SymMachine {
    stack: Vec<ValueExpr>,
    locals: BTreeMap<u32, ValueExpr>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ForwardError {
    StackUnderflow,
    UnknownLocal(u32),
    UnsupportedOp,
    StackTooHigh,
    LocalOutOfRange,
}

impl SymMachine {
    pub fn local_symbol(slot: u32) -> ValueExpr {
        parse_value_expr(&format!("?L{slot}"))
    }

    /// Entry state for a function: params are symbols, other locals are zero.
    pub fn function_entry(num_params: u32, total_locals: u32) -> Self {
        let mut locals = BTreeMap::new();
        for slot in 0..total_locals.min(MAX_LOCAL_SLOT + 1) {
            let init = if slot < num_params {
                Self::local_symbol(slot)
            } else {
                parse_value_expr("0")
            };
            locals.insert(slot, init);
        }
        Self {
            stack: Vec::new(),
            locals,
        }
    }

    pub fn exec(&mut self, op: &SemOp) -> Result<(), ForwardError> {
        match op {
            SemOp::I32Const(n) => {
                self.push_expr(parse_value_expr(&n.to_string()))?;
            }
            SemOp::I32Add | SemOp::I32Mul | SemOp::I32DivU | SemOp::I32DivS | SemOp::I32Shl => {
                let b = self.pop()?;
                let a = self.pop()?;
                let expr = match op {
                    SemOp::I32Add => parse_value_expr(&format!("(i32.add {a} {b})")),
                    SemOp::I32Mul => parse_value_expr(&format!("(i32.mul {a} {b})")),
                    SemOp::I32DivU => parse_value_expr(&format!("(i32.div_u {a} {b})")),
                    SemOp::I32DivS => parse_value_expr(&format!("(i32.div_s {a} {b})")),
                    SemOp::I32Shl => parse_value_expr(&format!("(i32.shl {a} {b})")),
                    _ => unreachable!(),
                };
                self.push_expr(expr)?;
            }
            SemOp::LocalGet(slot) => {
                if *slot > MAX_LOCAL_SLOT {
                    return Err(ForwardError::LocalOutOfRange);
                }
                let v = self
                    .locals
                    .get(slot)
                    .cloned()
                    .ok_or(ForwardError::UnknownLocal(*slot))?;
                self.push_expr(v)?;
            }
            SemOp::LocalSet(slot) => {
                if *slot > MAX_LOCAL_SLOT {
                    return Err(ForwardError::LocalOutOfRange);
                }
                let v = self.pop()?;
                self.locals.insert(*slot, v);
            }
            SemOp::LocalTee(slot) => {
                if *slot > MAX_LOCAL_SLOT {
                    return Err(ForwardError::LocalOutOfRange);
                }
                let v = self
                    .stack
                    .last()
                    .cloned()
                    .ok_or(ForwardError::StackUnderflow)?;
                self.locals.insert(*slot, v);
            }
        }
        Ok(())
    }

    pub fn pop(&mut self) -> Result<ValueExpr, ForwardError> {
        self.stack.pop().ok_or(ForwardError::StackUnderflow)
    }

    pub fn to_init_state(&self) -> MachineState {
        self.snapshot()
    }

    pub fn to_fin_state(&self) -> MachineState {
        self.snapshot()
    }

    fn snapshot(&self) -> MachineState {
        MachineState {
            stack: self.stack.clone(),
            locals: self
                .locals
                .iter()
                .filter(|&(&slot, _)| slot <= MAX_LOCAL_SLOT)
                .map(|(&slot, v)| (slot, LocalReq::Need(v.clone())))
                .collect(),
        }
    }

    fn push_expr(&mut self, expr: ValueExpr) -> Result<(), ForwardError> {
        if self.stack.len() >= MAX_STACK_HEIGHT {
            return Err(ForwardError::StackTooHigh);
        }
        self.stack.push(expr);
        Ok(())
    }
}

pub fn forward_goal(init: &MachineState, ops: &[SemOp]) -> Result<MachineState, ForwardError> {
    let mut machine = SymMachine {
        stack: init.stack.clone(),
        locals: init
            .locals
            .iter()
            .filter_map(|(&slot, req)| match req {
                LocalReq::Need(v) => Some((slot, v.clone())),
                LocalReq::DontCare => None,
            })
            .collect(),
    };
    for op in ops {
        machine.exec(op)?;
    }
    Ok(machine.to_fin_state())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::goal::example_init;
    use crate::search::verify_forward;
    use crate::semantics::SemOp;

    #[test]
    fn example_fin_from_forward_exec() {
        let init = example_init();
        let ops = [
            SemOp::LocalGet(0),
            SemOp::I32Const(1),
            SemOp::I32Add,
            SemOp::LocalTee(0),
            SemOp::I32Const(4),
            SemOp::I32Mul,
            SemOp::LocalGet(0),
        ];
        let fin = forward_goal(&init, &ops).expect("forward");
        assert!(fin.validate_bounds());
        assert!(verify_forward(&fin, &ops, 42));
    }

    #[test]
    fn function_entry_matches_example_init() {
        let entry = SymMachine::function_entry(1, 1);
        let init = entry.to_init_state();
        let expected = example_init();
        assert_eq!(init.stack, expected.stack);
        assert_eq!(init.locals, expected.locals);
    }
}
