//! Concrete executor for meta-level [`AlMetaStep`](super::meta::AlMetaStep) templates.

use super::eval::{eval_meta_expr, AlValue, MetaEnv};
use super::meta::{AlMetaExpr, AlMetaStep, PopPattern};

fn push_stack(stack: &mut Vec<i32>, val: AlValue) {
    match val {
        AlValue::Nat(n) => stack.push(n as i32),
        AlValue::Int(n) => stack.push(n),
        other => panic!("stack push expected nat/int, got {other:?}"),
    }
}

fn exec_meta_step(
    step: &AlMetaStep,
    stack: &mut Vec<i32>,
    trap: &mut bool,
    env: &mut MetaEnv,
) {
    match step {
        AlMetaStep::Assert(expr) => {
            if matches!(expr, AlMetaExpr::TopValue(_)) {
                return;
            }
            eval_meta_expr(expr, env).expect("assert expr");
        }
        AlMetaStep::Pop(pattern) => {
            let name = match pattern {
                PopPattern::NumConst(n) => *n,
            };
            let val = stack.pop().expect("stack underflow");
            env.bind(name, AlValue::Nat(val as u32));
        }
        AlMetaStep::Let { name, expr } => {
            env.bind(name, eval_meta_expr(expr, env).expect("let expr"));
        }
        AlMetaStep::If {
            cond,
            then_steps,
            else_steps,
        } => {
            let len = match eval_meta_expr(cond, env).expect("if cond") {
                AlValue::Nat(n) => n,
                other => panic!("if cond expected nat, got {other:?}"),
            };
            if len <= 0 {
                exec_meta_steps(then_steps, stack, trap, env);
            } else {
                exec_meta_steps(else_steps, stack, trap, env);
            }
        }
        AlMetaStep::Push(expr) => {
            push_stack(stack, eval_meta_expr(expr, env).expect("push expr"));
        }
        AlMetaStep::Trap => *trap = true,
    }
}

fn exec_meta_steps(
    steps: &[AlMetaStep],
    stack: &mut Vec<i32>,
    trap: &mut bool,
    env: &mut MetaEnv,
) {
    for step in steps {
        if *trap {
            return;
        }
        exec_meta_step(step, stack, trap, env);
    }
}

/// Concrete execution of a `Step_pure/...` meta template.
pub fn exec_meta_steps_concrete(steps: &[AlMetaStep], stack: &mut Vec<i32>) -> bool {
    let mut trap = false;
    let mut env = MetaEnv::new();
    exec_meta_steps(steps, stack, &mut trap, &mut env);
    trap
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::semantics::al::al_defs::{step_pure_binop_template, NumType, Sign, WasmBinOp};

    fn run_binop(binop: WasmBinOp, i_1: u32, i_2: u32) -> Option<u32> {
        let mut stack = vec![i_1 as i32, i_2 as i32];
        let trap = exec_meta_steps_concrete(
            &step_pure_binop_template(NumType::I32, binop),
            &mut stack,
        );
        if trap {
            None
        } else {
            Some(stack.last().copied().unwrap() as u32)
        }
    }

    #[test]
    fn binop_add_via_meta_steps() {
        assert_eq!(run_binop(WasmBinOp::Add, 3, 5), Some(8));
    }

    #[test]
    fn binop_div_s_trap_via_meta_steps() {
        assert_eq!(run_binop(WasmBinOp::Div(Sign::S), 0, 0), None);
        assert_eq!(
            run_binop(WasmBinOp::Div(Sign::S), i32::MIN as u32, (-1i32) as u32),
            None
        );
    }

    #[test]
    fn binop_div_s_defined_via_meta_steps() {
        assert_eq!(run_binop(WasmBinOp::Div(Sign::S), 8, 2), Some(4));
    }
}
