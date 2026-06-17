//! Concrete executor for [`RuleA`](super::super::ast::Algorithm::RuleA) bodies (`instr` in OCaml).

use super::func::{eval_expr, AlEnv, AlValue};
use super::super::ast::{Expr, Instr, InstrCond, LetLhs, PopTarget};

fn push_stack(stack: &mut Vec<i32>, val: AlValue) {
    match val {
        AlValue::Nat(n) => stack.push(n as i32),
        AlValue::Int(n) => stack.push(n),
        other => panic!("stack push expected nat/int, got {other:?}"),
    }
}

fn exec_instr(
    step: &Instr,
    stack: &mut Vec<i32>,
    trap: &mut bool,
    env: &mut AlEnv,
) {
    match step {
        Instr::AssertI(InstrCond::Expr(expr)) => {
            if matches!(expr, Expr::TopValue(_)) {
                return;
            }
            eval_expr(expr, env).expect("assert expr");
        }
        Instr::AssertI(InstrCond::Pred(_)) => panic!("pred assert in rule body"),
        Instr::PopI(pattern) => {
            let name = match pattern {
                PopTarget::NumConst(n) => *n,
            };
            let val = stack.pop().expect("stack underflow");
            env.bind(name, AlValue::Nat(val as u32));
        }
        Instr::LetI {
            lhs: LetLhs::Var(name),
            expr,
        } => {
            env.bind(name, eval_expr(expr, env).expect("let expr"));
        }
        Instr::LetI { .. } => panic!("binop-case let in rule body"),
        Instr::IfI {
            cond: InstrCond::Expr(cond),
            then_steps,
            else_steps,
        } => {
            let len = match eval_expr(cond, env).expect("if cond") {
                AlValue::Nat(n) => n,
                other => panic!("if cond expected nat, got {other:?}"),
            };
            if len <= 0 {
                exec_instrs(then_steps, stack, trap, env);
            } else {
                exec_instrs(else_steps, stack, trap, env);
            }
        }
        Instr::IfI {
            cond: InstrCond::Pred(_), ..
        } => panic!("pred if in rule body"),
        Instr::PushI(expr) => {
            push_stack(stack, eval_expr(expr, env).expect("push expr"));
        }
        Instr::TrapI => *trap = true,
        Instr::ReturnI(_) | Instr::FailI => panic!("func instr in rule body"),
    }
}

fn exec_instrs(
    steps: &[Instr],
    stack: &mut Vec<i32>,
    trap: &mut bool,
    env: &mut AlEnv,
) {
    for step in steps {
        if *trap {
            return;
        }
        exec_instr(step, stack, trap, env);
    }
}

/// Concrete execution of a `Step_pure/...` rule body.
pub fn exec_instrs_concrete(steps: &[Instr], stack: &mut Vec<i32>) -> bool {
    let mut trap = false;
    let mut env = AlEnv::new();
    exec_instrs(steps, stack, &mut trap, &mut env);
    trap
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sema::defs::{step_pure_binop_template, NumType, Sign, WasmBinOp};

    fn run_binop(binop: WasmBinOp, i_1: u32, i_2: u32) -> Option<u32> {
        let mut stack = vec![i_1 as i32, i_2 as i32];
        let trap = exec_instrs_concrete(
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
    fn binop_add_via_instrs() {
        assert_eq!(run_binop(WasmBinOp::Add, 3, 5), Some(8));
    }

    #[test]
    fn binop_div_s_trap_via_instrs() {
        assert_eq!(run_binop(WasmBinOp::Div(Sign::S), 0, 0), None);
        assert_eq!(
            run_binop(WasmBinOp::Div(Sign::S), i32::MIN as u32, (-1i32) as u32),
            None
        );
    }

    #[test]
    fn binop_div_s_defined_via_instrs() {
        assert_eq!(run_binop(WasmBinOp::Div(Sign::S), 8, 2), Some(4));
    }
}
