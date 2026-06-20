//! Concrete executor for [`RuleA`](super::super::ast::Algorithm::RuleA) bodies (`instr` in OCaml).

use super::super::ast::{Arg, Expr, Instr, InstrCond, LetLhs, PopTarget};
use super::super::defs::step_local_set_template;
use super::func::{AlEnv, AlValue, eval_expr};
use crate::semantics::ConcreteState;

fn push_stack(stack: &mut Vec<i32>, val: AlValue) {
    match val {
        AlValue::Nat(n) => stack.push(n as i32),
        AlValue::Int(n) => stack.push(n),
        other => panic!("stack push expected nat/int, got {other:?}"),
    }
}

fn alval_to_i32(val: &AlValue) -> i32 {
    match val {
        AlValue::Nat(n) => *n as i32,
        AlValue::Int(n) => *n,
        other => panic!("expected nat/int, got {other:?}"),
    }
}

fn local_index(args: &[Arg]) -> u32 {
    match args {
        [Arg::Var(_), Arg::Nat(x)] => *x,
        [Arg::Nat(x)] => *x,
        _ => panic!("$local(z, x) expected store + nat index, got {args:?}"),
    }
}

fn with_local_args(args: &[Arg]) -> (u32, &'static str) {
    match args {
        [Arg::Var(_), Arg::Nat(x), Arg::Var(val)] => (*x, val),
        [Arg::Nat(x), Arg::Var(val)] => (*x, val),
        _ => panic!("$with_local(z, x, val) expected 3 args, got {args:?}"),
    }
}

fn push_expr(expr: &Expr, stack: &mut Vec<i32>, state: &ConcreteState, env: &AlEnv) {
    if let Expr::Call("local", args) = expr {
        let x = local_index(args);
        stack.push(state.locals[x as usize]);
        return;
    }
    push_stack(stack, eval_expr(expr, env).expect("push expr"));
}

fn perform_with_local(args: &[Arg], state: &mut ConcreteState, env: &AlEnv) {
    let (x, val_name) = with_local_args(args);
    state.locals[x as usize] = alval_to_i32(env.get(val_name));
}

fn exec_instr(
    step: &Instr,
    stack: &mut Vec<i32>,
    state: &mut ConcreteState,
    trap: &mut bool,
    env: &mut AlEnv,
) {
    match step {
        Instr::AssertI(InstrCond::Expr(expr)) => {
            if matches!(expr, Expr::TopValue(_) | Expr::TopValueAny) {
                return;
            }
            eval_expr(expr, env).expect("assert expr");
        }
        Instr::AssertI(InstrCond::Pred(_)) => panic!("pred assert in rule body"),
        Instr::PopI(pattern) => {
            let name = match pattern {
                PopTarget::NumConst(n) | PopTarget::Val(n) => *n,
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
                exec_instrs(then_steps, stack, state, trap, env);
            } else {
                exec_instrs(else_steps, stack, state, trap, env);
            }
        }
        Instr::IfI {
            cond: InstrCond::Pred(_),
            ..
        } => panic!("pred if in rule body"),
        Instr::PushI(expr) => push_expr(expr, stack, state, env),
        Instr::ExecuteI(expr) => {
            if let Expr::CaseE("LOCAL.SET", args) = expr {
                let x = match args.first() {
                    Some(Expr::NatLit(x)) => *x,
                    _ => panic!("LOCAL.SET expected nat index"),
                };
                exec_instrs(&step_local_set_template(x), stack, state, trap, env);
            } else {
                panic!("unsupported ExecuteI: {expr:?}");
            }
        }
        Instr::PerformI(name, args) => {
            if *name == "with_local" {
                perform_with_local(args, state, env);
            } else {
                panic!("unsupported PerformI: {name}");
            }
        }
        Instr::TrapI => *trap = true,
        Instr::ReturnI(_) | Instr::FailI | Instr::ReplaceI { .. } => {
            panic!("func instr in rule body")
        }
    }
}

fn exec_instrs(
    steps: &[Instr],
    stack: &mut Vec<i32>,
    state: &mut ConcreteState,
    trap: &mut bool,
    env: &mut AlEnv,
) {
    for step in steps {
        if *trap {
            return;
        }
        exec_instr(step, stack, state, trap, env);
    }
}

/// Concrete execution of a `Step_...` rule body.
pub fn exec_instrs_concrete(
    steps: &[Instr],
    stack: &mut Vec<i32>,
    state: &mut ConcreteState,
) -> bool {
    let mut trap = false;
    let mut env = AlEnv::new();
    exec_instrs(steps, stack, state, &mut trap, &mut env);
    trap
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::al::defs::{
        NumType, Sign, WasmBinOp, step_local_set_template, step_pure_binop_template,
        step_pure_local_tee_template, step_read_local_get_template,
    };
    use crate::semantics::ConcreteState;

    const LOCAL_SLOTS: usize = 8;
    const MEM_SLOTS: usize = 16;

    fn run_binop(binop: WasmBinOp, i_1: u32, i_2: u32) -> Option<u32> {
        let mut stack = vec![i_1 as i32, i_2 as i32];
        let mut state = ConcreteState::new([0; LOCAL_SLOTS], [0; MEM_SLOTS]);
        let trap = exec_instrs_concrete(
            &step_pure_binop_template(NumType::I32, binop),
            &mut stack,
            &mut state,
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

    #[test]
    fn local_get_pushes_state() {
        let mut state = ConcreteState::new([42; LOCAL_SLOTS], [0; MEM_SLOTS]);
        let mut stack = vec![];
        exec_instrs_concrete(&step_read_local_get_template(0), &mut stack, &mut state);
        assert_eq!(stack, vec![42]);
    }

    #[test]
    fn local_set_writes_state() {
        let mut state = ConcreteState::new([0; LOCAL_SLOTS], [0; MEM_SLOTS]);
        let mut stack = vec![99];
        exec_instrs_concrete(&step_local_set_template(0), &mut stack, &mut state);
        assert_eq!(stack, Vec::<i32>::new());
        assert_eq!(state.locals[0], 99);
    }

    #[test]
    fn local_tee_dup_and_set() {
        let mut state = ConcreteState::new([0; LOCAL_SLOTS], [0; MEM_SLOTS]);
        let mut stack = vec![77];
        exec_instrs_concrete(&step_pure_local_tee_template(1), &mut stack, &mut state);
        assert_eq!(stack, vec![77]);
        assert_eq!(state.locals[1], 77);
    }
}
