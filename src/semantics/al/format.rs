//! Pretty-print AL specs as Z3 lowering summaries.

use super::ir::{AlCond, AlExpr, AlSpec, AlStep};
use super::util::is_trap_else_push;

pub fn format_al_z3(al: &AlSpec) -> String {
    let mut parts = Vec::new();
    for step in &al.steps {
        format_step(step, &mut parts);
    }
    parts.join("; ")
}

fn format_step(step: &AlStep, parts: &mut Vec<String>) {
    match step {
        AlStep::Pop(name) => parts.push(format!("pop {name}")),
        AlStep::Push(expr) => parts.push(format!("push {}", format_expr(expr))),
        AlStep::SetLocal { idx, .. } => parts.push(format!("store locals[{idx}]")),
        AlStep::StoreMem { .. } => parts.push("store memory[addr]".into()),
        AlStep::If {
            cond,
            then_steps,
            else_steps,
        } => {
            if is_trap_else_push(then_steps, else_steps) {
                let push = match &else_steps[0] {
                    AlStep::Push(e) => format_expr(e),
                    _ => "?".into(),
                };
                parts.push(format!("ite({},{},0)", format_cond(cond), push));
            } else {
                parts.push(format!(
                    "if {} {{ {} }} else {{ {} }}",
                    format_cond(cond),
                    format_steps(then_steps),
                    format_steps(else_steps)
                ));
            }
        }
        AlStep::Trap => parts.push("trap".into()),
    }
}

fn format_steps(steps: &[AlStep]) -> String {
    let mut parts = Vec::new();
    for s in steps {
        format_step(s, &mut parts);
    }
    parts.join("; ")
}

fn format_cond(cond: &AlCond) -> String {
    match cond {
        AlCond::BinOpEmpty(kind, lhs, rhs) => {
            format!("empty({kind:?},{lhs},{rhs})")
        }
    }
}

fn format_expr(expr: &AlExpr) -> String {
    match expr {
        AlExpr::ConstI32(n) => format!("BV const {n}"),
        AlExpr::Var(name) => name.to_string(),
        AlExpr::BinOp(kind, lhs, rhs) => format!("{kind:?}({lhs},{rhs})"),
        AlExpr::LocalGet(i) => format!("select locals[{i}]"),
        AlExpr::MemLoad(addr) => format!("select memory[{addr}]"),
    }
}
