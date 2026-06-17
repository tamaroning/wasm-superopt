//! Flat AL IR for hand-written instruction specs (not binop meta encoding).

pub use super::defs::BinOpKind;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AlSpec {
    pub steps: Vec<AlStep>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AlStep {
    Pop(&'static str),
    Push(AlExpr),
    SetLocal {
        idx: u32,
        var: &'static str,
    },
    StoreMem {
        addr: &'static str,
        val: &'static str,
    },
    If {
        cond: AlCond,
        then_steps: Vec<AlStep>,
        else_steps: Vec<AlStep>,
    },
    Trap,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AlExpr {
    ConstI32(i32),
    #[allow(dead_code)]
    Var(&'static str),
    BinOp(BinOpKind, &'static str, &'static str),
    LocalGet(u32),
    MemLoad(&'static str),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AlCond {
    BinOpEmpty(BinOpKind, &'static str, &'static str),
}

/// Pretty-print flattened [`AlSpec`] steps (for `--print-semantics`).
pub fn format_al_pretty(al: &AlSpec) -> String {
    let mut lines = Vec::new();
    for step in &al.steps {
        format_step_pretty(step, 0, &mut lines);
    }
    lines.join("\n")
}

fn format_step_pretty(step: &AlStep, indent: usize, lines: &mut Vec<String>) {
    let pad = "  ".repeat(indent);
    match step {
        AlStep::Pop(name) => lines.push(format!("{pad}pop {name}")),
        AlStep::Push(expr) => lines.push(format!("{pad}push {}", format_expr_pretty(expr))),
        AlStep::SetLocal { idx, var } => {
            lines.push(format!("{pad}set local[{idx}] = {var}"))
        }
        AlStep::StoreMem { addr, val } => {
            lines.push(format!("{pad}store memory[{addr}] = {val}"))
        }
        AlStep::If {
            cond,
            then_steps,
            else_steps,
        } => {
            lines.push(format!("{pad}if {} then", format_cond_pretty(cond)));
            for s in then_steps {
                format_step_pretty(s, indent + 1, lines);
            }
            lines.push(format!("{pad}else"));
            for s in else_steps {
                format_step_pretty(s, indent + 1, lines);
            }
        }
        AlStep::Trap => lines.push(format!("{pad}trap")),
    }
}

fn format_cond_pretty(cond: &AlCond) -> String {
    match cond {
        AlCond::BinOpEmpty(kind, lhs, rhs) => {
            format!("empty({}, {lhs}, {rhs})", kind.label())
        }
    }
}

fn format_expr_pretty(expr: &AlExpr) -> String {
    match expr {
        AlExpr::ConstI32(n) => format!("const {n}"),
        AlExpr::Var(name) => (*name).to_string(),
        AlExpr::BinOp(kind, lhs, rhs) => format!("{}({lhs}, {rhs})", kind.label()),
        AlExpr::LocalGet(idx) => format!("local[{idx}]"),
        AlExpr::MemLoad(addr) => format!("memory[{addr}]"),
    }
}
