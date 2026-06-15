//! Shared helpers for AL analysis and lowering.

use super::ir::{AlExpr, AlStep};

pub(crate) fn is_trap_else_push(then_steps: &[AlStep], else_steps: &[AlStep]) -> bool {
    then_steps == [AlStep::Trap]
        && else_steps.len() == 1
        && matches!(else_steps[0], AlStep::Push(_))
}

pub(crate) fn else_push_expr<'a>(else_steps: &'a [AlStep]) -> &'a AlExpr {
    match &else_steps[0] {
        AlStep::Push(e) => e,
        _ => unreachable!("expected single Push in else branch"),
    }
}
