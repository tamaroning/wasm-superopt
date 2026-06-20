//! Shared helpers for AL analysis and lowering.

use super::ir::{AlStep};

pub(crate) fn is_trap_else_push(then_steps: &[AlStep], else_steps: &[AlStep]) -> bool {
    then_steps == [AlStep::Trap]
        && else_steps.len() == 1
        && matches!(else_steps[0], AlStep::Push(_))
}
