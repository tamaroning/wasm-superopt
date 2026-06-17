//! Straight-line embedding policy for AL lowering.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EmbeddingPolicy {
    /// When lowering `if trap else push`, push a dummy value on the trap path.
    pub trap_dummy_push: bool,
}

pub const STRAIGHT_LINE_EMBED: EmbeddingPolicy = EmbeddingPolicy {
    trap_dummy_push: true,
};
