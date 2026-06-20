//! Shared Z3 solver configuration.

use z3::{Config, Context};

pub fn z3_context() -> Context {
    let mut cfg = Config::new();
    cfg.set_timeout_msec(5_000);
    Context::new(&cfg)
}
