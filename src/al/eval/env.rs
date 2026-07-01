//! Variable environment for AL evaluation.

use super::value::AlValue;
use std::collections::HashMap;

#[derive(Clone, Debug, Default)]
pub struct Env {
    bindings: HashMap<String, AlValue>,
}

impl Env {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn bind(&mut self, name: &str, value: AlValue) {
        self.bindings.insert(name.to_string(), value);
    }

    pub fn get(&self, name: &str) -> Option<&AlValue> {
        self.bindings.get(name)
    }
}
