//! Variable environment for AL step execution.

use std::collections::HashMap;

pub(crate) struct AlEnv<V> {
    vars: HashMap<&'static str, V>,
}

impl<V: Clone> Clone for AlEnv<V> {
    fn clone(&self) -> Self {
        Self {
            vars: self.vars.clone(),
        }
    }
}

impl<V: Clone> AlEnv<V> {
    pub(crate) fn new() -> Self {
        Self {
            vars: HashMap::new(),
        }
    }

    pub(crate) fn bind(&mut self, name: &'static str, val: V) {
        self.vars.insert(name, val);
    }

    pub(crate) fn get(&self, name: &str) -> &V {
        self.vars.get(name).expect("unbound AL variable")
    }
}
