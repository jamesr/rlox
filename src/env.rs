use std::collections::HashMap;

use crate::eval;

pub struct Env {
    values: HashMap<String, eval::Value>,
}

impl Env {
    pub fn new() -> Self {
        Self {
            values: HashMap::new(),
        }
    }

    pub fn define(&mut self, name: String, value: eval::Value) {
        self.values.insert(name, value);
    }

    pub fn get(&self, name: String) -> anyhow::Result<eval::Value, String> {
        match self.values.get(&name) {
            Some(v) => Ok(v.clone()),
            None => Err(format!("Undefined variable '{}'.", name)),
        }
    }
}
