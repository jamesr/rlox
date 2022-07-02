use std::collections::HashMap;

use crate::{error::RuntimeError, eval};

type Values<'a> = HashMap<String, eval::Value<'a>>;

pub struct Env<'a> {
    stack: Vec<Values<'a>>,
}

impl<'a> Env<'a> {
    pub fn new() -> Self {
        Self {
            stack: vec![Values::new()],
        }
    }

    fn top_mut(&mut self) -> &mut Values<'a> {
        self.stack.last_mut().unwrap()
    }

    pub fn define(&mut self, name: String, value: eval::Value<'a>) {
        self.top_mut().insert(name, value);
    }

    fn find_mut(&mut self, name: &String) -> Option<&mut eval::Value<'a>> {
        for values in self.stack.iter_mut().rev() {
            if let Some(v) = values.get_mut(name) {
                return Some(v);
            }
        }
        None
    }

    fn find(&self, name: &String) -> Option<eval::Value<'a>> {
        for values in self.stack.iter().rev() {
            if let Some(v) = values.get(name) {
                return Some(v.clone());
            }
        }
        None
    }

    pub fn get(&self, name: String) -> anyhow::Result<eval::Value<'a>, RuntimeError> {
        match self.find(&name) {
            Some(v) => Ok(v.clone()),
            None => Err(format!("Undefined variable '{}'.", name).into()),
        }
    }

    pub fn assign(
        &mut self,
        name: String,
        value: eval::Value<'a>,
    ) -> anyhow::Result<(), RuntimeError> {
        if let Some(mut_ref) = self.find_mut(&name) {
            *mut_ref = value;
            return Ok(());
        }
        Err(format!("Undefined variable '{}'.", name).into())
    }

    pub fn push_block(&mut self) {
        self.stack.push(Values::new());
    }

    pub fn pop_block(&mut self) {
        self.stack.pop();
    }
}
