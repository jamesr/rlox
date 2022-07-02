use std::{
    cell::RefCell,
    collections::{hash_map, HashMap},
    rc::Rc,
};

use crate::{error::RuntimeError, eval};

type Values = HashMap<String, eval::Value>;

pub struct Env {
    parent: Option<Rc<RefCell<Env>>>,
    values: Values,
}

impl Env {
    pub fn new() -> Env {
        Env {
            parent: None,
            values: Values::new(),
        }
    }

    pub fn with_parent(parent: Rc<RefCell<Env>>) -> Env {
        Env {
            parent: Some(parent),
            values: Values::new(),
        }
    }

    pub fn define(&mut self, name: String, value: eval::Value) {
        self.values.insert(name, value);
    }

    fn find(&self, name: &String) -> Option<eval::Value> {
        if let Some(v) = self.values.get(name) {
            return Some(v.clone());
        }
        if let Some(parent) = self.parent.clone() {
            return parent.borrow().find(name);
        }
        None
    }

    pub fn get(&self, name: String) -> anyhow::Result<eval::Value, RuntimeError> {
        match self.find(&name) {
            Some(v) => Ok(v.clone()),
            None => Err(format!("Undefined variable '{}'.", name).into()),
        }
    }

    pub fn assign(&mut self, name: String, value: eval::Value) -> anyhow::Result<(), RuntimeError> {
        if let hash_map::Entry::Occupied(mut entry) = self.values.entry(name.clone()) {
            entry.insert(value);
            return Ok(());
        }
        if let Some(parent) = &self.parent {
            return parent.borrow_mut().assign(name.clone(), value);
        }
        Err(format!("Undefined variable '{}'.", name).into())
    }
}
