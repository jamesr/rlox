use std::{
    cell::RefCell,
    collections::{hash_map, HashMap},
    rc::Rc,
};

use crate::{
    error::{self, RuntimeError},
    eval,
};

type Values = HashMap<String, eval::Value>;

#[derive(Debug)]
pub struct Env {
    parent: Option<Rc<RefCell<Env>>>,
    values: Values,
}

pub fn ancestor(start: &Rc<RefCell<Env>>, depth: usize) -> Option<Rc<RefCell<Env>>> {
    let mut node = Some(start.clone());

    for _ in 0..depth {
        let mut next = None;
        if let Some(ref node) = node {
            let bn = node.borrow();
            next = bn.parent.clone();
        }
        if next.is_none() {
            return None;
        }
        node = next;
    }

    node
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

    pub fn values(&self) -> &Values {
        &self.values
    }

    pub fn define(&mut self, name: String, value: eval::Value) {
        self.values.insert(name, value);
    }

    pub fn get(&self, name: &String, loc: error::Location) -> Result<eval::Value, RuntimeError> {
        if let Some(v) = self.values.get(name) {
            return Ok(v.clone());
        }
        Err((format!("Undefined variable '{}'.", name), loc).into())
    }

    pub fn assign(
        &mut self,
        name: String,
        value: eval::Value,
        loc: error::Location,
    ) -> Result<(), RuntimeError> {
        if let hash_map::Entry::Occupied(mut entry) = self.values.entry(name.clone()) {
            entry.insert(value);
            return Ok(());
        }
        Err((format!("Undefined variable '{}'.", name), loc).into())
    }
}
