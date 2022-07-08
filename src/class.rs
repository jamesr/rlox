use std::{cell::RefCell, collections::HashMap, rc::Rc};

use by_address::ByAddress;

use crate::{
    error::{self, RuntimeError},
    eval::{self, Interpreter, Value},
    function,
};

#[derive(Debug)]
pub struct Callable {
    pub class: Rc<Class>,
}

impl Callable {
    pub fn new(class: Rc<Class>) -> Self {
        Callable { class }
    }
}

type MethodMap = HashMap<String, by_address::ByAddress<Rc<function::Function>>>;

#[derive(Debug, PartialEq)]
pub struct Class {
    pub name: String,
    methods: MethodMap,
    superclass: Option<ByAddress<Rc<Class>>>,
}

impl Class {
    pub fn new(name: String, methods: MethodMap, superclass: Option<ByAddress<Rc<Class>>>) -> Self {
        Class {
            name,
            methods,
            superclass,
        }
    }

    pub fn find_method(&self, name: &str) -> Option<Rc<function::Function>> {
        if let Some(method) = self.methods.get(name) {
            return Some((**method).clone());
        }
        if let Some(superclass) = &self.superclass {
            return superclass.find_method(name);
        }
        None
    }
}

#[derive(Debug, PartialEq)]
pub struct Instance {
    pub class: Rc<Class>,
    fields: HashMap<String, Value>,
}

impl Instance {
    pub fn new(class: Rc<Class>) -> Self {
        Instance {
            class,
            fields: HashMap::new(),
        }
    }

    pub fn get(&self, name: &str, this: Value) -> Result<Value, RuntimeError> {
        if let Some(value) = self.fields.get(name) {
            return Ok(value.clone());
        }

        if let Some(method) = self.class.find_method(name) {
            return Ok(method.bind(this));
        }

        Err(RuntimeError::new(
            format!("Undefined property '{}'.", name),
            error::Location::default(),
        ))
    }

    pub fn set(&mut self, name: String, value: Value) -> Result<Value, RuntimeError> {
        self.fields.insert(name, value.clone());
        Ok(value)
    }
}

impl eval::Callable for Callable {
    fn call(&self, interpreter: &mut Interpreter, args: Vec<Value>) -> Result<Value, RuntimeError> {
        let instance = Value::Instance(Rc::new(RefCell::new(Instance::new(self.class.clone()))));

        if let Some(initializer) = self.class.methods.get("init") {
            if let Value::Callable(bound_initializer) = initializer.bind(instance.clone()) {
                bound_initializer.call(interpreter, args)?;
            } else {
                return Err(RuntimeError::new(
                    format!("Failed to bind initializer for '{}'.", &self.class.name),
                    error::Location::default(),
                ));
            }
        }

        Ok(instance)
    }

    fn arity(&self) -> usize {
        match self.class.methods.get("init") {
            Some(initializer) => initializer.arity(),
            None => 0,
        }
    }

    fn display_name(&self) -> String {
        format!("<fn {}>", &self.class.name)
    }
}
