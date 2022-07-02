use std::rc::Rc;

use crate::{
    ast,
    error::RuntimeError,
    eval::{self, Value},
};

#[derive(Debug)]
pub struct Function {
    decl: Rc<ast::FunctionStmt>,
}

impl Function {
    pub fn new(decl: &Rc<ast::FunctionStmt>) -> Function {
        Function { decl: decl.clone() }
    }
}

impl eval::Callable for Function {
    fn call(
        &self,
        interpreter: &mut eval::Interpreter,
        args: Vec<eval::Value>,
    ) -> anyhow::Result<eval::Value, RuntimeError> {
        // Make environment
        interpreter.env().push_block(); // TODO - wrong scope
        for i in 0..self.decl.params.len() {
            interpreter
                .env()
                .define(self.decl.params[i].clone(), args[i].clone());
        }
        let result = interpreter.interpret(&self.decl.body);
        let value = match result {
            Err(RuntimeError::Return(v)) => v,
            Err(e) => {
                return Err(e);
            }
            _ => Value::Nil,
        };
        interpreter.env().pop_block();
        Ok(value)
    }

    fn arity(&self) -> usize {
        self.decl.params.len()
    }
}
