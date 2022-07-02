use std::rc::Rc;

use crate::{
    ast,
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
    ) -> anyhow::Result<eval::Value, crate::error::RuntimeError> {
        // Make environment
        interpreter.env().push_block(); // TODO - wrong scope
        for i in 0..self.decl.params.len() {
            interpreter
                .env()
                .define(self.decl.params[i].clone(), args[i].clone());
        }
        interpreter.interpret(&self.decl.body)?;
        interpreter.env().pop_block();
        Ok(Value::Nil)
    }

    fn arity(&self) -> usize {
        self.decl.params.len()
    }
}
