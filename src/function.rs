use crate::{
    ast,
    eval::{self, Value},
};

#[derive(Debug)]
pub struct Function<'a> {
    decl: &'a ast::FunctionStmt,
}

impl<'a> Function<'a> {
    pub fn new(decl: &'a ast::FunctionStmt) -> Function<'a> {
        Function { decl }
    }
}

impl<'a> eval::Callable<'a> for Function<'a> {
    fn call(
        &self,
        interpreter: &mut eval::Interpreter<'a>,
        args: Vec<eval::Value<'a>>,
    ) -> anyhow::Result<eval::Value<'a>, crate::error::RuntimeError> {
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
