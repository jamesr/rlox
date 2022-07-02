use std::{cell::RefCell, rc::Rc};

use crate::{
    ast, env,
    error::RuntimeError,
    eval::{self, Value},
};

#[derive(Debug)]
pub struct Function {
    decl: Rc<ast::FunctionStmt>,
    closure: Rc<RefCell<env::Env>>,
}

impl Function {
    pub fn new(decl: &Rc<ast::FunctionStmt>, closure: Rc<RefCell<env::Env>>) -> Function {
        Function {
            decl: decl.clone(),
            closure,
        }
    }
}

impl eval::Callable for Function {
    fn call(
        &self,
        interpreter: &mut eval::Interpreter,
        args: Vec<eval::Value>,
    ) -> anyhow::Result<eval::Value, RuntimeError> {
        // Make environment
        let env = Rc::new(RefCell::new(env::Env::with_parent(self.closure.clone())));

        {
            let mut env_mut = env.borrow_mut();
            for i in 0..self.decl.params.len() {
                env_mut.define(self.decl.params[i].clone(), args[i].clone());
            }
        }

        let result = interpreter.execute_block(&self.decl.body, env);
        let value = match result {
            Err(RuntimeError::Return(v)) => v,
            Err(e) => {
                return Err(e);
            }
            _ => Value::Nil,
        };
        Ok(value)
    }

    fn arity(&self) -> usize {
        self.decl.params.len()
    }
}
