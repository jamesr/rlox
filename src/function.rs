use std::{cell::RefCell, rc::Rc};

use by_address::ByAddress;

use crate::{
    ast, env,
    error::RuntimeError,
    eval::{self, Value},
};

#[derive(Debug)]
pub struct Function {
    decl: Rc<ast::FunctionStmt>,
    closure: Rc<RefCell<env::Env>>,
    initializer: bool,
}

impl Function {
    pub fn new(decl: &Rc<ast::FunctionStmt>, closure: Rc<RefCell<env::Env>>) -> Function {
        Function {
            decl: decl.clone(),
            closure,
            initializer: false,
        }
    }

    pub fn initializer(decl: &Rc<ast::FunctionStmt>, closure: Rc<RefCell<env::Env>>) -> Function {
        Function {
            decl: decl.clone(),
            closure,
            initializer: true,
        }
    }

    pub fn bind(&self, this: eval::Value) -> eval::Value {
        let env = Rc::new(RefCell::new(env::Env::with_parent(self.closure.clone())));
        env.borrow_mut().define("this".to_string(), this);
        let function = if self.initializer {
            Function::initializer(&self.decl, env)
        } else {
            Function::new(&self.decl, env)
        };
        eval::Value::Callable(ByAddress(Rc::new(function)))
    }
}

impl eval::Callable for Function {
    fn call(
        &self,
        interpreter: &mut eval::Interpreter,
        args: Vec<eval::Value>,
    ) -> Result<eval::Value, RuntimeError> {
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
            Err(RuntimeError::Return(v)) => {
                if self.initializer {
                    self.closure.borrow().get(&"this".to_string())?
                } else {
                    v
                }
            }
            Err(e) => {
                return Err(e);
            }
            _ => {
                if self.initializer {
                    self.closure.borrow().get(&"this".to_string())?
                } else {
                    Value::Nil
                }
            }
        };
        Ok(value)
    }

    fn arity(&self) -> usize {
        self.decl.params.len()
    }

    fn display_name(&self) -> String {
        format!("<fn {}>", &self.decl.name)
    }
}
