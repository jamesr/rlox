use std::collections::HashMap;

use crate::ast;
use crate::eval::Interpreter;
use crate::visitor::{self, Visitor};
use anyhow::anyhow;

#[derive(PartialEq)]
enum VariableState {
    Declared,
    Defined,
}

#[derive(PartialEq, Clone, Copy)]
enum FunctionType {
    None,
    Function,
    Initializer,
    Method,
}

#[derive(PartialEq, Clone, Copy)]
enum ClassType {
    None,
    Class,
    Subclass,
}

pub struct Resolver<'a> {
    scopes: Vec<HashMap<String, VariableState>>,
    current_function: FunctionType,
    current_class: ClassType,
    interpreter: &'a mut Interpreter,
}

type Result = anyhow::Result<(), anyhow::Error>;

impl<'a> Resolver<'a> {
    pub fn new(interpreter: &'a mut Interpreter) -> Resolver<'a> {
        Resolver {
            scopes: vec![],
            current_function: FunctionType::None,
            current_class: ClassType::None,
            interpreter,
        }
    }

    pub fn resolve(&mut self, v: &Vec<Box<ast::Stmt>>) -> Result {
        for stmt in v {
            self.visit_stmt(stmt)?;
        }
        Ok(())
    }

    pub fn resolve_expr(&mut self, e: &ast::Expr) -> Result {
        self.visit_expr(e)
    }

    fn resolve_local(&mut self, name: &String, expr_id: u64) {
        for i in (0..self.scopes.len()).rev() {
            if self.scopes[i].contains_key(name) {
                self.interpreter.resolve(expr_id, self.scopes.len() - i - 1)
            }
        }
    }

    fn declare(&mut self, name: String) {
        if let Some(map) = self.scopes.last_mut() {
            map.insert(name, VariableState::Declared);
        }
    }

    fn define(&mut self, name: String) {
        if let Some(map) = self.scopes.last_mut() {
            map.insert(name, VariableState::Defined);
        }
    }

    fn resolve_function(&mut self, f: &ast::FunctionStmt, fun_type: FunctionType) -> Result {
        let enclosing_function = self.current_function;
        self.current_function = fun_type;
        self.begin_scope();

        for p in &f.params {
            self.declare(p.clone());
            self.define(p.clone());
        }

        self.resolve(&f.body)?;

        self.end_scope();
        self.current_function = enclosing_function;
        Ok(())
    }

    fn begin_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    fn end_scope(&mut self) {
        self.scopes.pop();
    }
}

impl visitor::Visitor<Result, Result> for Resolver<'_> {
    fn expr_result_to_stmt_result(&self, e: Result) -> Result {
        e
    }

    fn visit_literal(&mut self, _: &ast::LiteralExpr) -> Result {
        Ok(())
    }

    fn visit_binary_expr(&mut self, e: &ast::BinaryExpr) -> Result {
        self.visit_expr(&e.left)?;
        self.visit_expr(&e.right)
    }

    fn visit_grouping_expr(&mut self, e: &ast::GroupingExpr) -> Result {
        self.visit_expr(&e.expr)
    }

    fn visit_unary_expr(&mut self, e: &ast::UnaryExpr) -> Result {
        self.visit_expr(&e.right)
    }

    fn visit_variable(&mut self, v: &ast::VariableExpr) -> Result {
        if let Some(scope) = self.scopes.last() {
            if scope.get(&v.name) == Some(&VariableState::Declared) {
                return Err(anyhow!(
                    "Can't read local variable from its own initializer."
                ));
            }
        }
        self.resolve_local(&v.name, v.id());
        Ok(())
    }

    fn visit_assign(&mut self, a: &ast::AssignExpr) -> Result {
        self.visit_expr(&a.value)?;
        self.resolve_local(&a.name, a.id());

        Ok(())
    }

    fn visit_logical(&mut self, l: &ast::LogicalExpr) -> Result {
        self.visit_expr(&l.left)?;
        self.visit_expr(&l.right)
    }

    fn visit_call(&mut self, c: &ast::CallExpr) -> Result {
        self.visit_expr(&c.callee)?;

        for arg in &c.args {
            self.visit_expr(arg)?;
        }

        Ok(())
    }

    fn visit_set(&mut self, s: &ast::SetExpr) -> Result {
        self.resolve_expr(&s.value)?;
        self.resolve_expr(&s.object)?;
        Ok(())
    }

    fn visit_get(&mut self, g: &ast::GetExpr) -> Result {
        self.resolve_expr(&g.object)
    }

    fn visit_super(&mut self, s: &ast::SuperExpr) -> Result {
        if self.current_class == ClassType::None {
            return Err(anyhow!("Can't use 'super' outside of a class."));
        }
        if self.current_class != ClassType::Subclass {
            return Err(anyhow!("Can't use 'super' in a class with no subclass."));
        }
        self.resolve_local(&"super".to_string(), s.id());
        Ok(())
    }

    fn visit_this(&mut self, t: &ast::ThisExpr) -> Result {
        if self.current_class != ClassType::Class {
            return Err(anyhow!("Can't use 'this' outside of a class."));
        }
        self.resolve_local(&"this".to_string(), t.id());
        Ok(())
    }

    fn visit_block(&mut self, v: &Vec<Box<ast::Stmt>>) -> Result {
        self.begin_scope();

        self.resolve(v)?;

        self.end_scope();

        Ok(())
    }

    fn visit_print_stmt(&mut self, e: &ast::Expr) -> Result {
        self.visit_expr(e)
    }

    fn visit_return_stmt(&mut self, r: &Option<Box<ast::Expr>>) -> Result {
        if self.current_function == FunctionType::None {
            return Err(anyhow!("Can't return from top-level code."));
        }
        if let Some(e) = r {
            if self.current_function == FunctionType::Initializer {
                return Err(anyhow!("Can't return a value from an initializer."));
            }
            self.visit_expr(e)?;
        }
        Ok(())
    }

    fn visit_var_decl_stmt(&mut self, v: &ast::VarDecl) -> Result {
        self.declare(v.name.clone());
        if let Some(initializer) = &v.initializer {
            self.visit_expr(initializer)?;
        }
        self.define(v.name.clone());
        Ok(())
    }

    fn visit_if_stmt(&mut self, i: &ast::IfStmt) -> Result {
        self.visit_expr(&i.condition)?;
        self.visit_stmt(&i.then_branch)?;
        if let Some(stmt) = &i.else_branch {
            self.visit_stmt(stmt)?;
        }
        Ok(())
    }

    fn visit_while_stmt(&mut self, w: &ast::WhileStmt) -> Result {
        self.visit_expr(&w.condition)?;
        self.visit_stmt(&w.body)
    }

    fn visit_function_stmt(&mut self, f: &std::rc::Rc<ast::FunctionStmt>) -> Result {
        self.declare(f.name.clone());
        self.define(f.name.clone());

        let fun_type = if f.name == "init" {
            FunctionType::Initializer
        } else {
            FunctionType::Function
        };
        self.resolve_function(f, fun_type)?;
        Ok(())
    }

    fn visit_class_stmt(&mut self, c: &ast::ClassStmt) -> Result {
        let enclosing_class = self.current_class;
        self.current_class = ClassType::Class;

        self.declare(c.name.clone());
        self.define(c.name.clone());

        if let Some(superclass) = &c.superclass {
            self.current_class = ClassType::Subclass;
            if let ast::Expr::Variable(v) = &**superclass {
                if v.name == c.name {
                    return Err(anyhow!("A class can't inherit from itself."));
                }
            }
            self.resolve_expr(&superclass)?;

            self.begin_scope();

            self.scopes
                .last_mut()
                .unwrap()
                .insert("super".to_string(), VariableState::Defined);
        }

        self.begin_scope();
        self.scopes
            .last_mut()
            .unwrap()
            .insert("this".to_string(), VariableState::Defined);

        for method in &c.methods {
            self.resolve_function(&method, FunctionType::Method)?;
        }

        self.end_scope();

        if c.superclass.is_some() {
            self.end_scope();
        }

        self.current_class = enclosing_class;
        Ok(())
    }
}
