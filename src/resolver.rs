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
}

pub struct Resolver<'a> {
    scopes: Vec<HashMap<String, VariableState>>,
    current_function: FunctionType,
    interpreter: &'a mut Interpreter,
}

type Result = anyhow::Result<(), anyhow::Error>;

impl<'a> Resolver<'a> {
    pub fn new(interpreter: &'a mut Interpreter) -> Resolver<'a> {
        Resolver {
            scopes: vec![],
            current_function: FunctionType::None,
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
        self.resolve_expr(&g.object)?;
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
        if self.current_function != FunctionType::Function {
            return Err(anyhow!("Can't return from top-level code."));
        }
        if let Some(e) = r {
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

        self.resolve_function(f, FunctionType::Function)?;
        Ok(())
    }

    fn visit_class_stmt(&mut self, c: &ast::ClassStmt) -> Result {
        self.declare(c.name.clone());
        self.define(c.name.clone());
        Ok(())
    }
}
