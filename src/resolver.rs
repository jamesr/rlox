use std::collections::HashMap;

use crate::eval::Interpreter;
use crate::visitor::{self, Visitor};
use crate::{ast, error, parser};

#[derive(PartialEq)]
enum VariableState {
    Declared,
    Defined,
}

#[derive(PartialEq, Clone, Copy, Debug)]
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
    location_table: &'a parser::LocationTable,
}

type ResolverResult = Result<(), error::Error>;

impl<'a> Resolver<'a> {
    pub fn new(
        interpreter: &'a mut Interpreter,
        location_table: &'a parser::LocationTable,
    ) -> Resolver<'a> {
        Resolver {
            scopes: vec![],
            current_function: FunctionType::None,
            current_class: ClassType::None,
            interpreter,
            location_table,
        }
    }

    pub fn resolve(&mut self, v: &Vec<Box<ast::Stmt>>) -> ResolverResult {
        for stmt in v {
            self.visit_stmt(stmt)?;
        }
        Ok(())
    }

    pub fn resolve_expr(&mut self, e: &ast::Expr) -> ResolverResult {
        self.visit_expr(e)
    }

    fn ast_loc(&self, id: u64) -> error::Location {
        self.location_table
            .get(&id)
            .unwrap_or(&error::Location::default())
            .clone()
    }

    fn resolve_local(&mut self, name: &String, expr_id: u64) {
        for i in (0..self.scopes.len()).rev() {
            if self.scopes[i].contains_key(name) {
                self.interpreter.resolve(expr_id, self.scopes.len() - i - 1);
                return;
            }
        }
    }

    fn declare(&mut self, name: String, loc: error::Location) -> ResolverResult {
        if let Some(map) = self.scopes.last_mut() {
            if map.contains_key(&name) {
                return Err(error::Error::Parse(error::ParseError::new(
                    &format!(
                        "Error at '{}': Already a variable with this name in this scope.",
                        name
                    ),
                    loc,
                )));
            }
            map.insert(name, VariableState::Declared);
        }
        Ok(())
    }

    fn define(&mut self, name: String) {
        if let Some(map) = self.scopes.last_mut() {
            map.insert(name, VariableState::Defined);
        }
    }

    fn resolve_function(
        &mut self,
        f: &ast::FunctionStmt,
        fun_type: FunctionType,
    ) -> ResolverResult {
        let enclosing_function = self.current_function;
        self.current_function = fun_type;
        self.begin_scope();

        for p in &f.params {
            self.declare(p.clone(), self.ast_loc(f.id()))?;
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

impl visitor::Visitor<ResolverResult, ResolverResult> for Resolver<'_> {
    fn expr_result_to_stmt_result(&self, e: ResolverResult) -> ResolverResult {
        e
    }

    fn visit_literal(&mut self, _l: &ast::LiteralExpr) -> ResolverResult {
        Ok(())
    }

    fn visit_binary_expr(&mut self, e: &ast::BinaryExpr) -> ResolverResult {
        self.visit_expr(&e.left)?;
        self.visit_expr(&e.right)
    }

    fn visit_grouping_expr(&mut self, e: &ast::GroupingExpr) -> ResolverResult {
        self.visit_expr(&e.expr)
    }

    fn visit_unary_expr(&mut self, e: &ast::UnaryExpr) -> ResolverResult {
        self.visit_expr(&e.right)
    }

    fn visit_variable(&mut self, v: &ast::VariableExpr) -> ResolverResult {
        if let Some(scope) = self.scopes.last() {
            if scope.get(&v.name) == Some(&VariableState::Declared) {
                return Err(error::ParseError::new(
                    &format!(
                        "Error at '{}': Can't read local variable in its own initializer.",
                        &v.name
                    ),
                    self.ast_loc(v.id()),
                )
                .into());
            }
        }
        self.resolve_local(&v.name, v.id());
        Ok(())
    }

    fn visit_assign(&mut self, a: &ast::AssignExpr) -> ResolverResult {
        self.visit_expr(&a.value)?;
        self.resolve_local(&a.name, a.id());

        Ok(())
    }

    fn visit_logical(&mut self, l: &ast::LogicalExpr) -> ResolverResult {
        self.visit_expr(&l.left)?;
        self.visit_expr(&l.right)
    }

    fn visit_call(&mut self, c: &ast::CallExpr) -> ResolverResult {
        self.visit_expr(&c.callee)?;

        for arg in &c.args {
            self.visit_expr(arg)?;
        }

        Ok(())
    }

    fn visit_set(&mut self, s: &ast::SetExpr) -> ResolverResult {
        self.resolve_expr(&s.value)?;
        self.resolve_expr(&s.object)?;
        Ok(())
    }

    fn visit_get(&mut self, g: &ast::GetExpr) -> ResolverResult {
        self.resolve_expr(&g.object)
    }

    fn visit_super(&mut self, s: &ast::SuperExpr) -> ResolverResult {
        if self.current_class == ClassType::None {
            return Err(error::ParseError::new(
                "Error at 'super': Can't use 'super' outside of a class.",
                self.ast_loc(s.id()),
            )
            .into());
        }
        if self.current_class != ClassType::Subclass {
            return Err(error::ParseError::new(
                "Error at 'super': Can't use 'super' in a class with no superclass.",
                self.ast_loc(s.id()),
            )
            .into());
        }
        self.resolve_local(&"super".to_string(), s.id());
        Ok(())
    }

    fn visit_this(&mut self, t: &ast::ThisExpr) -> ResolverResult {
        if self.current_class == ClassType::None {
            return Err(error::ParseError::new(
                "Error at 'this': Can't use 'this' outside of a class.",
                self.ast_loc(t.id()),
            )
            .into());
        }
        self.resolve_local(&"this".to_string(), t.id());
        Ok(())
    }

    fn visit_block(&mut self, v: &Vec<Box<ast::Stmt>>) -> ResolverResult {
        self.begin_scope();

        self.resolve(v)?;

        self.end_scope();

        Ok(())
    }

    fn visit_print_stmt(&mut self, e: &ast::Expr) -> ResolverResult {
        self.visit_expr(e)
    }

    fn visit_return_stmt(&mut self, r: &ast::ReturnStmt) -> ResolverResult {
        if self.current_function == FunctionType::None {
            return Err(error::ParseError::new(
                "Error at 'return': Can't return from top-level code.",
                self.ast_loc(r.id()),
            )
            .into());
        }
        if let Some(e) = &r.value {
            if self.current_function == FunctionType::Initializer {
                return Err(error::ParseError::new(
                    "Error at 'return': Can't return a value from an initializer.",
                    self.ast_loc(e.id()),
                )
                .into());
            }
            self.visit_expr(e)?;
        }
        Ok(())
    }

    fn visit_var_decl_stmt(&mut self, v: &ast::VarDecl) -> ResolverResult {
        self.declare(v.name.clone(), self.ast_loc(v.id()))?;
        if let Some(initializer) = &v.initializer {
            self.visit_expr(initializer)?;
        }
        self.define(v.name.clone());
        Ok(())
    }

    fn visit_if_stmt(&mut self, i: &ast::IfStmt) -> ResolverResult {
        self.visit_expr(&i.condition)?;
        self.visit_stmt(&i.then_branch)?;
        if let Some(stmt) = &i.else_branch {
            self.visit_stmt(stmt)?;
        }
        Ok(())
    }

    fn visit_while_stmt(&mut self, w: &ast::WhileStmt) -> ResolverResult {
        self.visit_expr(&w.condition)?;
        self.visit_stmt(&w.body)
    }

    fn visit_function_stmt(&mut self, f: &std::rc::Rc<ast::FunctionStmt>) -> ResolverResult {
        self.declare(f.name.clone(), self.ast_loc(f.id()))?;
        self.define(f.name.clone());

        self.resolve_function(f, FunctionType::Function)?;
        Ok(())
    }

    fn visit_class_stmt(&mut self, c: &ast::ClassStmt) -> ResolverResult {
        let enclosing_class = self.current_class;
        self.current_class = ClassType::Class;

        self.declare(c.name.clone(), self.ast_loc(c.id()))?;
        self.define(c.name.clone());

        if let Some(superclass) = &c.superclass {
            self.current_class = ClassType::Subclass;
            if let ast::Expr::Variable(v) = &**superclass {
                if v.name == c.name {
                    return Err(error::ParseError::new(
                        &format!("Error at '{}': A class can't inherit from itself.", &v.name),
                        self.ast_loc(v.id()),
                    )
                    .into());
                }
            }
            self.resolve_expr(&superclass)?;

            self.begin_scope();

            self.define("super".to_string());
        }

        self.begin_scope();
        self.define("this".to_string());

        for method in &c.methods {
            let fun_type = if method.name == "init" {
                FunctionType::Initializer
            } else {
                FunctionType::Method
            };
            self.resolve_function(&method, fun_type)?;
        }

        self.end_scope();

        if c.superclass.is_some() {
            self.end_scope();
        }

        self.current_class = enclosing_class;
        Ok(())
    }
}
