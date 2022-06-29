use std::fmt::Display;

use crate::{
    ast, env,
    error::RuntimeError,
    scanner::{self, Token, TokenValue},
    visitor::Visitor,
};

#[derive(Debug, PartialEq, Clone)]
pub enum Value {
    String(String),
    Number(f64),
    Bool(bool),
    Nil,
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::String(s) => write!(f, "\"{}\"", s),
            Value::Number(n) => write!(f, "{}", n),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Nil => write!(f, "nil"),
        }
    }
}

pub struct Interpreter {
    env: Box<env::Env>,
}

type ExprResult = anyhow::Result<Value, RuntimeError>;
type StmtResult = anyhow::Result<(), RuntimeError>;

impl Interpreter {
    pub fn new() -> Interpreter {
        Interpreter {
            env: Box::new(env::Env::new()),
        }
    }

    pub fn interpret<'a>(&mut self, stmts: Vec<Box<ast::Stmt<'a>>>) -> StmtResult {
        for s in stmts {
            self.visit_stmt(&*s)?;
        }
        Ok(())
    }

    pub fn interpret_expr(&mut self, e: &ast::Expr) -> ExprResult {
        self.visit_expr(e)
    }
}

fn truthy(v: &Value) -> bool {
    match v {
        Value::Nil => false,
        Value::Bool(b) => *b,
        _ => true,
    }
}

fn as_number(v: &Value) -> anyhow::Result<f64, RuntimeError> {
    match v {
        Value::Number(n) => Ok(*n),
        _ => Err(format!("value {:?} is not a number", v).into()),
    }
}

impl Visitor<ExprResult, StmtResult> for Interpreter {
    fn expr_result_to_stmt_result(&self, e: ExprResult) -> StmtResult {
        match e {
            Ok(_) => Ok(()),
            Err(e) => Err(e),
        }
    }

    fn visit_literal(&mut self, v: &scanner::TokenValue) -> ExprResult {
        Ok(match v {
            TokenValue::String(s) => Value::String(s.to_string()),
            TokenValue::Number(n) => Value::Number(*n),
            TokenValue::Bool(b) => Value::Bool(*b),
            TokenValue::Nil => Value::Nil,
        })
    }

    fn visit_binary_expr(&mut self, e: &ast::BinaryExpr) -> ExprResult {
        let left = self.visit_expr(&e.left)?;
        let right = self.visit_expr(&e.right)?;

        use scanner::TokenType::*;
        match e.operator.token_type {
            Minus => Ok(Value::Number(as_number(&left)? - as_number(&right)?)),
            Slash => Ok(Value::Number(as_number(&left)? / as_number(&right)?)),
            Star => Ok(Value::Number(as_number(&left)? * as_number(&right)?)),
            Plus => match left {
                Value::Number(left_number) => match right {
                    Value::Number(right_number) => Ok(Value::Number(left_number + right_number)),
                    _ => {
                        Err(format!("type mismatch for operator +, number and {:?}", right).into())
                    }
                },

                Value::String(left_string) => match right {
                    Value::String(right_string) => Ok(Value::String(left_string + &right_string)),

                    _ => {
                        Err(format!("type mismatch for operator +, string and {:?}", right).into())
                    }
                },

                _ => Err(format!("unsupported type for operator + {:?}", left).into()),
            },
            Greater => Ok(Value::Bool(as_number(&left)? > as_number(&right)?)),
            GreaterEqual => Ok(Value::Bool(as_number(&left)? >= as_number(&right)?)),
            Less => Ok(Value::Bool(as_number(&left)? < as_number(&right)?)),
            LessEqual => Ok(Value::Bool(as_number(&left)? <= as_number(&right)?)),
            BangEqual => Ok(Value::Bool(left != right)),
            EqualEqual => Ok(Value::Bool(left == right)),

            _ => Err(format!("unknown operator {}", e.operator.lexeme).into()),
        }
    }

    fn visit_grouping_expr(&mut self, e: &ast::Expr) -> ExprResult {
        self.visit_expr(e)
    }

    fn visit_unary_expr(&mut self, e: &ast::UnaryExpr) -> ExprResult {
        use scanner::TokenType::*;
        let val = self.visit_expr(&e.right)?;
        match e.operator.token_type {
            Minus => match val {
                Value::Number(n) => Ok(Value::Number(-n)),
                _ => Err("unary - must be applied to a number".into()),
            },
            Bang => Ok(Value::Bool(!truthy(&val))),
            _ => Err("unsupported unary operator".into()),
        }
    }

    fn visit_variable(&mut self, t: &Token) -> ExprResult {
        self.env.get(t.lexeme.to_string())
    }

    fn visit_assign(&mut self, a: &ast::AssignExpr) -> ExprResult {
        let value = self.visit_expr(&*a.value)?;
        self.env.assign(a.name.lexeme.to_string(), value.clone())?;
        Ok(value)
    }

    fn visit_logical(&mut self, l: &ast::LogicalExpr) -> ExprResult {
        let left = self.visit_expr(&l.left).ok().unwrap();

        if l.operator.token_type == scanner::TokenType::Or {
            if truthy(&left) {
                return Ok(left);
            }
        } else {
            assert_eq!(l.operator.token_type, scanner::TokenType::And);
            if !truthy(&left) {
                return Ok(left);
            }
        }
        self.visit_expr(&l.right)
    }

    fn visit_block(&mut self, v: &Vec<Box<ast::Stmt>>) -> StmtResult {
        self.env.push_block();
        for s in v {
            self.visit_stmt(s)?;
        }
        self.env.pop_block();
        Ok(())
    }

    fn visit_print_stmt(&mut self, e: &ast::Expr) -> StmtResult {
        println!("{}", self.interpret_expr(e)?);
        Ok(())
    }

    fn visit_var_decl_stmt(&mut self, v: &ast::VarDecl) -> StmtResult {
        let initial = match &v.initializer {
            Some(expr) => self.visit_expr(&expr)?,
            None => Value::Nil,
        };

        self.env.define(v.name.lexeme.to_string(), initial);
        Ok(())
    }

    fn visit_if_stmt(&mut self, i: &ast::IfStmt) -> StmtResult {
        let condition = self.visit_expr(&i.condition)?;

        if truthy(&condition) {
            self.visit_stmt(&i.then_branch)?;
        } else {
            if let Some(s) = &i.else_branch {
                self.visit_stmt(s)?;
            }
        }
        Ok(())
    }

    fn visit_while_stmt(&mut self, w: &ast::WhileStmt) -> StmtResult {
        while truthy(&self.visit_expr(&w.condition)?) {
            self.visit_stmt(&w.body)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::{error, eval::Value, parser::parse_expression};

    use super::Interpreter;

    macro_rules! eval_string_expr_test {
        ($name:ident, $source:expr, $expected_value:expr) => {
            #[test]
            fn $name() -> anyhow::Result<(), error::Error> {
                let mut interpreter = Interpreter::new();

                let expr = parse_expression($source)?;
                assert_eq!(interpreter.interpret_expr(&expr)?, $expected_value);
                Ok(())
            }
        };
    }

    eval_string_expr_test!(false_literal, "false", Value::Bool(false));

    eval_string_expr_test!(true_literal, "true", Value::Bool(true));

    eval_string_expr_test!(nil_literal, "nil", Value::Nil);

    eval_string_expr_test!(
        string_literal,
        "\"hello\"",
        Value::String("hello".to_string())
    );

    eval_string_expr_test!(number_literal, "-4.2", Value::Number(-4.2));

    eval_string_expr_test!(unary_minus, "-2.0", Value::Number(-2.0));

    eval_string_expr_test!(unary_negate, "!false", Value::Bool(true));

    eval_string_expr_test!(binary_plus, "4 + 0.3", Value::Number(4.3));

    eval_string_expr_test!(grouping, "! ( false )", Value::Bool(true));

    macro_rules! eval_string_stmts_test {
        ($name:ident, $source:expr) => {
            #[test]
            fn $name() -> anyhow::Result<(), error::Error> {
                let mut interpreter = Interpreter::new();

                let stmts = crate::parser::parse($source)?;
                let mut printer = crate::visitor::AstPrinter {};
                for stmt in &stmts {
                    use crate::visitor::Visitor;
                    printer.visit_stmt(&stmt);
                }
                interpreter.interpret(stmts)?;

                let all_tests_passed_expr = crate::parser::parse_expression("all_tests_passed")?;
                let result = interpreter.interpret_expr(&all_tests_passed_expr)?;
                assert_eq!(result, Value::Bool(true));
                Ok(())
            }
        };
    }

    eval_string_stmts_test!(var_decl, "var foo = 3; var all_tests_passed = foo == 3;");

    eval_string_stmts_test!(
        block,
        r#"var foo = 3;
         { var foo = 5; }
         var all_tests_passed = foo == 3;"#
    );

    eval_string_stmts_test!(
        if_statement,
        r#"var all_tests_passed;
           if (true) {
               all_tests_passed = true;
           }"#
    );

    eval_string_stmts_test!(logical_or, "var all_tests_passed = true or false;");

    eval_string_stmts_test!(logical_or_nil, "var all_tests_passed = true or nil;");

    eval_string_stmts_test!(logical_and, "var all_tests_passed = true and true;");

    eval_string_stmts_test!(logical_and_nil, "var all_tests_passed = ! nil and true;");

    eval_string_stmts_test!(
        while_false,
        r#"
    var all_tests_passed = true;
    while (false) all_tests_passed = false;"#
    );

    eval_string_stmts_test!(
        while_true,
        r#"
    var all_tests_passed = false;
    while (!all_tests_passed) all_tests_passed = true;"#
    );

    eval_string_stmts_test!(
        for_loop,
        r#"var i = 0;
    for (var j = 0; j < 5; j = j + 1) {
        i = i + 1;
    }
    var all_tests_passed = i == 5;"#
    );
}
