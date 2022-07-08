use std::{cell::RefCell, collections::HashMap, fmt::Display, rc::Rc, time::Instant};

use by_address::ByAddress;

use crate::{
    ast, class, env,
    error::{self, RuntimeError},
    function, parser,
    visitor::Visitor,
};

pub trait Callable: std::fmt::Debug {
    fn call(
        &self,
        interpreter: &mut Interpreter,
        args: Vec<Value>,
        loc: error::Location,
    ) -> Result<Value, RuntimeError>;

    fn arity(&self) -> usize;

    fn display_name(&self) -> String;
}

#[derive(Debug, PartialEq, Clone)]
pub enum Value {
    String(String),
    Number(f64),
    Bool(bool),
    Callable(by_address::ByAddress<Rc<dyn Callable>>),
    Class(by_address::ByAddress<Rc<class::Callable>>),
    Instance(Rc<RefCell<class::Instance>>),
    Nil,
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::String(s) => write!(f, "{}", s),
            Value::Number(n) => write!(f, "{}", n),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Callable(c) => write!(f, "{}", c.display_name()),
            Value::Class(c) => write!(f, "{}", &c.class.name),
            Value::Instance(i) => {
                write!(f, "{} instance", &RefCell::borrow(&*i).class.name)
            }
            Value::Nil => write!(f, "nil"),
        }
    }
}

pub struct Interpreter {
    env: Rc<RefCell<env::Env>>,
    globals: Rc<RefCell<env::Env>>,
    errors: Vec<error::Error>,
    locals: HashMap<u64, usize>,
    location_table: Option<parser::LocationTable>,
}

type ExprResult = Result<Value, RuntimeError>;
type StmtResult = Result<(), RuntimeError>;

impl Interpreter {
    pub fn new() -> Interpreter {
        let globals = Rc::new(RefCell::new(env::Env::new()));

        globals.borrow_mut().define(
            "clock".to_string(),
            Value::Callable(by_address::ByAddress(Rc::new(Clock::new()))),
        );

        Interpreter {
            env: globals.clone(),
            globals,
            errors: vec![],
            locals: HashMap::new(),
            location_table: None,
        }
    }

    pub fn interpret(
        &mut self,
        stmts: &Vec<Box<ast::Stmt>>,
        location_table: parser::LocationTable,
    ) -> StmtResult {
        self.location_table = Some(location_table);
        for s in stmts {
            self.visit_stmt(&*s)?;
        }
        self.location_table = None;
        Ok(())
    }

    pub fn interpret_expr(
        &mut self,
        e: &ast::Expr,
        location_table: parser::LocationTable,
    ) -> ExprResult {
        self.location_table = Some(location_table);
        let result = self.visit_expr(e);
        self.location_table = None;
        result
    }

    pub fn has_error(&self) -> bool {
        !self.errors.is_empty()
    }

    pub fn errors(&self) -> &[error::Error] {
        &self.errors
    }

    pub fn env(&self) -> Rc<RefCell<env::Env>> {
        self.env.clone()
    }

    fn env_mut(&self) -> std::cell::RefMut<env::Env> {
        self.env.borrow_mut()
    }

    pub fn globals(&self) -> Rc<RefCell<env::Env>> {
        self.globals.clone()
    }

    pub fn execute_block(
        &mut self,
        v: &Vec<Box<ast::Stmt>>,
        environ: Rc<RefCell<env::Env>>,
    ) -> StmtResult {
        let previous = self.env.clone();

        self.env = environ;

        let result = (|| -> StmtResult {
            for stmt in v {
                self.visit_stmt(stmt)?;
            }
            Ok(())
        })();

        self.env = previous;

        result
    }

    pub fn resolve(&mut self, expr_id: u64, depth: usize) {
        self.locals.insert(expr_id, depth);
    }

    fn ast_loc(&self, ast_id: u64) -> error::Location {
        match self.location_table.as_ref().unwrap().get(&ast_id) {
            Some(loc) => loc.clone(),
            None => error::Location::default(),
        }
    }

    fn lookup_variable(&mut self, name: &String, expr_id: u64) -> ExprResult {
        let env = match self.locals.get(&expr_id) {
            Some(depth) => env::ancestor(&self.env, *depth),
            None => Some(self.globals.clone()),
        }
        .unwrap();

        let env_ref = RefCell::borrow(&*env);

        env_ref.get(name, self.ast_loc(expr_id))
    }

    fn assign_variable(
        &mut self,
        name: &String,
        value: Value,
        expr_id: u64,
    ) -> Result<(), error::RuntimeError> {
        let env = match self.locals.get(&expr_id) {
            Some(depth) => env::ancestor(&self.env, *depth),
            None => Some(self.globals.clone()),
        }
        .unwrap();

        let mut env_ref = env.borrow_mut();

        env_ref.assign(name.clone(), value, self.ast_loc(expr_id))
    }
}

#[derive(Debug)]
struct Clock {
    start: Instant,
}

impl Clock {
    fn new() -> Clock {
        Clock {
            start: Instant::now(),
        }
    }
}

impl Callable for Clock {
    fn call(
        &self,
        _interpreter: &mut Interpreter,
        _args: Vec<Value>,
        _loc: error::Location,
    ) -> Result<Value, RuntimeError> {
        Ok(Value::Number(self.start.elapsed().as_secs_f64()))
    }
    fn arity(&self) -> usize {
        0
    }
    fn display_name(&self) -> String {
        "<native fn>".to_string()
    }
}

fn truthy(v: &Value) -> bool {
    match v {
        Value::Nil => false,
        Value::Bool(b) => *b,
        _ => true,
    }
}

fn as_number(v: &Value, loc: error::Location) -> Result<f64, RuntimeError> {
    match v {
        Value::Number(n) => Ok(*n),
        _ => Err(RuntimeError::new(
            "Operands must be numbers.".to_string(),
            loc,
        )),
    }
}

impl<'a> Visitor<ExprResult, StmtResult> for Interpreter {
    fn expr_result_to_stmt_result(&self, e: ExprResult) -> StmtResult {
        match e {
            Ok(_) => Ok(()),
            Err(e) => Err(e),
        }
    }

    fn report_error(&mut self, e: error::Error) {
        self.errors.push(e)
    }

    fn visit_literal(&mut self, v: &ast::LiteralExpr) -> ExprResult {
        Ok(match &v.value {
            ast::LiteralValue::String(s) => Value::String(s.to_string()),
            ast::LiteralValue::Number(n) => Value::Number(*n),
            ast::LiteralValue::Bool(b) => Value::Bool(*b),
            ast::LiteralValue::Nil => Value::Nil,
        })
    }

    fn visit_call(&mut self, c: &ast::CallExpr) -> ExprResult {
        let callee = self.visit_expr(&c.callee)?;

        let args_result: Result<Vec<Value>, error::RuntimeError> =
            c.args.iter().map(|e| self.visit_expr(e)).collect();

        let args = args_result?;

        // Value::Callable and Value::Class can be called in the same way.
        let callable = match callee {
            Value::Callable(c) => (*c).clone(),
            Value::Class(c) => (*c).clone() as Rc<dyn Callable>,
            _ => {
                return Err(error::RuntimeError::new(
                    "Can only call functions and classes.".to_string(),
                    self.ast_loc(c.id()),
                ))
            }
        };

        if args.len() != callable.arity() {
            return Err(error::RuntimeError::new(
                format!(
                    "Expected {} arguments but got {}.",
                    callable.arity(),
                    args.len()
                ),
                self.ast_loc(c.id()),
            ));
        }

        return Ok(callable.call(self, args, self.ast_loc(c.id()))?);
    }

    fn visit_set(&mut self, s: &ast::SetExpr) -> ExprResult {
        let object = self.visit_expr(&s.object)?;
        if let Value::Instance(instance) = object {
            let value = self.visit_expr(&s.value)?;

            return instance.borrow_mut().set(s.name.clone(), value);
        }

        Err(error::RuntimeError::new(
            "Only instances have fields.".to_string(),
            self.ast_loc(s.id()),
        ))
    }

    fn visit_get(&mut self, g: &ast::GetExpr) -> ExprResult {
        let object = self.visit_expr(&g.object)?;
        if let Value::Instance(instance) = object.clone() {
            return RefCell::borrow(&*instance).get(&g.name, object, self.ast_loc(g.id()));
        }

        Err(error::RuntimeError::new(
            "Only instances have properties.".to_string(),
            self.ast_loc(g.id()),
        ))
    }

    fn visit_super(&mut self, s: &ast::SuperExpr) -> ExprResult {
        let distance = match self.locals.get(&s.id()) {
            Some(d) => *d,
            None => {
                return Err(error::RuntimeError::new(
                    "'super' not found in locals".to_string(),
                    self.ast_loc(s.id()),
                ));
            }
        };
        let superclass = env::ancestor(&self.env, distance)
            .unwrap()
            .borrow()
            .get(&"super".to_string(), self.ast_loc(s.id()))?;

        let object = env::ancestor(&self.env, distance - 1)
            .unwrap()
            .borrow()
            .get(&"this".to_string(), self.ast_loc(s.id()))?;

        if let Value::Class(superclass) = superclass {
            let method = match superclass.class.find_method(&s.name) {
                Some(m) => m,
                None => {
                    return Err(error::RuntimeError::new(
                        format!("Undefined property '{}'.", &s.name),
                        self.ast_loc(s.id()),
                    ));
                }
            };
            return Ok(method.bind(object));
        }

        Err(error::RuntimeError::new(
            "'super' not a a class.".to_string(),
            self.ast_loc(s.id()),
        ))
    }

    fn visit_this(&mut self, t: &ast::ThisExpr) -> ExprResult {
        self.lookup_variable(&"this".to_string(), t.id())
    }

    fn visit_binary_expr(&mut self, e: &ast::BinaryExpr) -> ExprResult {
        let left = self.visit_expr(&e.left)?;
        let right = self.visit_expr(&e.right)?;

        use ast::Operator::*;
        match e.operator {
            Minus => Ok(Value::Number(
                as_number(&left, self.ast_loc(e.id()))? - as_number(&right, self.ast_loc(e.id()))?,
            )),
            Slash => Ok(Value::Number(
                as_number(&left, self.ast_loc(e.id()))? / as_number(&right, self.ast_loc(e.id()))?,
            )),
            Star => Ok(Value::Number(
                as_number(&left, self.ast_loc(e.id()))? * as_number(&right, self.ast_loc(e.id()))?,
            )),
            Plus => match left {
                Value::Number(left_number) => match right {
                    Value::Number(right_number) => Ok(Value::Number(left_number + right_number)),
                    _ => Err((
                        "Operands must be two numbers or two strings.",
                        self.ast_loc(e.id()),
                    )
                        .into()),
                },

                Value::String(left_string) => match right {
                    Value::String(right_string) => Ok(Value::String(left_string + &right_string)),

                    _ => Err((
                        "Operands must be two numbers or two strings.",
                        self.ast_loc(e.id()),
                    )
                        .into()),
                },

                _ => Err((
                    "Operands must be two numbers or two strings.",
                    self.ast_loc(e.id()),
                )
                    .into()),
            },
            Greater => Ok(Value::Bool(
                as_number(&left, self.ast_loc(e.id()))? > as_number(&right, self.ast_loc(e.id()))?,
            )),
            GreaterEqual => Ok(Value::Bool(
                as_number(&left, self.ast_loc(e.id()))? >= as_number(&right, self.ast_loc(e.id()))?,
            )),
            Less => Ok(Value::Bool(
                as_number(&left, self.ast_loc(e.id()))? < as_number(&right, self.ast_loc(e.id()))?,
            )),
            LessEqual => Ok(Value::Bool(
                as_number(&left, self.ast_loc(e.id()))? <= as_number(&right, self.ast_loc(e.id()))?,
            )),
            BangEqual => Ok(Value::Bool(left != right)),
            EqualEqual => Ok(Value::Bool(left == right)),

            _ => Err((
                format!("unknown operator {}", e.operator),
                self.ast_loc(e.id()),
            )
                .into()),
        }
    }

    fn visit_grouping_expr(&mut self, e: &ast::GroupingExpr) -> ExprResult {
        self.visit_expr(&e.expr)
    }

    fn visit_unary_expr(&mut self, e: &ast::UnaryExpr) -> ExprResult {
        let val = self.visit_expr(&e.right)?;
        use ast::Operator::*;
        match e.operator {
            Minus => match val {
                Value::Number(n) => Ok(Value::Number(-n)),
                _ => Err(("Operand must be a number.", self.ast_loc(e.id())).into()),
            },
            Bang => Ok(Value::Bool(!truthy(&val))),
            _ => Err(("unsupported unary operator", self.ast_loc(e.id())).into()),
        }
    }

    fn visit_variable(&mut self, v: &ast::VariableExpr) -> ExprResult {
        self.lookup_variable(&v.name, v.id())
    }

    fn visit_assign(&mut self, a: &ast::AssignExpr) -> ExprResult {
        let value = self.visit_expr(&*a.value)?;
        self.assign_variable(&a.name, value.clone(), a.id())?;
        Ok(value)
    }

    fn visit_logical(&mut self, l: &ast::LogicalExpr) -> ExprResult {
        let left = self.visit_expr(&l.left).ok().unwrap();

        if l.operator == ast::Operator::Or {
            if truthy(&left) {
                return Ok(left);
            }
        } else {
            assert_eq!(l.operator, ast::Operator::And);
            if !truthy(&left) {
                return Ok(left);
            }
        }
        self.visit_expr(&l.right)
    }

    fn visit_block(&mut self, v: &Vec<Box<ast::Stmt>>) -> StmtResult {
        let block_env = Rc::new(RefCell::new(env::Env::with_parent(self.env.clone())));
        self.execute_block(v, block_env)
    }

    fn visit_print_stmt(&mut self, e: &ast::Expr) -> StmtResult {
        println!("{}", self.visit_expr(e)?);
        Ok(())
    }

    fn visit_return_stmt(&mut self, r: &ast::ReturnStmt) -> StmtResult {
        let value = match &r.value {
            Some(e) => self.visit_expr(e)?,
            None => Value::Nil,
        };
        Err(RuntimeError::Return(value))
    }

    fn visit_var_decl_stmt(&mut self, v: &ast::VarDecl) -> StmtResult {
        let initial = match &v.initializer {
            Some(expr) => self.visit_expr(&expr)?,
            None => Value::Nil,
        };

        self.env_mut().define(v.name.to_string(), initial);
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

    fn visit_function_stmt(&mut self, decl: &Rc<ast::FunctionStmt>) -> StmtResult {
        let fun: by_address::ByAddress<Rc<dyn Callable>> =
            by_address::ByAddress(Rc::new(function::Function::new(decl, self.env.clone())));
        let value: Value = Value::Callable(fun);
        self.env_mut().define(decl.name.to_string(), value);

        Ok(())
    }

    fn visit_class_stmt(&mut self, c: &ast::ClassStmt) -> StmtResult {
        let superclass = if let Some(superclass_expr) = &c.superclass {
            let superclass = self.visit_expr(superclass_expr)?;
            if let Value::Class(c) = superclass {
                Some(ByAddress(c.class.clone()))
            } else {
                return Err(error::RuntimeError::new(
                    "Superclass must be a class.".to_string(),
                    self.ast_loc(c.id()),
                ));
            }
        } else {
            None
        };

        self.env_mut().define(c.name.clone(), Value::Nil);

        let mut previous = None;
        if let Some(superclass) = superclass.clone() {
            // push new env
            previous = Some(self.env.clone());
            let super_env = Rc::new(RefCell::new(env::Env::with_parent(self.env.clone())));
            self.env = super_env;

            // define 'super' to superclass
            let superclass_callable =
                by_address::ByAddress(Rc::new(class::Callable::new((*superclass).clone())));
            self.env_mut()
                .define("super".to_string(), Value::Class(superclass_callable));
        }

        let mut methods = HashMap::new();

        for method in &c.methods {
            let function = if method.name == "init" {
                function::Function::initializer(&method, self.env.clone())
            } else {
                function::Function::new(&method, self.env.clone())
            };
            let fn_rc = Rc::new(function);

            methods.insert(method.name.clone(), by_address::ByAddress(fn_rc));
        }

        let class = Rc::new(class::Class::new(c.name.clone(), methods, superclass));
        let class_callable = by_address::ByAddress(Rc::new(class::Callable::new(class)));

        if let Some(previous_env) = previous {
            self.env = previous_env;
        }

        self.env_mut().assign(
            c.name.clone(),
            Value::Class(class_callable),
            self.ast_loc(c.id()),
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::{error, eval::Value, parser, resolver, scanner};

    use super::Interpreter;

    macro_rules! eval_string_expr_test {
        ($name:ident, $source:expr, $expected_value:expr) => {
            #[test]
            fn $name() -> Result<(), error::Error> {
                let mut interpreter = Interpreter::new();

                let scanner = scanner::Scanner::new($source);
                let mut parser = parser::Parser::new(scanner);
                let expr = parser.parse_expression()?;
                let location_table = parser.take_location_table();
                let mut resolver = resolver::Resolver::new(&mut interpreter, &location_table);
                resolver.resolve_expr(&expr)?;
                assert_eq!(
                    interpreter.interpret_expr(&expr, location_table)?,
                    $expected_value
                );
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
            fn $name() -> Result<(), error::Error> {
                let mut interpreter = Interpreter::new();
                let scanner = scanner::Scanner::new($source);
                let mut parser = parser::Parser::new(scanner);

                let stmts = match parser.parse() {
                    Ok(s) => s,
                    Err(e) => {
                        return Err(error::convert_parse(&e));
                    }
                };
                let mut printer = crate::visitor::AstPrinter {};
                for stmt in &stmts {
                    use crate::visitor::Visitor;
                    printer.visit_stmt(&stmt);
                }
                let location_table = parser.take_location_table();
                let mut resolver = resolver::Resolver::new(&mut interpreter, &location_table);
                resolver.resolve(&stmts)?;
                interpreter.interpret(&stmts, location_table.clone())?;

                let all_tests_passed_expr = crate::parser::parse_expression("all_tests_passed")?;
                let result = interpreter.interpret_expr(&all_tests_passed_expr, location_table)?;
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

    eval_string_stmts_test!(
        clock,
        r#"var start = clock();
        for (var i = 0; i < 100; i = i + 1) { }
        var end = clock();
        var all_tests_passed = end >= start;"#
    );

    eval_string_stmts_test!(
        recursive,
        r#"var all_tests_passed = false;
            fun count(n) {
                if (n > 1) {
                    count(n - 1);
                } else {
                    all_tests_passed = true;
                }
            }
            count(3);"#
    );
}
