use std::{
    borrow::Borrow, cell::RefCell, collections::HashMap, fmt::Display, rc::Rc, time::Instant,
};

use crate::{
    ast, env,
    error::{self, RuntimeError},
    function,
    visitor::Visitor,
};

pub trait Callable: std::fmt::Debug {
    fn call(
        &self,
        interpreter: &mut Interpreter,
        args: Vec<Value>,
    ) -> anyhow::Result<Value, RuntimeError>;

    fn arity(&self) -> usize;
}

#[derive(Debug, PartialEq, Clone)]
pub enum Value {
    String(String),
    Number(f64),
    Bool(bool),
    Callable(by_address::ByAddress<Rc<dyn Callable>>),
    Instance(Rc<RefCell<Instance>>),
    Nil,
}

#[derive(Debug)]
struct ClassCallable {
    class: Rc<Class>,
}

impl ClassCallable {
    fn new(class: Rc<Class>) -> Self {
        ClassCallable { class }
    }
}

type MethodMap = HashMap<String, by_address::ByAddress<Rc<function::Function>>>;
#[derive(Debug, PartialEq)]
pub struct Class {
    name: String,
    methods: MethodMap,
}

impl Class {
    fn new(name: String, methods: MethodMap) -> Self {
        Class { name, methods }
    }
}

#[derive(Debug, PartialEq)]
pub struct Instance {
    class: Rc<Class>,
    fields: HashMap<String, Value>,
}

impl Instance {
    fn new(class: Rc<Class>) -> Self {
        Instance {
            class,
            fields: HashMap::new(),
        }
    }

    fn get(&self, name: &str, this: Value) -> ExprResult {
        if let Some(value) = self.fields.get(name) {
            return Ok(value.clone());
        }

        let class = (*self.class).borrow();

        if let Some(method) = class.methods.get(name) {
            return Ok(method.bind(this));
        }

        Err(error::RuntimeError::Message(format!(
            "Undefined property '{}'.",
            name
        )))
    }

    fn set(&mut self, name: String, value: Value) -> ExprResult {
        self.fields.insert(name, value.clone());
        Ok(value)
    }
}

impl Callable for ClassCallable {
    fn call(
        &self,
        interpreter: &mut Interpreter,
        args: Vec<Value>,
    ) -> anyhow::Result<Value, RuntimeError> {
        let instance = Value::Instance(Rc::new(RefCell::new(Instance::new(self.class.clone()))));

        if let Some(initializer) = self.class.methods.get("init") {
            initializer.bind(instance.clone());
            initializer.call(interpreter, args)?;
        }

        Ok(instance)
    }

    fn arity(&self) -> usize {
        match self.class.methods.get("init") {
            Some(initializer) => initializer.arity(),
            None => 0,
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::String(s) => write!(f, "\"{}\"", s),
            Value::Number(n) => write!(f, "{}", n),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Callable(_) => write!(f, "<fn>"),
            Value::Instance(i) => {
                write!(f, "<instance of {}>", &RefCell::borrow(&*i).class.name)
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
}

type ExprResult = anyhow::Result<Value, RuntimeError>;
type StmtResult = anyhow::Result<(), RuntimeError>;

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
        }
    }

    pub fn interpret(&mut self, stmts: &Vec<Box<ast::Stmt>>) -> StmtResult {
        for s in stmts {
            self.visit_stmt(&*s)?;
        }
        Ok(())
    }

    pub fn interpret_expr(&mut self, e: &ast::Expr) -> ExprResult {
        self.visit_expr(e)
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

    fn lookup_variable(&mut self, name: &String, expr_id: u64) -> ExprResult {
        let env = match self.locals.get(&expr_id) {
            Some(depth) => env::ancestor(&self.env, *depth),
            None => Some(self.globals.clone()),
        }
        .unwrap();

        let env_ref = RefCell::borrow(&*env);

        env_ref.get(name)
    }

    fn assign_variable(&mut self, name: &String, value: Value, expr_id: u64) {
        let env = match self.locals.get(&expr_id) {
            Some(depth) => env::ancestor(&self.env, *depth),
            None => Some(self.globals.clone()),
        }
        .unwrap();

        let mut env_ref = env.borrow_mut();

        env_ref.assign(name.clone(), value).unwrap();
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
    ) -> anyhow::Result<Value, RuntimeError> {
        Ok(Value::Number(self.start.elapsed().as_secs_f64()))
    }
    fn arity(&self) -> usize {
        0
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

        if let Value::Callable(c) = callee {
            if args.len() != c.arity() {
                return Err(error::RuntimeError::new(format!(
                    "Expected {} arguments but got {}.",
                    c.arity(),
                    args.len()
                )));
            }
            return Ok(c.call(self, args)?);
        } else {
            return Err(error::RuntimeError::new(
                "Can only call functions.".to_string(),
            ));
        }
    }

    fn visit_set(&mut self, s: &ast::SetExpr) -> ExprResult {
        let object = self.visit_expr(&s.object)?;
        if let Value::Instance(instance) = object {
            let value = self.visit_expr(&s.value)?;

            return instance.borrow_mut().set(s.name.clone(), value);
        }

        Err(error::RuntimeError::Message(
            "Only instances have fields.".to_string(),
        ))
    }

    fn visit_get(&mut self, g: &ast::GetExpr) -> ExprResult {
        let object = self.visit_expr(&g.object)?;
        if let Value::Instance(instance) = object.clone() {
            return RefCell::borrow(&*instance).get(&g.name, object);
        }

        Err(error::RuntimeError::Message(
            "Only instances have properties.".to_string(),
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

            _ => Err(format!("unknown operator {}", e.operator).into()),
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
                _ => Err("unary - must be applied to a number".into()),
            },
            Bang => Ok(Value::Bool(!truthy(&val))),
            _ => Err("unsupported unary operator".into()),
        }
    }

    fn visit_variable(&mut self, v: &ast::VariableExpr) -> ExprResult {
        self.lookup_variable(&v.name, v.id())
    }

    fn visit_assign(&mut self, a: &ast::AssignExpr) -> ExprResult {
        let value = self.visit_expr(&*a.value)?;
        self.assign_variable(&a.name, value.clone(), a.id());
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
        println!("{}", self.interpret_expr(e)?);
        Ok(())
    }

    fn visit_return_stmt(&mut self, r: &Option<Box<ast::Expr>>) -> StmtResult {
        let value = match r {
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
        self.env_mut().define(c.name.clone(), Value::Nil);

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

        let class = Rc::new(Class::new(c.name.clone(), methods));
        let class_callable: by_address::ByAddress<Rc<dyn Callable>> =
            by_address::ByAddress(Rc::new(ClassCallable::new(class)));
        self.env_mut()
            .assign(c.name.clone(), Value::Callable(class_callable))?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::{error, eval::Value, parser::parse_expression, resolver};

    use super::Interpreter;

    macro_rules! eval_string_expr_test {
        ($name:ident, $source:expr, $expected_value:expr) => {
            #[test]
            fn $name() -> anyhow::Result<(), anyhow::Error> {
                let mut interpreter = Interpreter::new();

                let expr = parse_expression($source)?;
                let mut resolver = resolver::Resolver::new(&mut interpreter);
                resolver.resolve_expr(&expr)?;
                assert_eq!(
                    interpreter
                        .interpret_expr(&expr)
                        .map_err(|e| anyhow::anyhow!(e.to_string()))?,
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
            fn $name() -> anyhow::Result<(), anyhow::Error> {
                let mut interpreter = Interpreter::new();

                let stmts = match crate::parser::parse($source) {
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
                let mut resolver = resolver::Resolver::new(&mut interpreter);
                resolver.resolve(&stmts)?;
                interpreter
                    .interpret(&stmts)
                    .map_err(|e| anyhow::anyhow!(e.to_string()))?;

                let all_tests_passed_expr = crate::parser::parse_expression("all_tests_passed")?;
                let result = interpreter
                    .interpret_expr(&all_tests_passed_expr)
                    .map_err(|e| anyhow::anyhow!(e.to_string()))?;
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
