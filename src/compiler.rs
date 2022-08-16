use std::ops::{AddAssign, SubAssign};

use crate::{
    ast,
    error::{self, ParseError},
    parser, vm,
    vmgc::{self, Function},
};

#[derive(Debug)]
enum VariableState {
    Global,
    Declared,
    Local(usize),
}

struct State {
    locals: Vec<(String, VariableState)>,
    scope_depth: usize,
}

impl State {
    fn new() -> Self {
        Self {
            locals: vec![("".to_string(), VariableState::Declared)], // Reserve first slot for function.
            scope_depth: 0,
        }
    }
}

pub struct Compiler<'a> {
    location_table: parser::LocationTable,
    state: State,
    heap: &'a mut vmgc::Heap,
}

impl<'a> Compiler<'a> {
    pub fn new(location_table: parser::LocationTable, heap: &'a mut vmgc::Heap) -> Self {
        Self {
            location_table,
            state: State::new(),
            heap,
        }
    }

    pub fn compile(
        &mut self,
        stmts: &[Box<ast::Stmt>],
        arity: usize,
        name: &str,
    ) -> Result<Function, error::Error> {
        let mut function = Function::new(arity, name);
        for stmt in stmts {
            self.compile_stmt(stmt, &mut function)?;
        }
        function.chunk.add_nil(error::Location::default());
        function.chunk.add_return(error::Location::default());
        Ok(function)
    }

    fn compile_stmt(
        &mut self,
        stmt: &ast::Stmt,
        function: &mut vmgc::Function,
    ) -> Result<(), error::Error> {
        let loc = match self.location_table.get(&stmt.id()) {
            Some(loc) => loc.clone(),
            None => error::Location::default(),
        };
        match stmt {
            ast::Stmt::Expr(e) => self.compile_expr(&*e.expr, function)?,
            ast::Stmt::Print(p) => {
                self.compile_expr(&p.expr, function)?;
                function.chunk.add_print(loc);
            }
            ast::Stmt::Return(r) => {
                if let Some(value) = &r.value {
                    self.compile_expr(&value, function)?;
                } else {
                    function.chunk.add_nil(loc.clone());
                }
                function.chunk.add_return(loc);
            }
            ast::Stmt::Block(b) => {
                self.begin_scope();
                for bs in &b.stmts {
                    self.compile_stmt(&*bs, function)?;
                }
                self.end_scope(&mut function.chunk, loc.clone());
            }
            ast::Stmt::Var(v) => {
                self.declare_variable(v.name.clone(), loc.clone())?;
                match &v.initializer {
                    Some(e) => self.compile_expr(e, function)?,
                    None => function.chunk.add_nil(loc.clone()),
                }
                if self.state.scope_depth == 0 {
                    function
                        .chunk
                        .add_define_global(self.alloc_string(&v.name), loc);
                } else {
                    self.state.locals.last_mut().unwrap().1 =
                        VariableState::Local(self.state.scope_depth);
                }
            }
            ast::Stmt::If(i) => {
                self.compile_expr(&i.condition, function)?;

                let then_offset = function
                    .chunk
                    .add_jump(vm::OpCode::JumpIfFalse(i16::MAX), loc.clone());
                function.chunk.add_pop(loc.clone());

                self.compile_stmt(&*i.then_branch, function)?;

                let else_offset = function
                    .chunk
                    .add_jump(vm::OpCode::Jump(i16::MAX), loc.clone());

                function.chunk.patch_jump(then_offset);
                function.chunk.add_pop(loc);

                if let Some(else_branch) = &i.else_branch {
                    self.compile_stmt(else_branch, function)?;
                }
                function.chunk.patch_jump(else_offset);
            }
            ast::Stmt::While(w) => {
                let loop_start = function.chunk.current_code_offset();
                self.compile_expr(&&w.condition, function)?;
                let end_jump = function
                    .chunk
                    .add_jump(vm::OpCode::JumpIfFalse(i16::MAX), loc.clone());
                function.chunk.add_pop(loc.clone());

                self.compile_stmt(&*w.body, function)?;
                let loop_len = (function.chunk.current_code_offset() - loop_start + 1) as i16;
                function
                    .chunk
                    .add_jump(vm::OpCode::Jump(-loop_len), loc.clone());

                function.chunk.patch_jump(end_jump);
                function.chunk.add_pop(loc);
            }
            ast::Stmt::Function(f) => {
                // Declare variable
                self.declare_variable(f.name.to_string(), loc.clone())?;
                // Mark variable as initialized.
                self.resolve_variable(&f.name);
                // Compile function.
                let fun = self.compile(&f.body, f.params.len(), &f.name)?;
                // Assign function to constant.
                let fun_ptr = self
                    .heap
                    .alloc_cell(fun)
                    .map_err(|_| error::ParseError::new("Could not allocate value", loc.clone()))?;
                let fun_val = vmgc::Value::Function(fun_ptr);
                function.chunk.add_constant(fun_val, loc);
            }
            ast::Stmt::Class(_) => todo!(),
        }
        Ok(())
    }

    fn compile_expr(
        &mut self,
        expr: &ast::Expr,
        function: &mut Function,
    ) -> Result<(), error::Error> {
        let loc = match self.location_table.get(&expr.id()) {
            Some(loc) => loc.clone(),
            None => error::Location::default(),
        };
        match expr {
            ast::Expr::Unary(u) => {
                self.compile_expr(&u.right, function)?;
                match &u.operator {
                    ast::Operator::Minus => function.chunk.add_negate(loc),
                    ast::Operator::Bang => function.chunk.add_not(loc),
                    _ => {
                        return Err(error::Error::Parse(ParseError::new(
                            "unknown unary operator",
                            loc,
                        )));
                    }
                }
            }
            ast::Expr::Literal(l) => match &l.value {
                ast::LiteralValue::Number(n) => {
                    function.chunk.add_constant(vmgc::Value::Number(*n), loc)
                }
                ast::LiteralValue::String(s) => {
                    function.chunk.add_constant(self.alloc_string(s), loc)
                }
                ast::LiteralValue::Bool(b) => match b {
                    true => function.chunk.add_true(loc),
                    false => function.chunk.add_false(loc),
                },
                ast::LiteralValue::Nil => function.chunk.add_nil(loc),
            },
            ast::Expr::Binary(b) => {
                self.compile_expr(&b.left, function)?;
                self.compile_expr(&b.right, function)?;
                match b.operator {
                    ast::Operator::Minus => {
                        // a - b is equivalent to a + (- b) and b is at the top of the stack.
                        function.chunk.add_negate(loc.clone());
                        function.chunk.add_add(loc);
                    }
                    ast::Operator::Plus => function.chunk.add_add(loc),
                    ast::Operator::Slash => function.chunk.add_divide(loc),
                    ast::Operator::Star => function.chunk.add_multiply(loc),
                    ast::Operator::BangEqual => {
                        function.chunk.add_equal(loc.clone());
                        function.chunk.add_not(loc);
                    }
                    ast::Operator::EqualEqual => function.chunk.add_equal(loc),
                    ast::Operator::Greater => function.chunk.add_greater(loc),
                    ast::Operator::GreaterEqual => {
                        function.chunk.add_less(loc.clone());
                        function.chunk.add_not(loc);
                    }
                    ast::Operator::Less => function.chunk.add_less(loc),
                    ast::Operator::LessEqual => {
                        function.chunk.add_greater(loc.clone());
                        function.chunk.add_not(loc);
                    }
                    _ => {
                        return Err(error::Error::Parse(ParseError::new(
                            "unknown binary operator",
                            loc,
                        )));
                    }
                }
            }
            ast::Expr::Variable(v) => {
                match self.resolve_variable(&v.name) {
                    VariableState::Local(depth) => function.chunk.add_get_local(depth, loc),
                    VariableState::Global => function
                        .chunk
                        .add_get_global(self.alloc_string(&v.name), loc),
                    VariableState::Declared => {
                        return Err(error::Error::Parse(ParseError::new(
                            "Can't read local variable in its own initializer.",
                            loc,
                        )));
                    }
                };
            }
            ast::Expr::Assign(a) => {
                self.compile_expr(&a.value, function)?;
                match self.resolve_variable(&a.name) {
                    VariableState::Local(depth) => function.chunk.add_set_local(depth, loc),
                    VariableState::Global => function
                        .chunk
                        .add_set_global(self.alloc_string(&a.name), loc),
                    VariableState::Declared => panic!("declared variable found in assignment"),
                };
            }
            ast::Expr::Logical(l) => match l.operator {
                ast::Operator::And => {
                    self.compile_expr(&l.left, function)?;
                    let end_jump = function
                        .chunk
                        .add_jump(vm::OpCode::JumpIfFalse(i16::MAX), loc.clone());
                    function.chunk.add_pop(loc.clone());

                    self.compile_expr(&l.right, function)?;
                    function.chunk.patch_jump(end_jump);
                }
                ast::Operator::Or => {
                    self.compile_expr(&l.left, function)?;
                    function
                        .chunk
                        .add_jump(vm::OpCode::JumpIfFalse(1), loc.clone());
                    let end_jump = function
                        .chunk
                        .add_jump(vm::OpCode::Jump(i16::MAX), loc.clone());

                    function.chunk.add_pop(loc.clone());

                    self.compile_expr(&l.right, function)?;
                    function.chunk.patch_jump(end_jump);
                }
                _ => {
                    return Err(error::Error::Parse(ParseError::new(
                        &format!("Invalid logical operator {:?}.", l.operator),
                        loc,
                    )));
                }
            },
            ast::Expr::Call(c) => {
                self.compile_expr(&c.callee, function)?;
                function.chunk.add_call(c.args.len(), loc);
            }
            _ => {
                return Err(error::Error::Parse(ParseError::new(
                    "unknown expression kind",
                    loc,
                )));
            }
        }
        Ok(())
    }

    fn begin_scope(&mut self) {
        self.state.scope_depth.add_assign(1);
    }

    fn end_scope(&mut self, chunk: &mut vm::Chunk, loc: error::Location) {
        self.state.scope_depth.sub_assign(1);
        let mut num_popped = 0;
        for local in self.state.locals.iter().rev() {
            if let VariableState::Local(depth) = local.1 {
                if depth <= self.state.scope_depth {
                    break;
                }
            }
            chunk.add_pop(loc.clone());
            num_popped.add_assign(1);
        }
        self.state
            .locals
            .truncate(self.state.locals.len() - num_popped);
    }

    fn declare_variable(&mut self, name: String, loc: error::Location) -> Result<(), error::Error> {
        if self.state.scope_depth == 0 {
            return Ok(());
        }

        for local in &self.state.locals {
            if let VariableState::Local(depth) = local.1 {
                if depth < self.state.scope_depth {
                    break;
                }
            }

            if local.0 == name {
                return Err(error::Error::Parse(ParseError::new(
                    "Already a variable with this name in this scope.",
                    loc,
                )));
            }
        }

        self.state.locals.push((name, VariableState::Declared));
        Ok(())
    }

    fn resolve_variable(&self, name: &str) -> VariableState {
        if !self.state.locals.is_empty() {
            for i in (0..self.state.locals.len()).rev() {
                if self.state.locals[i].0 == name {
                    return VariableState::Local(i);
                }
            }
        }
        VariableState::Global
    }

    fn alloc_string(&mut self, s: &str) -> vmgc::Value {
        vmgc::Value::String(self.heap.alloc_cell(s.to_string()).unwrap())
    }
}

#[cfg(test)]
mod tests {
    use std::cell::RefCell;

    use super::*;
    use crate::{ast, error, vm};

    macro_rules! compile_expr_test {
        ($name:ident, $expr:expr, [ $($code:expr),* ], [ $($constant:expr),* ]) => {
            #[test]
            fn $name() -> Result<(), error::Error> {
                let mut heap = vmgc::Heap::new();
                let expr = $expr;
                let mut compiler = Compiler::new(parser::LocationTable::new(), &mut heap);
                let mut function = Function::new(0, "<script>");
                compiler.compile_expr(&expr, &mut function)?;
                assert_eq!(function.chunk.code, vec![ $($code),* ]);
                let expected_constants : Vec<vmgc::Value> = vec![$($constant),*];
                assert_eq!(function.chunk.constants.len(), expected_constants.len());
                for i in 0..expected_constants.len() {
                    assert_eq!(expected_constants[i], function.chunk.constants[i]);
                }
                Ok(())
            }

        };
    }

    compile_expr_test!(
        compile_constant,
        ast::Expr::literal_number(3.4),
        [vm::OpCode::Constant(0)],
        [vmgc::Value::Number(3.4)]
    );

    compile_expr_test!(
        compile_negate_number,
        ast::Expr::unary(
            ast::Operator::Minus,
            Box::new(ast::Expr::literal_number(1.2)),
        ),
        // - 1.2
        [vm::OpCode::Constant(0), vm::OpCode::Negate],
        [vmgc::Value::Number(1.2)]
    );

    compile_expr_test!(
        compile_not_boolean,
        ast::Expr::unary(
            ast::Operator::Bang,
            Box::new(ast::Expr::literal_bool(false)),
        ),
        // - 1.2
        [vm::OpCode::False, vm::OpCode::Not],
        []
    );

    compile_expr_test!(
        compile_add_numbers,
        ast::Expr::binary(
            Box::new(ast::Expr::literal_number(1.2)),
            ast::Operator::Plus,
            Box::new(ast::Expr::literal_number(4.7)),
        ),
        // 1.2 + 4.7
        [
            vm::OpCode::Constant(0),
            vm::OpCode::Constant(1),
            vm::OpCode::Add
        ],
        [vmgc::Value::Number(1.2), vmgc::Value::Number(4.7)]
    );

    thread_local! {
        static TEST_HEAP: RefCell<vmgc::Heap>  = RefCell::new(vmgc::Heap::new());
    }

    fn test_alloc_string(s: &str) -> vmgc::Value {
        vmgc::Value::String(TEST_HEAP.with(|h| h.borrow_mut().alloc_cell(s.to_string()).unwrap()))
    }

    compile_expr_test!(
        compile_add_strings,
        ast::Expr::binary(
            Box::new(ast::Expr::literal_string("foo".to_string())),
            ast::Operator::Plus,
            Box::new(ast::Expr::literal_string("bar".to_string())),
        ),
        [
            vm::OpCode::Constant(0),
            vm::OpCode::Constant(1),
            vm::OpCode::Add
        ],
        [test_alloc_string("foo"), test_alloc_string("bar")]
    );

    compile_expr_test!(
        compile_less,
        ast::Expr::binary(
            Box::new(ast::Expr::literal_number(2.1)),
            ast::Operator::Less,
            Box::new(ast::Expr::literal_number(4.2)),
        ),
        [
            vm::OpCode::Constant(0),
            vm::OpCode::Constant(1),
            vm::OpCode::Less
        ],
        [vmgc::Value::Number(2.1), vmgc::Value::Number(4.2)]
    );

    compile_expr_test!(
        compile_greater_equal,
        ast::Expr::binary(
            Box::new(ast::Expr::literal_number(2.1)),
            ast::Operator::GreaterEqual,
            Box::new(ast::Expr::literal_number(4.2)),
        ),
        [
            vm::OpCode::Constant(0),
            vm::OpCode::Constant(1),
            vm::OpCode::Less,
            vm::OpCode::Not
        ],
        [vmgc::Value::Number(2.1), vmgc::Value::Number(4.2)]
    );

    compile_expr_test!(
        compile_logical_and,
        ast::Expr::logical(
            Box::new(ast::Expr::literal_bool(true)),
            ast::Operator::And,
            Box::new(ast::Expr::literal_bool(false))
        ),
        [
            vm::OpCode::True,
            vm::OpCode::JumpIfFalse(2),
            vm::OpCode::Pop,
            vm::OpCode::False
        ],
        []
    );

    compile_expr_test!(
        compile_logical_or,
        ast::Expr::logical(
            Box::new(ast::Expr::literal_bool(true)),
            ast::Operator::Or,
            Box::new(ast::Expr::literal_bool(false))
        ),
        [
            vm::OpCode::True,
            vm::OpCode::JumpIfFalse(1),
            vm::OpCode::Jump(2),
            vm::OpCode::Pop,
            vm::OpCode::False
        ],
        []
    );

    macro_rules! compile_stmts_test {
        ($name:ident, $stmts:expr, [ $($code:expr),* ], [ $($constant:expr),* ]) => {
            #[test]
            fn $name() -> Result<(), error::Error> {
                let mut heap = vmgc::Heap::new();
                let stmts = $stmts;
                let mut compiler = Compiler::new(parser::LocationTable::new(), &mut heap);
                let mut function = Function::new(0, "<script>");
                for stmt in stmts {
                    compiler.compile_stmt(&stmt, &mut function)?;
                }
                assert_eq!(function.chunk.code, vec![ $($code),* ]);
                let expected_constants : Vec<vmgc::Value> = vec![$($constant),*];
                assert_eq!(function.chunk.constants.len(), expected_constants.len());
                for i in 0..expected_constants.len() {
                    assert_eq!(expected_constants[i], function.chunk.constants[i]);
                }
                Ok(())
            }

        };
    }

    compile_stmts_test!(
        compile_print_constant,
        [ast::Stmt::print(Box::new(ast::Expr::literal_number(0.5),))],
        [vm::OpCode::Constant(0), vm::OpCode::Print],
        [vmgc::Value::Number(0.5)]
    );

    compile_stmts_test!(
        compile_return_nothing,
        [ast::Stmt::return_stmt(None)],
        [vm::OpCode::Nil, vm::OpCode::Return],
        []
    );

    compile_stmts_test!(
        compile_return_literal,
        [ast::Stmt::return_stmt(Some(Box::new(
            ast::Expr::literal_number(1.2)
        )))],
        [vm::OpCode::Constant(0), vm::OpCode::Return],
        [vmgc::Value::Number(1.2)]
    );
    compile_stmts_test!(
        compile_if_literal,
        [ast::Stmt::if_stmt(
            Box::new(ast::Expr::literal_bool(true)),
            Box::new(ast::Stmt::return_stmt(None)),
            None
        )],
        [
            vm::OpCode::True,
            vm::OpCode::JumpIfFalse(4),
            vm::OpCode::Pop,
            vm::OpCode::Nil,
            vm::OpCode::Return,
            vm::OpCode::Jump(1),
            vm::OpCode::Pop
        ],
        []
    );

    compile_stmts_test!(
        compile_if_else_literal,
        [ast::Stmt::if_stmt(
            Box::new(ast::Expr::literal_bool(true)),
            Box::new(ast::Stmt::return_stmt(None)),
            Some(Box::new(ast::Stmt::return_stmt(None)))
        )],
        [
            vm::OpCode::True,
            vm::OpCode::JumpIfFalse(4),
            vm::OpCode::Pop,
            vm::OpCode::Nil,
            vm::OpCode::Return,
            vm::OpCode::Jump(3),
            vm::OpCode::Pop,
            vm::OpCode::Nil,
            vm::OpCode::Return
        ],
        []
    );

    compile_stmts_test!(
        compile_while_else_literal,
        [ast::Stmt::while_stmt(
            Box::new(ast::Expr::literal_bool(true)),
            Box::new(ast::Stmt::return_stmt(None))
        )],
        [
            vm::OpCode::True,
            vm::OpCode::JumpIfFalse(4),
            vm::OpCode::Pop,
            vm::OpCode::Nil,
            vm::OpCode::Return,
            vm::OpCode::Jump(-6),
            vm::OpCode::Pop
        ],
        []
    );
}
