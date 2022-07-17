use crate::{
    ast,
    error::{self, ParseError},
    parser, vm,
};

pub struct Compiler {
    location_table: parser::LocationTable,
}

impl Compiler {
    pub fn new(location_table: parser::LocationTable) -> Self {
        Self { location_table }
    }

    pub fn compile_stmt(
        &mut self,
        stmt: &ast::Stmt,
        chunk: &mut vm::Chunk,
    ) -> Result<(), error::Error> {
        let loc = match self.location_table.get(&stmt.id()) {
            Some(loc) => loc.clone(),
            None => error::Location::default(),
        };
        match stmt {
            ast::Stmt::Expr(e) => self.compile_expr(&*e.expr, chunk)?,
            ast::Stmt::Print(p) => {
                self.compile_expr(&p.expr, chunk)?;
                chunk.add_print(loc);
            }
            ast::Stmt::Return(_) => chunk.add_return(loc),
            ast::Stmt::Block(b) => {
                for bs in &b.stmts {
                    self.compile_stmt(&*bs, chunk)?;
                }
            }
            ast::Stmt::Var(v) => {
                match &v.initializer {
                    Some(e) => self.compile_expr(e, chunk)?,
                    None => chunk.add_nil(loc.clone()),
                }
                chunk.add_define_global(&v.name, loc);
            }
            ast::Stmt::If(i) => {
                self.compile_expr(&i.condition, chunk)?;

                let then_offset = chunk.add_jump(vm::OpCode::JumpIfFalse(i16::MAX), loc.clone());
                chunk.add_pop(loc.clone());

                self.compile_stmt(&*i.then_branch, chunk)?;

                let else_offset = chunk.add_jump(vm::OpCode::Jump(i16::MAX), loc.clone());

                chunk.patch_jump(then_offset);
                chunk.add_pop(loc.clone());

                if let Some(else_branch) = &i.else_branch {
                    self.compile_stmt(else_branch, chunk)?;
                }
                chunk.patch_jump(else_offset);
            }
            ast::Stmt::While(_) => todo!(),
            ast::Stmt::Function(_) => todo!(),
            ast::Stmt::Class(_) => todo!(),
        }
        Ok(())
    }

    pub fn compile_expr(
        &mut self,
        expr: &ast::Expr,
        chunk: &mut vm::Chunk,
    ) -> Result<(), error::Error> {
        let loc = match self.location_table.get(&expr.id()) {
            Some(loc) => loc.clone(),
            None => error::Location::default(),
        };
        match expr {
            ast::Expr::Unary(u) => {
                self.compile_expr(&u.right, chunk)?;
                match &u.operator {
                    ast::Operator::Minus => chunk.add_negate(loc),
                    ast::Operator::Bang => chunk.add_not(loc),
                    _ => {
                        return Err(error::Error::Parse(ParseError::new(
                            "unknown unary operator",
                            loc,
                        )));
                    }
                }
            }
            ast::Expr::Literal(l) => match &l.value {
                ast::LiteralValue::Number(n) => chunk.add_constant(vm::Value::Number(*n), loc),
                ast::LiteralValue::String(s) => {
                    chunk.add_constant(vm::Value::String(s.clone()), loc)
                }
                ast::LiteralValue::Bool(b) => chunk.add_constant(vm::Value::Bool(*b), loc),
                ast::LiteralValue::Nil => chunk.add_constant(vm::Value::Nil, loc),
            },
            ast::Expr::Binary(b) => {
                self.compile_expr(&b.left, chunk)?;
                self.compile_expr(&b.right, chunk)?;
                match b.operator {
                    ast::Operator::Minus => {
                        // a - b is equivalent to a + (- b) and b is at the top of the stack.
                        chunk.add_negate(loc.clone());
                        chunk.add_add(loc);
                    }
                    ast::Operator::Plus => chunk.add_add(loc),
                    ast::Operator::Slash => chunk.add_divide(loc),
                    ast::Operator::Star => chunk.add_multiply(loc),
                    ast::Operator::BangEqual => {
                        chunk.add_equal(loc.clone());
                        chunk.add_not(loc);
                    }
                    ast::Operator::EqualEqual => chunk.add_equal(loc),
                    ast::Operator::Greater => chunk.add_greater(loc),
                    ast::Operator::GreaterEqual => {
                        chunk.add_less(loc.clone());
                        chunk.add_not(loc);
                    }
                    ast::Operator::Less => chunk.add_less(loc),
                    ast::Operator::LessEqual => {
                        chunk.add_greater(loc.clone());
                        chunk.add_not(loc);
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
                chunk.add_get_global(&v.name, loc);
            }
            ast::Expr::Assign(a) => {
                self.compile_expr(&a.value, chunk)?;
                chunk.add_set_global(&a.name, loc);
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
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ast, error, vm};

    macro_rules! compile_expr_test {
        ($name:ident, $expr:expr, [ $($code:expr),* ], [ $($constant:expr),* ]) => {
            #[test]
            fn $name() -> Result<(), error::Error> {
                let expr = $expr;
                let mut compiler = Compiler::new(parser::LocationTable::new());
                let mut chunk = vm::Chunk::new();
                compiler.compile_expr(&expr, &mut chunk)?;
                assert_eq!(chunk.code, vec![ $($code),* ]);
                assert_eq!(chunk.constants, vec![ $($constant),* ]);
                Ok(())
            }

        };
    }

    compile_expr_test!(
        compile_constant,
        ast::Expr::literal_number(3.4),
        [vm::OpCode::Constant(0)],
        [vm::Value::Number(3.4)]
    );

    compile_expr_test!(
        compile_negate_number,
        ast::Expr::unary(
            ast::Operator::Minus,
            Box::new(ast::Expr::literal_number(1.2)),
        ),
        // - 1.2
        [vm::OpCode::Constant(0), vm::OpCode::Negate],
        [vm::Value::Number(1.2)]
    );

    compile_expr_test!(
        compile_not_boolean,
        ast::Expr::unary(
            ast::Operator::Bang,
            Box::new(ast::Expr::literal_bool(false)),
        ),
        // - 1.2
        [vm::OpCode::Constant(0), vm::OpCode::Not],
        [vm::Value::Bool(false)]
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
        [vm::Value::Number(1.2), vm::Value::Number(4.7)]
    );

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
        [
            vm::Value::String("foo".to_string()),
            vm::Value::String("bar".to_string())
        ]
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
        [vm::Value::Number(2.1), vm::Value::Number(4.2)]
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
        [vm::Value::Number(2.1), vm::Value::Number(4.2)]
    );

    macro_rules! compile_stmts_test {
        ($name:ident, $stmts:expr, [ $($code:expr),* ], [ $($constant:expr),* ]) => {
            #[test]
            fn $name() -> Result<(), error::Error> {
                let stmts = $stmts;
                let mut compiler = Compiler::new(parser::LocationTable::new());
                let mut chunk = vm::Chunk::new();
                for stmt in stmts {
                    compiler.compile_stmt(&stmt, &mut chunk)?;
                }
                assert_eq!(chunk.code, vec![ $($code),* ]);
                assert_eq!(chunk.constants, vec![ $($constant),* ]);
                Ok(())
            }

        };
    }

    compile_stmts_test!(
        compile_print_constant,
        [ast::Stmt::print(Box::new(ast::Expr::literal_number(0.5),))],
        [vm::OpCode::Constant(0), vm::OpCode::Print],
        [vm::Value::Number(0.5)]
    );

    compile_stmts_test!(
        compile_if_literal,
        [ast::Stmt::if_stmt(
            Box::new(ast::Expr::literal_bool(true)),
            Box::new(ast::Stmt::return_stmt(None)),
            None
        )],
        [
            vm::OpCode::Constant(0),
            vm::OpCode::JumpIfFalse(3),
            vm::OpCode::Pop,
            vm::OpCode::Return,
            vm::OpCode::Jump(1),
            vm::OpCode::Pop
        ],
        [vm::Value::Bool(true)]
    );

    compile_stmts_test!(
        compile_if_else_literal,
        [ast::Stmt::if_stmt(
            Box::new(ast::Expr::literal_bool(true)),
            Box::new(ast::Stmt::return_stmt(None)),
            Some(Box::new(ast::Stmt::return_stmt(None)))
        )],
        [
            vm::OpCode::Constant(0),
            vm::OpCode::JumpIfFalse(3),
            vm::OpCode::Pop,
            vm::OpCode::Return,
            vm::OpCode::Jump(2),
            vm::OpCode::Pop,
            vm::OpCode::Return
        ],
        [vm::Value::Bool(true)]
    );
}
