use crate::{ast, error, parser, vm};

struct Compiler {
    location_table: parser::LocationTable,
}

impl Compiler {
    pub fn new(location_table: parser::LocationTable) -> Self {
        Self { location_table }
    }

    fn compile_expr(
        &mut self,
        expr: &ast::Expr,
        chunk: &mut vm::Chunk,
    ) -> Result<(), error::Error> {
        let loc = match self.location_table.get(&expr.id()) {
            Some(loc) => loc.clone(),
            None => error::Location::default(),
        };
        match expr {
            ast::Expr::Unary(u) => match &u.operator {
                ast::Operator::Minus => chunk.add_negate(loc),
                ast::Operator::Bang => chunk.add_not(loc),
                _ => {
                    return Err(error::Error::CompileError);
                }
            },
            ast::Expr::Literal(l) => match &l.value {
                ast::LiteralValue::Number(n) => chunk.add_constant(vm::Value::Number(*n), loc),
                ast::LiteralValue::String(s) => {
                    chunk.add_constant(vm::Value::String(s.clone()), loc)
                }
                _ => {
                    return Err(error::Error::CompileError);
                }
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
                        return Err(error::Error::CompileError);
                    }
                }
            }
            _ => {
                return Err(error::Error::CompileError);
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ast, error, vm};

    macro_rules! compile_test {
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

    compile_test!(
        compile_constant,
        ast::Expr::literal_number(3.4),
        [vm::OpCode::Constant(0)],
        [vm::Value::Number(3.4)]
    );

    compile_test!(
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

    compile_test!(
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

    compile_test!(
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

    compile_test!(
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
}
