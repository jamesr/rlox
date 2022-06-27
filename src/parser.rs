use std::cell::RefCell;

use crate::scanner::{Scanner, Token, TokenType, TokenValue};
use crate::{ast, error};

struct ParserState<'a> {
    scanner: Scanner<'a>,
    current: Option<Token<'a>>,
    prev: Option<Token<'a>>,
}
pub struct Parser<'a> {
    state: RefCell<ParserState<'a>>,
}

type ExprResult<'a> = anyhow::Result<Box<ast::Expr<'a>>, error::Error>;
type StmtResult<'a> = anyhow::Result<Box<ast::Stmt<'a>>, error::Error>;
type StmtsResult<'a> = anyhow::Result<Vec<Box<ast::Stmt<'a>>>, error::Error>;

impl<'a> Parser<'a> {
    pub fn new(scanner: Scanner<'a>) -> Parser<'a> {
        Parser {
            state: RefCell::new(ParserState {
                scanner,
                current: None,
                prev: None,
            }),
        }
    }

    pub fn parse_expression(&mut self) -> ExprResult<'a> {
        self.prime()?;
        self.expression()
    }

    pub fn parse(&mut self) -> StmtsResult<'a> {
        self.prime()?;

        self.program()
    }

    // program → declaration* EOF ;
    fn program(&self) -> StmtsResult<'a> {
        let mut statements = Vec::new();

        while !self.at_end() {
            statements.push(self.declaration()?);
        }

        Ok(statements)
    }

    // declaration → varDecl | statement ;
    fn declaration(&self) -> StmtResult<'a> {
        // TODO - synchronize on errors here

        if self.matches(&[TokenType::Var])? {
            return self.var_decl();
        }

        self.statement()
    }

    // varDecl → "var" IDENTIFIER ( "=" expression )? ";" ;
    fn var_decl(&self) -> StmtResult<'a> {
        self.consume(TokenType::Identifier, "Expect variable name.")?;
        let name = self.previous().unwrap();

        let initializer = if self.matches(&[TokenType::Equal])? {
            Some(self.expression()?)
        } else {
            None
        };

        self.consume(
            TokenType::Semicolon,
            "Expect ';' after variable declaration.",
        )?;
        Ok(Box::new(ast::Stmt::Var(ast::VarDecl { name, initializer })))
    }

    fn prime(&self) -> anyhow::Result<(), error::Error> {
        let first = match self.state.borrow_mut().scanner.next() {
            Some(result) => result,
            None => return Err(error::Error::new("Expected expression".to_string())),
        };
        self.state.borrow_mut().current = Some(first?);
        Ok(())
    }

    fn peek(&self) -> Option<Token<'a>> {
        self.state.borrow().current
    }

    fn at_end(&self) -> bool {
        self.state.borrow().current.is_none()
    }

    fn previous(&self) -> Option<Token<'a>> {
        self.state.borrow().prev
    }

    fn check(&self, token_type: TokenType) -> bool {
        match self.peek() {
            Some(token) => token.token_type == token_type,
            None => false,
        }
    }

    fn error(&self, message: String) -> error::Error {
        let scanner = &self.state.borrow().scanner;
        error::Error::with_col(scanner.line, scanner.current.clone(), message)
    }

    fn advance(&self) -> anyhow::Result<(), error::Error> {
        let mut current = self.state.borrow_mut().current.take();
        self.state.borrow_mut().prev = current.take();
        let mut new_current = match self.state.borrow_mut().scanner.next() {
            None => None,
            Some(result) => Some(result?),
        };
        self.state.borrow_mut().current = new_current.take();
        Ok(())
    }

    fn matches(&self, types: &[TokenType]) -> anyhow::Result<bool, error::Error> {
        for token_type in types {
            if self.check(*token_type) {
                self.advance()?;
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn consume(&self, token_type: TokenType, message: &str) -> anyhow::Result<(), error::Error> {
        if self.check(token_type) {
            return self.advance();
        }
        Err(self.error(format!(
            "expected to find type {:?} {}",
            token_type, message
        )))
    }

    /*
    fn synchronize(&self) {
        self.advance()
    }
    */

    // expression → equality ;
    fn expression(&self) -> ExprResult<'a> {
        self.equality()
    }

    // equality → comparison ( ( "!=" | "==" ) comparison )* ;
    fn equality(&self) -> ExprResult<'a> {
        let mut expr = self.comparison()?;

        while self.matches(&[TokenType::BangEqual, TokenType::EqualEqual])? {
            let operator = self.previous();
            let right = self.comparison()?;
            expr = Box::new(ast::Expr::Binary(ast::BinaryExpr {
                left: expr,
                operator: operator.unwrap(),
                right,
            }));
        }

        Ok(expr)
    }

    // comparison → term ( ( ">" | ">=" | "<" | "<=" ) term )* ;
    fn comparison(&self) -> ExprResult<'a> {
        let mut expr = self.term()?;

        while self.matches(&[
            TokenType::Greater,
            TokenType::GreaterEqual,
            TokenType::Less,
            TokenType::LessEqual,
        ])? {
            let operator = self.previous();
            let right = self.term()?;
            expr = Box::new(ast::Expr::Binary(ast::BinaryExpr {
                left: expr,
                operator: operator.unwrap(),
                right,
            }))
        }

        Ok(expr)
    }

    // term → factor ( ( "-" | "+" ) factor )* ;
    fn term(&self) -> ExprResult<'a> {
        let mut expr = self.factor()?;

        while self.matches(&[TokenType::Minus, TokenType::Plus])? {
            let operator = self.previous();
            let right = self.factor()?;
            expr = Box::new(ast::Expr::Binary(ast::BinaryExpr {
                left: expr,
                operator: operator.unwrap(),
                right,
            }))
        }

        Ok(expr)
    }

    // factor → unary ( ( "/" | "*" ) unary )* ;
    fn factor(&self) -> ExprResult<'a> {
        let mut expr = self.unary()?;

        while self.matches(&[TokenType::Slash, TokenType::Star])? {
            let operator = self.previous();
            let right = self.unary()?;
            expr = Box::new(ast::Expr::Binary(ast::BinaryExpr {
                left: expr,
                operator: operator.unwrap(),
                right,
            }))
        }

        Ok(expr)
    }

    // unary → ( "!" | "-" ) unary | primary ;
    fn unary(&self) -> ExprResult<'a> {
        if self.matches(&[TokenType::Bang, TokenType::Minus])? {
            let operator = self.previous();
            let right = self.unary()?;
            return Ok(Box::new(ast::Expr::Unary(ast::UnaryExpr {
                operator: operator.unwrap(),
                right,
            })));
        }
        self.primary()
    }

    // primary  → "true" | "false" | "nil"
    //          | NUMBER | STRING
    //          | "(" expression ")"
    //          | IDENTIFIER ;
    fn primary(&self) -> ExprResult<'a> {
        if self.matches(&[TokenType::True])? {
            return Ok(Box::new(ast::Expr::Literal(TokenValue::Bool(true))));
        }
        if self.matches(&[TokenType::False])? {
            return Ok(Box::new(ast::Expr::Literal(TokenValue::Bool(false))));
        }
        if self.matches(&[TokenType::Nil])? {
            return Ok(Box::new(ast::Expr::Literal(TokenValue::Nil)));
        }
        if self.matches(&[TokenType::Number, TokenType::String])? {
            return Ok(Box::new(ast::Expr::Literal(
                self.previous().unwrap().value.unwrap(),
            )));
        }
        if self.matches(&[TokenType::LeftParen])? {
            let expr = self.expression()?;
            self.consume(TokenType::RightParen, "Expect ')' after expression.")?;
            return Ok(Box::new(ast::Expr::Grouping(expr)));
        }
        if self.matches(&[TokenType::Identifier])? {
            let token = self.previous().unwrap();
            return Ok(Box::new(ast::Expr::Variable(token)));
        }
        Err(self.error("expected expression".to_string()))
    }

    // statement → exprStmt | printStmt ;
    fn statement(&self) -> StmtResult<'a> {
        if self.matches(&[TokenType::Print])? {
            return self.print_stmt();
        }

        self.expr_stmt()
    }

    // exprStmt → expression ";" ;
    fn expr_stmt(&self) -> StmtResult<'a> {
        let expr = self.expression()?;
        self.consume(TokenType::Semicolon, "Expect ';' after value.")?;
        Ok(Box::new(ast::Stmt::Expr(expr)))
    }

    // printStmt → "print" expression ";"
    fn print_stmt(&self) -> StmtResult<'a> {
        let expr = self.expression()?;
        self.consume(TokenType::Semicolon, "Expect ';' after value.")?;
        Ok(Box::new(ast::Stmt::Print(expr)))
    }
}

pub fn parse<'a>(source: &'a str) -> StmtsResult<'a> {
    let scanner = Scanner::new(source);
    let mut parser = Parser::new(scanner);
    parser.parse()
}

pub fn parse_expression<'a>(source: &str) -> ExprResult {
    let scanner = Scanner::new(source);
    let mut parser = Parser::new(scanner);
    parser.parse_expression()
}

#[cfg(test)]
mod tests {
    use crate::ast::UnaryExpr;
    use crate::parser::parse_expression;
    use crate::scanner::{Token, TokenType, TokenValue};
    use crate::{ast, error};

    #[test]
    fn comparison() -> Result<(), error::Error> {
        let expr = parse_expression("0 == 2")?;
        assert!(matches!(*expr, ast::Expr::Binary { .. }));
        if let ast::Expr::Binary(b) = *expr {
            assert!(matches!(*b.left, ast::Expr::Literal { .. }));
        }
        Ok(())
    }

    #[test]
    fn literal() -> Result<(), error::Error> {
        let false_literal = parse_expression("false")?;
        assert_eq!(*false_literal, ast::Expr::Literal(TokenValue::Bool(false)));

        let true_literal = parse_expression("true")?;
        assert_eq!(*true_literal, ast::Expr::Literal(TokenValue::Bool(true)));

        Ok(())
    }

    #[test]
    fn unary() -> Result<(), error::Error> {
        let unary_minus = parse_expression("- 5")?;
        assert_eq!(
            *unary_minus,
            ast::Expr::Unary(UnaryExpr {
                operator: Token {
                    token_type: TokenType::Minus,
                    lexeme: "-",
                    value: None,
                    line: 0,
                },
                right: Box::new(ast::Expr::Literal(TokenValue::Number(5.0))),
            })
        );

        let unary_negate = parse_expression("!false")?;
        assert_eq!(
            *unary_negate,
            ast::Expr::Unary(UnaryExpr {
                operator: Token {
                    token_type: TokenType::Bang,
                    lexeme: "!",
                    value: None,
                    line: 0,
                },
                right: Box::new(ast::Expr::Literal(TokenValue::Bool(false))),
            })
        );
        Ok(())
    }
}
