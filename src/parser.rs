use std::cell::RefCell;

use crate::scanner::{Scanner, Token, TokenType, TokenValue};
use crate::{ast, error};

struct ParserState<'a> {
    scanner: &'a mut Scanner<'a>,
    current: Option<Token<'a>>,
    prev: Option<Token<'a>>,
}
pub struct Parser<'a> {
    state: RefCell<ParserState<'a>>,
}

type ParseResult<'a> = anyhow::Result<Box<ast::Expr<'a>>, error::Error>;

impl<'a> Parser<'a> {
    pub fn new(scanner: &'a mut Scanner<'a>) -> Parser<'a> {
        Parser {
            state: RefCell::new(ParserState {
                scanner,
                current: None,
                prev: None,
            }),
        }
    }

    pub fn parse(&self) -> ParseResult<'a> {
        let first = match self.state.borrow_mut().scanner.next() {
            Some(result) => result,
            None => return Err(error::Error::new("Expected expression".to_string())),
        };
        self.state.borrow_mut().current = Some(first?);
        self.expression()
    }

    fn peek(&self) -> Option<Token<'a>> {
        self.state.borrow().current
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

    fn matches(&self, types: &[TokenType]) -> bool {
        for token_type in types {
            if self.check(*token_type) {
                self.advance();
                return true;
            }
        }
        false
    }

    fn consume(&self, token_type: TokenType, message: &str) {
        if self.check(token_type) {
            self.advance();
            return;
        }
        panic!("expected to find type {:?} {}", token_type, message);
    }

    // expression → equality ;
    fn expression(&self) -> ParseResult<'a> {
        self.equality()
    }

    // equality → comparison ( ( "!=" | "==" ) comparison )* ;
    fn equality(&self) -> ParseResult<'a> {
        let mut expr = self.comparison()?;

        while self.matches(&[TokenType::BangEqual, TokenType::EqualEqual]) {
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
    fn comparison(&self) -> ParseResult<'a> {
        let mut expr = self.term()?;

        while self.matches(&[
            TokenType::Greater,
            TokenType::GreaterEqual,
            TokenType::Less,
            TokenType::LessEqual,
        ]) {
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
    fn term(&self) -> ParseResult<'a> {
        let mut expr = self.factor()?;

        while self.matches(&[TokenType::Minus, TokenType::Plus]) {
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
    fn factor(&self) -> ParseResult<'a> {
        let mut expr = self.unary()?;

        while self.matches(&[TokenType::Slash, TokenType::Star]) {
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
    fn unary(&self) -> ParseResult<'a> {
        if self.matches(&[TokenType::Plus, TokenType::Minus]) {
            let operator = self.previous();
            let right = self.unary()?;
            return Ok(Box::new(ast::Expr::Unary(ast::UnaryExpr {
                operator: operator.unwrap(),
                right,
            })));
        }
        self.primary()
    }

    // primary → NUMBER | STRING | "true" | "false" | "nil" | "(" expression ")" ;
    fn primary(&self) -> ParseResult<'a> {
        if self.matches(&[TokenType::Number, TokenType::String]) {
            return Ok(Box::new(ast::Expr::Literal(
                self.previous().unwrap().value.unwrap(),
            )));
        }
        if self.matches(&[TokenType::True]) {
            return Ok(Box::new(ast::Expr::Literal(TokenValue::Bool(true))));
        }
        if self.matches(&[TokenType::False]) {
            return Ok(Box::new(ast::Expr::Literal(TokenValue::Bool(false))));
        }
        if self.matches(&[TokenType::Nil]) {
            return Ok(Box::new(ast::Expr::Literal(TokenValue::Nil)));
        }
        if self.matches(&[TokenType::LeftParen]) {
            let expr = self.expression()?;
            self.consume(TokenType::RightParen, "Expect ')' after expression.");
            return Ok(Box::new(ast::Expr::Grouping(expr)));
        }
        let scanner = &self.state.borrow().scanner;
        Err(error::Error::with_col(
            scanner.line,
            scanner.current.clone(),
            "expected expression".to_string(),
        ))
    }
}

#[cfg(test)]
mod tests {
    use crate::scanner::Scanner;
    use crate::{ast, error};

    use super::Parser;

    #[test]
    fn parse_comparison() -> Result<(), error::Error> {
        let source = "0 == 2";
        let mut scanner = Scanner::new(source);
        let parser = Parser::new(&mut scanner);
        let expr = parser.parse()?;
        assert!(matches!(*expr, ast::Expr::Binary { .. }));
        if let ast::Expr::Binary(b) = *expr {
            assert!(matches!(*b.left, ast::Expr::Literal { .. }));
        }
        Ok(())
    }
}
