use std::cell::RefCell;

use crate::ast;
use crate::scanner::{Scanner, Token, TokenType, TokenValue};

struct ParserState<'a> {
    scanner: &'a mut Scanner<'a>,
    current: Option<Token<'a>>,
    prev: Option<Token<'a>>,
}
pub struct Parser<'a> {
    state: RefCell<ParserState<'a>>,
}

impl<'a> Parser<'a> {
    pub fn new(scanner: &'a mut Scanner<'a>) -> Parser<'a> {
        let first = scanner.next().unwrap().ok();
        Parser {
            state: RefCell::new(ParserState {
                scanner,
                current: first,
                prev: None,
            }),
        }
    }

    pub fn parse(&self) -> Box<ast::Expr> {
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

    fn advance(&self) {
        let mut current = self.state.borrow_mut().current.take();
        self.state.borrow_mut().prev = current.take();
        let mut new_current = match self.state.borrow_mut().scanner.next() {
            None => None,
            Some(result) => match result {
                Ok(token) => Some(token),
                Err(e) => panic!("{:?}", e),
            },
        };
        self.state.borrow_mut().current = new_current.take();
    }

    fn matches(&self, types: &[TokenType]) -> bool {
        for token_type in types {
            if self.check(*token_type) {
                println!("found a match for {:?}", *token_type);
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
    fn expression(&self) -> Box<ast::Expr> {
        self.equality()
    }

    // equality → comparison ( ( "!=" | "==" ) comparison )* ;
    fn equality(&self) -> Box<ast::Expr> {
        let mut expr = self.comparison();

        while self.matches(&[TokenType::BangEqual, TokenType::EqualEqual]) {
            let operator = self.previous();
            let right = self.comparison();
            expr = Box::new(ast::Expr::Binary(ast::BinaryExpr {
                left: expr,
                operator: operator.unwrap(),
                right,
            }));
        }

        expr
    }

    // comparison → term ( ( ">" | ">=" | "<" | "<=" ) term )* ;
    fn comparison(&self) -> Box<ast::Expr> {
        let mut expr = self.term();

        while self.matches(&[
            TokenType::Greater,
            TokenType::GreaterEqual,
            TokenType::Less,
            TokenType::LessEqual,
        ]) {
            let operator = self.previous();
            let right = self.term();
            expr = Box::new(ast::Expr::Binary(ast::BinaryExpr {
                left: expr,
                operator: operator.unwrap(),
                right,
            }))
        }

        expr
    }

    // term → factor ( ( "-" | "+" ) factor )* ;
    fn term(&self) -> Box<ast::Expr> {
        let mut expr = self.factor();

        while self.matches(&[TokenType::Minus, TokenType::Plus]) {
            let operator = self.previous();
            let right = self.factor();
            expr = Box::new(ast::Expr::Binary(ast::BinaryExpr {
                left: expr,
                operator: operator.unwrap(),
                right,
            }))
        }

        expr
    }

    // factor → unary ( ( "/" | "*" ) unary )* ;
    fn factor(&self) -> Box<ast::Expr> {
        let mut expr = self.unary();

        while self.matches(&[TokenType::Slash, TokenType::Star]) {
            let operator = self.previous();
            let right = self.unary();
            expr = Box::new(ast::Expr::Binary(ast::BinaryExpr {
                left: expr,
                operator: operator.unwrap(),
                right,
            }))
        }

        expr
    }

    // unary → ( "!" | "-" ) unary | primary ;
    fn unary(&self) -> Box<ast::Expr> {
        if self.matches(&[TokenType::Plus, TokenType::Minus]) {
            let operator = self.previous();
            let right = self.unary();
            return Box::new(ast::Expr::Unary(ast::UnaryExpr {
                operator: operator.unwrap(),
                right,
            }));
        }
        self.primary()
    }

    // primary → NUMBER | STRING | "true" | "false" | "nil" | "(" expression ")" ;
    fn primary(&self) -> Box<ast::Expr> {
        if self.matches(&[TokenType::Number, TokenType::String]) {
            return Box::new(ast::Expr::Literal(self.previous().unwrap().value.unwrap()));
        }
        if self.matches(&[TokenType::True]) {
            return Box::new(ast::Expr::Literal(TokenValue::Bool(true)));
        }
        if self.matches(&[TokenType::False]) {
            return Box::new(ast::Expr::Literal(TokenValue::Bool(false)));
        }
        if self.matches(&[TokenType::Nil]) {
            return Box::new(ast::Expr::Literal(TokenValue::Nil));
        }
        if self.matches(&[TokenType::LeftParen]) {
            let expr = self.expression();
            self.consume(TokenType::RightParen, "Expect ')' after expression.");
            return Box::new(ast::Expr::Grouping(expr));
        }
        panic!("expected expression");
    }
}

#[cfg(test)]
mod tests {
    use crate::ast;
    use crate::scanner::Scanner;

    use super::Parser;

    #[test]
    fn parse_comparison() {
        let source = "0 == 2";
        let mut scanner = Scanner::new(source);
        let parser = Parser::new(&mut scanner);
        let expr = parser.expression();
        assert!(matches!(*expr, ast::Expr::Binary { .. }));
        if let ast::Expr::Binary(b) = *expr {
            assert!(matches!(*b.left, ast::Expr::Literal { .. }));
        }
    }
}
