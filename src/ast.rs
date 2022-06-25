use crate::scanner::{self, Token, TokenValue};
pub enum Expr<'a> {
    Binary(BinaryExpr<'a>),
    Grouping(Box<Expr<'a>>),
    Literal(TokenValue<'a>),
    Unary(UnaryExpr<'a>),
}

pub struct UnaryExpr<'a> {
    pub operator: Token<'a>,
    pub right: Box<Expr<'a>>,
}

pub struct BinaryExpr<'a> {
    pub left: Box<Expr<'a>>,
    pub operator: Token<'a>,
    pub right: Box<Expr<'a>>,
}

pub trait Visitor<T> {
    fn visit_literal(&mut self, v: &scanner::TokenValue) -> T;
    fn visit_token(&mut self, t: &scanner::Token) -> T;
    fn visit_expr(&mut self, e: &Expr) -> T;
}

pub struct AstPrinter;
impl Visitor<String> for AstPrinter {
    fn visit_literal(&mut self, v: &scanner::TokenValue) -> String {
        match v {
            TokenValue::String(s) => s.to_string(),
            TokenValue::Number(n) => n.to_string(),
            TokenValue::Bool(b) => b.to_string(),
            TokenValue::Nil => "nil".to_string(),
        }
    }

    fn visit_token(&mut self, t: &scanner::Token) -> String {
        t.lexeme.to_string()
    }

    fn visit_expr(&mut self, e: &Expr) -> String {
        use Expr::*;
        match e {
            Binary(b) => {
                format!(
                    "( {} {} {} )",
                    self.visit_expr(&*b.left),
                    self.visit_token(&b.operator),
                    self.visit_expr(&*b.right)
                )
            }
            Grouping(e) => format!("group ( {} )", self.visit_expr(&*e)),
            Literal(v) => self.visit_literal(v),
            Unary(u) => format!(
                "( {} {} )",
                self.visit_token(&u.operator),
                self.visit_expr(&*u.right)
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::*;
    use crate::scanner::{Token, TokenType, TokenValue};

    #[test]
    fn print_binary_expr() {
        let expr = Expr::Binary(BinaryExpr {
            left: Box::new(Expr::Literal(TokenValue::Number(5.0))),
            operator: Token {
                token_type: TokenType::Plus,
                lexeme: "+",
                value: None,
                line: 0,
            },
            right: Box::new(Expr::Literal(TokenValue::Number(4.0))),
        });
        let mut printer = AstPrinter {};
        assert_eq!(printer.visit_expr(&expr), "( 5 + 4 )");
    }

    #[test]
    fn print_grouping_expr() {
        let expr = Expr::Grouping(Box::new(Expr::Literal(TokenValue::Number(5.0))));
        let mut printer = AstPrinter {};
        assert_eq!(printer.visit_expr(&expr), "group ( 5 )");
    }

    #[test]
    fn print_literal() {
        let mut printer = AstPrinter {};
        assert_eq!(
            printer.visit_expr(&Expr::Literal(TokenValue::Number(1.0))),
            "1"
        );
        assert_eq!(
            printer.visit_expr(&Expr::Literal(TokenValue::String("hi"))),
            "hi"
        );
    }

    #[test]
    fn print_unary() {
        let mut printer = AstPrinter {};
        assert_eq!(
            printer.visit_expr(&Expr::Unary(UnaryExpr {
                operator: Token {
                    token_type: TokenType::Minus,
                    line: 0,
                    lexeme: "-",
                    value: None,
                },
                right: Box::new(Expr::Literal(TokenValue::Number(5.0))),
            })),
            "( - 5 )"
        );
    }
}
