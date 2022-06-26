use crate::scanner::{self, Token, TokenValue};

#[derive(PartialEq, Debug)]
pub enum Expr<'a> {
    Binary(BinaryExpr<'a>),
    Grouping(Box<Expr<'a>>),
    Literal(TokenValue<'a>),
    Unary(UnaryExpr<'a>),
}

#[derive(PartialEq, Debug)]
pub struct UnaryExpr<'a> {
    pub operator: Token<'a>,
    pub right: Box<Expr<'a>>,
}

#[derive(PartialEq, Debug)]
pub struct BinaryExpr<'a> {
    pub left: Box<Expr<'a>>,
    pub operator: Token<'a>,
    pub right: Box<Expr<'a>>,
}

pub trait Visitor<T> {
    fn visit_literal(&mut self, v: &scanner::TokenValue) -> T;
    fn visit_expr(&mut self, e: &Expr) -> T {
        use Expr::*;
        match e {
            Binary(b) => self.visit_binary_expr(b),
            Grouping(g) => self.visit_grouping_expr(g),
            Literal(l) => self.visit_literal(l),
            Unary(u) => self.visit_unary_expr(u),
        }
    }
    fn visit_binary_expr(&mut self, e: &BinaryExpr) -> T;
    fn visit_grouping_expr(&mut self, e: &Expr) -> T;
    fn visit_unary_expr(&mut self, e: &UnaryExpr) -> T;
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

    fn visit_binary_expr(&mut self, b: &BinaryExpr) -> String {
        format!(
            "( {} {} {} )",
            self.visit_expr(&*b.left),
            b.operator.lexeme,
            self.visit_expr(&*b.right)
        )
    }

    fn visit_grouping_expr(&mut self, e: &Expr) -> String {
        format!("group ( {} )", self.visit_expr(&*e))
    }

    fn visit_unary_expr(&mut self, u: &UnaryExpr) -> String {
        format!("( {} {} )", u.operator.lexeme, self.visit_expr(&*u.right))
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
