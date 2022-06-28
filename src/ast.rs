use crate::scanner::{self, Token, TokenValue};

#[derive(PartialEq, Debug)]
pub enum Expr<'a> {
    Binary(BinaryExpr<'a>),
    Grouping(Box<Expr<'a>>),
    Literal(TokenValue<'a>),
    Unary(UnaryExpr<'a>),
    Variable(Token<'a>),
    Assign(AssignExpr<'a>),
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

#[derive(PartialEq, Debug)]
pub struct AssignExpr<'a> {
    pub name: Token<'a>,
    pub value: Box<Expr<'a>>,
}

#[derive(PartialEq, Debug)]
pub enum Stmt<'a> {
    Expr(Box<Expr<'a>>),
    Print(Box<Expr<'a>>),
    Block(Vec<Box<Stmt<'a>>>),
    Var(VarDecl<'a>),
}

#[derive(PartialEq, Debug)]
pub struct VarDecl<'a> {
    pub name: Token<'a>,
    pub initializer: Option<Box<Expr<'a>>>,
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
            Variable(t) => self.visit_variable(t),
            Assign(a) => self.visit_assign(a),
        }
    }
    fn visit_binary_expr(&mut self, e: &BinaryExpr) -> T;
    fn visit_grouping_expr(&mut self, e: &Expr) -> T;
    fn visit_unary_expr(&mut self, e: &UnaryExpr) -> T;
    fn visit_variable(&mut self, t: &Token) -> T;
    fn visit_assign(&mut self, a: &AssignExpr) -> T;

    fn visit_stmt(&mut self, s: &Stmt) {
        use Stmt::*;
        match s {
            Expr(e) => {
                self.visit_expr(e);
            }
            Print(e) => self.visit_print_stmt(e),
            Block(v) => {
                for s in v {
                    self.visit_stmt(s);
                }
            }
            Var(v) => {
                self.visit_var_decl_stmt(v);
            }
        }
    }

    fn visit_print_stmt(&mut self, e: &Expr);
    fn visit_var_decl_stmt(&mut self, v: &VarDecl);
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

    fn visit_variable(&mut self, t: &Token) -> String {
        format!("variable ( {} )", t.lexeme)
    }

    fn visit_assign(&mut self, a: &AssignExpr) -> String {
        format!("assign {} = ( {} )", a.name, self.visit_expr(&a.value))
    }

    fn visit_print_stmt(&mut self, _: &Expr) {}
    fn visit_var_decl_stmt(&mut self, _: &VarDecl) {}
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
