use crate::{ast::*, error, scanner::*};

pub trait Visitor<ExprResult, StmtResult> {
    fn expr_result_to_stmt_result(&self, e: ExprResult) -> StmtResult;
    fn report_error(&mut self, _: error::Error) {}

    fn visit_literal(&mut self, v: &TokenValue) -> ExprResult;
    fn visit_expr(&mut self, e: &Expr) -> ExprResult {
        use Expr::*;
        match e {
            Binary(b) => self.visit_binary_expr(b),
            Grouping(g) => self.visit_grouping_expr(g),
            Literal(l) => self.visit_literal(l),
            Unary(u) => self.visit_unary_expr(u),
            Variable(t) => self.visit_variable(t),
            Assign(a) => self.visit_assign(a),
            Logical(a) => self.visit_logical(a),
        }
    }
    fn visit_binary_expr(&mut self, e: &BinaryExpr) -> ExprResult;
    fn visit_grouping_expr(&mut self, e: &Expr) -> ExprResult;
    fn visit_unary_expr(&mut self, e: &UnaryExpr) -> ExprResult;
    fn visit_variable(&mut self, t: &Token) -> ExprResult;
    fn visit_assign(&mut self, a: &AssignExpr) -> ExprResult;
    fn visit_logical(&mut self, l: &LogicalExpr) -> ExprResult;

    fn visit_stmt(&mut self, s: &Stmt) -> StmtResult {
        use Stmt::*;
        match s {
            Expr(e) => {
                let expr_result = self.visit_expr(e);
                return self.expr_result_to_stmt_result(expr_result);
            }
            Print(e) => self.visit_print_stmt(e),
            Block(v) => self.visit_block(v),
            Var(v) => self.visit_var_decl_stmt(v),
            If(i) => self.visit_if_stmt(i),
            While(i) => self.visit_while_stmt(i),
        }
    }

    fn visit_block(&mut self, v: &Vec<Box<Stmt>>) -> StmtResult;
    fn visit_print_stmt(&mut self, e: &Expr) -> StmtResult;
    fn visit_var_decl_stmt(&mut self, v: &VarDecl) -> StmtResult;
    fn visit_if_stmt(&mut self, i: &IfStmt) -> StmtResult;
    fn visit_while_stmt(&mut self, w: &WhileStmt) -> StmtResult;
}

pub struct AstPrinter;
impl Visitor<String, String> for AstPrinter {
    fn expr_result_to_stmt_result(&self, e: String) -> String {
        e
    }

    fn visit_literal(&mut self, v: &TokenValue) -> String {
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

    fn visit_logical(&mut self, l: &LogicalExpr) -> String {
        format!(
            "logic ( {} ) {} ( {} )",
            self.visit_expr(&l.left),
            l.operator.lexeme,
            self.visit_expr(&l.right)
        )
    }

    fn visit_block(&mut self, stmts: &Vec<Box<Stmt>>) -> String {
        stmts.iter().fold("block {\n".to_string(), |acc, stmt| {
            acc + &self.visit_stmt(stmt) + "\n"
        }) + "}\n"
    }
    fn visit_print_stmt(&mut self, e: &Expr) -> String {
        format!("{} ;", self.visit_expr(e))
    }
    fn visit_var_decl_stmt(&mut self, v: &VarDecl) -> String {
        let mut s = format!("var {}", v.name.lexeme).to_string();

        if let Some(initializer) = &v.initializer {
            s.push_str(&format!(" = ( {} )", self.visit_expr(&initializer)));
        }
        s.push_str(" ;");
        return s;
    }
    fn visit_if_stmt(&mut self, i: &IfStmt) -> String {
        let mut s = format!(
            "if ( {} ) {{\n  {}\n}}",
            self.visit_expr(&i.condition),
            self.visit_stmt(&i.then_branch)
        )
        .to_string();

        if let Some(else_branch) = &i.else_branch {
            s.push_str(&format!(
                " else {{\n  {}\n}}",
                self.visit_stmt(&else_branch)
            ));
        }
        return s;
    }
    fn visit_while_stmt(&mut self, w: &WhileStmt) -> String {
        format!(
            "while ( {} ) {{\n  {}\n}}",
            self.visit_expr(&w.condition),
            self.visit_stmt(&w.body)
        )
        .to_string()
    }
}

#[cfg(test)]
mod tests {
    use crate::scanner::{Token, TokenType, TokenValue};
    use crate::visitor::*;

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
