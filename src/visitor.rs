use std::rc::Rc;

use crate::{ast::*, error};

pub trait Visitor<ExprResult, StmtResult> {
    fn expr_result_to_stmt_result(&self, e: ExprResult) -> StmtResult;
    fn report_error(&mut self, _: error::Error) {}

    fn visit_literal(&mut self, v: &LiteralExpr) -> ExprResult;
    fn visit_expr(&mut self, e: &Expr) -> ExprResult {
        use Expr::*;
        match e {
            Binary(b) => self.visit_binary_expr(b),
            Grouping(g) => self.visit_grouping_expr(g),
            Literal(l) => self.visit_literal(l),
            Unary(u) => self.visit_unary_expr(u),
            Variable(v) => self.visit_variable(v),
            Assign(a) => self.visit_assign(a),
            Logical(a) => self.visit_logical(a),
            Call(c) => self.visit_call(c),
            Set(s) => self.visit_set(s),
            Get(g) => self.visit_get(g),
            Super(s) => self.visit_super(s),
            This(t) => self.visit_this(t),
        }
    }
    fn visit_binary_expr(&mut self, e: &BinaryExpr) -> ExprResult;
    fn visit_grouping_expr(&mut self, e: &GroupingExpr) -> ExprResult;
    fn visit_unary_expr(&mut self, e: &UnaryExpr) -> ExprResult;
    fn visit_variable(&mut self, s: &VariableExpr) -> ExprResult;
    fn visit_assign(&mut self, a: &AssignExpr) -> ExprResult;
    fn visit_logical(&mut self, l: &LogicalExpr) -> ExprResult;
    fn visit_call(&mut self, c: &CallExpr) -> ExprResult;
    fn visit_set(&mut self, s: &SetExpr) -> ExprResult;
    fn visit_get(&mut self, g: &GetExpr) -> ExprResult;
    fn visit_super(&mut self, s: &SuperExpr) -> ExprResult;
    fn visit_this(&mut self, t: &ThisExpr) -> ExprResult;

    fn visit_stmt(&mut self, s: &Stmt) -> StmtResult {
        use Stmt::*;
        match s {
            Expr(e) => {
                let expr_result = self.visit_expr(&e.expr);
                return self.expr_result_to_stmt_result(expr_result);
            }
            Print(e) => self.visit_print_stmt(&e.expr),
            Return(r) => self.visit_return_stmt(&r),
            Block(v) => self.visit_block(&v.stmts),
            Var(v) => self.visit_var_decl_stmt(v),
            If(i) => self.visit_if_stmt(i),
            While(i) => self.visit_while_stmt(i),
            Function(f) => self.visit_function_stmt(f),
            Class(c) => self.visit_class_stmt(c),
        }
    }

    fn visit_block(&mut self, v: &Vec<Box<Stmt>>) -> StmtResult;
    fn visit_print_stmt(&mut self, e: &Expr) -> StmtResult;
    fn visit_return_stmt(&mut self, r: &ReturnStmt) -> StmtResult;
    fn visit_var_decl_stmt(&mut self, v: &VarDecl) -> StmtResult;
    fn visit_if_stmt(&mut self, i: &IfStmt) -> StmtResult;
    fn visit_while_stmt(&mut self, w: &WhileStmt) -> StmtResult;
    fn visit_function_stmt(&mut self, f: &Rc<FunctionStmt>) -> StmtResult;
    fn visit_class_stmt(&mut self, c: &ClassStmt) -> StmtResult;
}

pub struct AstPrinter;
impl Visitor<String, String> for AstPrinter {
    fn expr_result_to_stmt_result(&self, e: String) -> String {
        e
    }

    fn visit_literal(&mut self, v: &LiteralExpr) -> String {
        match &v.value {
            LiteralValue::String(s) => s.to_string(),
            LiteralValue::Number(n) => n.to_string(),
            LiteralValue::Bool(b) => b.to_string(),
            LiteralValue::Nil => "nil".to_string(),
        }
    }

    fn visit_binary_expr(&mut self, b: &BinaryExpr) -> String {
        format!(
            "( {} {} {} )",
            self.visit_expr(&*b.left),
            b.operator,
            self.visit_expr(&*b.right)
        )
    }

    fn visit_grouping_expr(&mut self, e: &GroupingExpr) -> String {
        format!("group ( {} )", self.visit_expr(&e.expr))
    }

    fn visit_unary_expr(&mut self, u: &UnaryExpr) -> String {
        format!("( {} {} )", u.operator, self.visit_expr(&*u.right))
    }

    fn visit_variable(&mut self, v: &VariableExpr) -> String {
        format!("variable ( {} )", v.name)
    }

    fn visit_assign(&mut self, a: &AssignExpr) -> String {
        format!("assign {} = ( {} )", a.name, self.visit_expr(&a.value))
    }

    fn visit_logical(&mut self, l: &LogicalExpr) -> String {
        format!(
            "logic ( {} ) {} ( {} )",
            self.visit_expr(&l.left),
            l.operator,
            self.visit_expr(&l.right)
        )
    }
    fn visit_call(&mut self, c: &CallExpr) -> String {
        format!(
            "call ( {} ) ( {} )",
            self.visit_expr(&c.callee),
            c.args
                .iter()
                .map(|e| self.visit_expr(e))
                .collect::<Vec<_>>()
                .join(",")
        )
    }

    fn visit_set(&mut self, s: &SetExpr) -> String {
        format!(
            "set ( {} ) . ( {} ) to ( {} )",
            self.visit_expr(&s.object),
            &s.name,
            self.visit_expr(&s.value),
        )
    }

    fn visit_get(&mut self, g: &GetExpr) -> String {
        format!(
            "get ( {} ) from ( {} )",
            &g.name,
            self.visit_expr(&g.object)
        )
    }

    fn visit_super(&mut self, s: &SuperExpr) -> String {
        format!("super . ( {} )", &s.name)
    }

    fn visit_this(&mut self, _t: &ThisExpr) -> String {
        "this".to_string()
    }

    fn visit_block(&mut self, stmts: &Vec<Box<Stmt>>) -> String {
        stmts.iter().fold("block {\n".to_string(), |acc, stmt| {
            acc + &self.visit_stmt(stmt) + "\n"
        }) + "}\n"
    }
    fn visit_print_stmt(&mut self, e: &Expr) -> String {
        format!("{} ;", self.visit_expr(e))
    }
    fn visit_return_stmt(&mut self, r: &ReturnStmt) -> String {
        match &r.value {
            Some(e) => format!("return ( {} );", self.visit_expr(e)),
            None => format!("return;"),
        }
    }
    fn visit_var_decl_stmt(&mut self, v: &VarDecl) -> String {
        let mut s = format!("var {}", v.name).to_string();

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
    fn visit_function_stmt(&mut self, _f: &Rc<FunctionStmt>) -> String {
        format!("function ( <params> ) {{ <body> }} ").to_string()
    }
    fn visit_class_stmt(&mut self, c: &ClassStmt) -> String {
        format!(
            "class ( {} ) {{
                {}
            }}",
            c.name,
            c.methods
                .iter()
                .map(|method| self.visit_function_stmt(method))
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::visitor::*;

    #[test]
    fn print_binary_expr() {
        let expr = Expr::binary(
            Box::new(Expr::literal_number(5.0)),
            Operator::Plus,
            Box::new(Expr::literal_number(4.0)),
        );
        let mut printer = AstPrinter {};
        assert_eq!(printer.visit_expr(&expr), "( 5 + 4 )");
    }

    #[test]
    fn print_grouping_expr() {
        let expr = Expr::grouping(Box::new(Expr::literal_number(5.0)));
        let mut printer = AstPrinter {};
        assert_eq!(printer.visit_expr(&expr), "group ( 5 )");
    }

    #[test]
    fn print_literal() {
        let mut printer = AstPrinter {};
        assert_eq!(printer.visit_expr(&Expr::literal_number(1.0)), "1");
        assert_eq!(
            printer.visit_expr(&Expr::literal_string("hi".to_string())),
            "hi"
        );
    }

    #[test]
    fn print_unary() {
        let mut printer = AstPrinter {};
        assert_eq!(
            printer.visit_expr(&Expr::unary(
                Operator::Minus,
                Box::new(Expr::literal_number(5.0)),
            )),
            "( - 5 )"
        );
    }
}
