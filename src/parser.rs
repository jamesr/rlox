use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::ast::FunctionStmt;
use crate::scanner::{Scanner, Token, TokenType, TokenValue};
use crate::{ast, error};

pub type LocationTable = HashMap<u64, error::Location>;

struct ParserState<'a> {
    scanner: Scanner<'a>,
    current: Option<Token<'a>>,
    prev: Option<Token<'a>>,
    errors: Vec<error::ParseError>,
    loc: LocationTable,
}
pub struct Parser<'a> {
    state: RefCell<ParserState<'a>>,
}

type ExprResult = Result<Box<ast::Expr>, error::ParseError>;
type StmtResult = Result<Box<ast::Stmt>, error::ParseError>;
type StmtsResult = Result<Vec<Box<ast::Stmt>>, error::ParseError>;
type ParseResult = Result<Vec<Box<ast::Stmt>>, Vec<error::ParseError>>;

macro_rules! make_ast_node {
    ($name:ident, $ast_type:ident, $expr_type:ident, $($param:ident: $param_type:ty),*) => {
        fn $name(&self, $($param: $param_type),*) -> Box<ast::$ast_type> {
            let ast_node = Box::new(ast::$ast_type::$expr_type($($param),*));
            let ast_node_loc = self.state.borrow().scanner.loc();
            self.state.borrow_mut().loc.insert(ast_node.id(), ast_node_loc);
            ast_node
        }

    };
}

macro_rules! make_expr {
    ($name:ident, $expr_type:ident, $($param:ident: $param_type:ty),*) => {
        make_ast_node!($name, Expr, $expr_type, $($param: $param_type),*);
    };
}

macro_rules! make_stmt {
    ($name:ident, $stmt_type:ident, $($param:ident: $param_type:ty),*) => {
        make_ast_node!($name, Stmt, $stmt_type, $($param: $param_type),*);
    };
}

impl<'a> Parser<'a> {
    pub fn new(scanner: Scanner<'a>) -> Parser<'a> {
        Parser {
            state: RefCell::new(ParserState {
                scanner,
                current: None,
                prev: None,
                errors: vec![],
                loc: LocationTable::new(),
            }),
        }
    }

    pub fn parse_expression(&mut self) -> ExprResult {
        self.prime()?;

        self.expression()
    }

    pub fn parse(&mut self) -> ParseResult {
        if let Err(e) = self.prime() {
            return Err(vec![e]);
        }

        let stmts = match self.program() {
            Ok(s) => s,
            Err(e) => return Err(vec![e]),
        };

        let errors = std::mem::take(&mut self.state.borrow_mut().errors);
        if !errors.is_empty() {
            return Err(errors);
        }
        Ok(stmts)
    }

    pub fn take_location_table(&mut self) -> LocationTable {
        std::mem::take(&mut self.state.borrow_mut().loc)
    }

    fn operator(&self) -> Result<ast::Operator, error::ParseError> {
        let token = self.previous().unwrap();
        match token.token_type {
            TokenType::Minus => Ok(ast::Operator::Minus),
            TokenType::Plus => Ok(ast::Operator::Plus),
            TokenType::Slash => Ok(ast::Operator::Slash),
            TokenType::Star => Ok(ast::Operator::Star),
            TokenType::Bang => Ok(ast::Operator::Bang),
            TokenType::BangEqual => Ok(ast::Operator::BangEqual),
            TokenType::Equal => Ok(ast::Operator::Equal),
            TokenType::EqualEqual => Ok(ast::Operator::EqualEqual),
            TokenType::Greater => Ok(ast::Operator::Greater),
            TokenType::GreaterEqual => Ok(ast::Operator::GreaterEqual),
            TokenType::Less => Ok(ast::Operator::Less),
            TokenType::LessEqual => Ok(ast::Operator::LessEqual),
            TokenType::And => Ok(ast::Operator::And),
            TokenType::Or => Ok(ast::Operator::Or),
            _ => Err(self.error(&format!("Expected operator found '{}'.", token.lexeme))),
        }
    }

    // program → declaration* EOF ;
    fn program(&self) -> StmtsResult {
        let mut statements = Vec::new();

        while !self.at_end() {
            statements.push(self.declaration()?);
        }

        Ok(statements)
    }

    // declaration → classDecl | funDecl | varDecl | statement ;
    fn declaration(&self) -> StmtResult {
        match (|| {
            if self.matches(&[TokenType::Class])? {
                return self.class_decl();
            }
            if self.matches(&[TokenType::Fun])? {
                return self.fun_decl("function");
            }

            if self.matches(&[TokenType::Var])? {
                return self.var_decl();
            }

            self.statement()
        })() {
            Ok(s) => Ok(s),
            Err(e) => {
                self.synchronize();
                Err(e)
            }
        }
    }

    make_expr!(
        make_unary_expr,
        unary,
        operator: ast::Operator,
        right: Box<ast::Expr>
    );
    make_expr!(
        make_binary_expr,
        binary,
        left: Box<ast::Expr>,
        operator: ast::Operator,
        right: Box<ast::Expr>
    );
    make_expr!(make_grouping_expr, grouping, expr: Box<ast::Expr>);
    make_expr!(make_literal_string_expr, literal_string, s: String);
    make_expr!(make_literal_number_expr, literal_number, n: f64);
    make_expr!(make_literal_bool_expr, literal_bool, b: bool);
    make_expr!(make_literal_nil_expr, literal_nil,);
    make_expr!(make_variable_expr, variable, name: String);
    make_expr!(
        make_assign_expr,
        assign,
        name: String,
        value: Box<ast::Expr>
    );
    make_expr!(
        make_logical_expr,
        logical,
        left: Box<ast::Expr>,
        operator: ast::Operator,
        right: Box<ast::Expr>
    );
    make_expr!(
        make_call_expr,
        call,
        callee: Box<ast::Expr>,
        args: Vec<Box<ast::Expr>>
    );
    make_expr!(
        make_set_expr,
        set,
        object: Box<ast::Expr>,
        name: String,
        value: Box<ast::Expr>
    );
    make_expr!(make_super_expr, super_expr, name: String);
    make_expr!(make_this_expr, this,);
    make_expr!(make_get_expr, get, object: Box<ast::Expr>, name: String);

    make_stmt!(make_expr_stmt, expr, expr: Box<ast::Expr>);
    make_stmt!(make_print_stmt, print, expr: Box<ast::Expr>);
    make_stmt!(make_return_stmt, return_stmt, value: Option<Box<ast::Expr>>);
    make_stmt!(make_block_stmt, block, stmts: Vec<Box<ast::Stmt>>);
    make_stmt!(
        make_var_stmt,
        var,
        name: String,
        initializer: Option<Box<ast::Expr>>
    );
    make_stmt!(
        make_if_stmt,
        if_stmt,
        condition: Box<ast::Expr>,
        then_branch: Box<ast::Stmt>,
        else_branch: Option<Box<ast::Stmt>>
    );
    make_stmt!(
        make_while_stmt,
        while_stmt,
        condition: Box<ast::Expr>,
        body: Box<ast::Stmt>
    );
    fn make_function_stmt(&self, function: Rc<ast::FunctionStmt>) -> Box<ast::Stmt> {
        let ast_node_loc = self.state.borrow().scanner.loc();
        self.state
            .borrow_mut()
            .loc
            .insert(function.id(), ast_node_loc);
        Box::new(ast::Stmt::Function(function))
    }
    make_stmt!(
        make_class_stmt,
        class,
        name: String,
        superclass: Option<Box<ast::Expr>>,
        methods: Vec<Rc<FunctionStmt>>
    );

    //  classDecl → "class" IDENTIFIER ( "<" IDENTIFIER )? "{" function* "}" ;
    fn class_decl(&self) -> StmtResult {
        self.consume(TokenType::Identifier, "Expect class name.")?;
        let name = self.previous().unwrap().lexeme.to_string();

        let superclass = if self.matches(&[TokenType::Less])? {
            self.consume(TokenType::Identifier, "Expect superclass name.")?;
            Some(self.make_variable_expr(self.previous().unwrap().lexeme.to_string()))
        } else {
            None
        };

        self.consume(TokenType::LeftBrace, "Expect '{' before class body.")?;

        let mut methods = vec![];
        while !self.check(TokenType::RightBrace) && !self.at_end() {
            methods.push(self.function("method")?);
        }

        self.consume(TokenType::RightBrace, "Expect '}' after class body.")?;

        Ok(self.make_class_stmt(name, superclass, methods))
    }

    // funDecl → "fun" function ;
    fn fun_decl(&self, kind: &str) -> StmtResult {
        Ok(self.make_function_stmt(self.function(kind)?))
    }

    // function → IDENTIFIER "(" parameters? ")" block ;
    // parameters → IDENTIFIER ( "," IDENTIFIER )* ;
    fn function(&self, kind: &str) -> Result<Rc<FunctionStmt>, error::ParseError> {
        self.consume(TokenType::Identifier, &format!("Expect {} name.", kind))?;
        let name = self.previous().unwrap().lexeme.to_string();
        self.consume(
            TokenType::LeftParen,
            &format!("Expect '(' after {} name.", kind),
        )?;

        let mut params = vec![];
        if !self.check(TokenType::RightParen) {
            loop {
                if params.len() >= 255 {
                    return Err(self.error("Can't have more than 255 parameters."));
                }

                self.consume(TokenType::Identifier, "Expect parameter name.")?;
                params.push(self.previous().unwrap().lexeme.to_string());

                if !self.matches(&[TokenType::Comma])? {
                    break;
                }
            }
        }
        self.consume(TokenType::RightParen, "Expect ')' after parameters.")?;

        self.consume(
            TokenType::LeftBrace,
            &format!("Expect '{{' before {} body.", kind),
        )?;

        let body = self.block()?;

        Ok(Rc::new(ast::Stmt::function(name, params, body)))
    }

    // varDecl → "var" IDENTIFIER ( "=" expression )? ";" ;
    fn var_decl(&self) -> StmtResult {
        self.consume(TokenType::Identifier, "Expect variable name.")?;
        let name = self.previous().unwrap().lexeme.to_string();

        let initializer = if self.matches(&[TokenType::Equal])? {
            Some(self.expression()?)
        } else {
            None
        };

        self.consume(
            TokenType::Semicolon,
            "Expect ';' after variable declaration.",
        )?;
        Ok(self.make_var_stmt(name, initializer))
    }

    fn prime(&self) -> Result<(), error::ParseError> {
        let first = self.state.borrow_mut().scanner.next();
        if first.is_some() {
            self.state.borrow_mut().current = Some(first.unwrap()?);
        }
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

    fn error(&self, message: &str) -> error::ParseError {
        let peeked = match self.peek() {
            Some(token) => format!("'{}'", token.lexeme),
            None => "end".to_string(),
        };
        self.error_at(message, &peeked)
    }

    fn error_at(&self, message: &str, peeked: &str) -> error::ParseError {
        self.state
            .borrow()
            .scanner
            .error(&format!("Error at {}: {}", peeked, message))
    }

    fn add_error(&self, e: error::ParseError) {
        self.state.borrow_mut().errors.push(e);
    }

    fn advance(&self) -> Result<(), error::ParseError> {
        let mut current = self.state.borrow_mut().current.take();
        self.state.borrow_mut().prev = current.take();
        let mut new_current = match self.state.borrow_mut().scanner.next() {
            None => None,
            Some(result) => Some(result?),
        };
        self.state.borrow_mut().current = new_current.take();
        Ok(())
    }

    fn matches(&self, types: &[TokenType]) -> Result<bool, error::ParseError> {
        for token_type in types {
            if self.check(*token_type) {
                self.advance()?;
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn consume(&self, token_type: TokenType, message: &str) -> Result<(), error::ParseError> {
        if self.check(token_type) {
            return self.advance();
        }
        Err(self.error(message))
    }

    fn synchronize(&self) {
        if let Err(e) = self.advance() {
            self.add_error(e);
        }

        while !self.at_end() {
            if self.previous().is_none()
                || self.previous().unwrap().token_type == TokenType::Semicolon
            {
                return;
            }

            match self.peek().unwrap().token_type {
                // Look for a statement-like token.
                TokenType::Class
                | TokenType::Fun
                | TokenType::Var
                | TokenType::For
                | TokenType::If
                | TokenType::While
                | TokenType::Print
                | TokenType::Return => {
                    return;
                }
                _ => {
                    if let Err(e) = self.advance() {
                        self.add_error(e);
                    }
                }
            }
        }
    }

    // expression → assignment ;
    fn expression(&self) -> ExprResult {
        self.assignment()
    }

    // assignment → ( call "." )? IDENTIFIER "=" assignment
    //              | logic_or ;
    fn assignment(&self) -> ExprResult {
        let expr = self.logic_or()?;

        if self.matches(&[TokenType::Equal])? {
            let value = self.assignment()?;

            match *expr {
                ast::Expr::Variable(v) => {
                    return Ok(self.make_assign_expr(v.name, value));
                }
                ast::Expr::Get(g) => {
                    return Ok(self.make_set_expr(g.object, g.name, value));
                }
                _ => return Err(self.error_at("Invalid assignment target.", "'='")),
            }
        }

        Ok(expr)
    }

    // logic_or       → logic_and ( "or" logic_and )* ;
    fn logic_or(&self) -> ExprResult {
        let mut expr = self.logic_and()?;

        while self.matches(&[TokenType::Or])? {
            let operator = self.operator()?;
            let right = self.logic_and()?;
            expr = self.make_logical_expr(expr, operator, right);
        }

        Ok(expr)
    }
    // logic_and      → equality ( "and" equality )* ;
    fn logic_and(&self) -> ExprResult {
        let mut expr = self.equality()?;

        while self.matches(&[TokenType::And])? {
            let operator = self.operator()?;
            let right = self.equality()?;
            expr = self.make_logical_expr(expr, operator, right);
        }

        Ok(expr)
    }

    // equality → comparison ( ( "!=" | "==" ) comparison )* ;
    fn equality(&self) -> ExprResult {
        let mut expr = self.comparison()?;

        while self.matches(&[TokenType::BangEqual, TokenType::EqualEqual])? {
            let operator = self.operator()?;
            let right = self.comparison()?;
            expr = self.make_binary_expr(expr, operator, right);
        }

        Ok(expr)
    }

    // comparison → term ( ( ">" | ">=" | "<" | "<=" ) term )* ;
    fn comparison(&self) -> ExprResult {
        let mut expr = self.term()?;

        while self.matches(&[
            TokenType::Greater,
            TokenType::GreaterEqual,
            TokenType::Less,
            TokenType::LessEqual,
        ])? {
            let operator = self.operator()?;
            let right = self.term()?;
            expr = self.make_binary_expr(expr, operator, right);
        }

        Ok(expr)
    }

    // term → factor ( ( "-" | "+" ) factor )* ;
    fn term(&self) -> ExprResult {
        let mut expr = self.factor()?;

        while self.matches(&[TokenType::Minus, TokenType::Plus])? {
            let operator = self.operator()?;
            let right = self.factor()?;
            expr = self.make_binary_expr(expr, operator, right);
        }

        Ok(expr)
    }

    // factor → unary ( ( "/" | "*" ) unary )* ;
    fn factor(&self) -> ExprResult {
        let mut expr = self.unary()?;

        while self.matches(&[TokenType::Slash, TokenType::Star])? {
            let operator = self.operator()?;
            let right = self.unary()?;
            expr = self.make_binary_expr(expr, operator, right);
        }

        Ok(expr)
    }

    // unary → ( "!" | "-" ) unary | call ;
    fn unary(&self) -> ExprResult {
        if self.matches(&[TokenType::Bang, TokenType::Minus])? {
            let operator = self.operator()?;
            let right = self.unary()?;
            return Ok(self.make_unary_expr(operator, right));
        }
        self.call()
    }

    // call → primary ( "(" arguments? ")" | "." IDENTIFIER )* ;
    fn call(&self) -> ExprResult {
        let mut expr = self.primary()?;

        loop {
            if self.matches(&[TokenType::LeftParen])? {
                expr = self.finish_call(expr)?;
            } else if self.matches(&[TokenType::Dot])? {
                self.consume(TokenType::Identifier, "Expect property name after '.'.")?;
                let name = self.previous().unwrap().lexeme.to_string();
                expr = self.make_get_expr(expr, name);
            } else {
                break;
            }
        }

        Ok(expr)
    }

    // arguments → expression ( "," expression )* ;
    fn finish_call(&self, callee: Box<ast::Expr>) -> ExprResult {
        let mut args = vec![];

        if !self.check(TokenType::RightParen) {
            loop {
                if args.len() >= 255 {
                    self.add_error(self.error("Can't have more than 255 arguments."));
                }
                args.push(self.expression()?);
                if !self.matches(&[TokenType::Comma])? {
                    break;
                }
            }
        }

        self.consume(TokenType::RightParen, "Expect ')' after arguments.")?;

        Ok(self.make_call_expr(callee, args))
    }

    // primary  → "true" | "false" | "nil" | "this"
    //          | NUMBER | STRING
    //          | IDENTIFIER
    //          | "(" expression ")"
    //          | "super" "." IDENTIFIER ;
    fn primary(&self) -> ExprResult {
        if self.matches(&[TokenType::True])? {
            return Ok(self.make_literal_bool_expr(true));
        }
        if self.matches(&[TokenType::False])? {
            return Ok(self.make_literal_bool_expr(false));
        }
        if self.matches(&[TokenType::Nil])? {
            return Ok(self.make_literal_nil_expr());
        }
        if self.matches(&[TokenType::This])? {
            return Ok(self.make_this_expr());
        }
        if self.matches(&[TokenType::Number])? {
            if let TokenValue::Number(n) = self.previous().unwrap().value.unwrap() {
                return Ok(self.make_literal_number_expr(n));
            }
        }
        if self.matches(&[TokenType::String])? {
            if let TokenValue::String(s) = self.previous().unwrap().value.unwrap() {
                return Ok(self.make_literal_string_expr(s.to_string()));
            }
        }
        if self.matches(&[TokenType::Identifier])? {
            let token = self.previous().unwrap();
            return Ok(self.make_variable_expr(token.lexeme.to_string()));
        }
        if self.matches(&[TokenType::LeftParen])? {
            let expr = self.expression()?;
            self.consume(TokenType::RightParen, "Expect ')' after expression.")?;
            return Ok(self.make_grouping_expr(expr));
        }
        if self.matches(&[TokenType::Super])? {
            self.consume(TokenType::Dot, "Expect '.' after 'super'.")?;
            self.consume(TokenType::Identifier, "Expect superclass method name.")?;
            let method = self.previous().unwrap().lexeme.to_string();
            return Ok(self.make_super_expr(method));
        }
        Err(self.error("Expect expression."))
    }

    // statement → exprStmt
    //           | forStmt
    //           | ifStmt
    //           | printStmt
    //           | returnStmt
    //           | whileStmt
    //           | block ;
    fn statement(&self) -> StmtResult {
        if self.matches(&[TokenType::For])? {
            return self.for_stmt();
        }
        if self.matches(&[TokenType::If])? {
            return self.if_stmt();
        }
        if self.matches(&[TokenType::Print])? {
            return self.print_stmt();
        }
        if self.matches(&[TokenType::Return])? {
            return self.return_stmt();
        }
        if self.matches(&[TokenType::While])? {
            return self.while_stmt();
        }
        if self.matches(&[TokenType::LeftBrace])? {
            return Ok(self.make_block_stmt(self.block()?));
        }

        self.expr_stmt()
    }

    // block → "{" declaration* "}" ;
    fn block(&self) -> StmtsResult {
        let mut stmts = Vec::new();

        while !self.check(TokenType::RightBrace) && !self.at_end() {
            stmts.push(self.declaration()?);
        }

        self.consume(TokenType::RightBrace, "Expect ';' after block.")?;

        Ok(stmts)
    }

    // exprStmt → expression ";" ;
    fn expr_stmt(&self) -> StmtResult {
        let expr = self.expression()?;
        self.consume(TokenType::Semicolon, "Expect ';' after value.")?;
        Ok(self.make_expr_stmt(expr))
    }

    // printStmt → "print" expression ";"
    fn print_stmt(&self) -> StmtResult {
        let expr = self.expression()?;
        self.consume(TokenType::Semicolon, "Expect ';' after value.")?;
        Ok(self.make_print_stmt(expr))
    }

    // returnStmt → "return" expression? ";" ;
    fn return_stmt(&self) -> StmtResult {
        let value = if self.check(TokenType::Semicolon) {
            None
        } else {
            Some(self.expression()?)
        };

        self.consume(TokenType::Semicolon, "Expect ';' after return value.")?;
        Ok(self.make_return_stmt(value))
    }

    // ifStmt → "if" "(" expression ")" statement
    //          ( "else" statement )? ;
    fn if_stmt(&self) -> StmtResult {
        self.consume(TokenType::LeftParen, "Expect '(' after 'if'.")?;
        let condition = self.expression()?;
        self.consume(TokenType::RightParen, "Expect ')' after if condition.")?;

        let then_branch = self.statement()?;
        let else_branch = if self.matches(&[TokenType::Else])? {
            Some(self.statement()?)
        } else {
            None
        };

        Ok(self.make_if_stmt(condition, then_branch, else_branch))
    }

    // whileStmt → "while" "(" expression ")" statement ;
    fn while_stmt(&self) -> StmtResult {
        self.consume(TokenType::LeftParen, "Expect '(' after 'while'.")?;

        let condition = self.expression()?;

        self.consume(TokenType::RightParen, "Expect '(' after 'while'.")?;

        let body = self.statement()?;

        Ok(self.make_while_stmt(condition, body))
    }

    // forStmt → "for" "(" ( varDecl | exprStmt | ";" )
    //           expression? ";"
    //           expression? ")" statement ;
    fn for_stmt(&self) -> StmtResult {
        self.consume(TokenType::LeftParen, "Expect '(' after 'for'.")?;

        let initializer = if self.matches(&[TokenType::Semicolon])? {
            None
        } else if self.matches(&[TokenType::Var])? {
            Some(self.var_decl()?)
        } else {
            Some(self.expr_stmt()?)
        };

        let condition = if self.check(TokenType::Semicolon) {
            self.make_literal_bool_expr(true)
        } else {
            self.expression()?
        };
        self.consume(TokenType::Semicolon, "Expect ';' after loop condition.")?;

        let increment = if self.check(TokenType::RightParen) {
            None
        } else {
            Some(self.expression()?)
        };
        self.consume(TokenType::RightParen, "Expect ')' after for clauses.")?;

        let body = self.statement()?;

        // for (initializer; condition; increment) {
        //  body ;
        // }
        // desugar to:
        // {
        //    initializer;
        //    while ( condition ) {
        //      body ;
        //      increment ;
        //    }
        // }

        let mut outer_block_stmts = vec![];
        if let Some(init_stmt) = initializer {
            outer_block_stmts.push(init_stmt);
        }

        let mut while_block_stmts = vec![body];
        if let Some(increment_expr) = increment {
            while_block_stmts.push(self.make_expr_stmt(increment_expr));
        }

        outer_block_stmts
            .push(self.make_while_stmt(condition, self.make_block_stmt(while_block_stmts)));

        Ok(self.make_block_stmt(outer_block_stmts))
    }
}

pub fn parse<'a>(source: &'a str) -> ParseResult {
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
    use std::rc::Rc;

    use crate::ast::{self, *};
    use crate::error;
    use crate::parser::{parse, parse_expression};

    #[test]
    fn comparison() -> Result<(), error::ParseError> {
        let expr = parse_expression("0 == 2")?;
        assert!(matches!(*expr, ast::Expr::Binary { .. }));
        if let ast::Expr::Binary(b) = *expr {
            assert!(matches!(*b.left, ast::Expr::Literal { .. }));
        }
        Ok(())
    }

    #[test]
    fn literal() -> Result<(), error::ParseError> {
        let false_literal = parse_expression("false")?;
        assert_eq!(*false_literal, ast::Expr::literal_bool(false));

        let true_literal = parse_expression("true")?;
        assert_eq!(*true_literal, ast::Expr::literal_bool(true));

        Ok(())
    }

    #[test]
    fn unary() -> Result<(), error::ParseError> {
        let unary_minus = parse_expression("- 5")?;
        assert_eq!(
            *unary_minus,
            ast::Expr::unary(Operator::Minus, Box::new(ast::Expr::literal_number(5.0)),)
        );

        let unary_negate = parse_expression("!false")?;
        assert_eq!(
            *unary_negate,
            ast::Expr::unary(Operator::Bang, Box::new(ast::Expr::literal_bool(false)),)
        );
        Ok(())
    }

    #[test]
    fn assignment() -> Result<(), error::ParseError> {
        let assign_simple = parse_expression("foo = 3")?;

        assert_eq!(
            *assign_simple,
            ast::Expr::assign("foo".to_string(), Box::new(ast::Expr::literal_number(3.0)),)
        );

        Ok(())
    }

    #[test]
    fn block() -> Result<(), Vec<error::ParseError>> {
        let block = parse("{ 5; }")?;

        assert_eq!(
            block[0],
            Box::new(ast::Stmt::block(vec![Box::new(ast::Stmt::expr(Box::new(
                ast::Expr::literal_number(5.0)
            )))]))
        );

        Ok(())
    }

    #[test]
    fn if_statement() -> Result<(), Vec<error::ParseError>> {
        let if_statement = parse("if ( true ) { print 5; }")?;

        assert_eq!(
            if_statement[0],
            Box::new(ast::Stmt::if_stmt(
                Box::new(ast::Expr::literal_bool(true)),
                Box::new(ast::Stmt::block(vec![Box::new(ast::Stmt::print(
                    Box::new(ast::Expr::literal_number(5.0))
                ))])),
                None,
            ))
        );

        Ok(())
    }

    #[test]
    fn multiple_statements() -> Result<(), Vec<error::ParseError>> {
        let stmts = parse(
            r#"var all_tests_passed;
           if (true) {
               all_tests_passed = true;
           }"#,
        )?;

        assert_eq!(
            stmts[0],
            Box::new(ast::Stmt::var("all_tests_passed".to_string(), None,))
        );

        assert_eq!(
            stmts[1],
            Box::new(ast::Stmt::if_stmt(
                Box::new(ast::Expr::literal_bool(true)),
                Box::new(ast::Stmt::block(vec![Box::new(ast::Stmt::expr(Box::new(
                    ast::Expr::assign(
                        "all_tests_passed".to_string(),
                        Box::new(ast::Expr::literal_bool(true))
                    )
                )))])),
                None,
            ))
        );

        assert_eq!(stmts.len(), 2);

        Ok(())
    }

    #[test]
    fn logical_or() -> Result<(), Vec<error::ParseError>> {
        let stmts = parse("false and true;")?;

        assert_eq!(
            stmts[0],
            Box::new(ast::Stmt::expr(Box::new(ast::Expr::logical(
                Box::new(ast::Expr::literal_bool(false)),
                Operator::And,
                Box::new(ast::Expr::literal_bool(true)),
            ))))
        );

        assert_eq!(stmts.len(), 1);

        Ok(())
    }

    #[test]
    fn while_loop() -> Result<(), Vec<error::ParseError>> {
        let stmts = parse("while (i < 5) i = i + 1;")?;

        assert_eq!(
            stmts[0],
            Box::new(ast::Stmt::while_stmt(
                Box::new(ast::Expr::binary(
                    Box::new(ast::Expr::variable("i".to_string())),
                    Operator::Less,
                    Box::new(ast::Expr::literal_number(5.0))
                )),
                Box::new(ast::Stmt::expr(Box::new(ast::Expr::assign(
                    "i".to_string(),
                    Box::new(ast::Expr::binary(
                        Box::new(ast::Expr::variable("i".to_string())),
                        Operator::Plus,
                        Box::new(ast::Expr::literal_number(1.0))
                    ))
                ))))
            ))
        );

        assert_eq!(stmts.len(), 1);

        Ok(())
    }

    #[test]
    fn for_loop() -> Result<(), Vec<error::ParseError>> {
        //   for (var i = 0; i < 10; i = i + 1) print i;
        // Desugars to:
        //   {
        //     var i = 0;
        //     while (i < 10) {
        //       print i;
        //       i = i + 1;
        //     }
        //   }
        let stmts = parse("for (var i = 0; i < 10; i = i + 1) print i;")?;

        assert_eq!(
            stmts,
            vec![Box::new(ast::Stmt::block(vec![
                // "var i = 0;"
                Box::new(ast::Stmt::var(
                    "i".to_string(),
                    Some(Box::new(ast::Expr::literal_number(0.0)))
                )),
                // "while (i < 10) {"
                Box::new(ast::Stmt::while_stmt(
                    Box::new(ast::Expr::binary(
                        Box::new(ast::Expr::variable("i".to_string())),
                        Operator::Less,
                        Box::new(ast::Expr::literal_number(10.0)),
                    )),
                    Box::new(ast::Stmt::block(vec![
                        // "print i;"
                        Box::new(ast::Stmt::print(Box::new(ast::Expr::variable(
                            "i".to_string()
                        )))),
                        // "i = i + 1;"
                        Box::new(ast::Stmt::expr(Box::new(ast::Expr::assign(
                            "i".to_string(),
                            Box::new(ast::Expr::binary(
                                Box::new(ast::Expr::variable("i".to_string())),
                                Operator::Plus,
                                Box::new(ast::Expr::literal_number(1.0)),
                            ))
                        ))))
                    ])),
                ))
            ]))]
        );

        Ok(())
    }

    #[test]
    fn call_expression() -> Result<(), error::Error> {
        let expr = parse_expression("callback(5, true)")?;

        assert_eq!(
            expr,
            Box::new(ast::Expr::call(
                Box::new(ast::Expr::variable("callback".to_string())),
                vec![
                    Box::new(ast::Expr::literal_number(5.0)),
                    Box::new(ast::Expr::literal_bool(true)),
                ],
            ))
        );

        Ok(())
    }

    #[test]
    fn multiple_call_statement() -> Result<(), error::ParseError> {
        let stmts = parse("getCallback()();").map_err(|v| v.first().unwrap().clone())?;

        assert_eq!(
            stmts,
            vec![Box::new(ast::Stmt::expr(Box::new(ast::Expr::call(
                Box::new(ast::Expr::call(
                    Box::new(ast::Expr::variable("getCallback".to_string())),
                    vec![],
                )),
                vec![]
            ))))]
        );

        Ok(())
    }

    #[test]
    fn function_definition() -> Result<(), Vec<error::ParseError>> {
        let source = "fun add(a, b) { print a + b; }";
        let stmts = parse(source)?;

        assert_eq!(
            stmts,
            vec![Box::new(ast::Stmt::Function(Rc::new(ast::Stmt::function(
                "add".to_string(),
                vec!["a".to_string(), "b".to_string(),],
                vec![Box::new(ast::Stmt::print(Box::new(ast::Expr::binary(
                    Box::new(ast::Expr::variable("a".to_string())),
                    Operator::Plus,
                    Box::new(ast::Expr::variable("b".to_string()))
                ))))],
            ))))]
        );

        Ok(())
    }

    #[test]
    fn class_definition() -> Result<(), Vec<error::ParseError>> {
        let source = r#"class Breakfast {
            cook() {
              print "Eggs a-fryin'!";
            }
          
            serve(who) {
              print "Enjoy your breakfast, " + who + ".";
            }
          }"#;
        let stmts = parse(source)?;
        assert_eq!(
            stmts,
            vec![Box::new(ast::Stmt::class(
                "Breakfast".to_string(),
                None,
                vec![
                    Rc::new(ast::Stmt::function(
                        "cook".to_string(),
                        vec![],
                        vec![Box::new(ast::Stmt::print(Box::new(
                            ast::Expr::literal_string("Eggs a-fryin'!".to_string())
                        )))]
                    )),
                    Rc::new(ast::Stmt::function(
                        "serve".to_string(),
                        vec!["who".to_string()],
                        vec![Box::new(ast::Stmt::print(Box::new(ast::Expr::binary(
                            Box::new(ast::Expr::binary(
                                Box::new(ast::Expr::literal_string(
                                    "Enjoy your breakfast, ".to_string()
                                )),
                                Operator::Plus,
                                Box::new(ast::Expr::variable("who".to_string())),
                            )),
                            Operator::Plus,
                            Box::new(ast::Expr::literal_string(".".to_string()))
                        ))))]
                    )),
                ],
            ))]
        );

        Ok(())
    }

    #[test]
    fn class_with_superclass() -> Result<(), Vec<error::ParseError>> {
        let source = r#"class Breakfast < Meal {
            cook() {}
        }"#;

        let stmts = parse(source)?;
        assert_eq!(
            stmts,
            vec![Box::new(ast::Stmt::class(
                "Breakfast".to_string(),
                Some(Box::new(ast::Expr::variable("Meal".to_string()),)),
                vec![Rc::new(ast::Stmt::function(
                    "cook".to_string(),
                    vec![],
                    vec![]
                ))],
            ))]
        );

        Ok(())
    }
}
