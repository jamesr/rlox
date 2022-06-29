use crate::scanner::{Token, TokenValue};

#[derive(PartialEq, Debug)]
pub enum Expr<'a> {
    Binary(BinaryExpr<'a>),
    Grouping(Box<Expr<'a>>),
    Literal(TokenValue<'a>),
    Unary(UnaryExpr<'a>),
    Variable(Token<'a>),
    Assign(AssignExpr<'a>),
    Logical(LogicalExpr<'a>),
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
pub struct LogicalExpr<'a> {
    pub left: Box<Expr<'a>>,
    pub operator: Token<'a>,
    pub right: Box<Expr<'a>>,
}

#[derive(PartialEq, Debug)]
pub enum Stmt<'a> {
    Expr(Box<Expr<'a>>),
    Print(Box<Expr<'a>>),
    Block(Vec<Box<Stmt<'a>>>),
    Var(VarDecl<'a>),
    If(IfStmt<'a>),
    While(WhileStmt<'a>),
}

#[derive(PartialEq, Debug)]
pub struct VarDecl<'a> {
    pub name: Token<'a>,
    pub initializer: Option<Box<Expr<'a>>>,
}

#[derive(PartialEq, Debug)]
pub struct IfStmt<'a> {
    pub condition: Box<Expr<'a>>,
    pub then_branch: Box<Stmt<'a>>,
    pub else_branch: Option<Box<Stmt<'a>>>,
}

#[derive(PartialEq, Debug)]
pub struct WhileStmt<'a> {
    pub condition: Box<Expr<'a>>,
    pub body: Box<Stmt<'a>>,
}
