use std::rc::Rc;

#[derive(PartialEq, Debug)]
pub enum Expr {
    Unary(UnaryExpr),
    Binary(BinaryExpr),
    Grouping(Box<Expr>),
    Literal(LiteralValue),
    Variable(String),
    Assign(AssignExpr),
    Logical(LogicalExpr),
    Call(CallExpr),
}

#[derive(PartialEq, Debug)]
pub enum Operator {
    Minus,
    Plus,
    Slash,
    Star,
    Bang,
    BangEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,
    And,
    Or,
}

#[derive(PartialEq, Debug)]
pub struct UnaryExpr {
    pub operator: Operator,
    pub right: Box<Expr>,
}

#[derive(PartialEq, Debug)]
pub struct BinaryExpr {
    pub left: Box<Expr>,
    pub operator: Operator,
    pub right: Box<Expr>,
}

#[derive(PartialEq, Debug)]
pub enum LiteralValue {
    String(String),
    Number(f64),
    Bool(bool),
    Nil,
}

#[derive(PartialEq, Debug)]
pub struct AssignExpr {
    pub name: String,
    pub value: Box<Expr>,
}

#[derive(PartialEq, Debug)]
pub struct LogicalExpr {
    pub left: Box<Expr>,
    pub operator: Operator,
    pub right: Box<Expr>,
}

#[derive(PartialEq, Debug)]
pub struct CallExpr {
    pub callee: Box<Expr>,
    pub args: Vec<Box<Expr>>,
    // TODO: Track source location for error reporting
}

#[derive(PartialEq, Debug)]
pub enum Stmt {
    Expr(Box<Expr>),
    Print(Box<Expr>),
    Return(Option<Box<Expr>>),
    Block(Vec<Box<Stmt>>),
    Var(VarDecl),
    If(IfStmt),
    While(WhileStmt),
    Function(Rc<FunctionStmt>),
}

#[derive(PartialEq, Debug)]
pub struct VarDecl {
    pub name: String,
    pub initializer: Option<Box<Expr>>,
}

#[derive(PartialEq, Debug)]
pub struct IfStmt {
    pub condition: Box<Expr>,
    pub then_branch: Box<Stmt>,
    pub else_branch: Option<Box<Stmt>>,
}

#[derive(PartialEq, Debug)]
pub struct WhileStmt {
    pub condition: Box<Expr>,
    pub body: Box<Stmt>,
}

#[derive(PartialEq, Debug)]
pub struct FunctionStmt {
    pub name: String,
    pub params: Vec<String>,
    pub body: Vec<Box<Stmt>>,
}

impl std::fmt::Display for Operator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                Operator::Minus => "-",
                Operator::Plus => "+",
                Operator::Slash => "/",
                Operator::Star => "*",
                Operator::Bang => "!",
                Operator::BangEqual => "!=",
                Operator::Equal => "=",
                Operator::EqualEqual => "==",
                Operator::Greater => ">",
                Operator::GreaterEqual => ">=",
                Operator::Less => "<",
                Operator::LessEqual => "<=",
                Operator::And => "and",
                Operator::Or => "or",
            }
        )
    }
}
