use std::{rc::Rc, sync::Mutex};

#[derive(PartialEq, Debug)]
pub enum Expr {
    Unary(UnaryExpr),
    Binary(BinaryExpr),
    Grouping(GroupingExpr),
    Literal(LiteralExpr),
    Variable(VariableExpr),
    Assign(AssignExpr),
    Logical(LogicalExpr),
    Call(CallExpr),
}

impl Expr {
    pub fn unary(operator: Operator, right: Box<Expr>) -> Expr {
        Expr::Unary(UnaryExpr {
            id: generate_expr_id(),
            operator,
            right,
        })
    }

    pub fn binary(left: Box<Expr>, operator: Operator, right: Box<Expr>) -> Expr {
        Expr::Binary(BinaryExpr {
            id: generate_expr_id(),
            left,
            operator,
            right,
        })
    }

    pub fn grouping(expr: Box<Expr>) -> Expr {
        Expr::Grouping(GroupingExpr {
            id: generate_expr_id(),
            expr,
        })
    }

    pub fn literal_string(s: String) -> Expr {
        Expr::Literal(LiteralExpr {
            id: generate_expr_id(),
            value: LiteralValue::String(s),
        })
    }

    pub fn literal_number(n: f64) -> Expr {
        Expr::Literal(LiteralExpr {
            id: generate_expr_id(),
            value: LiteralValue::Number(n),
        })
    }

    pub fn literal_bool(b: bool) -> Expr {
        Expr::Literal(LiteralExpr {
            id: generate_expr_id(),
            value: LiteralValue::Bool(b),
        })
    }

    pub fn literal_nil() -> Expr {
        Expr::Literal(LiteralExpr {
            id: generate_expr_id(),
            value: LiteralValue::Nil,
        })
    }

    pub fn variable(name: String) -> Expr {
        Expr::Variable(VariableExpr {
            id: generate_expr_id(),
            name,
        })
    }

    pub fn assign(name: String, value: Box<Expr>) -> Expr {
        Expr::Assign(AssignExpr {
            id: generate_expr_id(),
            name,
            value,
        })
    }

    pub fn logical(left: Box<Expr>, operator: Operator, right: Box<Expr>) -> Expr {
        Expr::Logical(LogicalExpr {
            id: generate_expr_id(),
            left,
            operator,
            right,
        })
    }

    pub fn call(callee: Box<Expr>, args: Vec<Box<Expr>>) -> Expr {
        Expr::Call(CallExpr {
            id: generate_expr_id(),
            callee,
            args,
        })
    }
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

#[derive(Debug)]
pub struct UnaryExpr {
    id: u64,
    pub operator: Operator,
    pub right: Box<Expr>,
}

#[derive(Debug)]
pub struct BinaryExpr {
    id: u64,
    pub left: Box<Expr>,
    pub operator: Operator,
    pub right: Box<Expr>,
}

#[derive(Debug)]
pub struct GroupingExpr {
    id: u64,
    pub expr: Box<Expr>,
}

#[derive(Debug)]
pub struct LiteralExpr {
    id: u64,
    pub value: LiteralValue,
}

#[derive(PartialEq, Debug)]
pub enum LiteralValue {
    String(String),
    Number(f64),
    Bool(bool),
    Nil,
}

#[derive(Debug)]
pub struct VariableExpr {
    id: u64,
    pub name: String,
}

#[derive(Debug)]
pub struct AssignExpr {
    id: u64,
    pub name: String,
    pub value: Box<Expr>,
}

#[derive(Debug)]
pub struct LogicalExpr {
    id: u64,
    pub left: Box<Expr>,
    pub operator: Operator,
    pub right: Box<Expr>,
}

#[derive(Debug)]
pub struct CallExpr {
    id: u64,
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
    Class(ClassStmt),
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

#[derive(PartialEq, Debug)]
pub struct ClassStmt {
    pub name: String,
    pub methods: Vec<Rc<FunctionStmt>>,
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

macro_rules! partial_eq_expr_field_eq {
    ($self:ident, $other:ident, $field:ident) => {
        $self.$field == $other.$field
    };

    ($self:ident, $other:ident, $field:ident, $($fields:ident),+) => {
        partial_eq_expr_field_eq!($self, $other, $field) &&
        partial_eq_expr_field_eq!($self, $other, $($fields),+)
    };
}

macro_rules! expr_impl {
    ($expr:ident, $($fields:ident),+) => {
        impl $expr {
            pub fn id(self: &$expr) -> u64 { self.id }
        }

        impl PartialEq for $expr {
            fn eq(self: &$expr, other: &Self) -> bool {
                partial_eq_expr_field_eq!(self, other, $($fields),+)
            }
        }

        impl Eq for $expr {}
    };
}

expr_impl!(UnaryExpr, operator, right);
expr_impl!(BinaryExpr, left, operator, right);
expr_impl!(GroupingExpr, expr);
expr_impl!(LiteralExpr, value);
expr_impl!(VariableExpr, name);
expr_impl!(AssignExpr, name, value);
expr_impl!(LogicalExpr, left, operator, right);
expr_impl!(CallExpr, callee, args);

lazy_static::lazy_static! {
    static ref NEXT_EXPR_ID: std::sync::Mutex<u64> = Mutex::new(0);
}

fn generate_expr_id() -> u64 {
    let mut next_expr_id = NEXT_EXPR_ID.lock().unwrap();
    let id = *next_expr_id;
    *next_expr_id = id + 1;
    id
}
