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
    Get(GetExpr),
    Set(SetExpr),
    Super(SuperExpr),
    This(ThisExpr),
}

impl Expr {
    pub fn unary(line: usize, operator: Operator, right: Box<Expr>) -> Expr {
        Expr::Unary(UnaryExpr {
            id: generate_expr_id(),
            line,
            operator,
            right,
        })
    }

    pub fn binary(line: usize, left: Box<Expr>, operator: Operator, right: Box<Expr>) -> Expr {
        Expr::Binary(BinaryExpr {
            id: generate_expr_id(),
            line,
            left,
            operator,
            right,
        })
    }

    pub fn grouping(line: usize, expr: Box<Expr>) -> Expr {
        Expr::Grouping(GroupingExpr {
            id: generate_expr_id(),
            line,
            expr,
        })
    }

    pub fn literal_string(line: usize, s: String) -> Expr {
        Expr::Literal(LiteralExpr {
            id: generate_expr_id(),
            line,
            value: LiteralValue::String(s),
        })
    }

    pub fn literal_number(line: usize, n: f64) -> Expr {
        Expr::Literal(LiteralExpr {
            id: generate_expr_id(),
            line,
            value: LiteralValue::Number(n),
        })
    }

    pub fn literal_bool(line: usize, b: bool) -> Expr {
        Expr::Literal(LiteralExpr {
            id: generate_expr_id(),
            line,
            value: LiteralValue::Bool(b),
        })
    }

    pub fn literal_nil(line: usize) -> Expr {
        Expr::Literal(LiteralExpr {
            id: generate_expr_id(),
            line,
            value: LiteralValue::Nil,
        })
    }

    pub fn variable(line: usize, name: String) -> Expr {
        Expr::Variable(VariableExpr {
            id: generate_expr_id(),
            line,
            name,
        })
    }

    pub fn assign(line: usize, name: String, value: Box<Expr>) -> Expr {
        Expr::Assign(AssignExpr {
            id: generate_expr_id(),
            line,
            name,
            value,
        })
    }

    pub fn logical(line: usize, left: Box<Expr>, operator: Operator, right: Box<Expr>) -> Expr {
        Expr::Logical(LogicalExpr {
            id: generate_expr_id(),
            line,
            left,
            operator,
            right,
        })
    }

    pub fn call(line: usize, callee: Box<Expr>, args: Vec<Box<Expr>>) -> Expr {
        Expr::Call(CallExpr {
            id: generate_expr_id(),
            line,
            callee,
            args,
        })
    }

    pub fn get(line: usize, object: Box<Expr>, name: String) -> Expr {
        Expr::Get(GetExpr {
            id: generate_expr_id(),
            line,
            object,
            name,
        })
    }

    pub fn set(line: usize, object: Box<Expr>, name: String, value: Box<Expr>) -> Expr {
        Expr::Set(SetExpr {
            id: generate_expr_id(),
            line,
            object,
            name,
            value,
        })
    }

    pub fn super_expr(line: usize, name: String) -> Expr {
        Expr::Super(SuperExpr {
            id: generate_expr_id(),
            line,
            name,
        })
    }

    pub fn this(line: usize) -> Expr {
        Expr::This(ThisExpr {
            id: generate_expr_id(),
            line,
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

macro_rules! partial_eq_expr_field_eq {
    ($self:ident, $other:ident, ) => {
        true
    };

    ($self:ident, $other:ident, $field:ident) => {
        $self.$field == $other.$field
    };

    ($self:ident, $other:ident, $field:ident, $($fields:ident),*) => {
        partial_eq_expr_field_eq!($self, $other, $field) &&
        partial_eq_expr_field_eq!($self, $other, $($fields),*)
    };
}

macro_rules! define_expr {
    ($name:ident, $($field:ident: $type:ty),*) => {
        #[derive(Debug)]
        pub struct $name {
            id: u64,
            line: usize,
            //line: u64,
            $(pub $field: $type,)*
        }

        impl $name {
            pub fn id(self: &$name) -> u64 { self.id }
            pub fn line(self: &$name) -> usize { self.line }
        }

        impl PartialEq for $name {
            #[allow(unused_variables)]
            fn eq(self: &$name, other: &Self) -> bool {
                partial_eq_expr_field_eq!(self, other, $($field),*)
            }
        }

        impl Eq for $name {}
    };
}

define_expr!(UnaryExpr, operator: Operator, right: Box<Expr>);
define_expr!(
    BinaryExpr,
    left: Box<Expr>,
    operator: Operator,
    right: Box<Expr>
);
define_expr!(GroupingExpr, expr: Box<Expr>);
define_expr!(LiteralExpr, value: LiteralValue);
define_expr!(VariableExpr, name: String);
define_expr!(AssignExpr, name: String, value: Box<Expr>);
define_expr!(
    LogicalExpr,
    left: Box<Expr>,
    operator: Operator,
    right: Box<Expr>
);
define_expr!(CallExpr, callee: Box<Expr>, args: Vec<Box<Expr>>);
define_expr!(SetExpr, object: Box<Expr>, name: String, value: Box<Expr>);
define_expr!(SuperExpr, name: String);
define_expr!(ThisExpr,);
define_expr!(GetExpr, object: Box<Expr>, name: String);

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
pub enum LiteralValue {
    String(String),
    Number(f64),
    Bool(bool),
    Nil,
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
    pub superclass: Option<Box<Expr>>,
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

lazy_static::lazy_static! {
    static ref NEXT_EXPR_ID: std::sync::Mutex<u64> = Mutex::new(0);
}

fn generate_expr_id() -> u64 {
    let mut next_expr_id = NEXT_EXPR_ID.lock().unwrap();
    let id = *next_expr_id;
    *next_expr_id = id + 1;
    id
}
