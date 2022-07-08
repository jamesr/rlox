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

macro_rules! ast_node_constructor {
    ($name:ident, $variant:ident, $ast_ty:ident, $inner:ident, $($pname:ident : $pty:ty),*) => {
        pub fn $name($($pname: $pty),*) -> $ast_ty {
            $ast_ty::$variant($inner {
                id: generate_ast_node_id(),
                $($pname),*
            })
        }
    };
}

impl Expr {
    pub fn id(&self) -> u64 {
        match self {
            Expr::Unary(e) => e.id(),
            Expr::Binary(e) => e.id(),
            Expr::Grouping(e) => e.id(),
            Expr::Literal(e) => e.id(),
            Expr::Variable(e) => e.id(),
            Expr::Assign(e) => e.id(),
            Expr::Logical(e) => e.id(),
            Expr::Call(e) => e.id(),
            Expr::Get(e) => e.id(),
            Expr::Set(e) => e.id(),
            Expr::Super(e) => e.id(),
            Expr::This(e) => e.id(),
        }
    }
    ast_node_constructor!(
        unary,
        Unary,
        Expr,
        UnaryExpr,
        operator: Operator,
        right: Box<Expr>
    );

    ast_node_constructor!(
        binary,
        Binary,
        Expr,
        BinaryExpr,
        left: Box<Expr>,
        operator: Operator,
        right: Box<Expr>
    );

    ast_node_constructor!(grouping, Grouping, Expr, GroupingExpr, expr: Box<Expr>);

    pub fn literal_string(s: String) -> Expr {
        Expr::Literal(LiteralExpr {
            id: generate_ast_node_id(),
            value: LiteralValue::String(s),
        })
    }

    pub fn literal_number(n: f64) -> Expr {
        Expr::Literal(LiteralExpr {
            id: generate_ast_node_id(),
            value: LiteralValue::Number(n),
        })
    }

    pub fn literal_bool(b: bool) -> Expr {
        Expr::Literal(LiteralExpr {
            id: generate_ast_node_id(),
            value: LiteralValue::Bool(b),
        })
    }

    pub fn literal_nil() -> Expr {
        Expr::Literal(LiteralExpr {
            id: generate_ast_node_id(),
            value: LiteralValue::Nil,
        })
    }

    ast_node_constructor!(variable, Variable, Expr, VariableExpr, name: String);

    ast_node_constructor!(
        assign,
        Assign,
        Expr,
        AssignExpr,
        name: String,
        value: Box<Expr>
    );

    ast_node_constructor!(
        logical,
        Logical,
        Expr,
        LogicalExpr,
        left: Box<Expr>,
        operator: Operator,
        right: Box<Expr>
    );

    ast_node_constructor!(
        call,
        Call,
        Expr,
        CallExpr,
        callee: Box<Expr>,
        args: Vec<Box<Expr>>
    );

    ast_node_constructor!(get, Get, Expr, GetExpr, object: Box<Expr>, name: String);

    ast_node_constructor!(
        set,
        Set,
        Expr,
        SetExpr,
        object: Box<Expr>,
        name: String,
        value: Box<Expr>
    );

    ast_node_constructor!(super_expr, Super, Expr, SuperExpr, name: String);

    ast_node_constructor!(this, This, Expr, ThisExpr,);
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

macro_rules! define_ast_node {
    ($name:ident, $($field:ident: $type:ty),*) => {
        #[derive(Debug)]
        pub struct $name {
            id: u64,
            $(pub $field: $type,)*
        }

        impl $name {
            pub fn id(self: &$name) -> u64 { self.id }
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

define_ast_node!(UnaryExpr, operator: Operator, right: Box<Expr>);
define_ast_node!(
    BinaryExpr,
    left: Box<Expr>,
    operator: Operator,
    right: Box<Expr>
);
define_ast_node!(GroupingExpr, expr: Box<Expr>);
define_ast_node!(LiteralExpr, value: LiteralValue);
define_ast_node!(VariableExpr, name: String);
define_ast_node!(AssignExpr, name: String, value: Box<Expr>);
define_ast_node!(
    LogicalExpr,
    left: Box<Expr>,
    operator: Operator,
    right: Box<Expr>
);
define_ast_node!(CallExpr, callee: Box<Expr>, args: Vec<Box<Expr>>);
define_ast_node!(SetExpr, object: Box<Expr>, name: String, value: Box<Expr>);
define_ast_node!(SuperExpr, name: String);
define_ast_node!(ThisExpr,);
define_ast_node!(GetExpr, object: Box<Expr>, name: String);

#[derive(PartialEq, Debug)]
pub enum LiteralValue {
    String(String),
    Number(f64),
    Bool(bool),
    Nil,
}

#[derive(PartialEq, Debug)]
pub enum Stmt {
    Expr(ExprStmt),
    Print(PrintStmt),
    Return(ReturnStmt),
    Block(BlockStmt),
    Var(VarDecl),
    If(IfStmt),
    While(WhileStmt),
    Function(Rc<FunctionStmt>),
    Class(ClassStmt),
}

impl Stmt {
    pub fn id(&self) -> u64 {
        0
    }

    ast_node_constructor!(expr, Expr, Stmt, ExprStmt, expr: Box<Expr>);
    ast_node_constructor!(print, Print, Stmt, PrintStmt, expr: Box<Expr>);
    ast_node_constructor!(
        return_stmt,
        Return,
        Stmt,
        ReturnStmt,
        value: Option<Box<Expr>>
    );
    ast_node_constructor!(block, Block, Stmt, BlockStmt, stmts: Vec<Box<Stmt>>);
    ast_node_constructor!(
        var,
        Var,
        Stmt,
        VarDecl,
        name: String,
        initializer: Option<Box<Expr>>
    );
    ast_node_constructor!(
        if_stmt,
        If,
        Stmt,
        IfStmt,
        condition: Box<Expr>,
        then_branch: Box<Stmt>,
        else_branch: Option<Box<Stmt>>
    );
    ast_node_constructor!(
        while_stmt,
        While,
        Stmt,
        WhileStmt,
        condition: Box<Expr>,
        body: Box<Stmt>
    );

    pub fn function(name: String, params: Vec<String>, body: Vec<Box<Stmt>>) -> FunctionStmt {
        FunctionStmt {
            id: generate_ast_node_id(),
            name,
            params,
            body,
        }
    }

    ast_node_constructor!(
        class,
        Class,
        Stmt,
        ClassStmt,
        name: String,
        superclass: Option<Box<Expr>>,
        methods: Vec<Rc<FunctionStmt>>
    );
}

define_ast_node!(ExprStmt, expr: Box<Expr>);
define_ast_node!(PrintStmt, expr: Box<Expr>);
define_ast_node!(ReturnStmt, value: Option<Box<Expr>>);
define_ast_node!(BlockStmt, stmts: Vec<Box<Stmt>>);
define_ast_node!(VarDecl, name: String, initializer: Option<Box<Expr>>);
define_ast_node!(
    IfStmt,
    condition: Box<Expr>,
    then_branch: Box<Stmt>,
    else_branch: Option<Box<Stmt>>
);
define_ast_node!(WhileStmt, condition: Box<Expr>, body: Box<Stmt>);
define_ast_node!(
    FunctionStmt,
    name: String,
    params: Vec<String>,
    body: Vec<Box<Stmt>>
);
define_ast_node!(
    ClassStmt,
    name: String,
    superclass: Option<Box<Expr>>,
    methods: Vec<Rc<FunctionStmt>>
);

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
    static ref NEXT_AST_NODE_ID: std::sync::Mutex<u64> = Mutex::new(0);
}

fn generate_ast_node_id() -> u64 {
    let mut next_ast_node_id = NEXT_AST_NODE_ID.lock().unwrap();
    let id = *next_ast_node_id;
    *next_ast_node_id = id + 1;
    id
}
