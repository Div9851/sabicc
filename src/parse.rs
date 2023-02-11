use std::collections::HashMap;
use std::rc::Rc;

use crate::error::Error;
use crate::tokenize::{self, Token, TokenKind};

pub enum Type {
    Int,
    Ptr(Rc<Type>),
}

impl Type {
    fn new_int() -> Rc<Type> {
        Rc::new(Type::Int)
    }
    fn new_ptr(base_ty: &Rc<Type>) -> Rc<Type> {
        Rc::new(Type::Ptr(Rc::clone(base_ty)))
    }
    pub fn is_int(&self) -> bool {
        match self {
            Type::Int => true,
            _ => false,
        }
    }
    pub fn is_ptr(&self) -> bool {
        match self {
            Type::Ptr(_) => true,
            _ => false,
        }
    }
    pub fn get_base_ty(&self) -> Rc<Type> {
        match self {
            Type::Ptr(base_ty) => Rc::clone(base_ty),
            _ => panic!("try to get base_ty of a non pointer type"),
        }
    }
}

fn type_of_binary_expr(
    op: BinaryOperator,
    lhs: &Rc<Type>,
    rhs: &Rc<Type>,
    loc: usize,
) -> Result<Rc<Type>, Error> {
    match op {
        BinaryOperator::ADD => type_of_add_expr(lhs, rhs, loc),
        BinaryOperator::SUB => type_of_sub_expr(lhs, rhs, loc),
        BinaryOperator::MUL | BinaryOperator::DIV => {
            if lhs.is_int() && rhs.is_int() {
                Ok(Type::new_int())
            } else {
                Err(Error {
                    loc,
                    msg: "invalid operands".to_owned(),
                })
            }
        }
        BinaryOperator::EQ | BinaryOperator::NE | BinaryOperator::LT | BinaryOperator::LE => {
            Ok(Type::new_int())
        }
    }
}

fn type_of_add_expr(lhs: &Rc<Type>, rhs: &Rc<Type>, loc: usize) -> Result<Rc<Type>, Error> {
    if lhs.is_int() && rhs.is_int() {
        // `int + int`
        Ok(Type::new_int())
    } else if lhs.is_ptr() && rhs.is_int() {
        // `ptr + int`
        Ok(Rc::clone(lhs))
    } else if lhs.is_int() && rhs.is_ptr() {
        // `int + ptr`
        Ok(Rc::clone(rhs))
    } else {
        // `ptr + ptr`
        Err(Error {
            loc,
            msg: "invalid operands".to_owned(),
        })
    }
}

fn type_of_sub_expr(lhs: &Rc<Type>, rhs: &Rc<Type>, loc: usize) -> Result<Rc<Type>, Error> {
    if lhs.is_int() && rhs.is_int() {
        // `int - int`
        Ok(Type::new_int())
    } else if lhs.is_ptr() && rhs.is_int() {
        // `ptr - int`
        Ok(Rc::clone(lhs))
    } else if lhs.is_int() && rhs.is_ptr() {
        // `int - ptr`
        Err(Error {
            loc,
            msg: "invalid operands".to_owned(),
        })
    } else {
        // `ptr - ptr`
        Ok(Type::new_int())
    }
}

fn type_of_unary_expr(op: UnaryOperator, ty: &Rc<Type>, loc: usize) -> Result<Rc<Type>, Error> {
    match op {
        UnaryOperator::NEG => {
            if ty.is_int() {
                Ok(Type::new_int())
            } else {
                Err(Error {
                    loc,
                    msg: "invalid operand".to_owned(),
                })
            }
        }
        UnaryOperator::DEREF => {
            if ty.is_ptr() {
                Ok(ty.get_base_ty())
            } else {
                Err(Error {
                    loc,
                    msg: "invalid operand".to_owned(),
                })
            }
        }
        UnaryOperator::ADDR => Ok(Type::new_ptr(ty)),
    }
}

#[derive(Clone)]
pub struct Obj {
    pub offset: usize, // Offset from RBP
    pub ty: Rc<Type>,  // Type
}

pub struct ParseContext {
    pub locals: HashMap<String, Obj>,
    pub stack_size: usize,
}

impl ParseContext {
    pub fn new_lvar(&mut self, decl: Decl) -> Obj {
        self.stack_size += 8;
        let obj = Obj {
            offset: self.stack_size,
            ty: decl.ty,
        };
        self.locals.insert(decl.name, obj.clone());
        obj
    }
    pub fn find_lvar(&mut self, name: &str) -> Option<Obj> {
        if let Some(obj) = self.locals.get(name) {
            Some(obj.clone())
        } else {
            None
        }
    }
}

pub struct Func {
    pub body: Box<Stmt>,
    pub stack_size: usize,
}

pub struct Decl {
    name: String,
    ty: Rc<Type>,
}

pub enum StmtKind {
    DeclStmt(Vec<Box<Stmt>>),
    NullStmt,
    ReturnStmt(Box<Expr>),
    CompoundStmt(Vec<Box<Stmt>>),
    ExprStmt(Box<Expr>),
    IfStmt {
        cond: Box<Expr>,
        then: Box<Stmt>,
        els: Option<Box<Stmt>>,
    },
    ForStmt {
        init: Box<Stmt>,
        cond: Option<Box<Expr>>,
        inc: Option<Box<Expr>>,
        body: Box<Stmt>,
    },
    WhileStmt {
        cond: Box<Expr>,
        body: Box<Stmt>,
    },
}

pub struct Stmt {
    pub kind: StmtKind,
    pub loc: usize,
}

#[derive(Clone, Copy)]
pub enum BinaryOperator {
    ADD, // +
    SUB, // -
    MUL, // *
    DIV, // /
    EQ,  // ==
    NE,  // !=
    LT,  // <
    LE,  // <=
}

#[derive(Clone, Copy)]
pub enum UnaryOperator {
    NEG,   // -
    DEREF, // *
    ADDR,  // &
}

pub enum ExprKind {
    Assign {
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Binary {
        op: BinaryOperator,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Unary {
        op: UnaryOperator,
        expr: Box<Expr>,
    },
    Var(Obj),
    Num(i32),
    FunCall {
        name: String,
        args: Vec<Box<Expr>>,
    },
}

pub struct Expr {
    pub kind: ExprKind,
    pub ty: Rc<Type>,
    pub loc: usize,
}

impl Expr {
    fn new_assign(lhs: Box<Expr>, rhs: Box<Expr>, loc: usize) -> Box<Expr> {
        let result_ty = Rc::clone(&lhs.ty);
        Box::new(Expr {
            kind: ExprKind::Assign { lhs, rhs },
            ty: result_ty,
            loc,
        })
    }
    fn new_binary(
        op: BinaryOperator,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        loc: usize,
    ) -> Result<Box<Expr>, Error> {
        let result_ty = type_of_binary_expr(op, &lhs.ty, &rhs.ty, loc)?;
        Ok(Box::new(Expr {
            kind: ExprKind::Binary { op, lhs, rhs },
            ty: result_ty,
            loc,
        }))
    }
    fn new_unary(op: UnaryOperator, expr: Box<Expr>, loc: usize) -> Result<Box<Expr>, Error> {
        let result_ty = type_of_unary_expr(op, &expr.ty, loc)?;
        Ok(Box::new(Expr {
            kind: ExprKind::Unary { op, expr },
            ty: result_ty,
            loc,
        }))
    }
    fn new_var(obj: Obj, loc: usize) -> Box<Expr> {
        let ty = Rc::clone(&obj.ty);
        Box::new(Expr {
            kind: ExprKind::Var(obj),
            ty,
            loc,
        })
    }
    fn new_num(val: i32, loc: usize) -> Box<Expr> {
        Box::new(Expr {
            kind: ExprKind::Num(val),
            ty: Type::new_int(),
            loc,
        })
    }
    fn new_funcall(name: &str, args: Vec<Box<Expr>>, loc: usize) -> Box<Expr> {
        Box::new(Expr {
            kind: ExprKind::FunCall {
                name: name.to_owned(),
                args,
            },
            ty: Type::new_int(),
            loc,
        })
    }
}

pub fn func(tok: &mut &Token) -> Result<Box<Func>, Error> {
    let mut ctx = ParseContext {
        locals: HashMap::new(),
        stack_size: 0,
    };
    let body = compound_stmt(tok, &mut ctx)?;
    Ok(Box::new(Func {
        body,
        stack_size: ctx.stack_size,
    }))
}

// declspec = "int"
fn declspec(tok: &mut &Token) -> Result<Rc<Type>, Error> {
    tokenize::expect(tok, "int")?;
    Ok(Type::new_int())
}

// declarator = "*"* ident
fn declarator(tok: &mut &Token, base_ty: &Rc<Type>) -> Result<Decl, Error> {
    let mut ty = Rc::clone(base_ty);
    while tokenize::consume(tok, "*") {
        ty = Type::new_ptr(&ty);
    }
    if tok.kind != TokenKind::Ident {
        return Err(Error {
            loc: tok.loc,
            msg: "expected an identifier".to_owned(),
        });
    }
    let ident = tokenize::consume_ident(tok).unwrap();
    Ok(Decl {
        name: ident.text.to_owned(),
        ty,
    })
}

// declaration = declspec (declarator ("=" expr)? ("," declarator ("=" expr)?)*)? ";"
fn declaration(tok: &mut &Token, ctx: &mut ParseContext) -> Result<Box<Stmt>, Error> {
    let loc = tok.loc;
    let base_ty = declspec(tok)?;
    let mut stmt_vec = Vec::new();
    while !tokenize::equal(tok, ";") {
        if stmt_vec.len() > 0 {
            tokenize::expect(tok, ",")?;
        }
        let loc = tok.loc;
        let decl = declarator(tok, &base_ty)?;
        let obj = ctx.new_lvar(decl);
        let mut lhs = Expr::new_var(obj, loc);
        if tokenize::consume(tok, "=") {
            let rhs = expr(tok, ctx)?;
            lhs = Expr::new_assign(lhs, rhs, loc);
        }
        let stmt = Box::new(Stmt {
            kind: StmtKind::ExprStmt(lhs),
            loc,
        });
        stmt_vec.push(stmt);
    }
    Ok(Box::new(Stmt {
        kind: StmtKind::DeclStmt(stmt_vec),
        loc,
    }))
}

// stmt = declaration
//      | "return" expr ";"
//      | "if" "(" expr ")" stmt ("else" stmt)?
//      | "for" "(" expr-stmt? ";" expr? ";" expr? ")" stmt
//      | "while" "(" expr ")" stmt
//      | "{" block-item* "}"
//      | expr-stmt
//      | null-stmt
fn stmt(tok: &mut &Token, ctx: &mut ParseContext) -> Result<Box<Stmt>, Error> {
    if tokenize::equal(tok, "int") {
        Ok(declaration(tok, ctx)?)
    } else if tokenize::equal(tok, ";") {
        Ok(null_stmt(tok)?)
    } else if tokenize::equal(tok, "return") {
        Ok(return_stmt(tok, ctx)?)
    } else if tokenize::equal(tok, "{") {
        Ok(compound_stmt(tok, ctx)?)
    } else if tokenize::equal(tok, "if") {
        Ok(if_stmt(tok, ctx)?)
    } else if tokenize::equal(tok, "for") {
        Ok(for_stmt(tok, ctx)?)
    } else if tokenize::equal(tok, "while") {
        Ok(while_stmt(tok, ctx)?)
    } else {
        Ok(expr_stmt(tok, ctx)?)
    }
}

fn null_stmt(tok: &mut &Token) -> Result<Box<Stmt>, Error> {
    let loc = tok.loc;
    tokenize::expect(tok, ";")?;
    let stmt = Stmt {
        kind: StmtKind::NullStmt,
        loc,
    };
    Ok(Box::new(stmt))
}

fn return_stmt(tok: &mut &Token, ctx: &mut ParseContext) -> Result<Box<Stmt>, Error> {
    let loc = tok.loc;
    tokenize::expect(tok, "return")?;
    let stmt = Stmt {
        kind: StmtKind::ReturnStmt(expr(tok, ctx)?),
        loc,
    };
    tokenize::expect(tok, ";")?;
    Ok(Box::new(stmt))
}

fn compound_stmt(tok: &mut &Token, ctx: &mut ParseContext) -> Result<Box<Stmt>, Error> {
    let loc = tok.loc;
    tokenize::expect(tok, "{")?;
    let mut block = Vec::new();
    while !tokenize::consume(tok, "}") {
        block.push(stmt(tok, ctx)?);
    }
    let stmt = Stmt {
        kind: StmtKind::CompoundStmt(block),
        loc,
    };
    Ok(Box::new(stmt))
}

fn expr_stmt(tok: &mut &Token, ctx: &mut ParseContext) -> Result<Box<Stmt>, Error> {
    let loc = tok.loc;
    let stmt = Stmt {
        kind: StmtKind::ExprStmt(expr(tok, ctx)?),
        loc,
    };
    tokenize::expect(tok, ";")?;
    Ok(Box::new(stmt))
}

fn if_stmt(tok: &mut &Token, ctx: &mut ParseContext) -> Result<Box<Stmt>, Error> {
    let loc = tok.loc;
    tokenize::expect(tok, "if")?;
    tokenize::expect(tok, "(")?;
    let cond = expr(tok, ctx)?;
    tokenize::expect(tok, ")")?;
    let then = stmt(tok, ctx)?;
    let mut els = None;
    if tokenize::consume(tok, "else") {
        els = Some(stmt(tok, ctx)?);
    }
    let stmt = Stmt {
        kind: StmtKind::IfStmt { cond, then, els },
        loc,
    };
    Ok(Box::new(stmt))
}

fn for_stmt(tok: &mut &Token, ctx: &mut ParseContext) -> Result<Box<Stmt>, Error> {
    let loc = tok.loc;
    tokenize::expect(tok, "for")?;
    tokenize::expect(tok, "(")?;
    let init = stmt(tok, ctx)?;
    let mut cond = None;
    if !tokenize::equal(tok, ";") {
        cond = Some(expr(tok, ctx)?);
    }
    tokenize::expect(tok, ";")?;
    let mut inc = None;
    if !tokenize::equal(tok, ")") {
        inc = Some(expr(tok, ctx)?);
    }
    tokenize::expect(tok, ")")?;
    let body = stmt(tok, ctx)?;
    let stmt = Stmt {
        kind: StmtKind::ForStmt {
            init,
            cond,
            inc,
            body,
        },
        loc,
    };
    Ok(Box::new(stmt))
}

fn while_stmt(tok: &mut &Token, ctx: &mut ParseContext) -> Result<Box<Stmt>, Error> {
    let loc = tok.loc;
    tokenize::expect(tok, "while")?;
    tokenize::expect(tok, "(")?;
    let cond = expr(tok, ctx)?;
    tokenize::expect(tok, ")")?;
    let body = stmt(tok, ctx)?;
    let stmt = Stmt {
        kind: StmtKind::WhileStmt { cond, body },
        loc,
    };
    Ok(Box::new(stmt))
}

// expr = assign
fn expr(tok: &mut &Token, ctx: &mut ParseContext) -> Result<Box<Expr>, Error> {
    assign(tok, ctx)
}

// assign = equality ("=" assign)?
fn assign(tok: &mut &Token, ctx: &mut ParseContext) -> Result<Box<Expr>, Error> {
    let lhs = equality(tok, ctx)?;
    let loc = tok.loc;
    if tokenize::consume(tok, "=") {
        let rhs = assign(tok, ctx)?;
        Ok(Expr::new_assign(lhs, rhs, loc))
    } else {
        Ok(lhs)
    }
}

// equality = relational ("==" relational | "!=" relational)*
fn equality(tok: &mut &Token, ctx: &mut ParseContext) -> Result<Box<Expr>, Error> {
    let mut expr = relational(tok, ctx)?;
    loop {
        let loc = tok.loc;
        if tokenize::consume(tok, "==") {
            expr = Expr::new_binary(BinaryOperator::EQ, expr, relational(tok, ctx)?, loc)?;
            continue;
        }
        if tokenize::consume(tok, "!=") {
            expr = Expr::new_binary(BinaryOperator::NE, expr, relational(tok, ctx)?, loc)?;
            continue;
        }
        break Ok(expr);
    }
}

// relational = add ("<" add | "<=" add | ">" add | ">=" add)*
fn relational(tok: &mut &Token, ctx: &mut ParseContext) -> Result<Box<Expr>, Error> {
    let mut expr = add(tok, ctx)?;
    loop {
        let loc = tok.loc;
        if tokenize::consume(tok, "<") {
            expr = Expr::new_binary(BinaryOperator::LT, expr, add(tok, ctx)?, loc)?;
            continue;
        }
        if tokenize::consume(tok, "<=") {
            expr = Expr::new_binary(BinaryOperator::LE, expr, add(tok, ctx)?, loc)?;
            continue;
        }
        if tokenize::consume(tok, ">") {
            expr = Expr::new_binary(BinaryOperator::LT, add(tok, ctx)?, expr, loc)?;
            continue;
        }
        if tokenize::consume(tok, ">=") {
            expr = Expr::new_binary(BinaryOperator::LE, add(tok, ctx)?, expr, loc)?;
            continue;
        }
        break Ok(expr);
    }
}

// add = mul ("+" mul | "-" mul)*
fn add(tok: &mut &Token, ctx: &mut ParseContext) -> Result<Box<Expr>, Error> {
    let mut expr = mul(tok, ctx)?;
    loop {
        let loc = tok.loc;
        if tokenize::consume(tok, "+") {
            let mut rhs = mul(tok, ctx)?;
            if expr.ty.is_int() && rhs.ty.is_ptr() {
                expr = Expr::new_binary(BinaryOperator::MUL, expr, Expr::new_num(8, loc), loc)?;
            }
            if expr.ty.is_ptr() && rhs.ty.is_int() {
                rhs = Expr::new_binary(BinaryOperator::MUL, rhs, Expr::new_num(8, loc), loc)?;
            }
            expr = Expr::new_binary(BinaryOperator::ADD, expr, rhs, loc)?;
            continue;
        }
        if tokenize::consume(tok, "-") {
            let mut rhs = mul(tok, ctx)?;
            if expr.ty.is_ptr() && rhs.ty.is_int() {
                rhs = Expr::new_binary(BinaryOperator::MUL, rhs, Expr::new_num(8, loc), loc)?;
            }
            let ptr_diff = expr.ty.is_ptr() && rhs.ty.is_ptr();
            expr = Expr::new_binary(BinaryOperator::SUB, expr, rhs, loc)?;
            if ptr_diff {
                expr = Expr::new_binary(BinaryOperator::DIV, expr, Expr::new_num(8, loc), loc)?;
            }
            continue;
        }
        break Ok(expr);
    }
}

// mul = unary ("*" unary | "/" unary)*
fn mul(tok: &mut &Token, ctx: &mut ParseContext) -> Result<Box<Expr>, Error> {
    let mut expr = unary(tok, ctx)?;
    loop {
        let loc = tok.loc;
        if tokenize::consume(tok, "*") {
            expr = Expr::new_binary(BinaryOperator::MUL, expr, unary(tok, ctx)?, loc)?;
            continue;
        }
        if tokenize::consume(tok, "/") {
            expr = Expr::new_binary(BinaryOperator::DIV, expr, unary(tok, ctx)?, loc)?;
            continue;
        }
        break Ok(expr);
    }
}

// unary = ("+" | "-" | "*" | "&") unary
//       | primary
fn unary(tok: &mut &Token, ctx: &mut ParseContext) -> Result<Box<Expr>, Error> {
    let loc = tok.loc;
    if tokenize::consume(tok, "+") {
        unary(tok, ctx)
    } else if tokenize::consume(tok, "-") {
        Ok(Expr::new_unary(UnaryOperator::NEG, unary(tok, ctx)?, loc))?
    } else if tokenize::consume(tok, "*") {
        Ok(Expr::new_unary(UnaryOperator::DEREF, unary(tok, ctx)?, loc))?
    } else if tokenize::consume(tok, "&") {
        Ok(Expr::new_unary(UnaryOperator::ADDR, unary(tok, ctx)?, loc))?
    } else {
        primary(tok, ctx)
    }
}

// funcall = ident "(" (expr ("," expr)*)? ")"
fn funcall(ident: &Token, tok: &mut &Token, ctx: &mut ParseContext) -> Result<Box<Expr>, Error> {
    tokenize::expect(tok, "(")?;
    let mut args = Vec::new();
    while !tokenize::consume(tok, ")") {
        if args.len() > 0 {
            tokenize::expect(tok, ",")?;
        }
        args.push(expr(tok, ctx)?);
    }
    Ok(Expr::new_funcall(&ident.text, args, ident.loc))
}

// primary = "(" expr ")" | ident | funcall | num
fn primary(tok: &mut &Token, ctx: &mut ParseContext) -> Result<Box<Expr>, Error> {
    let loc = tok.loc;

    if tokenize::consume(tok, "(") {
        let expr = expr(tok, ctx)?;
        tokenize::expect(tok, ")")?;
        return Ok(expr);
    }

    if let Some(val) = tokenize::consume_number(tok) {
        return Ok(Expr::new_num(val, loc));
    }

    if let Some(ident) = tokenize::consume_ident(tok) {
        // Function call
        if tokenize::equal(tok, "(") {
            return funcall(ident, tok, ctx);
        }
        // Variable
        if let Some(obj) = ctx.find_lvar(&ident.text) {
            return Ok(Expr::new_var(obj, loc));
        } else {
            return Err(Error {
                loc,
                msg: "undefined variable".to_owned(),
            });
        }
    }

    Err(Error {
        loc: tok.loc,
        msg: "expected an expression".to_owned(),
    })
}
