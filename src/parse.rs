use std::collections::HashMap;
use std::mem;
use std::rc::Rc;

use crate::error::Error;
use crate::tokenize::{self, Token, TokenKind};

pub enum TypeKind {
    Int,
    Ptr(Rc<Type>),
    Array(Rc<Type>, usize),
    Func {
        params: Vec<Decl>,
        return_ty: Rc<Type>,
    },
}

pub struct Type {
    pub kind: TypeKind,
    pub size: usize,
}

impl Type {
    fn new_int() -> Rc<Type> {
        Rc::new(Type {
            kind: TypeKind::Int,
            size: 8,
        })
    }
    fn new_ptr(base_ty: &Rc<Type>) -> Rc<Type> {
        Rc::new(Type {
            kind: TypeKind::Ptr(Rc::clone(base_ty)),
            size: 8,
        })
    }
    fn new_array(base_ty: &Rc<Type>, len: usize) -> Rc<Type> {
        Rc::new(Type {
            kind: TypeKind::Array(Rc::clone(base_ty), len),
            size: base_ty.size * len,
        })
    }
    fn new_func(params: Vec<Decl>, return_ty: &Rc<Type>) -> Rc<Type> {
        Rc::new(Type {
            kind: TypeKind::Func {
                params,
                return_ty: Rc::clone(return_ty),
            },
            size: 0,
        })
    }
    pub fn is_int(&self) -> bool {
        match self.kind {
            TypeKind::Int => true,
            _ => false,
        }
    }
    pub fn is_ptr(&self) -> bool {
        match self.kind {
            TypeKind::Ptr(_) | TypeKind::Array(_, _) => true,
            _ => false,
        }
    }
    pub fn get_base_ty(&self) -> &Rc<Type> {
        match &self.kind {
            TypeKind::Ptr(base_ty) | TypeKind::Array(base_ty, _) => base_ty,
            _ => panic!("try to get base_ty of a non pointer type"),
        }
    }
    pub fn equal(a: &Self, b: &Self) -> bool {
        if a.is_int() {
            b.is_int()
        } else {
            let a_base_ty = a.get_base_ty();
            if b.is_ptr() {
                let b_base_ty = b.get_base_ty();
                Type::equal(a_base_ty, b_base_ty)
            } else {
                false
            }
        }
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
        self.stack_size += decl.ty.size;
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
    pub name: String,
    pub return_ty: Rc<Type>,
    pub params: Vec<Obj>,
    pub body: Box<Stmt>,
    pub stack_size: usize,
}

#[derive(Clone)]
pub struct Decl {
    pub name: String,
    pub ty: Rc<Type>,
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
pub enum BinaryOp {
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
pub enum UnaryOp {
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
        op: BinaryOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Unary {
        op: UnaryOp,
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
        op: BinaryOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        loc: usize,
    ) -> Result<Box<Expr>, Error> {
        match op {
            BinaryOp::ADD => Expr::new_add(lhs, rhs, loc),
            BinaryOp::SUB => Expr::new_sub(lhs, rhs, loc),
            BinaryOp::MUL | BinaryOp::DIV => {
                if lhs.ty.is_int() && rhs.ty.is_int() {
                    let expr = Expr {
                        kind: ExprKind::Binary { op, lhs, rhs },
                        ty: Type::new_int(),
                        loc,
                    };
                    Ok(Box::new(expr))
                } else {
                    Err(Error {
                        loc,
                        msg: "invalid operands".to_owned(),
                    })
                }
            }
            BinaryOp::EQ | BinaryOp::NE | BinaryOp::LT | BinaryOp::LE => {
                let expr = Expr {
                    kind: ExprKind::Binary { op, lhs, rhs },
                    ty: Type::new_int(),
                    loc,
                };
                Ok(Box::new(expr))
            }
        }
    }

    fn new_add(mut lhs: Box<Expr>, mut rhs: Box<Expr>, loc: usize) -> Result<Box<Expr>, Error> {
        if lhs.ty.is_int() && rhs.ty.is_ptr() {
            mem::swap(&mut lhs, &mut rhs);
        }
        let result_ty;
        if lhs.ty.is_int() && rhs.ty.is_int() {
            // `int + int`
            result_ty = Type::new_int();
        } else if lhs.ty.is_ptr() && rhs.ty.is_int() {
            // `ptr + int`
            rhs = Expr::new_binary(
                BinaryOp::MUL,
                rhs,
                Expr::new_num(lhs.ty.get_base_ty().size as i32, loc),
                loc,
            )?;
            result_ty = Rc::clone(&lhs.ty);
        } else {
            // `ptr + ptr`
            return Err(Error {
                loc,
                msg: "invalid operands".to_owned(),
            });
        }
        Ok(Box::new(Expr {
            kind: ExprKind::Binary {
                op: BinaryOp::ADD,
                lhs,
                rhs,
            },
            ty: result_ty,
            loc,
        }))
    }

    fn new_sub(lhs: Box<Expr>, mut rhs: Box<Expr>, loc: usize) -> Result<Box<Expr>, Error> {
        let result_ty;
        let mut div = 1;
        if lhs.ty.is_int() && rhs.ty.is_int() {
            // `int - int`
            result_ty = Type::new_int();
        } else if lhs.ty.is_ptr() && rhs.ty.is_int() {
            // `ptr - int`
            rhs = Expr::new_binary(
                BinaryOp::MUL,
                rhs,
                Expr::new_num(lhs.ty.get_base_ty().size as i32, loc),
                loc,
            )?;
            result_ty = Rc::clone(&lhs.ty);
        } else if lhs.ty.is_int() && rhs.ty.is_ptr() {
            // `int - ptr`
            return Err(Error {
                loc,
                msg: "invalid operands".to_owned(),
            });
        } else {
            // `ptr - ptr`
            if !Type::equal(&lhs.ty, &rhs.ty) {
                return Err(Error {
                    loc,
                    msg: "invalid operands".to_owned(),
                });
            }
            div = lhs.ty.size as i32;
            result_ty = Type::new_int();
        }
        let mut expr = Box::new(Expr {
            kind: ExprKind::Binary {
                op: BinaryOp::SUB,
                lhs,
                rhs,
            },
            ty: result_ty,
            loc,
        });
        if div > 1 {
            expr = Expr::new_binary(BinaryOp::DIV, expr, Expr::new_num(div, loc), loc)?;
        }
        Ok(expr)
    }

    fn new_unary(op: UnaryOp, expr: Box<Expr>, loc: usize) -> Result<Box<Expr>, Error> {
        let result_ty;
        match op {
            UnaryOp::NEG => {
                if expr.ty.is_int() {
                    result_ty = Type::new_int();
                } else {
                    return Err(Error {
                        loc,
                        msg: "invalid operand".to_owned(),
                    });
                }
            }
            UnaryOp::DEREF => {
                if expr.ty.is_ptr() {
                    result_ty = Rc::clone(expr.ty.get_base_ty());
                } else {
                    return Err(Error {
                        loc,
                        msg: "invalid operand".to_owned(),
                    });
                }
            }
            UnaryOp::ADDR => {
                result_ty = Type::new_ptr(&expr.ty);
            }
        }
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
    let loc = tok.loc;
    let ty = declspec(tok)?;
    let decl = declarator(tok, &ty)?;
    let mut ctx = ParseContext {
        locals: HashMap::new(),
        stack_size: 0,
    };
    match &decl.ty.kind {
        TypeKind::Func { params, return_ty } => {
            let mut new_params = Vec::new();
            for param in params {
                let obj = ctx.new_lvar(param.clone());
                new_params.push(obj);
            }
            let body = compound_stmt(tok, &mut ctx)?;
            Ok(Box::new(Func {
                name: decl.name,
                return_ty: Rc::clone(return_ty),
                params: new_params,
                body,
                stack_size: ctx.stack_size,
            }))
        }
        _ => Err(Error {
            loc,
            msg: "expected a function".to_owned(),
        }),
    }
}

// declspec = "int"
fn declspec(tok: &mut &Token) -> Result<Rc<Type>, Error> {
    tokenize::expect(tok, "int")?;
    Ok(Type::new_int())
}

// func-params = "(" (param ("," param)*)? ")"
// param       = declspec declarator
fn func_params(tok: &mut &Token) -> Result<Vec<Decl>, Error> {
    tokenize::expect(tok, "(")?;
    let mut params = Vec::new();
    while !tokenize::consume(tok, ")") {
        if params.len() > 0 {
            tokenize::expect(tok, ",")?;
        }
        let param_base_ty = declspec(tok)?;
        let param = declarator(tok, &param_base_ty)?;
        params.push(param);
    }
    Ok(params)
}

// type-suffix = func-params
//             = "[" num "]" type-suffix
//             = ε
fn type_suffix(tok: &mut &Token, ty: &Rc<Type>) -> Result<Rc<Type>, Error> {
    if tokenize::equal(tok, "(") {
        let params = func_params(tok)?;
        Ok(Type::new_func(params, ty))
    } else if tokenize::equal(tok, "[") {
        tokenize::expect(tok, "[")?;
        let len = tokenize::expect_number(tok)?;
        tokenize::expect(tok, "]")?;
        let base_ty = type_suffix(tok, ty)?;
        Ok(Type::new_array(&base_ty, len as usize))
    } else {
        Ok(Rc::clone(ty))
    }
}

// declarator = "*"* ident type-suffix
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
    ty = type_suffix(tok, &ty)?;
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
    let mut count = 0;
    while !tokenize::consume(tok, ";") {
        if count > 0 {
            tokenize::expect(tok, ",")?;
        }
        let loc = tok.loc;
        let decl = declarator(tok, &base_ty)?;
        let obj = ctx.new_lvar(decl);
        if tokenize::consume(tok, "=") {
            let lhs = Expr::new_var(obj, loc);
            let rhs = expr(tok, ctx)?;
            let expr = Expr::new_assign(lhs, rhs, loc);
            let stmt = Box::new(Stmt {
                kind: StmtKind::ExprStmt(expr),
                loc,
            });
            stmt_vec.push(stmt);
        }
        count += 1;
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
            expr = Expr::new_binary(BinaryOp::EQ, expr, relational(tok, ctx)?, loc)?;
            continue;
        }
        if tokenize::consume(tok, "!=") {
            expr = Expr::new_binary(BinaryOp::NE, expr, relational(tok, ctx)?, loc)?;
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
            expr = Expr::new_binary(BinaryOp::LT, expr, add(tok, ctx)?, loc)?;
            continue;
        }
        if tokenize::consume(tok, "<=") {
            expr = Expr::new_binary(BinaryOp::LE, expr, add(tok, ctx)?, loc)?;
            continue;
        }
        if tokenize::consume(tok, ">") {
            expr = Expr::new_binary(BinaryOp::LT, add(tok, ctx)?, expr, loc)?;
            continue;
        }
        if tokenize::consume(tok, ">=") {
            expr = Expr::new_binary(BinaryOp::LE, add(tok, ctx)?, expr, loc)?;
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
            let rhs = mul(tok, ctx)?;
            expr = Expr::new_binary(BinaryOp::ADD, expr, rhs, loc)?;
            continue;
        }
        if tokenize::consume(tok, "-") {
            let rhs = mul(tok, ctx)?;
            expr = Expr::new_binary(BinaryOp::SUB, expr, rhs, loc)?;
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
            expr = Expr::new_binary(BinaryOp::MUL, expr, unary(tok, ctx)?, loc)?;
            continue;
        }
        if tokenize::consume(tok, "/") {
            expr = Expr::new_binary(BinaryOp::DIV, expr, unary(tok, ctx)?, loc)?;
            continue;
        }
        break Ok(expr);
    }
}

// unary = ("+" | "-" | "*" | "&") unary
//       | postfix
fn unary(tok: &mut &Token, ctx: &mut ParseContext) -> Result<Box<Expr>, Error> {
    let loc = tok.loc;
    if tokenize::consume(tok, "+") {
        unary(tok, ctx)
    } else if tokenize::consume(tok, "-") {
        Ok(Expr::new_unary(UnaryOp::NEG, unary(tok, ctx)?, loc))?
    } else if tokenize::consume(tok, "*") {
        Ok(Expr::new_unary(UnaryOp::DEREF, unary(tok, ctx)?, loc))?
    } else if tokenize::consume(tok, "&") {
        Ok(Expr::new_unary(UnaryOp::ADDR, unary(tok, ctx)?, loc))?
    } else {
        postfix(tok, ctx)
    }
}

// postfix = primary ("[" expr "]")*
fn postfix(tok: &mut &Token, ctx: &mut ParseContext) -> Result<Box<Expr>, Error> {
    let mut ret = primary(tok, ctx)?;
    while tokenize::equal(tok, "[") {
        let loc = tok.loc;
        tokenize::expect(tok, "[")?;
        let index = expr(tok, ctx)?;
        tokenize::expect(tok, "]")?;
        ret = Expr::new_unary(
            UnaryOp::DEREF,
            Expr::new_binary(BinaryOp::ADD, ret, index, loc)?,
            loc,
        )?;
    }
    Ok(ret)
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
