use std::collections::HashMap;

use crate::error::Error;
use crate::tokenize::{self, Token};

#[derive(Clone)]
pub struct Obj {
    pub offset: usize, // Offset from RBP
}

pub struct ParseContext {
    pub locals: HashMap<String, Obj>,
    pub stack_size: usize,
}

impl ParseContext {
    pub fn new_lvar(&mut self, name: String) -> Obj {
        self.stack_size += 8;
        let obj = Obj {
            offset: self.stack_size,
        };
        self.locals.insert(name, obj.clone());
        obj
    }
    pub fn get_lvar(&mut self, name: &str) -> Obj {
        if let Some(obj) = self.locals.get(name) {
            obj.clone()
        } else {
            self.new_lvar(name.to_owned())
        }
    }
}

pub struct Func {
    pub body: Box<Stmt>,
    pub stack_size: usize,
}

pub enum StmtKind {
    NullStmt,
    ReturnStmt(Box<Expr>),
    Block(Vec<Box<Stmt>>),
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
}

pub struct Expr {
    pub kind: ExprKind,
    pub loc: usize,
}

impl Expr {
    fn new_assign(lhs: Box<Expr>, rhs: Box<Expr>, loc: usize) -> Box<Expr> {
        Box::new(Expr {
            kind: ExprKind::Assign { lhs, rhs },
            loc,
        })
    }
    fn new_binary(op: BinaryOperator, lhs: Box<Expr>, rhs: Box<Expr>, loc: usize) -> Box<Expr> {
        Box::new(Expr {
            kind: ExprKind::Binary { op, lhs, rhs },
            loc,
        })
    }
    fn new_unary(op: UnaryOperator, expr: Box<Expr>, loc: usize) -> Box<Expr> {
        Box::new(Expr {
            kind: ExprKind::Unary { op, expr },
            loc,
        })
    }
    fn new_var(obj: Obj, loc: usize) -> Box<Expr> {
        Box::new(Expr {
            kind: ExprKind::Var(obj),
            loc,
        })
    }
    fn new_num(val: i32, loc: usize) -> Box<Expr> {
        Box::new(Expr {
            kind: ExprKind::Num(val),
            loc,
        })
    }
}

pub fn func(tok: &mut &Token) -> Result<Box<Func>, Error> {
    let mut ctx = ParseContext {
        locals: HashMap::new(),
        stack_size: 0,
    };
    let block = block_stmt(tok, &mut ctx)?;
    Ok(Box::new(Func {
        body: block,
        stack_size: ctx.stack_size,
    }))
}

fn stmt(tok: &mut &Token, ctx: &mut ParseContext) -> Result<Box<Stmt>, Error> {
    if tokenize::equal(tok, ";") {
        Ok(null_stmt(tok)?)
    } else if tokenize::equal(tok, "return") {
        Ok(return_stmt(tok, ctx)?)
    } else if tokenize::equal(tok, "{") {
        Ok(block_stmt(tok, ctx)?)
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

fn block_stmt(tok: &mut &Token, ctx: &mut ParseContext) -> Result<Box<Stmt>, Error> {
    let loc = tok.loc;
    tokenize::expect(tok, "{")?;
    let mut block = Vec::new();
    while !tokenize::consume(tok, "}") {
        block.push(stmt(tok, ctx)?);
    }
    let stmt = Stmt {
        kind: StmtKind::Block(block),
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
            expr = Expr::new_binary(BinaryOperator::EQ, expr, relational(tok, ctx)?, loc);
            continue;
        }
        if tokenize::consume(tok, "!=") {
            expr = Expr::new_binary(BinaryOperator::NE, expr, relational(tok, ctx)?, loc);
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
            expr = Expr::new_binary(BinaryOperator::LT, expr, add(tok, ctx)?, loc);
            continue;
        }
        if tokenize::consume(tok, "<=") {
            expr = Expr::new_binary(BinaryOperator::LE, expr, add(tok, ctx)?, loc);
            continue;
        }
        if tokenize::consume(tok, ">") {
            expr = Expr::new_binary(BinaryOperator::LT, add(tok, ctx)?, expr, loc);
            continue;
        }
        if tokenize::consume(tok, ">=") {
            expr = Expr::new_binary(BinaryOperator::LE, add(tok, ctx)?, expr, loc);
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
            expr = Expr::new_binary(BinaryOperator::ADD, expr, mul(tok, ctx)?, loc);
            continue;
        }
        if tokenize::consume(tok, "-") {
            expr = Expr::new_binary(BinaryOperator::SUB, expr, mul(tok, ctx)?, loc);
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
            expr = Expr::new_binary(BinaryOperator::MUL, expr, unary(tok, ctx)?, loc);
            continue;
        }
        if tokenize::consume(tok, "/") {
            expr = Expr::new_binary(BinaryOperator::DIV, expr, unary(tok, ctx)?, loc);
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
        Ok(Expr::new_unary(UnaryOperator::NEG, unary(tok, ctx)?, loc))
    } else if tokenize::consume(tok, "*") {
        Ok(Expr::new_unary(UnaryOperator::DEREF, unary(tok, ctx)?, loc))
    } else if tokenize::consume(tok, "&") {
        Ok(Expr::new_unary(UnaryOperator::ADDR, unary(tok, ctx)?, loc))
    } else {
        primary(tok, ctx)
    }
}

// primary = "(" expr ")" | ident | num
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

    if let Some(name) = tokenize::consume_ident(tok) {
        return Ok(Expr::new_var(ctx.get_lvar(name), loc));
    }

    Err(Error {
        loc: tok.loc,
        msg: "expected an expression".to_owned(),
    })
}
