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

pub enum Stmt {
    NullStmt,
    ReturnStmt(Box<Expr>),
    Block(Vec<Box<Stmt>>),
    ExprStmt(Box<Expr>),
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
    NEG, // -
}

pub enum Expr {
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

impl Expr {
    fn new_binary(op: BinaryOperator, lhs: Box<Expr>, rhs: Box<Expr>) -> Box<Expr> {
        Box::new(Expr::Binary { op, lhs, rhs })
    }
    fn new_unary(op: UnaryOperator, expr: Box<Expr>) -> Box<Expr> {
        Box::new(Expr::Unary { op, expr })
    }
    fn new_var(obj: Obj) -> Box<Expr> {
        Box::new(Expr::Var(obj))
    }
    fn new_num(val: i32) -> Box<Expr> {
        Box::new(Expr::Num(val))
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
    if tokenize::consume(tok, ";") {
        Ok(Box::new(Stmt::NullStmt))
    } else if tokenize::equal(tok, "return") {
        Ok(return_stmt(tok, ctx)?)
    } else if tokenize::equal(tok, "{") {
        Ok(block_stmt(tok, ctx)?)
    } else {
        Ok(expr_stmt(tok, ctx)?)
    }
}

fn return_stmt(tok: &mut &Token, ctx: &mut ParseContext) -> Result<Box<Stmt>, Error> {
    tokenize::expect(tok, "return")?;
    let stmt = Box::new(Stmt::ReturnStmt(expr(tok, ctx)?));
    tokenize::expect(tok, ";")?;
    Ok(stmt)
}

fn block_stmt(tok: &mut &Token, ctx: &mut ParseContext) -> Result<Box<Stmt>, Error> {
    tokenize::expect(tok, "{")?;
    let mut block = Vec::new();
    while !tokenize::consume(tok, "}") {
        block.push(stmt(tok, ctx)?);
    }
    Ok(Box::new(Stmt::Block(block)))
}

fn expr_stmt(tok: &mut &Token, ctx: &mut ParseContext) -> Result<Box<Stmt>, Error> {
    let stmt = Box::new(Stmt::ExprStmt(expr(tok, ctx)?));
    tokenize::expect(tok, ";")?;
    Ok(stmt)
}

fn expr(tok: &mut &Token, ctx: &mut ParseContext) -> Result<Box<Expr>, Error> {
    assign(tok, ctx)
}

// assign = equality ("=" assign)?
fn assign(tok: &mut &Token, ctx: &mut ParseContext) -> Result<Box<Expr>, Error> {
    let lhs = equality(tok, ctx)?;
    if tokenize::consume(tok, "=") {
        let rhs = assign(tok, ctx)?;
        Ok(Box::new(Expr::Assign { lhs, rhs }))
    } else {
        Ok(lhs)
    }
}

fn equality(tok: &mut &Token, ctx: &mut ParseContext) -> Result<Box<Expr>, Error> {
    let mut expr = relational(tok, ctx)?;
    loop {
        if tokenize::consume(tok, "==") {
            expr = Expr::new_binary(BinaryOperator::EQ, expr, relational(tok, ctx)?);
            continue;
        }
        if tokenize::consume(tok, "!=") {
            expr = Expr::new_binary(BinaryOperator::NE, expr, relational(tok, ctx)?);
            continue;
        }
        break Ok(expr);
    }
}

fn relational(tok: &mut &Token, ctx: &mut ParseContext) -> Result<Box<Expr>, Error> {
    let mut expr = add(tok, ctx)?;
    loop {
        if tokenize::consume(tok, "<") {
            expr = Expr::new_binary(BinaryOperator::LT, expr, add(tok, ctx)?);
            continue;
        }
        if tokenize::consume(tok, "<=") {
            expr = Expr::new_binary(BinaryOperator::LE, expr, add(tok, ctx)?);
            continue;
        }
        if tokenize::consume(tok, ">") {
            expr = Expr::new_binary(BinaryOperator::LT, add(tok, ctx)?, expr);
            continue;
        }
        if tokenize::consume(tok, ">=") {
            expr = Expr::new_binary(BinaryOperator::LE, add(tok, ctx)?, expr);
            continue;
        }
        break Ok(expr);
    }
}

fn add(tok: &mut &Token, ctx: &mut ParseContext) -> Result<Box<Expr>, Error> {
    let mut expr = mul(tok, ctx)?;
    loop {
        if tokenize::consume(tok, "+") {
            expr = Expr::new_binary(BinaryOperator::ADD, expr, mul(tok, ctx)?);
            continue;
        }
        if tokenize::consume(tok, "-") {
            expr = Expr::new_binary(BinaryOperator::SUB, expr, mul(tok, ctx)?);
            continue;
        }
        break Ok(expr);
    }
}

fn mul(tok: &mut &Token, ctx: &mut ParseContext) -> Result<Box<Expr>, Error> {
    let mut expr = unary(tok, ctx)?;
    loop {
        if tokenize::consume(tok, "*") {
            expr = Expr::new_binary(BinaryOperator::MUL, expr, unary(tok, ctx)?);
            continue;
        }
        if tokenize::consume(tok, "/") {
            expr = Expr::new_binary(BinaryOperator::DIV, expr, unary(tok, ctx)?);
            continue;
        }
        break Ok(expr);
    }
}

fn unary(tok: &mut &Token, ctx: &mut ParseContext) -> Result<Box<Expr>, Error> {
    if tokenize::consume(tok, "+") {
        unary(tok, ctx)
    } else if tokenize::consume(tok, "-") {
        Ok(Expr::new_unary(UnaryOperator::NEG, unary(tok, ctx)?))
    } else {
        primary(tok, ctx)
    }
}

fn primary(tok: &mut &Token, ctx: &mut ParseContext) -> Result<Box<Expr>, Error> {
    if tokenize::consume(tok, "(") {
        let expr = expr(tok, ctx)?;
        tokenize::expect(tok, ")")?;
        return Ok(expr);
    }

    if let Some(val) = tokenize::consume_number(tok) {
        return Ok(Expr::new_num(val));
    }

    if let Some(name) = tokenize::consume_ident(tok) {
        return Ok(Expr::new_var(ctx.get_lvar(name)));
    }

    Err(Error {
        loc: tok.loc,
        msg: "expected an expression".to_owned(),
    })
}
