use std::collections::HashMap;

use crate::error::Error;
use crate::tokenize::{Token, TokenKind};

#[derive(Clone)]
pub struct Obj {
    pub offset: usize, // Offset from RBP
}

pub struct Func {
    pub body: Vec<Box<Stmt>>,
    pub locals: HashMap<String, Obj>,
    pub stack_size: usize,
}

impl Func {
    fn new_lvar(&mut self, name: String) -> Obj {
        self.stack_size += 8;
        let obj = Obj {
            offset: self.stack_size,
        };
        self.locals.insert(name, obj.clone());
        obj
    }
    fn get_lvar(&mut self, name: &str) -> Obj {
        if let Some(obj) = self.locals.get(name) {
            obj.clone()
        } else {
            self.new_lvar(name.to_owned())
        }
    }
}

pub enum Stmt {
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

fn consume(tok: &mut &Token, op: &str) -> bool {
    if tok.kind == TokenKind::Punct && tok.text == op {
        *tok = tok.next.as_ref().unwrap();
        true
    } else {
        false
    }
}

fn expect(tok: &mut &Token, op: &str) -> Result<(), Error> {
    if tok.kind == TokenKind::Punct && tok.text == op {
        *tok = tok.next.as_ref().unwrap();
        Ok(())
    } else {
        Err(Error {
            loc: tok.loc,
            msg: format!("'{}' expected", op),
        })
    }
}

fn consume_number(tok: &mut &Token) -> Option<i32> {
    if let TokenKind::Num(val) = tok.kind {
        *tok = tok.next.as_ref().unwrap();
        Some(val)
    } else {
        None
    }
}

fn consume_ident<'a>(tok: &mut &'a Token) -> Option<&'a str> {
    if tok.kind == TokenKind::Ident {
        let name = &tok.text;
        *tok = tok.next.as_ref().unwrap();
        Some(name)
    } else {
        None
    }
}

pub fn func(tok: &mut &Token) -> Result<Box<Func>, Error> {
    let mut f = Func {
        body: Vec::new(),
        locals: HashMap::new(),
        stack_size: 0,
    };
    while tok.kind != TokenKind::EOF {
        let stmt = stmt(tok, &mut f)?;
        f.body.push(stmt);
    }
    Ok(Box::new(f))
}

fn stmt(tok: &mut &Token, f: &mut Func) -> Result<Box<Stmt>, Error> {
    let stmt = Box::new(Stmt::ExprStmt(expr(tok, f)?));
    expect(tok, ";")?;
    Ok(stmt)
}

fn expr(tok: &mut &Token, f: &mut Func) -> Result<Box<Expr>, Error> {
    assign(tok, f)
}

// assign = equality ("=" assign)?
fn assign(tok: &mut &Token, f: &mut Func) -> Result<Box<Expr>, Error> {
    let lhs = equality(tok, f)?;
    if consume(tok, "=") {
        let rhs = assign(tok, f)?;
        Ok(Box::new(Expr::Assign { lhs, rhs }))
    } else {
        Ok(lhs)
    }
}

fn equality(tok: &mut &Token, f: &mut Func) -> Result<Box<Expr>, Error> {
    let mut expr = relational(tok, f)?;
    loop {
        if consume(tok, "==") {
            expr = Expr::new_binary(BinaryOperator::EQ, expr, relational(tok, f)?);
            continue;
        }
        if consume(tok, "!=") {
            expr = Expr::new_binary(BinaryOperator::NE, expr, relational(tok, f)?);
            continue;
        }
        break Ok(expr);
    }
}

fn relational(tok: &mut &Token, f: &mut Func) -> Result<Box<Expr>, Error> {
    let mut expr = add(tok, f)?;
    loop {
        if consume(tok, "<") {
            expr = Expr::new_binary(BinaryOperator::LT, expr, add(tok, f)?);
            continue;
        }
        if consume(tok, "<=") {
            expr = Expr::new_binary(BinaryOperator::LE, expr, add(tok, f)?);
            continue;
        }
        if consume(tok, ">") {
            expr = Expr::new_binary(BinaryOperator::LT, add(tok, f)?, expr);
            continue;
        }
        if consume(tok, ">=") {
            expr = Expr::new_binary(BinaryOperator::LE, add(tok, f)?, expr);
            continue;
        }
        break Ok(expr);
    }
}

fn add(tok: &mut &Token, f: &mut Func) -> Result<Box<Expr>, Error> {
    let mut expr = mul(tok, f)?;
    loop {
        if consume(tok, "+") {
            expr = Expr::new_binary(BinaryOperator::ADD, expr, mul(tok, f)?);
            continue;
        }
        if consume(tok, "-") {
            expr = Expr::new_binary(BinaryOperator::SUB, expr, mul(tok, f)?);
            continue;
        }
        break Ok(expr);
    }
}

fn mul(tok: &mut &Token, f: &mut Func) -> Result<Box<Expr>, Error> {
    let mut expr = unary(tok, f)?;
    loop {
        if consume(tok, "*") {
            expr = Expr::new_binary(BinaryOperator::MUL, expr, unary(tok, f)?);
            continue;
        }
        if consume(tok, "/") {
            expr = Expr::new_binary(BinaryOperator::DIV, expr, unary(tok, f)?);
            continue;
        }
        break Ok(expr);
    }
}

fn unary(tok: &mut &Token, f: &mut Func) -> Result<Box<Expr>, Error> {
    if consume(tok, "+") {
        unary(tok, f)
    } else if consume(tok, "-") {
        Ok(Expr::new_unary(UnaryOperator::NEG, unary(tok, f)?))
    } else {
        primary(tok, f)
    }
}

fn primary(tok: &mut &Token, f: &mut Func) -> Result<Box<Expr>, Error> {
    if consume(tok, "(") {
        let expr = expr(tok, f)?;
        expect(tok, ")")?;
        return Ok(expr);
    }

    if let Some(val) = consume_number(tok) {
        return Ok(Expr::new_num(val));
    }

    if let Some(name) = consume_ident(tok) {
        return Ok(Expr::new_var(f.get_lvar(name)));
    }

    Err(Error {
        loc: tok.loc,
        msg: "expected an expression".to_owned(),
    })
}
