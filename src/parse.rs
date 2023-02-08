use crate::error::Error;
use crate::tokenize::{Token, TokenKind};

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
    Binary {
        op: BinaryOperator,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Unary {
        op: UnaryOperator,
        expr: Box<Expr>,
    },
    Num(i32),
}

impl Expr {
    fn new_binary(op: BinaryOperator, lhs: Box<Expr>, rhs: Box<Expr>) -> Box<Expr> {
        Box::new(Expr::Binary { op, lhs, rhs })
    }
    fn new_unary(op: UnaryOperator, expr: Box<Expr>) -> Box<Expr> {
        Box::new(Expr::Unary { op, expr })
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

pub fn expr(tok: &mut &Token) -> Result<Box<Expr>, Error> {
    equality(tok)
}

fn equality(tok: &mut &Token) -> Result<Box<Expr>, Error> {
    let mut expr = relational(tok)?;
    loop {
        if consume(tok, "==") {
            expr = Expr::new_binary(BinaryOperator::EQ, expr, relational(tok)?);
            continue;
        }
        if consume(tok, "!=") {
            expr = Expr::new_binary(BinaryOperator::NE, expr, relational(tok)?);
            continue;
        }
        break Ok(expr);
    }
}

fn relational(tok: &mut &Token) -> Result<Box<Expr>, Error> {
    let mut expr = add(tok)?;
    loop {
        if consume(tok, "<") {
            expr = Expr::new_binary(BinaryOperator::LT, expr, add(tok)?);
            continue;
        }
        if consume(tok, "<=") {
            expr = Expr::new_binary(BinaryOperator::LE, expr, add(tok)?);
            continue;
        }
        if consume(tok, ">") {
            expr = Expr::new_binary(BinaryOperator::LT, add(tok)?, expr);
            continue;
        }
        if consume(tok, ">=") {
            expr = Expr::new_binary(BinaryOperator::LE, add(tok)?, expr);
            continue;
        }
        break Ok(expr);
    }
}

fn add(tok: &mut &Token) -> Result<Box<Expr>, Error> {
    let mut expr = mul(tok)?;
    loop {
        if consume(tok, "+") {
            expr = Expr::new_binary(BinaryOperator::ADD, expr, mul(tok)?);
            continue;
        }
        if consume(tok, "-") {
            expr = Expr::new_binary(BinaryOperator::SUB, expr, mul(tok)?);
            continue;
        }
        break Ok(expr);
    }
}

fn mul(tok: &mut &Token) -> Result<Box<Expr>, Error> {
    let mut expr = unary(tok)?;
    loop {
        if consume(tok, "*") {
            expr = Expr::new_binary(BinaryOperator::MUL, expr, unary(tok)?);
            continue;
        }
        if consume(tok, "/") {
            expr = Expr::new_binary(BinaryOperator::DIV, expr, unary(tok)?);
            continue;
        }
        break Ok(expr);
    }
}

fn unary(tok: &mut &Token) -> Result<Box<Expr>, Error> {
    if consume(tok, "+") {
        unary(tok)
    } else if consume(tok, "-") {
        Ok(Expr::new_unary(UnaryOperator::NEG, unary(tok)?))
    } else {
        primary(tok)
    }
}

fn primary(tok: &mut &Token) -> Result<Box<Expr>, Error> {
    if consume(tok, "(") {
        let expr = expr(tok)?;
        expect(tok, ")")?;
        return Ok(expr);
    }
    if let Some(val) = consume_number(tok) {
        return Ok(Expr::new_num(val));
    }
    Err(Error {
        loc: tok.loc,
        msg: "expected an expression".to_owned(),
    })
}
