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

pub enum Node {
    Binary {
        op: BinaryOperator,
        lhs: Box<Node>,
        rhs: Box<Node>,
    },
    Unary {
        op: UnaryOperator,
        expr: Box<Node>,
    },
    Num(i32),
}

impl Node {
    fn new_binary(op: BinaryOperator, lhs: Box<Node>, rhs: Box<Node>) -> Box<Node> {
        Box::new(Node::Binary { op, lhs, rhs })
    }
    fn new_unary(op: UnaryOperator, expr: Box<Node>) -> Box<Node> {
        Box::new(Node::Unary { op, expr })
    }
    fn new_num(val: i32) -> Box<Node> {
        Box::new(Node::Num(val))
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

pub fn expr(tok: &mut &Token) -> Result<Box<Node>, Error> {
    equality(tok)
}

fn equality(tok: &mut &Token) -> Result<Box<Node>, Error> {
    let mut node = relational(tok)?;
    loop {
        if consume(tok, "==") {
            node = Node::new_binary(BinaryOperator::EQ, node, relational(tok)?);
            continue;
        }
        if consume(tok, "!=") {
            node = Node::new_binary(BinaryOperator::NE, node, relational(tok)?);
            continue;
        }
        break Ok(node);
    }
}

fn relational(tok: &mut &Token) -> Result<Box<Node>, Error> {
    let mut node = add(tok)?;
    loop {
        if consume(tok, "<") {
            node = Node::new_binary(BinaryOperator::LT, node, add(tok)?);
            continue;
        }
        if consume(tok, "<=") {
            node = Node::new_binary(BinaryOperator::LE, node, add(tok)?);
            continue;
        }
        if consume(tok, ">") {
            node = Node::new_binary(BinaryOperator::LT, add(tok)?, node);
            continue;
        }
        if consume(tok, ">=") {
            node = Node::new_binary(BinaryOperator::LE, add(tok)?, node);
            continue;
        }
        break Ok(node);
    }
}

fn add(tok: &mut &Token) -> Result<Box<Node>, Error> {
    let mut node = mul(tok)?;
    loop {
        if consume(tok, "+") {
            node = Node::new_binary(BinaryOperator::ADD, node, mul(tok)?);
            continue;
        }
        if consume(tok, "-") {
            node = Node::new_binary(BinaryOperator::SUB, node, mul(tok)?);
            continue;
        }
        break Ok(node);
    }
}

fn mul(tok: &mut &Token) -> Result<Box<Node>, Error> {
    let mut node = unary(tok)?;
    loop {
        if consume(tok, "*") {
            node = Node::new_binary(BinaryOperator::MUL, node, unary(tok)?);
            continue;
        }
        if consume(tok, "/") {
            node = Node::new_binary(BinaryOperator::DIV, node, unary(tok)?);
            continue;
        }
        break Ok(node);
    }
}

fn unary(tok: &mut &Token) -> Result<Box<Node>, Error> {
    if consume(tok, "+") {
        unary(tok)
    } else if consume(tok, "-") {
        Ok(Node::new_unary(UnaryOperator::NEG, unary(tok)?))
    } else {
        primary(tok)
    }
}

fn primary(tok: &mut &Token) -> Result<Box<Node>, Error> {
    if consume(tok, "(") {
        let node = expr(tok)?;
        expect(tok, ")")?;
        return Ok(node);
    }
    if let Some(val) = consume_number(tok) {
        return Ok(Node::new_num(val));
    }
    Err(Error {
        loc: tok.loc,
        msg: "expected an expression".to_owned(),
    })
}
