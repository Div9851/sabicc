use crate::error::Error;
use crate::tokenize::{Token, TokenKind};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NodeKind {
    ADD, // +
    SUB, // -
    MUL, // *
    DIV, // /
    NEG, // unary -
    EQ,  // ==
    NE,  // !=
    LT,  // <
    LE,  // <=
    NUM, // Integer
}

pub struct Node {
    pub kind: NodeKind,         // Node kind
    pub lhs: Option<Box<Node>>, // Left-hand side
    pub rhs: Option<Box<Node>>, // Right-hand side
    pub val: Option<i32>,       // Used if kind == ND_NUM
}

impl Node {
    fn new_binary(kind: NodeKind, lhs: Box<Node>, rhs: Box<Node>) -> Box<Node> {
        Box::new(Node {
            kind,
            lhs: Some(lhs),
            rhs: Some(rhs),
            val: None,
        })
    }
    fn new_unary(kind: NodeKind, expr: Box<Node>) -> Box<Node> {
        Box::new(Node {
            kind,
            lhs: Some(expr),
            rhs: None,
            val: None,
        })
    }
    fn new_num(val: i32) -> Box<Node> {
        Box::new(Node {
            kind: NodeKind::NUM,
            lhs: None,
            rhs: None,
            val: Some(val),
        })
    }
}

fn consume(tok: &mut &Token, op: &str) -> bool {
    if tok.kind == TokenKind::PUNCT && tok.text == op {
        *tok = tok.next.as_ref().unwrap();
        true
    } else {
        false
    }
}

fn expect(tok: &mut &Token, op: &str) -> Result<(), Error> {
    if tok.kind == TokenKind::PUNCT && tok.text == op {
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
    if tok.kind == TokenKind::NUM {
        let num = tok.val.unwrap();
        *tok = tok.next.as_ref().unwrap();
        Some(num)
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
            node = Node::new_binary(NodeKind::EQ, node, relational(tok)?);
            continue;
        }
        if consume(tok, "!=") {
            node = Node::new_binary(NodeKind::NE, node, relational(tok)?);
            continue;
        }
        break Ok(node);
    }
}

fn relational(tok: &mut &Token) -> Result<Box<Node>, Error> {
    let mut node = add(tok)?;
    loop {
        if consume(tok, "<") {
            node = Node::new_binary(NodeKind::LT, node, add(tok)?);
            continue;
        }
        if consume(tok, "<=") {
            node = Node::new_binary(NodeKind::LE, node, add(tok)?);
            continue;
        }
        if consume(tok, ">") {
            node = Node::new_binary(NodeKind::LT, add(tok)?, node);
            continue;
        }
        if consume(tok, ">=") {
            node = Node::new_binary(NodeKind::LE, add(tok)?, node);
            continue;
        }
        break Ok(node);
    }
}

fn add(tok: &mut &Token) -> Result<Box<Node>, Error> {
    let mut node = mul(tok)?;
    loop {
        if consume(tok, "+") {
            node = Node::new_binary(NodeKind::ADD, node, mul(tok)?);
            continue;
        }
        if consume(tok, "-") {
            node = Node::new_binary(NodeKind::SUB, node, mul(tok)?);
            continue;
        }
        break Ok(node);
    }
}

fn mul(tok: &mut &Token) -> Result<Box<Node>, Error> {
    let mut node = unary(tok)?;
    loop {
        if consume(tok, "*") {
            node = Node::new_binary(NodeKind::MUL, node, unary(tok)?);
            continue;
        }
        if consume(tok, "/") {
            node = Node::new_binary(NodeKind::DIV, node, unary(tok)?);
            continue;
        }
        break Ok(node);
    }
}

fn unary(tok: &mut &Token) -> Result<Box<Node>, Error> {
    if consume(tok, "+") {
        unary(tok)
    } else if consume(tok, "-") {
        Ok(Node::new_unary(NodeKind::NEG, unary(tok)?))
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
