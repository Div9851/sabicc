use std::{env, process::exit};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TokenKind {
    PUNCT, // Punctuators
    NUM,   // Numeric literals
    EOF,   // End-of-file markers
}

// Token type
struct Token {
    kind: TokenKind,          // Token kind
    next: Option<Box<Token>>, // Next token
    val: Option<i32>,         // If kind is TK_NUM, its value
    loc: usize,               // Token location
    text: String,             // Token text
}

impl Token {
    fn new(kind: TokenKind, loc: usize, text: &str) -> Box<Token> {
        Box::new(Token {
            kind,
            next: None,
            val: None,
            loc,
            text: text.to_owned(),
        })
    }

    fn new_num(val: i32, loc: usize, text: &str) -> Box<Token> {
        Box::new(Token {
            kind: TokenKind::NUM,
            next: None,
            val: Some(val),
            loc,
            text: text.to_owned(),
        })
    }
}

#[derive(Debug)]
struct ParseError {
    loc: usize,
    msg: String,
}

fn consume(tok: &mut &Token, op: &str) -> bool {
    if tok.kind == TokenKind::PUNCT && tok.text == op {
        *tok = tok.next.as_ref().unwrap();
        true
    } else {
        false
    }
}

fn expect(tok: &mut &Token, op: &str) -> Result<(), ParseError> {
    if tok.kind == TokenKind::PUNCT && tok.text == op {
        *tok = tok.next.as_ref().unwrap();
        Ok(())
    } else {
        Err(ParseError {
            loc: tok.loc,
            msg: format!("'{}' expected", op),
        })
    }
}

fn expect_number(tok: &mut &Token) -> Result<i32, ParseError> {
    if tok.kind == TokenKind::NUM {
        let num = tok.val.unwrap();
        *tok = tok.next.as_ref().unwrap();
        Ok(num)
    } else {
        Err(ParseError {
            loc: tok.loc,
            msg: "expected a number".to_owned(),
        })
    }
}

fn tokenize(text: &str) -> Result<Box<Token>, ParseError> {
    let mut head = Token::new(TokenKind::PUNCT, 0, "");
    let mut cur = head.as_mut();
    let bytes = text.as_bytes();
    let mut pos = 0;

    while pos < text.len() {
        // Skip whitespace characters.
        if bytes[pos].is_ascii_whitespace() {
            pos += 1;
            continue;
        }

        // Numeric literal
        if bytes[pos].is_ascii_digit() {
            let loc = pos;
            while pos < text.len() && bytes[pos].is_ascii_digit() {
                pos += 1;
            }
            let val = i32::from_str_radix(&text[loc..pos], 10).unwrap();
            let tok = Token::new_num(val, loc, &text[loc..pos]);
            cur.next = Some(tok);
            cur = cur.next.as_mut().unwrap();
            continue;
        }

        // Punctuator
        if bytes[pos] == b'+'
            || bytes[pos] == b'-'
            || bytes[pos] == b'*'
            || bytes[pos] == b'/'
            || bytes[pos] == b'('
            || bytes[pos] == b')'
        {
            let tok = Token::new(TokenKind::PUNCT, pos, &text[pos..pos + 1]);
            cur.next = Some(tok);
            cur = cur.next.as_mut().unwrap();
            pos += 1;
            continue;
        }

        return Err(ParseError {
            loc: pos,
            msg: "invalid token".to_owned(),
        });
    }
    cur.next = Some(Token::new(TokenKind::EOF, pos, ""));

    Ok(head.next.unwrap())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NodeKind {
    ADD, // +
    SUB, // -
    MUL, // *
    DIV, // /
    NUM, // Integer
}

struct Node {
    kind: NodeKind,         // Node kind
    lhs: Option<Box<Node>>, // Left-hand side
    rhs: Option<Box<Node>>, // Right-hand side
    val: Option<i32>,       // Used if kind == ND_NUM
}

impl Node {
    fn new(kind: NodeKind, lhs: Box<Node>, rhs: Box<Node>) -> Box<Node> {
        Box::new(Node {
            kind,
            lhs: Some(lhs),
            rhs: Some(rhs),
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

fn expr(tok: &mut &Token) -> Result<Box<Node>, ParseError> {
    let mut node = mul(tok)?;
    loop {
        if consume(tok, "+") {
            node = Node::new(NodeKind::ADD, node, mul(tok)?);
            continue;
        }
        if consume(tok, "-") {
            node = Node::new(NodeKind::SUB, node, mul(tok)?);
            continue;
        }
        break Ok(node);
    }
}

fn mul(tok: &mut &Token) -> Result<Box<Node>, ParseError> {
    let mut node = primary(tok)?;
    loop {
        if consume(tok, "*") {
            node = Node::new(NodeKind::MUL, node, primary(tok)?);
            continue;
        }
        if consume(tok, "/") {
            node = Node::new(NodeKind::DIV, node, primary(tok)?);
            continue;
        }
        break Ok(node);
    }
}

fn primary(tok: &mut &Token) -> Result<Box<Node>, ParseError> {
    if consume(tok, "(") {
        let node = expr(tok)?;
        expect(tok, ")")?;
        Ok(node)
    } else {
        Ok(Node::new_num(expect_number(tok)?))
    }
}

fn gen(node: &Node) {
    if node.kind == NodeKind::NUM {
        println!("  push {}", node.val.unwrap());
        return;
    }
    gen(node.lhs.as_ref().unwrap());
    gen(node.rhs.as_ref().unwrap());
    println!("  pop rdi");
    println!("  pop rax");
    match node.kind {
        NodeKind::ADD => {
            println!("  add rax, rdi");
        }
        NodeKind::SUB => {
            println!("  sub rax, rdi");
        }
        NodeKind::MUL => {
            println!("  imul rax, rdi");
        }
        NodeKind::DIV => {
            println!("  cqo");
            println!("  idiv rdi");
        }
        _ => {}
    };
    println!("  push rax");
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("{}: invalid number of arguments", args[0]);
        exit(1);
    }
    let text = &args[1];
    let tok = match tokenize(text) {
        Ok(tok) => tok,
        Err(err) => {
            eprintln!("{}", text);
            eprintln!("{}^ {}", " ".repeat(err.loc), err.msg);
            exit(1);
        }
    };
    let mut rest = tok.as_ref();
    let node = match expr(&mut rest) {
        Ok(node) => node,
        Err(err) => {
            eprintln!("{}", text);
            eprintln!("{}^ {}", " ".repeat(err.loc), err.msg);
            exit(1);
        }
    };
    println!(".intel_syntax noprefix");
    println!(".globl main");
    println!("main:");
    gen(&node);
    println!("  pop rax");
    println!("  ret")
}
