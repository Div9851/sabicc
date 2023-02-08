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

fn consume_number(tok: &mut &Token) -> Option<i32> {
    if tok.kind == TokenKind::NUM {
        let num = tok.val.unwrap();
        *tok = tok.next.as_ref().unwrap();
        Some(num)
    } else {
        None
    }
}

fn read_punct(bytes: &[u8]) -> usize {
    if bytes.starts_with(b"==")
        || bytes.starts_with(b"!=")
        || bytes.starts_with(b"<=")
        || bytes.starts_with(b">=")
    {
        2
    } else if bytes[0].is_ascii_punctuation() {
        1
    } else {
        0
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
        let punct_len = read_punct(&bytes[pos..]);
        if punct_len > 0 {
            let tok = Token::new(TokenKind::PUNCT, pos, &text[pos..pos + punct_len]);
            cur.next = Some(tok);
            cur = cur.next.as_mut().unwrap();
            pos += punct_len;
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
    NEG, // unary -
    EQ,  // ==
    NE,  // !=
    LT,  // <
    LE,  // <=
    NUM, // Integer
}

struct Node {
    kind: NodeKind,         // Node kind
    lhs: Option<Box<Node>>, // Left-hand side
    rhs: Option<Box<Node>>, // Right-hand side
    val: Option<i32>,       // Used if kind == ND_NUM
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

fn expr(tok: &mut &Token) -> Result<Box<Node>, ParseError> {
    equality(tok)
}

fn equality(tok: &mut &Token) -> Result<Box<Node>, ParseError> {
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

fn relational(tok: &mut &Token) -> Result<Box<Node>, ParseError> {
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

fn add(tok: &mut &Token) -> Result<Box<Node>, ParseError> {
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

fn mul(tok: &mut &Token) -> Result<Box<Node>, ParseError> {
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

fn unary(tok: &mut &Token) -> Result<Box<Node>, ParseError> {
    if consume(tok, "+") {
        unary(tok)
    } else if consume(tok, "-") {
        Ok(Node::new_unary(NodeKind::NEG, unary(tok)?))
    } else {
        primary(tok)
    }
}

fn primary(tok: &mut &Token) -> Result<Box<Node>, ParseError> {
    if consume(tok, "(") {
        let node = expr(tok)?;
        expect(tok, ")")?;
        return Ok(node);
    }
    if let Some(val) = consume_number(tok) {
        return Ok(Node::new_num(val));
    }
    Err(ParseError {
        loc: tok.loc,
        msg: "expected an expression".to_owned(),
    })
}

fn push() {
    println!("  push rax");
}

fn pop(reg: &str) {
    println!("  pop {}", reg);
}

fn gen_expr(node: &Node) {
    if node.kind == NodeKind::NUM {
        println!("  mov rax, {}", node.val.unwrap());
        return;
    }
    if node.kind == NodeKind::NEG {
        gen_expr(node.lhs.as_ref().unwrap());
        println!("  neg rax");
        return;
    }
    gen_expr(node.rhs.as_ref().unwrap());
    push();
    gen_expr(node.lhs.as_ref().unwrap());
    pop("rdi");
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
        NodeKind::EQ => {
            println!("  cmp rax, rdi");
            println!("  sete al");
            println!("  movzb rax, al");
        }
        NodeKind::NE => {
            println!("  cmp rax, rdi");
            println!("  setne al");
            println!("  movzb rax, al");
        }
        NodeKind::LT => {
            println!("  cmp rax, rdi");
            println!("  setl al");
            println!("  movzb rax, al");
        }
        NodeKind::LE => {
            println!("  cmp rax, rdi");
            println!("  setle al");
            println!("  movzb rax, al");
        }
        _ => {
            panic!("NodeKind::{:?} is missing", node.kind);
        }
    };
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
    gen_expr(&node);
    println!("  ret")
}
