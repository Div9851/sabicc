use std::{env, process::exit};

#[derive(Clone, Copy, PartialEq, Eq)]
enum TokenKind {
    PUNCT, // Punctuators
    NUM,   // Numeric literals
    EOF,   // End-of-file markers
}

// Token type
struct Token {
    kind: TokenKind,  // Token kind
    val: Option<i32>, // If kind is TK_NUM, its value
    loc: usize,       // Token location
    text: Vec<u8>,    // Token text
}

impl Token {
    fn new(kind: TokenKind, loc: usize, text: &[u8]) -> Token {
        Token {
            kind,
            val: None,
            loc,
            text: text.to_vec(),
        }
    }

    fn new_num(val: i32, loc: usize, text: &[u8]) -> Token {
        Token {
            kind: TokenKind::NUM,
            val: Some(val),
            loc,
            text: text.to_vec(),
        }
    }
}

fn get_number(tok: &Token) -> i32 {
    if tok.kind != TokenKind::NUM {
        panic!("expected a number");
    }
    tok.val.unwrap()
}

fn equal(tok: &Token, op: &[u8]) -> bool {
    tok.text == op
}

fn tokenize(text: &[u8]) -> Vec<Token> {
    let text = text.to_vec();
    let mut tokens: Vec<Token> = Vec::new();
    let mut pos = 0;

    while pos < text.len() {
        // Skip whitespace characters.
        if text[pos].is_ascii_whitespace() {
            pos += 1;
            continue;
        }

        // Numeric literal
        if text[pos].is_ascii_digit() {
            let loc = pos;
            let mut val = 0;
            while pos < text.len() && text[pos].is_ascii_digit() {
                val *= 10;
                val += (text[pos] - b'0') as i32;
                pos += 1;
            }
            let tok = Token::new_num(val, loc, &text[loc..pos]);
            tokens.push(tok);
            continue;
        }

        // Punctuator
        if text[pos] == b'+' || text[pos] == b'-' {
            let tok = Token::new(TokenKind::PUNCT, pos, &text[pos..pos + 1]);
            tokens.push(tok);
            pos += 1;
            continue;
        }

        panic!("invalid token");
    }
    tokens.push(Token::new(TokenKind::EOF, pos, b""));

    tokens
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("{}: invalid number of arguments", args[0]);
        exit(1);
    }
    let text: Vec<u8> = args[1].bytes().collect();
    let tokens = tokenize(&text);
    println!(".intel_syntax noprefix");
    println!(".globl main");
    println!("main:");
    let mut pos = 0;
    println!("  mov rax, {}", get_number(&tokens[pos]));
    pos += 1;
    while tokens[pos].kind != TokenKind::EOF {
        if equal(&tokens[pos], b"+") {
            pos += 1;
            println!("  add rax, {}", get_number(&tokens[pos]));
            pos += 1;
            continue;
        }
        if equal(&tokens[pos], b"-") {
            pos += 1;
            println!("  sub rax, {}", get_number(&tokens[pos]));
            pos += 1;
            continue;
        }
        panic!("unexpected token");
    }
    println!("  ret");
}
