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
    msg: &'static str,
}

fn get_number(tok: &Token) -> Result<i32, ParseError> {
    if tok.kind != TokenKind::NUM {
        Err(ParseError {
            loc: tok.loc,
            msg: "expected a number",
        })
    } else {
        Ok(tok.val.unwrap())
    }
}

fn equal(tok: &Token, op: &str) -> bool {
    tok.text == op
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
        if bytes[pos] == b'+' || bytes[pos] == b'-' {
            let tok = Token::new(TokenKind::PUNCT, pos, &text[pos..pos + 1]);
            cur.next = Some(tok);
            cur = cur.next.as_mut().unwrap();
            pos += 1;
            continue;
        }

        return Err(ParseError {
            loc: pos,
            msg: "invalid token",
        });
    }
    cur.next = Some(Token::new(TokenKind::EOF, pos, ""));

    Ok(head.next.unwrap())
}

fn parse(tok: &Token) -> Result<String, ParseError> {
    let mut cur = tok;
    let mut result = String::new();
    result += ".intel_syntax noprefix\n";
    result += ".globl main\n";
    result += "main:\n";
    result += &format!("  mov rax, {}\n", get_number(cur)?);
    cur = cur.next.as_ref().unwrap();
    while cur.kind != TokenKind::EOF {
        if equal(cur, "+") {
            cur = cur.next.as_ref().unwrap();
            result += &format!("  add rax, {}\n", get_number(cur)?);
            cur = cur.next.as_ref().unwrap();
            continue;
        }
        if equal(cur, "-") {
            cur = cur.next.as_ref().unwrap();
            result += &format!("  sub rax, {}\n", get_number(cur)?);
            cur = cur.next.as_ref().unwrap();
            continue;
        }
        return Err(ParseError {
            loc: cur.loc,
            msg: "unexpected token",
        });
    }
    result += "  ret";
    Ok(result)
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
    let result = match parse(&tok) {
        Ok(result) => result,
        Err(err) => {
            eprintln!("{}", text);
            eprintln!("{}^ {}", " ".repeat(err.loc), err.msg);
            exit(1);
        }
    };
    println!("{}", result);
}
