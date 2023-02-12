use crate::error::Error;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenKind {
    Ident,    // Identifiers
    Punct,    // Punctuators
    Keyword,  // Keywords
    Num(i32), // Numeric literals
    EOF,      // End-of-file markers
}

// Token type
pub struct Token {
    pub kind: TokenKind,          // Token kind
    pub next: Option<Box<Token>>, // Next token
    pub loc: usize,               // Token location
    pub text: String,             // Token text
}

impl Token {
    pub fn new(kind: TokenKind, loc: usize, text: &str) -> Box<Token> {
        Box::new(Token {
            kind,
            next: None,
            loc,
            text: text.to_owned(),
        })
    }
}

pub fn at_eof(tok: &Token) -> bool {
    if let TokenKind::EOF = tok.kind {
        true
    } else {
        false
    }
}

pub fn equal(tok: &Token, op: &str) -> bool {
    (tok.kind == TokenKind::Punct || tok.kind == TokenKind::Keyword) && tok.text == op
}

pub fn consume(tok: &mut &Token, op: &str) -> bool {
    if (tok.kind == TokenKind::Punct || tok.kind == TokenKind::Keyword) && tok.text == op {
        *tok = tok.next.as_ref().unwrap();
        true
    } else {
        false
    }
}

pub fn expect(tok: &mut &Token, op: &str) -> Result<(), Error> {
    if (tok.kind == TokenKind::Punct || tok.kind == TokenKind::Keyword) && tok.text == op {
        *tok = tok.next.as_ref().unwrap();
        Ok(())
    } else {
        Err(Error {
            loc: tok.loc,
            msg: format!("'{}' expected, got '{}'", op, tok.text),
        })
    }
}

pub fn expect_number(tok: &mut &Token) -> Result<i32, Error> {
    if let TokenKind::Num(val) = tok.kind {
        *tok = tok.next.as_ref().unwrap();
        Ok(val)
    } else {
        Err(Error {
            loc: tok.loc,
            msg: "expected a number".to_owned(),
        })
    }
}

pub fn consume_number(tok: &mut &Token) -> Option<i32> {
    if let TokenKind::Num(val) = tok.kind {
        *tok = tok.next.as_ref().unwrap();
        Some(val)
    } else {
        None
    }
}

pub fn consume_ident<'a>(tok: &mut &'a Token) -> Option<&'a Token> {
    if tok.kind == TokenKind::Ident {
        let ident = *tok;
        *tok = tok.next.as_ref().unwrap();
        Some(ident)
    } else {
        None
    }
}

// Returns true if c is valid as the first character of an identifier.
fn is_ident1(c: u8) -> bool {
    (b'a' <= c && c <= b'z') || (b'A' <= c && c <= b'Z') || c == b'_'
}

// Returns true if c is valid as the non-first character of an identifier.
fn is_ident2(c: u8) -> bool {
    is_ident1(c) || (b'0' <= c && c <= b'9')
}

// Read a punctuator token and returns its length.
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

fn convert_keyword(tok: &mut Token) {
    if tok.text == "return"
        || tok.text == "if"
        || tok.text == "else"
        || tok.text == "for"
        || tok.text == "while"
        || tok.text == "sizeof"
        || tok.text == "int"
        || tok.text == "char"
    {
        tok.kind = TokenKind::Keyword;
    }
}

pub fn tokenize(text: &str) -> Result<Box<Token>, Error> {
    let mut head = Token::new(TokenKind::Punct, 0, "");
    let mut cur = head.as_mut();
    let bytes = text.as_bytes();
    let mut pos = 0;

    while pos < bytes.len() {
        // Skip whitespace characters.
        if bytes[pos].is_ascii_whitespace() {
            pos += 1;
            continue;
        }

        // Numeric literal
        if bytes[pos].is_ascii_digit() {
            let loc = pos;
            while pos < bytes.len() && bytes[pos].is_ascii_digit() {
                pos += 1;
            }
            let val = i32::from_str_radix(&text[loc..pos], 10).unwrap();
            let tok = Token::new(TokenKind::Num(val), loc, &text[loc..pos]);
            cur.next = Some(tok);
            cur = cur.next.as_mut().unwrap();
            continue;
        }

        // Punctuator
        let punct_len = read_punct(&bytes[pos..]);
        if punct_len > 0 {
            let tok = Token::new(TokenKind::Punct, pos, &text[pos..pos + punct_len]);
            cur.next = Some(tok);
            cur = cur.next.as_mut().unwrap();
            pos += punct_len;
            continue;
        }

        // Identifier or keyword
        if is_ident1(bytes[pos]) {
            let loc = pos;
            while pos < text.len() && is_ident2(bytes[pos]) {
                pos += 1;
            }
            let mut tok = Token::new(TokenKind::Ident, loc, &text[loc..pos]);
            convert_keyword(&mut tok);
            cur.next = Some(tok);
            cur = cur.next.as_mut().unwrap();
            continue;
        }

        return Err(Error {
            loc: pos,
            msg: "invalid token".to_owned(),
        });
    }
    cur.next = Some(Token::new(TokenKind::EOF, pos, ""));

    Ok(head.next.unwrap())
}
