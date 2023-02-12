use crate::error::CompileError;

#[derive(Debug, PartialEq, Eq)]
pub enum TokenKind {
    Ident,        // Identifiers
    Punct,        // Punctuators
    Keyword,      // Keywords
    Str(Vec<u8>), // String literals
    Num(i32),     // Numeric literals
    EOF,          // End-of-file markers
}

// Token type
pub struct Token {
    pub kind: TokenKind,          // Token kind
    pub next: Option<Box<Token>>, // Next token
    pub loc: usize,               // Token location
    pub text: String,             // Token bytes
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

pub fn expect(tok: &mut &Token, op: &str) -> Result<(), CompileError> {
    if (tok.kind == TokenKind::Punct || tok.kind == TokenKind::Keyword) && tok.text == op {
        *tok = tok.next.as_ref().unwrap();
        Ok(())
    } else {
        Err(CompileError {
            loc: tok.loc,
            msg: format!("'{}' expected, got '{}'", op, tok.text),
        })
    }
}

pub fn expect_number(tok: &mut &Token) -> Result<i32, CompileError> {
    if let TokenKind::Num(val) = tok.kind {
        *tok = tok.next.as_ref().unwrap();
        Ok(val)
    } else {
        Err(CompileError {
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

pub fn consume_str<'a>(tok: &mut &'a Token) -> Option<&'a Vec<u8>> {
    if let TokenKind::Str(bytes) = &tok.kind {
        *tok = tok.next.as_ref().unwrap();
        Some(bytes)
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

fn is_octdigit(ch: u8) -> bool {
    b'0' <= ch && ch <= b'7'
}

fn is_hexdigit(ch: u8) -> bool {
    (b'0' <= ch && ch <= b'9') || (b'a' <= ch && ch <= b'f') || (b'A' <= ch && ch <= b'F')
}

fn from_hex(ch: u8) -> u8 {
    if b'0' <= ch && ch <= b'9' {
        ch - b'0'
    } else if b'a' <= ch && ch <= b'f' {
        ch - b'a' + 10
    } else {
        ch - b'A' + 10
    }
}

fn read_escaped_char(bytes: &[u8], pos: &mut usize) -> Result<u8, CompileError> {
    if bytes[*pos] == b'\0' {
        return Err(CompileError {
            loc: *pos,
            msg: "unexpected end of file".to_owned(),
        });
    }
    if is_octdigit(bytes[*pos]) {
        let mut c = bytes[*pos] - b'0';
        *pos += 1;
        if is_octdigit(bytes[*pos]) {
            c = c * 8 + (bytes[*pos] - b'0');
            *pos += 1;
            if is_octdigit(bytes[*pos]) {
                c = c * 8 + (bytes[*pos] - b'0');
                *pos += 1;
            }
        }
        Ok(c)
    } else if bytes[*pos] == b'x' {
        // Read a hexadecimal number.
        *pos += 1;
        if is_hexdigit(bytes[*pos]) {
            let mut c = 0;
            while is_hexdigit(bytes[*pos]) {
                c = (c << 4) + from_hex(bytes[*pos]);
                *pos += 1;
            }
            Ok(c)
        } else {
            Err(CompileError {
                loc: *pos,
                msg: "invalid hex escape sequence".to_owned(),
            })
        }
    } else if bytes[*pos] == b'a' {
        *pos += 1;
        Ok(7)
    } else if bytes[*pos] == b'b' {
        *pos += 1;
        Ok(8)
    } else if bytes[*pos] == b't' {
        *pos += 1;
        Ok(b'\t')
    } else if bytes[*pos] == b'n' {
        *pos += 1;
        Ok(b'\n')
    } else if bytes[*pos] == b'v' {
        *pos += 1;
        Ok(11)
    } else if bytes[*pos] == b'f' {
        *pos += 1;
        Ok(12)
    } else if bytes[*pos] == b'r' {
        *pos += 1;
        Ok(b'\r')
    } else if bytes[*pos] == b'e' {
        *pos += 1;
        Ok(27)
    } else {
        let ch = bytes[*pos];
        *pos += 1;
        Ok(ch)
    }
}

fn read_string_literal(bytes: &[u8], pos: &mut usize) -> Result<Vec<u8>, CompileError> {
    let mut s = Vec::new();
    while bytes[*pos] != b'\0' {
        if bytes[*pos] == b'"' {
            *pos += 1;
            return Ok(s);
        }
        if bytes[*pos] == b'\n' {
            break;
        }
        if bytes[*pos] == b'\\' {
            *pos += 1;
            let ch = read_escaped_char(bytes, pos)?;
            s.push(ch);
            continue;
        }
        s.push(bytes[*pos]);
        *pos += 1;
    }
    Err(CompileError {
        loc: *pos,
        msg: "unclosed string literal".to_owned(),
    })
}

pub fn tokenize(text: &str) -> Result<Box<Token>, CompileError> {
    let mut head = Token::new(TokenKind::Punct, 0, "");
    let mut cur = head.as_mut();
    let mut pos = 0;

    let bytes = text.as_bytes();
    while bytes[pos] != b'\0' {
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

        // String literal
        if bytes[pos] == b'"' {
            pos += 1;
            let loc = pos;
            let bytes = read_string_literal(bytes, &mut pos)?;
            let tok = Token::new(TokenKind::Str(bytes), loc, "");
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
            while pos < bytes.len() && is_ident2(bytes[pos]) {
                pos += 1;
            }
            let mut tok = Token::new(TokenKind::Ident, loc, &text[loc..pos]);
            convert_keyword(&mut tok);
            cur.next = Some(tok);
            cur = cur.next.as_mut().unwrap();
            continue;
        }

        return Err(CompileError {
            loc: pos,
            msg: "invalid token".to_owned(),
        });
    }
    cur.next = Some(Token::new(TokenKind::EOF, pos, ""));

    Ok(head.next.unwrap())
}
