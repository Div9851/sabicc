use crate::error::Error;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenKind {
    Punct,    // Punctuators
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

pub fn tokenize(text: &str) -> Result<Box<Token>, Error> {
    let mut head = Token::new(TokenKind::Punct, 0, "");
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

        return Err(Error {
            loc: pos,
            msg: "invalid token".to_owned(),
        });
    }
    cur.next = Some(Token::new(TokenKind::EOF, pos, ""));

    Ok(head.next.unwrap())
}
