use sabicc::codegen;
use sabicc::error::Error;
use sabicc::parse;
use sabicc::tokenize;
use sabicc::tokenize::TokenKind;
use std::env;
use std::process;

fn handle_error(text: &str, err: Error) -> ! {
    eprintln!("{}", text);
    eprintln!("{}^ {}", " ".repeat(err.loc), err.msg);
    process::exit(1);
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("{}: invalid number of arguments", args[0]);
        process::exit(1);
    }
    let text = &args[1];
    let tok = match tokenize::tokenize(text) {
        Ok(tok) => tok,
        Err(err) => {
            handle_error(text, err);
        }
    };
    let mut rest = tok.as_ref();
    let mut stmt_vec = Vec::new();
    while rest.kind != TokenKind::EOF {
        let stmt = match parse::stmt(&mut rest) {
            Ok(stmt) => stmt,
            Err(err) => handle_error(text, err),
        };
        stmt_vec.push(stmt);
    }
    println!(".intel_syntax noprefix");
    println!(".globl main");
    println!("main:");
    // Prologue
    println!("  push rbp");
    println!("  mov rbp, rsp");
    println!("  sub rsp, 208");
    for stmt in &stmt_vec {
        if let Err(err) = codegen::gen_stmt(stmt) {
            handle_error(text, err);
        }
    }
    // Epilogue
    println!("  mov rsp, rbp");
    println!("  pop rbp");
    println!("  ret")
}
