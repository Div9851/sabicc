use sabicc::codegen;
use sabicc::parse;
use sabicc::tokenize;
use std::{env, process};

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
            eprintln!("{}", text);
            eprintln!("{}^ {}", " ".repeat(err.loc), err.msg);
            process::exit(1);
        }
    };
    let mut rest = tok.as_ref();
    let node = match parse::expr(&mut rest) {
        Ok(node) => node,
        Err(err) => {
            eprintln!("{}", text);
            eprintln!("{}^ {}", " ".repeat(err.loc), err.msg);
            process::exit(1);
        }
    };
    println!(".intel_syntax noprefix");
    println!(".globl main");
    println!("main:");
    codegen::gen_expr(&node);
    println!("  ret")
}
