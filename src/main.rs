use sabicc::codegen;
use sabicc::error::CompileError;
use sabicc::parse;
use sabicc::tokenize;
use std::env;
use std::error::Error;
use std::fs::File;
use std::io::{self, Read};
use std::process;

fn handle_error(text: &str, err: CompileError) -> ! {
    eprintln!("{}", text);
    eprintln!("{}^ {}", " ".repeat(err.loc), err.msg);
    process::exit(1);
}

fn read_to_string(path: &str) -> Result<String, Box<dyn Error>> {
    let mut buf = String::new();
    let mut reader: Box<dyn Read>;
    if path == "-" {
        reader = Box::new(io::stdin());
    } else {
        reader = Box::new(File::open(path)?);
    }
    reader.read_to_string(&mut buf)?;
    Ok(buf)
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("{}: invalid number of arguments", args[0]);
        process::exit(1);
    }
    let path = &args[1];
    let mut text = match read_to_string(path) {
        Ok(text) => text,
        Err(err) => {
            eprintln!("{}", err);
            process::exit(1);
        }
    };
    text.push('\0');
    let head = match tokenize::tokenize(&text) {
        Ok(tok) => tok,
        Err(err) => {
            handle_error(&text, err);
        }
    };
    let mut tok = head.as_ref();
    let program = match parse::program(&mut tok) {
        Ok(program) => program,
        Err(err) => {
            handle_error(&text, err);
        }
    };
    if let Err(err) = codegen::gen_program(&program) {
        handle_error(&text, err);
    }
}
