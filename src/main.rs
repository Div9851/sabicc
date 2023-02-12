use sabicc::codegen;
use sabicc::error::Error;
use sabicc::parse;
use sabicc::tokenize;
use std::env;
use std::process;

fn handle_error(text: &str, err: Error) -> ! {
    eprintln!("{}", text);
    eprintln!("{}^ {}", " ".repeat(err.loc), err.msg);
    process::exit(1);
}

fn main() {
    let mut args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("{}: invalid number of arguments", args[0]);
        process::exit(1);
    }
    let text = &mut args[1];
    text.push('\0');
    let head = match tokenize::tokenize(text) {
        Ok(tok) => tok,
        Err(err) => {
            handle_error(text, err);
        }
    };
    let mut tok = head.as_ref();
    let program = match parse::program(&mut tok) {
        Ok(program) => program,
        Err(err) => {
            handle_error(text, err);
        }
    };
    if let Err(err) = codegen::gen_program(&program) {
        handle_error(text, err);
    }
}
