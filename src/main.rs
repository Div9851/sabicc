use sabicc::codegen;
use sabicc::codegen::CodegenContext;
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
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("{}: invalid number of arguments", args[0]);
        process::exit(1);
    }
    let text = &args[1];
    let head = match tokenize::tokenize(text) {
        Ok(tok) => tok,
        Err(err) => {
            handle_error(text, err);
        }
    };
    let mut tok = head.as_ref();
    println!(".intel_syntax noprefix");
    let mut ctx = CodegenContext { label: 0 };
    while !tokenize::at_eof(tok) {
        let f = match parse::func(&mut tok) {
            Ok(f) => f,
            Err(err) => {
                handle_error(text, err);
            }
        };
        if let Err(err) = codegen::gen_func(&f, &mut ctx) {
            handle_error(text, err);
        }
    }
}
