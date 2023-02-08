use std::{env, process::exit};

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("{}: invalid number of arguments", args[0]);
        exit(1);
    }
    let n = u8::from_str_radix(&args[1], 10).unwrap();
    println!(".intel_syntax noprefix");
    println!(".globl main");
    println!("");
    println!("main:");
    println!("  mov rax, {}", n);
    println!("  ret");
}
