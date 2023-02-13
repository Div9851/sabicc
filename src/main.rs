use anyhow::{bail, Result};
use sabicc::codegen;
use sabicc::parse;
use std::env;
use std::fs::File;
use std::io::{self, Read};

fn read_file(path: &str) -> Result<String> {
    let mut buf = String::new();
    if path == "-" {
        io::stdin().read_to_string(&mut buf)?;
    } else {
        File::open(path)?.read_to_string(&mut buf)?;
    }
    buf.push('\0');
    Ok(buf)
}

fn main() -> Result<()> {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        bail!("{}: invalid number of arguments", args[0]);
    }
    let path = &args[1];
    let text = read_file(path)?;
    let mut program = parse::program(text)?;
    codegen::gen_program(&mut program)?;
    Ok(())
}
