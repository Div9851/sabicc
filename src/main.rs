use anyhow::{bail, Context as _, Result};
use sabicc::codegen;
use sabicc::parse;
use std::env::{self, Args};
use std::fs::File;
use std::io::Write;
use std::io::{self, Read};
use std::process;

fn read_file(path: &str) -> Result<String> {
    let mut buf = String::new();
    if path == "-" {
        io::stdin().read_to_string(&mut buf)?;
    } else {
        File::open(path)
            .with_context(|| format!("cannot open '{}'", path))?
            .read_to_string(&mut buf)?;
    }
    buf.push('\0');
    Ok(buf)
}

fn write_file(path: Option<&str>, text: &str) -> Result<()> {
    if let Some(path) = path {
        File::create(path)
            .with_context(|| format!("cannot open '{}'", path))?
            .write_all(text.as_bytes())?;
    } else {
        io::stdout().write_all(text.as_bytes())?;
    }
    Ok(())
}

fn usage(code: i32) {
    eprintln!("sabicc [ -o <path> ] <file>");
    process::exit(code);
}

struct Config {
    input_path: String,
    output_path: Option<String>,
}

fn parse_args(mut args: Args) -> Result<Config> {
    let mut input_path = None;
    let mut output_path = None;
    args.next();
    while let Some(arg) = args.next() {
        if arg == "--help" {
            usage(0);
        }
        if arg == "-o" {
            if let Some(path) = args.next() {
                output_path = Some(path);
            } else {
                usage(1);
            }
            continue;
        }
        if arg.starts_with("-o") {
            output_path = Some(arg[2..].to_owned());
            continue;
        }
        if arg != "-" && arg.starts_with("-") {
            bail!("unknown argument: {}", arg);
        }
        input_path = Some(arg);
    }
    if matches!(input_path, None) {
        bail!("no input files");
    }
    Ok(Config {
        input_path: input_path.unwrap(),
        output_path,
    })
}

fn main() -> Result<()> {
    let config = parse_args(env::args())?;
    let text = read_file(&config.input_path)?;
    let mut program = parse::program(text, &config.input_path)?;
    write_file(
        config.output_path.as_deref(),
        &codegen::gen_program(&mut program)?,
    )?;
    Ok(())
}
