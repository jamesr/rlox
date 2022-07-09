use std::io;
use std::{fs::File, io::Read, io::Write};

use eval::Interpreter;

pub mod ast;
pub mod class;
pub mod compiler;
pub mod env;
pub mod error;
pub mod eval;
pub mod function;
pub mod parser;
pub mod resolver;
pub mod scanner;
pub mod visitor;
pub mod vm;

fn run(source: &str, interpreter: &mut Interpreter) -> Result<(), error::Error> {
    let scanner = scanner::Scanner::new(source);
    let mut parser = parser::Parser::new(scanner);
    let stmts = match parser.parse() {
        Ok(s) => s,
        Err(v) => {
            return Err(error::convert_parse(&v));
        }
    };
    let location_table = parser.take_location_table();
    let mut resolver = resolver::Resolver::new(interpreter, &location_table);
    resolver.resolve(&stmts)?;
    interpreter.interpret(&stmts, location_table)?;
    if interpreter.has_error() {
        for e in interpreter.errors() {
            println!("{}", e);
        }
        return Err(error::Error::Runtime(error::RuntimeError::new(
            "interpretation failed",
            error::Location::default(),
        )));
    }
    Ok(())
}

fn run_file(filename: &str) -> Result<(), error::Error> {
    let mut file = File::open(filename)?;
    let mut contents = String::new();
    let mut interpreter = Interpreter::new();
    file.read_to_string(&mut contents)?;
    run(&contents, &mut interpreter)?;
    Ok(())
}

fn run_prompt() -> Result<(), error::Error> {
    let mut interpreter = Interpreter::new();
    loop {
        print!("> ");
        io::stdout().flush()?;
        let mut buffer = String::new();
        io::stdin().read_line(&mut buffer)?;
        if buffer.is_empty() {
            return Ok(());
        }
        if let Err(e) = run(&buffer, &mut interpreter) {
            println!("error: {}", e);
        }
    }
}

fn main() {
    match std::env::args().len() {
        2 => match run_file(&std::env::args().nth(1).unwrap()) {
            Ok(_) => {}
            Err(e) => match e {
                error::Error::Parse(_) => {
                    _ = write!(std::io::stderr(), "{}\n", &e);
                    std::process::exit(65);
                }
                error::Error::Runtime(_) => {
                    _ = write!(std::io::stderr(), "{}\n[line 1]\n", &e);
                    std::process::exit(70);
                }
                error::Error::CompileError => {
                    _ = write!(std::io::stderr(), "compile error\n");
                    std::process::exit(75);
                }
            },
        },
        1 => run_prompt().unwrap(),
        _ => println!("Usage: rlox [script]"),
    }
}
