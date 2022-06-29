use std::io;
use std::{fs::File, io::Read, io::Write};

use eval::Interpreter;

pub mod ast;
pub mod env;
pub mod error;
pub mod eval;
pub mod parser;
pub mod scanner;
pub mod visitor;

fn run(source: &str, interpreter: &mut Interpreter) -> anyhow::Result<(), error::Error> {
    let stmts = parser::parse(source)?;
    interpreter.interpret(stmts)?;
    Ok(())
}

fn run_file(filename: &str) -> anyhow::Result<(), error::Error> {
    let mut file = File::open(filename)?;
    let mut contents = String::new();
    let mut interpreter = Interpreter::new();
    file.read_to_string(&mut contents)?;
    run(&contents, &mut interpreter)?;
    Ok(())
}

fn run_prompt() -> anyhow::Result<(), error::Error> {
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
        2 => run_file(&std::env::args().nth(1).unwrap()).unwrap(),
        1 => run_prompt().unwrap(),
        _ => println!("Usage: rlox [script]"),
    }
}
