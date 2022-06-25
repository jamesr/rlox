use lazy_static::lazy_static;
use std::sync::Mutex;
use std::{env, io};
use std::{fs::File, io::Read, io::Write};

use crate::ast::Visitor;

pub mod ast;
pub mod error;
pub mod eval;
pub mod parser;
pub mod scanner;

fn run(source: &str) -> anyhow::Result<()> {
    let mut scanner = scanner::Scanner::new(source);
    let parser = parser::Parser::new(&mut scanner);
    let expr = parser.parse()?;
    let mut printer = ast::AstPrinter {};
    println!("{}", printer.visit_expr(&expr));
    Ok(())
}

fn run_file(filename: &str) -> anyhow::Result<()> {
    let mut file = File::open(filename)?;
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;
    run(&contents)?;
    Ok(())
}

fn run_prompt() -> anyhow::Result<()> {
    loop {
        print!("> ");
        io::stdout().flush()?;
        let mut buffer = String::new();
        io::stdin().read_line(&mut buffer)?;
        if buffer.is_empty() {
            return Ok(());
        }
        if let Err(e) = run(&buffer) {
            println!("error: {}", e);
        }
    }
}

fn main() {
    match env::args().len() {
        2 => run_file(&env::args().nth(1).unwrap()).unwrap(),
        1 => run_prompt().unwrap(),
        _ => println!("Usage: rlox [script]"),
    }
}
