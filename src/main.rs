use lazy_static::lazy_static;
use std::sync::Mutex;
use std::{env, io};
use std::{fs::File, io::Read, io::Write};

use crate::ast::Visitor;

pub mod ast;
pub mod parser;
pub mod scanner;

lazy_static! {
    static ref HAS_ERROR: Mutex<bool> = Mutex::new(false);
}

fn run(source: &str) -> anyhow::Result<()> {
    let mut scanner = scanner::Scanner::new(source);
    let parser = parser::Parser::new(&mut scanner);
    let expr = parser.parse();
    let mut printer = ast::AstPrinter {};
    println!("{}", printer.visit_expr(&expr));
    Ok(())
}

fn run_file(filename: &str) -> anyhow::Result<()> {
    let mut file = File::open(filename)?;
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;
    run(&contents)?;
    if *HAS_ERROR.lock().unwrap() {
        std::process::exit(65);
    }
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
        match run(buffer.trim_end()) {
            Ok(_) => {}
            Err(e) => return Err(e),
        }
        *HAS_ERROR.lock().unwrap() = false;
    }
}

fn error(line: usize, message: &str) {
    report(line, "", message);
}

fn report(line: usize, location: &str, message: &str) {
    println!("[line {}] Error {}: {}", line, location, message);
    *HAS_ERROR.lock().unwrap() = true;
}

fn main() {
    match env::args().len() {
        2 => run_file(&env::args().nth(1).unwrap()).unwrap(),
        1 => run_prompt().unwrap(),
        _ => println!("Usage: rlox [script]"),
    }
}
