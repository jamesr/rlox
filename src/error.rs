use std::ops::Range;

use anyhow::anyhow;

#[derive(Default, Debug)]
pub struct Location {
    pub line: usize,
    pub col: Range<usize>,
}

#[derive(Debug, Default)]
pub struct ParseError {
    pub message: String,
    pub loc: Location,
}

impl ParseError {
    pub fn new(message: String, loc: Location) -> ParseError {
        ParseError { message, loc }
    }
}

impl From<ParseError> for anyhow::Error {
    fn from(e: ParseError) -> Self {
        anyhow!(
            "{} at line {} columns {}..{}",
            e.message,
            e.loc.line,
            e.loc.col.start,
            e.loc.col.end
        )
    }
}

impl From<String> for ParseError {
    fn from(message: String) -> Self {
        ParseError {
            message,
            ..Default::default()
        }
    }
}

impl From<&str> for ParseError {
    fn from(message: &str) -> Self {
        ParseError {
            message: message.to_string(),
            ..Default::default()
        }
    }
}

impl From<(String, Location)> for ParseError {
    fn from(t: (String, Location)) -> Self {
        ParseError {
            message: t.0,
            loc: t.1,
        }
    }
}

impl From<(&str, Location)> for ParseError {
    fn from(t: (&str, Location)) -> Self {
        ParseError {
            message: t.0.to_string(),
            loc: t.1,
        }
    }
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}\nline {} col {}..{}",
            self.message, self.loc.line, self.loc.col.start, self.loc.col.end
        )
    }
}

impl From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Self {
        Error::Parse(ParseError {
            message: format!("I/O error {}", e.to_string()),
            ..Default::default()
        })
    }
}

#[derive(Debug)]
pub struct RuntimeError {
    message: String,
}

impl RuntimeError {
    pub fn new(message: String) -> Self {
        Self { message }
    }
}

impl From<String> for RuntimeError {
    fn from(m: String) -> Self {
        Self::new(m)
    }
}

impl From<&str> for RuntimeError {
    fn from(m: &str) -> Self {
        Self::new(m.to_string())
    }
}

impl From<RuntimeError> for anyhow::Error {
    fn from(e: RuntimeError) -> Self {
        anyhow!(e.message)
    }
}

#[derive(Debug)]
pub enum Error {
    Parse(ParseError),
    Runtime(RuntimeError),
}

impl From<ParseError> for Error {
    fn from(e: ParseError) -> Self {
        Error::Parse(e)
    }
}

impl From<RuntimeError> for Error {
    fn from(e: RuntimeError) -> Self {
        Error::Runtime(e)
    }
}

pub fn convert_parse(v: &[ParseError]) -> anyhow::Error {
    anyhow!(v
        .iter()
        .fold(String::new(), |s, e| s + &e.to_string() + "\n"))
}

pub fn convert(v: &[Error]) -> anyhow::Error {
    anyhow!(v
        .iter()
        .fold(String::new(), |s, e| s + &e.to_string() + "\n"))
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Parse(p) => write!(f, "{}", p.to_string()),
            Error::Runtime(r) => write!(f, "{}", r.message),
        }
    }
}
