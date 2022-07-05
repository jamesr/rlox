use std::ops::Range;

use crate::eval;

#[derive(Default, Debug)]
pub struct Location {
    pub line: usize,
    pub col: Range<usize>,
}

impl Clone for Location {
    fn clone(&self) -> Self {
        Location {
            line: self.line,
            col: self.col.clone(),
        }
    }
}

#[derive(Debug, Default, Clone)]
pub struct ParseError {
    pub message: String,
    pub loc: Location,
}

impl ParseError {
    pub fn new(message: String, loc: Location) -> ParseError {
        ParseError { message, loc }
    }

    pub fn with_message(message: &str) -> ParseError {
        ParseError {
            message: message.to_string(),
            ..Default::default()
        }
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
            "{}\n", //line {} col {}..{}",
            self.message,
            //self.loc.line,
            // self.loc.col.start, self.loc.col.end
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
pub enum RuntimeError {
    Message(String),
    Return(eval::Value),
}

impl RuntimeError {
    pub fn new(message: String) -> Self {
        Self::Message(message)
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

impl std::fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RuntimeError::Message(m) => write!(f, "{}", m),
            RuntimeError::Return(v) => write!(f, "return {}", v),
        }
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

pub fn convert_parse(v: &[ParseError]) -> Error {
    Error::Parse(v[0].clone())
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Parse(p) => write!(f, "{}", p.to_string()),
            Error::Runtime(r) => write!(f, "{}", r),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{error, eval};

    #[test]
    fn make_runtime_error() {
        let _msg_err = error::RuntimeError::Message("hi".to_string());
        let _return_err = error::RuntimeError::Return(eval::Value::Nil);
    }
}
