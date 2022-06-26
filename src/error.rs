use std::ops::Range;

use anyhow::anyhow;

#[derive(Default, Debug)]
pub struct Location {
    pub line: usize,
    pub col: Range<usize>,
}

#[derive(Debug)]
pub struct Error {
    pub loc: Location,
    pub message: String,
}

impl Error {
    pub fn new(message: String) -> Error {
        Error {
            loc: Location::default(),
            message,
        }
    }
    pub fn with_line(line: usize, message: String) -> Error {
        Error {
            loc: Location { line, col: (0..0) },
            message,
        }
    }

    pub fn with_col(line: usize, col: Range<usize>, message: String) -> Error {
        Error {
            loc: Location { line, col },
            message,
        }
    }
}

impl From<Error> for anyhow::Error {
    fn from(e: Error) -> Self {
        anyhow!(
            "{} at line {} columns {}..{}",
            e.message,
            e.loc.line,
            e.loc.col.start,
            e.loc.col.end
        )
    }
}

impl From<String> for Error {
    fn from(message: String) -> Self {
        Error {
            loc: Location::default(),
            message,
        }
    }
}

impl From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Self {
        Error {
            loc: Location::default(),
            message: format!("I/O error {}", e.to_string()),
        }
    }
}
