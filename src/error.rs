use std::ops::Range;

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
