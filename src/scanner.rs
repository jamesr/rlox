use crate::error;
use core::fmt;
use std::ops::Range;

#[derive(Debug, PartialEq, Copy, Clone)]
pub enum TokenType {
    // Single-character tokens.
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    Comma,
    Dot,
    Minus,
    Plus,
    Semicolon,
    Slash,
    Star,

    // One or two character tokens.
    Bang,
    BangEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,

    // literals.
    Identifier,
    String,
    Number,

    // keywords.
    And,
    Class,
    Else,
    False,
    Fun,
    For,
    If,
    Nil,
    Or,
    Print,
    Return,
    Super,
    This,
    True,
    Var,
    While,
}

#[derive(PartialEq, Debug, Copy, Clone)]
pub enum TokenValue<'a> {
    String(&'a str),
    Number(f64),
    Bool(bool),
    Nil,
}

impl std::fmt::Display for TokenValue<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenValue::String(s) => write!(f, "\"{}\"", s),
            TokenValue::Number(n) => write!(f, "{}", n),
            TokenValue::Bool(b) => write!(f, "{}", b),
            TokenValue::Nil => write!(f, "nil"),
        }
    }
}

#[derive(PartialEq, Debug, Copy, Clone)]
pub struct Token<'a> {
    pub token_type: TokenType,
    pub lexeme: &'a str,
    pub value: Option<TokenValue<'a>>,
    pub line: usize,
}

impl<'a> fmt::Display for Token<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!(
            "token {:?} lexeme \"{}\" value {:?} line {}",
            self.token_type, self.lexeme, self.value, self.line,
        ))
    }
}

#[derive(Default, Clone, Debug)]
struct Loc {
    lines: Range<usize>, // lines of the token being scanned
    cols: Range<usize>,  // columns of the token being scanned in chars
}

impl Loc {
    fn advance_lines(&mut self, lines: usize) {
        self.lines.end += lines;
        self.cols.end = 0;
    }

    fn advance_col(&mut self) {
        self.cols.end += 1;
    }

    fn consume(&mut self) {
        self.lines.start = self.lines.end;
        self.cols.start = self.cols.end;
    }

    fn line(&self) -> usize {
        self.lines.start
    }
}

pub struct Scanner<'a> {
    source: &'a str,
    loc: Loc,
    pub current: Range<usize>, // byte indices into |source|, must be on UTF-8 char boundaries
}

type ScanResult<'a> = Result<Token<'a>, error::ParseError>;

impl<'a> Scanner<'a> {
    pub fn new(source: &'a str) -> Scanner {
        Scanner {
            source,
            loc: Loc {
                lines: (1..1),
                cols: (0..0),
            },
            current: (0..0),
        }
    }

    pub fn line(&self) -> usize {
        self.loc.line()
    }

    pub fn loc(&self) -> error::Location {
        error::Location {
            line: self.line(),
            col: self.cols(),
        }
    }

    pub fn error(&self, message: &str) -> error::ParseError {
        error::ParseError::new(message, self.loc())
    }

    pub fn cols(&self) -> Range<usize> {
        self.loc.cols.clone()
    }

    fn current(&self) -> &'a str {
        self.source.get(self.current.clone()).unwrap()
    }

    fn rest(&self) -> &'a str {
        self.source.get(self.current.end..).unwrap()
    }

    fn at_end(&self) -> bool {
        return self.current.end == self.source.len();
    }

    fn advance(&mut self) -> Option<char> {
        if let Some(c) = self.rest().chars().next() {
            self.current.end += c.len_utf8();
            self.loc.advance_col();
            return Some(c);
        }
        return None;
    }

    fn matches(&mut self, expected: char) -> bool {
        match self.rest().chars().next() {
            Some(c) => {
                if c == expected {
                    self.current.end += c.len_utf8();
                    self.loc.advance_col();
                    return true;
                } else {
                    return false;
                }
            }
            _ => false,
        }
    }

    fn peek(&self) -> Option<char> {
        return self.rest().chars().next();
    }

    fn peek_next(&self) -> Option<char> {
        return self.rest().chars().nth(1);
    }

    fn string(&mut self) -> ScanResult<'a> {
        let mut lines = 0;
        self.advance_matching(|o| match o {
            Some('"') | None => false,
            Some('\n') => {
                lines += 1;
                true
            }
            _ => true,
        });
        self.loc.advance_lines(lines);

        if self.at_end() {
            return Err(self.error("Error: Unterminated string."));
        }
        self.advance(); // Consume closing "

        let lexeme = self.current();
        let value = lexeme.get(1..lexeme.len() - 1).unwrap();
        Ok(Token {
            token_type: TokenType::String,
            lexeme,
            value: Some(TokenValue::String(value)),
            line: self.line(),
        })
    }

    fn advance_matching<T>(&mut self, mut pred: T)
    where
        T: FnMut(Option<char>) -> bool,
    {
        loop {
            if pred(self.peek()) {
                self.advance();
                continue;
            }
            break;
        }
    }

    fn number(&mut self) -> ScanResult<'a> {
        fn advance_digits(scanner: &mut Scanner) {
            scanner.advance_matching(|o| match o {
                Some(c) => c.is_digit(10),
                _ => false,
            })
        }

        advance_digits(self);

        if self.peek() == Some('.') {
            if let Some(next) = self.peek_next() {
                if next.is_digit(10) {
                    self.advance(); // consume .
                    advance_digits(self);
                }
            }
        }

        let lexeme = self.current();
        let parsed_value = lexeme.parse::<f64>();
        if !parsed_value.is_ok() {
            return Err(self.error(&format!("Error parsing numeric literal {}", lexeme)));
        }
        Ok(Token {
            token_type: TokenType::Number,
            lexeme,
            value: Some(TokenValue::Number(parsed_value.unwrap())),
            line: self.line(),
        })
    }

    fn identifier(&mut self) -> ScanResult<'a> {
        self.advance_matching(|c| match c {
            Some('_') => true,
            Some(c) => c.is_ascii_alphanumeric(),
            _ => false,
        });

        let lexeme = self.current();
        use TokenType::*;
        let token_type = match lexeme {
            "and" => And,
            "class" => Class,
            "else" => Else,
            "false" => False,
            "for" => For,
            "fun" => Fun,
            "if" => If,
            "nil" => Nil,
            "or" => Or,
            "print" => Print,
            "return" => Return,
            "super" => Super,
            "this" => This,
            "true" => True,
            "var" => Var,
            "while" => While,
            _ => Identifier,
        };
        Ok(Token {
            token_type,
            line: self.line(),
            lexeme,
            value: None,
        })
    }

    fn make_token(&mut self, token_type: TokenType) -> Token<'a> {
        Token {
            token_type,
            lexeme: self.current(),
            value: None,
            line: self.line(),
        }
    }
}

impl<'a> Iterator for Scanner<'a> {
    type Item = ScanResult<'a>;

    fn next(&mut self) -> Option<ScanResult<'a>> {
        use TokenType::*;
        loop {
            self.loc.consume();
            self.current.start = self.current.end;
            let maybe_token = if let Some(c) = self.advance() {
                match c {
                    '(' => Some(self.make_token(LeftParen)),
                    ')' => Some(self.make_token(RightParen)),
                    '{' => Some(self.make_token(LeftBrace)),
                    '}' => Some(self.make_token(RightBrace)),
                    ',' => Some(self.make_token(Comma)),
                    '.' => Some(self.make_token(Dot)),
                    '-' => Some(self.make_token(Minus)),
                    '+' => Some(self.make_token(Plus)),
                    ';' => Some(self.make_token(Semicolon)),
                    '*' => Some(self.make_token(Star)),
                    '!' => {
                        let token_type = if self.matches('=') { BangEqual } else { Bang };
                        Some(self.make_token(token_type))
                    }
                    '=' => {
                        let token_type = if self.matches('=') { EqualEqual } else { Equal };
                        Some(self.make_token(token_type))
                    }
                    '<' => {
                        let token_type = if self.matches('=') { LessEqual } else { Less };
                        Some(self.make_token(token_type))
                    }
                    '>' => {
                        let token_type = if self.matches('=') {
                            GreaterEqual
                        } else {
                            Greater
                        };
                        Some(self.make_token(token_type))
                    }
                    '/' => {
                        if self.matches('/') {
                            // line comment
                            // peek() until we see a '\n' and then bail.
                            loop {
                                match self.peek() {
                                    Some('\n') => break,
                                    None => return None,
                                    _ => {
                                        self.advance();
                                    }
                                }
                            }
                            None
                        } else {
                            Some(self.make_token(Slash))
                        }
                    }

                    '"' => match self.string() {
                        Ok(token) => Some(token),
                        Err(e) => return Some(Err(e)),
                    },

                    // Skip whitespace
                    ' ' | '\r' | '\t' => None,

                    '\n' => {
                        self.loc.advance_lines(1);
                        None
                    }

                    c => {
                        if c.is_digit(10) {
                            match self.number() {
                                Ok(token) => Some(token),
                                Err(e) => return Some(Err(e)),
                            }
                        } else if c.is_ascii_alphabetic() || c == '_' {
                            match self.identifier() {
                                Ok(token) => Some(token),
                                Err(e) => return Some(Err(e)),
                            }
                        } else {
                            self.loc.consume();
                            self.current.start = self.current.end;
                            return Some(Err(self.error("Error: Unexpected character.")));
                        }
                    }
                }
            } else {
                return None;
            };
            if let Some(token) = maybe_token {
                // Consumed our lexeme, advance offset
                self.current.start = self.current.end;
                return Some(Ok(token));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::scanner::TokenType::*;
    use crate::scanner::*;
    #[test]
    fn scanner_basic() {
        let source = "foo";
        let scanner = Scanner::new(&source);
        assert_eq!(scanner.current(), "");
        assert_eq!(scanner.line(), 1);
        assert_eq!(scanner.rest(), "foo");
    }

    macro_rules! scan_ok_tokens_test {
        ($name:ident, $source:expr, $expected_tokens:expr) => {
            #[test]
            fn $name() {
                let source = $source;
                let scanner = Scanner::new(&source);
                let tokens = scanner.collect::<Vec<_>>();
                let expected_tokens = $expected_tokens;
                for i in 0..tokens.len() {
                    let result = tokens[i].as_ref();
                    assert!(
                        result.is_ok(),
                        "token {} is an error \"{}\" on line {} columns {}..{}",
                        i,
                        result.err().unwrap().message,
                        result.err().unwrap().loc.line,
                        result.err().unwrap().loc.col.start,
                        result.err().unwrap().loc.col.end,
                    );
                    let token = result.ok().unwrap();
                    assert_eq!(token.token_type, expected_tokens[i].token_type);
                    assert_eq!(token.line, expected_tokens[i].line);
                    assert_eq!(token.lexeme, expected_tokens[i].lexeme);
                }
            }
        };
    }

    scan_ok_tokens_test!(
        empty,
        "",
        [Token {
            token_type: LeftParen,
            line: 1,
            lexeme: "",
            value: None,
        }; 0]
    );

    scan_ok_tokens_test!(
        left_paren,
        "(",
        [Token {
            token_type: LeftParen,
            line: 1,
            lexeme: "(",
            value: None,
        }]
    );

    scan_ok_tokens_test!(
        left_paren_with_whitespace,
        "
        (",
        [Token {
            token_type: LeftParen,
            line: 2,
            lexeme: "(",
            value: None,
        }]
    );

    scan_ok_tokens_test!(
        string_literal,
        "\"hello, world\"",
        [Token {
            token_type: String,
            line: 1,
            lexeme: "\"hello, world\"",
            value: Some(TokenValue::String("hello, world")),
        }]
    );
    scan_ok_tokens_test!(
        number_ints,
        "123
        -456",
        [
            Token {
                token_type: Number,
                line: 1,
                lexeme: "123",
                value: Some(TokenValue::Number(123.0)),
            },
            Token {
                token_type: Minus,
                line: 2,
                lexeme: "-",
                value: None,
            },
            Token {
                token_type: Number,
                line: 2,
                lexeme: "456",
                value: Some(TokenValue::Number(456.0)),
            },
        ]
    );

    scan_ok_tokens_test!(
        number_decimals,
        "0.25
        25.() // not a decimal",
        [
            Token {
                token_type: Number,
                line: 1,
                lexeme: "0.25",
                value: Some(TokenValue::Number(0.25)),
            },
            Token {
                token_type: Number,
                line: 2,
                lexeme: "25",
                value: Some(TokenValue::Number(25.0)),
            },
            Token {
                token_type: Dot,
                line: 2,
                lexeme: ".",
                value: None,
            },
            Token {
                token_type: LeftParen,
                line: 2,
                lexeme: "(",
                value: None,
            },
            Token {
                token_type: RightParen,
                line: 2,
                lexeme: ")",
                value: None,
            },
        ]
    );

    scan_ok_tokens_test!(
        comments,
        "( // left paren
            0/5 // division",
        [
            Token {
                token_type: LeftParen,
                line: 1,
                lexeme: "(",
                value: None,
            },
            Token {
                token_type: Number,
                line: 2,
                lexeme: "0",
                value: None,
            },
            Token {
                token_type: Slash,
                line: 2,
                lexeme: "/",
                value: None,
            },
            Token {
                token_type: Number,
                line: 2,
                lexeme: "5",
                value: None,
            }
        ]
    );

    scan_ok_tokens_test!(
        identifiers_and_keywords,
        "foo
        true and false
        superman // 'super' is a reserved keyword
        with_underscores_And_Caps
        StartsWithCaps
        with_digits_420",
        [
            Token {
                token_type: Identifier,
                line: 1,
                lexeme: "foo",
                value: None,
            },
            Token {
                token_type: True,
                line: 2,
                lexeme: "true",
                value: None,
            },
            Token {
                token_type: And,
                line: 2,
                lexeme: "and",
                value: None,
            },
            Token {
                token_type: False,
                line: 2,
                lexeme: "false",
                value: None,
            },
            Token {
                token_type: Identifier,
                line: 3,
                lexeme: "superman",
                value: None,
            },
            Token {
                token_type: Identifier,
                line: 4,
                lexeme: "with_underscores_And_Caps",
                value: None,
            },
            Token {
                token_type: Identifier,
                line: 5,
                lexeme: "StartsWithCaps",
                value: None,
            },
            Token {
                token_type: Identifier,
                line: 6,
                lexeme: "with_digits_420",
                value: None,
            },
        ]
    );
}
