//! File reader

use std::{
    io::{Error, ErrorKind, Result},
    iter::Peekable,
};

/// A peekable iterator for bytes that records line and column information.
pub struct Input<'a> {
    /// The source of the input data
    source: Peekable<Box<dyn Iterator<Item = u8> + 'a>>,
    /// Whether we are parsing binary or textual data
    binary: bool,
    /// The current line number (if not binary)
    line: usize,
    /// The current column
    column: usize,
}

impl<'a> Input<'a> {
    /// Create a new `Input` from some source
    pub fn new(source: Box<dyn Iterator<Item = u8> + 'a>, binary: bool) -> Self {
        Input {
            source: source.peekable(),
            binary,
            line: 1,
            column: 1,
        }
    }
    /// Look at the next byte without consuming it
    pub fn peek(&mut self) -> Option<u8> {
        self.source.peek().cloned()
    }
    /// Create an io::Error with the given message and position information.
    pub fn error(&self, why: &'static str) -> Error {
        Error::new(
            ErrorKind::InvalidData,
            if self.binary {
                format!("{} at position {}", why, self.column)
            } else {
                format!("{} at line {} column {}", why, self.line, self.column)
            },
        )
    }

    /// Parse a decimal number.
    ///
    /// Consumes one or more decimal digits, returning the value of the
    /// resulting number on success. Fails if there is no digit or if the digits do
    /// not end in a whitespace or newline.
    pub fn parse_u64(&mut self) -> Result<u64> {
        match self.peek() {
            None => return Err(self.error(Self::NUMBER)),
            Some(c) => {
                if !Self::is_digit(c) {
                    return Err(self.error(Self::NUMBER));
                }
            }
        }
        let mut value: u64 = 0;
        while let Some(c) = self.peek() {
            if !Self::is_digit(c) {
                break;
            }
            self.next();
            value = value
                .checked_mul(10)
                .and_then(|val| val.checked_add(u64::from(c - b'0')))
                .ok_or_else(|| self.error(Self::OVERFLOW))?;
        }
        Ok(value)
    }
    // Error messages.
    /// A numeric overflow. This should only happen for user input.
    pub const OVERFLOW: &'static str = "overflow while parsing number";
    /// Parser error ("unexpected EOF")
    pub const EOF: &'static str = "premature end of file";
    /// Parser error (`expected ...`)
    pub const NUMBER: &'static str = "expected number";
    /// Parser error (`expected ...`)
    pub const SPACE: &'static str = "expected space";
    /// Parser error (`expected ...`)
    pub const NUMBER_OR_SPACE: &'static str = "expected number or space";
    /// Parser error (`expected ...`)
    pub const NUMBER_OR_MINUS: &'static str = "expected number or \"-\"";
    /// Parser error (`expected ...`)
    pub const P_CNF: &'static str = "expected \"p cnf\"";
    /// Parser error (`expected ...`)
    pub const DRAT: &'static str = "expected DRAT instruction";
    /// Parser error (`expected ...`)
    pub const NEWLINE: &'static str = "expected newline";

    /// Check if a character is a decimal digit.
    pub fn is_digit(value: u8) -> bool {
        value >= b'0' && value <= b'9'
    }

    /// Check if a character is a decimal digit or a dash.
    pub fn is_digit_or_dash(value: u8) -> bool {
        Self::is_digit(value) || value == b'-'
    }
}

impl Iterator for Input<'_> {
    type Item = u8;
    fn next(&mut self) -> Option<u8> {
        self.source.next().map(|c| {
            if !self.binary && c == b'\n' {
                self.line += 1;
                self.column = 0;
            }
            self.column += 1;
            c
        })
    }
}