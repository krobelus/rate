//! File reader

use std::{
    io::{Error, ErrorKind},
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