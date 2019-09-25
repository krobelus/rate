//! File reader

use std::{
    fs::File,
    io::{BufReader, Error, ErrorKind, Read, Result, StdinLock},
    iter::Peekable,
};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum CompressionFormat {
    ZSTD,
    GZIP,
    BZIP2,
    XZ,
    LZ4,
}

impl CompressionFormat {
    pub fn parse_extension(s: &str) -> Option<CompressionFormat> {
        for (extension, format) in Self::PAIRS {
            if s.ends_with(extension) {
                return Some(*format);
            }
        }
        None
    }
    const PAIRS : &'static [(&'static str, CompressionFormat)] = &[
        (".zst", CompressionFormat::ZSTD),
        (".gz", CompressionFormat::GZIP),
        (".bz2", CompressionFormat::BZIP2),
        (".xz", CompressionFormat::XZ),
        (".lz4", CompressionFormat::LZ4),
    ];
}

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
    pub fn from_file(filename: &str, binary: bool) -> Self {
        let source = Self::open(filename).peekable();
        Input {
            source,
            binary,
            line: 1,
            column: 1,
        }
    }

    pub fn from_stdin(stdin: StdinLock<'a>, binary: bool) -> Input<'a> {
        let source : Box<dyn Iterator<Item = u8>> = Box::new(stdin.bytes().map(panic_on_error));
        Input {
            source: source.peekable(),
            binary,
            line: 1,
            column: 1,
        }
    }

    pub fn peek_file(filename: &str, length: usize) -> Vec<u8> {
        let mut source = Self::open(filename);
        let mut vec = Vec::<u8>::with_capacity(length);
        for _ in 0..length {
            match source.next() {
                Some(c) => vec.push(c),
                None => break ,
            }
        }
        vec
    }

    fn open(filename: &str) -> Box<dyn Iterator<Item = u8>> {
        let file = File::open(filename).unwrap_or_else(|err| die!("cannot open file: {}", err));
        let compression = CompressionFormat::parse_extension(filename);
        match compression {
            None => Box::new(BufReader::new(file).bytes().map(panic_on_error)) ,
            Some(CompressionFormat::ZSTD) => {
                let de = zstd::stream::read::Decoder::new(file)
                    .unwrap_or_else(|err| die!("failed to decompress ZST archive: {}", err));
                Box::new(de.bytes().map(panic_on_error))
            }
            Some(CompressionFormat::GZIP) => {
                let de = flate2::read::GzDecoder::new(file);
                Box::new(de.bytes().map(panic_on_error))
            }
            Some(CompressionFormat::BZIP2) => {
                let de = bzip2::read::BzDecoder::new(file);
                Box::new(de.bytes().map(panic_on_error))
            }
            Some(CompressionFormat::XZ) => {
                let de = xz2::read::XzDecoder::new(file);
                Box::new(de.bytes().map(panic_on_error))
            }
            Some(CompressionFormat::LZ4) => {
                let de = lz4::Decoder::new(file)
                    .unwrap_or_else(|err| die!("failed to decode LZ4 archive: {}", err));
                Box::new(de.bytes().map(panic_on_error))
            }
        }
    }

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
    /// resulting number on success. Fails if there is no digit, or if the
    /// number does not lie within the range [-i64::MAX , i64::MAX].
    /// Otherwise, it is guaranteed to succeed.
    pub fn parse_dec64(&mut self) -> Result<i64> {
        let sign : bool = self.peek() == Some(b'-');
        if sign {
            self.next();
        }
        let mut value: i64 = 0;
        while let Some(c) = self.peek() {
            if !Self::is_digit(c) {
                break;
            }
            // Does not unnecessarily overflow because of the order of operations
            value = value.checked_mul(10)
                .and_then(|val| val.checked_add(i64::from(c - b'0')))
                .ok_or_else(|| self.error(Self::OVERFLOW))?;
            self.next();
        }
        // Does not unnecessary overflow because the positive range is smaller than the negative range
        if sign { Ok(-value) } else { Ok(value) }
    }

    /// Like parse_dec64, but returns an i32.
    /// Fails if the parsed number does not lie within the range
    /// [-i32::MAX , i32::MAX].
    pub fn parse_dec32(&mut self) -> Result<i32> {
        let sign : bool = self.peek() == Some(b'-');
        if sign {
            self.next();
        }
        let mut value: i32 = 0;
        while let Some(c) = self.peek() {
            if !Self::is_digit(c) {
                break;
            }
            // Does not unnecessarily overflow because of the order of operations
            value = value.checked_mul(10)
                .and_then(|val| val.checked_add(i32::from(c - b'0')))
                .ok_or_else(|| self.error(Self::OVERFLOW))?;
            self.next();
        }
        // Does not unnecessary overflow because the positive range is smaller than the negative range
        if sign { Ok(-value) } else { Ok(value) }
    }

    /// Parses a number in variable-bit encoding.
    /// Fails if the parsed number starts with 0x80,
    /// or if the number does not lie within the range [0 , u32::MAX].
    pub fn parse_vbe32(&mut self) -> Result<u32> {
        if self.peek() == Some(0x80) {
            Err(self.error(Self::OVERFLOW))
        } else {
            let mut abs: u64 = 0;
            let mut i: u64 = 0;
            while let Some(value) = self.next() {
                if i > 4 {
                    return Err(self.error(Input::OVERFLOW));
                }
                abs |= u64::from(value & 0x7F) << (7 * i);
                i += 1;
                if (value & 0x80) == 0x00 {
                    break;
                }
            }
            if abs > i32::max_value() as u64 {
                Err(self.error(Input::OVERFLOW))
            } else {
                Ok(abs as u32)
            }
        }
    }

    // todo: unify the two functions, possibly with generics. What's the least general unifier of i64 and i32?

    /// Parse zero or more spaces or linebreaks.
    pub fn skip_any_whitespace(&mut self) {
        while let Some(c) = self.peek() {
            if !Self::is_space(c) {
                break;
            }
            self.next();
        }
    }

    /// Skips whitespace, and returns and error if no space nor EOF was parsed.
    pub fn skip_some_whitespace(&mut self) -> Result<()> {
        if let Some(c) = self.peek() {
            if !Self::is_space(c) {
                return Err(self.error(Self::DRAT))
            }
        }
        while let Some(c) = self.peek() {
            if !Self::is_space(c) {
                break;
            }
            self.next();
        }
        Ok(())
    }

    pub fn skip_up_to(&mut self, c: u8) {
        while let Some(x) = self.next() {
            if x == c {
                break;
            }
        }
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

    /// Returns true if the character is one of the whitespace characters we allow.
    pub fn is_space(c: u8) -> bool {
        [b' ', b'\n', b'\r'].iter().any(|&s| s == c)
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

/// Unwraps a result, panicking on error.
pub fn panic_on_error<T>(result: Result<T>) -> T {
    result.unwrap_or_else(|error| die!("{}", error))
}