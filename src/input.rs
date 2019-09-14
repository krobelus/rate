use crate::{
    literal::Literal,
    output::{RuntimeError, RuntimeResult},
};
use std::{
    convert::TryInto,
    fs::File,
    io::{self, Read},
    iter::Peekable,
};

#[derive(Copy, Clone, Debug)]
enum CompressionFormat {
    ZSTD,
    GZIP,
    BZIP2,
    XZ,
    LZ4,
    NoCompression,
}
impl CompressionFormat {
    fn detect_compression(s: &str) -> CompressionFormat {
        let formats = [
            (".zst", CompressionFormat::ZSTD),
            (".gzip", CompressionFormat::GZIP),
            (".bz2", CompressionFormat::BZIP2),
            (".lz4", CompressionFormat::LZ4),
            (".xz", CompressionFormat::XZ),
        ];
        for (extension, format) in &formats {
            if s.ends_with(extension) {
                return *format;
            }
        }
        CompressionFormat::NoCompression
    }
}

type FileIterator = Box<dyn Iterator<Item = io::Result<u8>>>;

struct MaybeCompressedFile {
    name: String,
    compression: CompressionFormat,
    iterator: Peekable<FileIterator>,
}
impl MaybeCompressedFile {
    pub fn from_file(filename: &str) -> RuntimeResult<MaybeCompressedFile> {
        let format = CompressionFormat::detect_compression(filename);
        let file =
            File::open(filename).map_err(|_e| RuntimeError::FileOpening(filename.to_string()))?;
        let name = filename.to_string();
        let it: FileIterator = match format {
            CompressionFormat::ZSTD => Box::new(
                zstd::stream::read::Decoder::new(file)
                    .map_err(|_e| RuntimeError::FileDecompression(filename.to_string()))?
                    .bytes(),
            ),
            CompressionFormat::GZIP => Box::new(flate2::read::GzDecoder::new(file).bytes()),
            CompressionFormat::BZIP2 => Box::new(bzip2::read::BzDecoder::new(file).bytes()),
            CompressionFormat::XZ => Box::new(xz2::read::XzDecoder::new(file).bytes()),
            CompressionFormat::LZ4 => Box::new(
                lz4::Decoder::new(file)
                    .map_err(|_e| RuntimeError::FileDecompression(filename.to_string()))?
                    .bytes(),
            ),
            CompressionFormat::NoCompression => Box::new(std::io::BufReader::new(file).bytes()),
        };
        Ok(MaybeCompressedFile {
            name: name,
            compression: format,
            iterator: it.peekable(),
        })
    }
    pub fn next(&mut self) -> RuntimeResult<Option<u8>> {
        match self.iterator.next() {
            Some(Ok(x)) => Ok(Some(x)),
            Some(Err(_e)) => Err(self.throw_reading_error()),
            None => Ok(None),
        }
    }
    pub fn peek(&mut self) -> RuntimeResult<Option<u8>> {
        match self.iterator.peek() {
            Some(Ok(x)) => Ok(Some(x.clone())),
            Some(Err(_e)) => Err(self.throw_reading_error()),
            None => Ok(None),
        }
    }
    fn throw_reading_error(&self) -> RuntimeError {
        RuntimeError::FileReading(self.name.clone())
    }
}

pub struct Input {
    source: MaybeCompressedFile,
    binary: bool,
    line: usize,
}
impl Input {
    pub fn from_file(filename: &str, binary: bool) -> RuntimeResult<Input> {
        Ok(Input {
            source: MaybeCompressedFile::from_file(filename)?,
            binary: binary,
            line: 0,
        })
    }
    pub fn throw_out_of_bounds(&self) -> RuntimeError {
        RuntimeError::ParsingOutOfBounds(self.source.name.clone(), self.line())
    }
    pub fn throw_invalid_syntax(&self) -> RuntimeError {
        RuntimeError::ParsingInvalidSyntax(self.source.name.clone(), self.line())
    }
    pub fn filename(&self) -> String {
        self.source.name.clone()
    }
    pub fn next(&mut self) -> RuntimeResult<Option<u8>> {
        let r = self.source.next();
        if r == Ok(Some(b'\n')) {
            self.line = self.line + 1;
        }
        r
    }
    pub fn peek(&mut self) -> RuntimeResult<Option<u8>> {
        self.source.peek()
    }
    pub fn peek_unchecked(&mut self) -> Option<u8> {
        self.peek().unwrap()
    }
    pub fn line(&self) -> Option<usize> {
        if self.binary {
            None
        } else {
            Some(self.line)
        }
    }
    pub fn skip_spaces(&mut self) -> RuntimeResult<bool> {
        let mut found: bool = false;
        loop {
            match self.peek()? {
                Some(c) if Self::is_space(c) => {
                    self.next()?;
                    found = true;
                }
                None => return Ok(true),
                _ => return Ok(found),
            }
        }
    }
    pub fn parse_u32(&mut self) -> RuntimeResult<u32> {
        let value = self.parse_u64()?;
        if value > i32::max_value().try_into().unwrap() {
            Err(self.throw_out_of_bounds())
        } else {
            Ok(value as u32)
        }
    }
    pub fn parse_u64(&mut self) -> RuntimeResult<u64> {
        let mut value: u64 = 0u64;
        match self.peek()? {
            Some(c) if !Self::is_space(c) => (),
            _ => return Err(self.throw_invalid_syntax()),
        }
        while let Some(c) = self.next()? {
            if Self::is_space(c) {
                break;
            }
            if !Self::is_digit(c) {
                return Err(self.throw_invalid_syntax());
            }
            value = value
                .checked_mul(10)
                .ok_or(self.throw_out_of_bounds())?
                .checked_add(u64::from(c - b'0'))
                .ok_or(self.throw_out_of_bounds())?
        }
        Ok(value)
    }
    fn is_digit(value: u8) -> bool {
        value >= b'0' && value <= b'9'
    }
    pub fn is_digit_or_dash(value: u8) -> bool {
        Self::is_digit(value) || value == b'-'
    }
    fn is_space(c: u8) -> bool {
        [b' ', b'\n', b'\r', b'\t'].iter().any(|&s| s == c)
    }
    pub fn parse_literal(&mut self) -> RuntimeResult<Literal> {
        match self.peek()? {
            Some(b'-') => {
                self.next()?;
                Ok(Literal::new(-(self.parse_u32()? as i32)))
            }
            Some(c) if Self::is_digit(c) => {
                self.next()?;
                Ok(Literal::new(self.parse_u32()? as i32))
            }
            _ => Err(self.throw_invalid_syntax()),
        }
    }
    pub fn parse_atom(&mut self) -> RuntimeResult<Literal> {
        match self.peek()? {
            Some(b't') => Ok(Literal::TOP),
            Some(b'f') => Ok(Literal::BOTTOM),
            _ => self.parse_literal(),
        }
    }
    pub fn parse_literal_binary(&mut self) -> RuntimeResult<Literal> {
        let mut i = 0;
        let mut result = 0;
        while let Some(value) = self.next()? {
            result |= u32::from(value & 0x7f) << (7 * i);
            i += 1;
            if (value & 0x80) == 0 {
                return Ok(Literal::from_raw(result));
            }
        }
        Err(self.throw_invalid_syntax())
    }
    pub fn parse_atom_binary(&mut self) -> RuntimeResult<Literal> {
        match self.peek()? {
            Some(0x7f) => Ok(Literal::BOTTOM),
            _ => self.parse_literal_binary(),
        }
    }
}
