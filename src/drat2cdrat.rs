//! Convert DRAT to compressed (binary) DRAT
//!
//! This shares almost no code with the other files but it duplicates some of the parsing logic.

#![allow(dead_code)]
#![allow(unused_macros)]

#[macro_use]
mod output;
mod clause;
mod clausedatabase;
#[macro_use]
mod config;
mod features;
mod literal;
#[macro_use]
mod memory;
mod parser;

#[macro_use(Serialize, Deserialize)]
extern crate serde_derive;

use clap::Arg;
use std::io::{self, BufReader, BufWriter, Read, Result, Write};

use crate::parser::{create_file, open_file, panic_on_error};

fn write_number(output: &mut Write, number: i32) -> Result<()> {
    let mut encoding = number.abs() << 1;
    if number < 0 {
        encoding += 1;
    }
    loop {
        output.write_all(&[if encoding <= 0x7f {
            encoding
        } else {
            0x80 | (encoding & 0x7f)
        } as u8])?;
        encoding >>= 7;
        if encoding == 0 {
            return Ok(());
        }
    }
}

enum State {
    Begin,
    Number(bool, i32),
    Space,
}

fn start_number(byte: u8) -> State {
    let sign = byte == b'-';
    State::Number(sign, if sign { 0 } else { i32::from(byte - b'0') })
}

fn fail(line: usize, col: usize) -> ! {
    eprintln!(
        "*** Fatal error: unexpected byte at line {} column {}",
        line, col
    );
    std::process::exit(1)
}

fn main() -> Result<()> {
    crate::config::signals();
    let matches = clap::App::new("drat2cdrat")
        .version(env!("CARGO_PKG_VERSION"))
        .about("Read a textual proof from stdin and write its binary version to stdout")
        .arg(
            Arg::with_name("INPUT").help("input file in textual DRAT format (omit or - for stdin)"),
        )
        .arg(Arg::with_name("OUTPUT").help("output file (omit for stdout)"))
        .get_matches();
    let stdout = io::stdout();
    let stdin = io::stdin();
    let input: Box<Read> = match matches.value_of("INPUT") {
        None | Some("-") => Box::new(stdin.lock()),
        Some(filename) => Box::new(open_file(filename)),
    };
    let mut output: Box<Write> = match matches.value_of("OUTPUT") {
        None => Box::new(stdout.lock()),
        Some(filename) => Box::new(BufWriter::new(create_file(filename))),
    };
    let mut state = State::Begin;
    let mut line = 1;
    let mut col = 0;
    for byte in BufReader::new(input).bytes().map(panic_on_error) {
        if byte == b'\n' {
            line += 1;
            col = 0;
        } else {
            col += 1;
        }
        if byte == b'\r' {
            continue;
        }
        match state {
            State::Begin => match byte {
                b'd' => {
                    output.write_all(&[b'd'])?;
                    state = State::Space;
                }
                b'-' | b'0'..=b'9' => {
                    output.write_all(&[b'a'])?;
                    state = start_number(byte);
                }
                b' ' => (),
                _ => fail(line, col),
            },
            State::Number(sign, magnitude) => match byte {
                b'0'..=b'9' => {
                    let magnitude = magnitude.checked_mul(10).and_then(|m| m.checked_add(i32::from(byte - b'0')))
                    .unwrap_or_else(|| {
                        eprintln!("*** Fatal error: numeric overflow parsing literal at line {} column {}", line, col);
                        std::process::exit(1)
                    });
                    state = State::Number(sign, magnitude);
                }
                b' ' | b'\n' => {
                    write_number(&mut output, if sign { -magnitude } else { magnitude })?;
                    state = if byte == b'\n' {
                        State::Begin
                    } else {
                        State::Space
                    }
                }
                b'-' => state = start_number(b'-'),
                _ => fail(line, col),
            },
            State::Space => match byte {
                b' ' => (),
                b'd' => {
                    output.write_all(&[b'd'])?;
                }
                b'\n' => {
                    state = State::Begin;
                }
                b'-' | b'0'..=b'9' => {
                    state = start_number(byte);
                }
                _ => fail(line, col),
            },
        }
    }
    Ok(())
}
