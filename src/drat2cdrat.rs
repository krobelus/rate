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

use crate::parser::panic_on_error;
use std::io::{stdin, stdout, BufReader, Read, Result, Write};

fn write_number(output: &mut Write, number: i32) -> Result<()> {
    let mut encoding = number.abs() << 1;
    if number < 0 { encoding += 1; }
    loop {
        output.write(&[if encoding <= 0x7f {
            encoding
        } else {
            0x80 | (encoding & 0x7f)
        } as u8])?;
        encoding = encoding >> 7;
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
    State::Number(sign, if sign { 0 } else { (byte - b'0') as i32 })
}

fn main() -> Result<()> {
    clap::App::new("drat2cdrat")
        .version(env!("CARGO_PKG_VERSION"))
        .about("Read a textual proof from stdin and write its binary version to stdout")
        .get_matches();
    let stdin = stdin();
    let input = stdin.lock();
    let stdout = stdout();
    let mut output = stdout.lock();
    let mut state = State::Begin;
    for byte in BufReader::new(input).bytes().map(panic_on_error) {
        if byte == b'\r' {
            continue;
        }
        match state {
            State::Begin => match byte {
                b'd' => {
                    output.write(&[b'd'])?;
                    state = State::Space;
                }
                b'-' | b'0'..=b'9' => {
                    output.write(&[b'a'])?;
                    state = start_number(byte);
                }
                b' ' => (),
                _ => assert!(false),
            },
            State::Number(sign, magnitude) => match byte {
                b'0'..=b'9' => {
                    state = State::Number(sign, magnitude * 10 + (byte - b'0') as i32);
                }
                b' ' | b'\n' => {
                    write_number(&mut output, if sign { -magnitude } else { magnitude })?;
                    state = if byte == b'\n' {
                        State::Begin
                    } else {
                        State::Space
                    }
                }
                _ => assert!(false),
            },
            State::Space => match byte {
                b' ' => (),
                b'd' => {
                    output.write(&[b'd'])?;
                }
                b'\n' => {
                    state = State::Begin;
                }
                b'-' | b'0'..=b'9' => {
                    state = start_number(byte);
                }
                _ => assert!(false),
            },
        }
    }
    Ok(())
}
