//! Convert compressed DRAT to textual DRAT
//!
//! This shares little code with the other files but it duplicates some of the parsing logic.

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
use std::io::{self, Result, Write};

use crate::parser::{open_file_for_writing, parse_literal_binary, read_compressed_file_or_stdin};

fn fail(offset: usize) -> ! {
    eprintln!("*** Fatal error: unexpected byte at position {}", offset);
    std::process::exit(1)
}

fn main() -> Result<()> {
    crate::config::signals();
    let matches = clap::App::new("cdrat2drat")
        .version(env!("CARGO_PKG_VERSION"))
        .about("Read a binary proof from stdin and write its textual version to stdout")
        .arg(
            Arg::with_name("INPUT")
                .help("input file in binary DRAT format (omit or use \"-\" for stdin)"),
        )
        .arg(Arg::with_name("OUTPUT").help("output file (defaults to stdout)"))
        .get_matches();
    let stdin = io::stdin();
    let stdout = io::stdout();
    let input_filename = matches.value_of("INPUT").unwrap_or("-");
    let mut input =
        read_compressed_file_or_stdin(input_filename, /*binary=*/ true, stdin.lock());
    let mut output: Box<Write> = match matches.value_of("OUTPUT") {
        None => Box::new(stdout.lock()),
        Some(filename) => Box::new(open_file_for_writing(filename)),
    };
    while let Some(byte) = input.next() {
        match byte {
            b'a' => (),
            b'd' => output.write_all(b"d ")?,
            _ => return Err(input.error("expected \"a\" or \"d\"")),
        }
        loop {
            let literal = parse_literal_binary(&mut input)?;
            if literal.is_zero() {
                writeln!(output, "0")?;
                break;
            } else {
                write!(output, "{} ", literal)?;
            }
        }
    }
    Ok(())
}
