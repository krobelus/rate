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
mod hashtable;
mod input;
mod parser;
mod proof;

use clap::Arg;
use std::io::{self, Result, Write};

use crate::parser::open_file_for_writing;

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
    let stdout = io::stdout();
    let input_filename = matches.value_of("INPUT").unwrap_or("-");
    let mut input = crate::input::Input::from_file(input_filename, /*binary*/ true).unwrap();
    let mut output: Box<Write> = match matches.value_of("OUTPUT") {
        None => Box::new(stdout.lock()),
        Some(filename) => Box::new(open_file_for_writing(filename)),
    };
    while let Some(byte) = input.next().unwrap() {
        match byte {
            b'a' => (),
            b'd' => output.write_all(b"d ")?,
            _ => panic!("expected \"a\" or \"d\""),
        }
        loop {
            let literal = input.parse_literal_binary().unwrap();
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
