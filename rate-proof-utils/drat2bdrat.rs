//! Convert DRAT to binary DRAT
//!
//! This shares little code with the other files but it duplicates some of the parsing logic.

use clap::Arg;
use std::io::{self, Result, Write};

use rate_common::{
    output,
    parser::{open_file_for_writing, parse_literal, read_compressed_file_or_stdin},
};

/// Write a number in signed little-endian binary (SLEB) encoding.
fn write_number(output: &mut dyn Write, number: i32) -> Result<()> {
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

/// Run `drat2bdrat`.
fn main() {
    output::panic_on_error(run())
}

/// Run `drat2bdrat`, possibly returning an `io::Error`.
fn run() -> Result<()> {
    output::install_signal_handler();
    let matches = clap::App::new("drat2bdrat")
        .version(env!("CARGO_PKG_VERSION"))
        .about("Read a textual proof from stdin and write its binary version to stdout")
        .arg(
            Arg::with_name("INPUT").help("input file in textual DRAT format (omit or - for stdin)"),
        )
        .arg(Arg::with_name("OUTPUT").help("output file (omit for stdout)"))
        .get_matches();
    let stdout = io::stdout();
    let stdin = io::stdin();
    let mut input = read_compressed_file_or_stdin(
        matches.value_of("INPUT").unwrap_or("-"),
        /*binary=*/ false,
        stdin.lock(),
    );
    let mut output = open_file_for_writing(matches.value_of("OUTPUT").unwrap_or("-"), &stdout);
    while let Some(c) = input.peek() {
        output.write_all(&[if c == b'd' {
            input.next();
            b'd'
        } else {
            b'a'
        }])?;
        loop {
            let literal = parse_literal(&mut input)?;
            write_number(&mut output, literal.decode())?;
            if literal.is_zero() {
                break;
            }
        }
    }
    Ok(())
}
