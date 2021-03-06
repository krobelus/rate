//! Convert binary DRAT to textual DRAT
//!
//! This shares little code with the other files but it duplicates some of the parsing logic.

use clap::Arg;
use std::io::{self, Result, Write};

use rate_common::{
    output,
    parser::{open_file_for_writing, parse_literal_binary, read_compressed_file_or_stdin},
};

/// Run `bdrat2drat`.
fn main() {
    output::panic_on_error(run())
}

/// Run `bdrat2drat`, possibly returning an `io::Error`.
fn run() -> Result<()> {
    output::install_signal_handler();
    let matches = clap::App::new("bdrat2drat")
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
    let mut output = open_file_for_writing(matches.value_of("OUTPUT").unwrap_or("-"), &stdout);
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
