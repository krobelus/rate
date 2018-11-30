//! Compile-time and runtime configuration, plus macros

use clap::ArgMatches;

pub const BOUNDS_CHECKING: bool = true;

#[derive(Debug, PartialEq, Eq)]
pub struct Config {
    pub trace: bool,
}

impl Config {
    pub fn new(matches: ArgMatches) -> Config {
        Config {
            trace: matches.is_present("TRACE"),
        }
    }
}

// print to stdout
macro_rules! echo {
    ($($arg:tt)*) => ({
        println!($($arg)*);
    })
}

// trace of the algorithm, for comparison against crate
macro_rules! trace {
    ($checker:expr, $($arg:tt)*) => {{
        if $checker.config.trace
        {
            print!($($arg)*);
        }
    }};
}

// print a warning to stderr
macro_rules! warn {
    ($($arg:tt)*) => ({
        let style = ansi_term::Colour::Red.normal();
        eprint!("{}", style.paint("Warning: "));
        eprintln!("{}", style.paint(&format!($($arg)*)));
    })
}

macro_rules! die {
    ($($arg:tt)*) => ({
        eprint!("*** Fatal error: ");
        eprintln!($($arg)*);
        std::process::exit(2);
    })
}
