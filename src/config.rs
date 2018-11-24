//! Compile-time and runtime configuration, plus macros

use clap::ArgMatches;

pub const NAIVE: bool = true;
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

// print to stderr
macro_rules! info {
    ($($arg:tt)*) => ({
        if cfg!(debug_assertions) {
            eprintln!("{}", $($arg)*);
        }
    })
}

// print a warning to stderr
macro_rules! warn {
    ($($arg:tt)*) => ({
        if cfg!(debug_assertions) {
            let style = ansi_term::Colour::Red.normal();
            eprint!("{}", style.paint("Warning: "));
            eprintln!("{}", style.paint(&format!($($arg)*)));
        }
    })
}

macro_rules! die {
    () => ({
        die_impl!("");
    });
    ($($arg:tt)*) => ({
        die_impl!($($arg)*);
    })
}

#[cfg(debug_assertions)]
macro_rules! die_impl {
    ($($arg:tt)*) => ({
        panic!($($arg)*);
    })
}

#[cfg(not(debug_assertions))]
macro_rules! die_impl {
    ($($arg:tt)*) => ({
        print!("*** Fatal error: ");
        println!($($arg)*);
        std::process::exit(2);
    })
}
