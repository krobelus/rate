//! Compile-time and runtime configuration, plus macros

use clap::ArgMatches;

pub const DISABLE_CHECKS_AND_TRACING: bool = false;

macro_rules! enabled {
    ($ok:expr) => {
        $ok && !DISABLE_CHECKS_AND_TRACING
    };
}
pub const BOUNDS_CHECKING: bool = enabled!(true);
pub const ASSERTIONS: bool = enabled!(true);
pub const TRACE: bool = enabled!(true);

#[derive(Debug, PartialEq, Eq)]
pub struct Config {
    pub trace: bool,
    pub skip_deletions: bool,
}

impl Config {
    pub fn new(matches: ArgMatches) -> Config {
        Config {
            trace: matches.is_present("TRACE"),
            skip_deletions: matches.is_present("SKIP_DELETIONS"),
        }
    }
}

// print to stdout
macro_rules! echo {
    ($($arg:tt)*) => ({
        println!($($arg)*);
    })
}

macro_rules! trace {
    ($constants:expr, $($arg:tt)*) => {{
        if crate::config::TRACE && $constants.config.trace
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

macro_rules! ensure {
    ($($arg:tt)*) => ({
        if crate::config::ASSERTIONS {
            assert!($($arg)*);
        }
    })
}
