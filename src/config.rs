//! Compile-time and runtime configuration, plus macros

use clap::ArgMatches;

#[derive(Debug, PartialEq, Eq)]
pub struct Config {
    pub skip_deletions: bool,
    pub unmarked_rat_candidates: bool,
    pub trace: bool,
}

impl Config {
    pub fn new(matches: ArgMatches) -> Config {
        let drat_trim = matches.is_present("DRAT_TRIM");
        Config {
            skip_deletions: drat_trim || matches.is_present("SKIP_DELETIONS"),
            unmarked_rat_candidates: drat_trim || matches.is_present("UNMARKED_RAT_CANDIDATES"),
            trace: matches.is_present("TRACE"),
        }
    }
}

pub const DISABLE_CHECKS_AND_TRACING: bool = false;

macro_rules! enabled {
    ($ok:expr) => {
        $ok && !DISABLE_CHECKS_AND_TRACING
    };
}

pub const BOUNDS_CHECKING: bool = enabled!(true);
pub const ASSERTIONS: bool = enabled!(true);
pub const TRACE: bool = enabled!(true);

// print to stdout
macro_rules! echo {
    ($($arg:tt)*) => ({
        println!($($arg)*);
    })
}

macro_rules! _trace {
    ($enabled:expr, $($arg:tt)*) => {{
        if crate::config::TRACE && $enabled
        {
            print!($($arg)*);
        }
    }};
}
macro_rules! trace {
    ($checker:expr, $($arg:tt)*) => {
        _trace!($checker.config.trace, $($arg)*)
    };
}

// Trace upon scope exit without borrowing
macro_rules! defer_trace {
    ($checker:expr, $($arg:tt)*) => {
        let trace = $checker.config.trace;
        defer!(
            _trace!(trace, $($arg)*)
            );
    }
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
