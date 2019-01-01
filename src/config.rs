//! Compile-time and runtime configuration, plus macros

use clap::ArgMatches;

#[derive(Debug)]
pub struct Config {
    pub skip_deletions: bool,
    pub unmarked_rat_candidates: bool,
    pub pivot_is_first_literal: bool,
    pub no_core_first: bool,
    pub verbosity: u64,
    pub lrat_filename: Option<String>,
    pub sick_filename: Option<String>,
}

pub const DISABLE_CHECKS_AND_LOGGING: bool = cfg!(feature = "fast");

macro_rules! enabled {
    ($ok:expr) => {
        $ok && !DISABLE_CHECKS_AND_LOGGING
    };
}

pub const BOUNDS_CHECKING: bool = enabled!(true);
pub const ASSERTIONS: bool = enabled!(true);
pub const LOGGING: bool = enabled!(true);

// print to stdout
macro_rules! echo {
    ($($arg:tt)*) => ({
        println!($($arg)*);
    })
}

// print based on verbosity level
macro_rules! _log {
    ($verbosity:expr, $level:expr, $($arg:tt)*) => {
        if crate::config::LOGGING && $level <= $verbosity
        {
            print!($($arg)*);
            print!("\n");
        }
    };
}

macro_rules! log {
    ($checker:expr, $level:expr, $($arg:tt)*) => {
        _log!($checker.config.verbosity, $level, $($arg)*)
    };
}

// Trace upon scope exit without borrowing
macro_rules! defer_log {
    ($checker:expr, $level:expr, $($arg:tt)*) => {
        let verbosity = $checker.config.verbosity;
        defer!(
            _log!(verbosity, $level, $($arg)*)
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

macro_rules! invariant {
    ($($arg:tt)*) => ({
        if crate::config::ASSERTIONS {
            assert!($($arg)*);
        }
    })
}

macro_rules! requires {
    ($($arg:tt)*) => ({
        if crate::config::ASSERTIONS {
            assert!($($arg)*);
        }
    })
}

pub fn unreachable() -> ! {
    invariant!(false, "unreachable");
    unsafe { std::hint::unreachable_unchecked() }
}

impl Config {
    pub fn new(matches: ArgMatches) -> Config {
        let drat_trim = matches.is_present("DRAT_TRIM");
        let rupee = matches.is_present("RUPEE");
        Config {
            skip_deletions: drat_trim || matches.is_present("SKIP_DELETIONS"),
            unmarked_rat_candidates: !drat_trim && matches.is_present("UNMARKED_RAT_CANDIDATES"),
            pivot_is_first_literal: rupee || matches.is_present("ASSUME_PIVOT_IS_FIRST"),
            no_core_first: matches.is_present("NO_CORE_FIRST"),
            verbosity: match matches.occurrences_of("v") {
                i if i > 4 => {
                    warn!("verbosity can be at most 3");
                    4
                }
                i => i,
            },
            lrat_filename: matches.value_of("LRAT_FILE").map(String::from),
            sick_filename: matches.value_of("SICK_FILE").map(String::from),
        }
    }
}
