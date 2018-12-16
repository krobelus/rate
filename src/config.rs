//! Compile-time and runtime configuration, plus macros

use clap::ArgMatches;
use std::fs::File;

#[derive(Debug)]
pub struct Config {
    pub skip_deletions: bool,
    pub unmarked_rat_candidates: bool,
    pub verbosity: u64,
    pub lrat: bool,
    pub lrat_file: File,
}

pub const NO_WATCHES: bool = true;

pub const DISABLE_CHECKS_AND_LOGGING: bool = false;

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

macro_rules! ensure {
    ($($arg:tt)*) => ({
        if crate::config::ASSERTIONS {
            assert!($($arg)*);
        }
    })
}

impl Config {
    pub fn new(matches: ArgMatches) -> Config {
        let drat_trim = matches.is_present("DRAT_TRIM");
        let mut config = Config {
            skip_deletions: drat_trim || matches.is_present("SKIP_DELETIONS"),
            unmarked_rat_candidates: drat_trim || matches.is_present("UNMARKED_RAT_CANDIDATES"),
            verbosity: match matches.occurrences_of("v") {
                i if i > 3 => {
                    warn!("verbosity can be at most 3");
                    3
                }
                i => i,
            },
            lrat: matches.is_present("LRAT_FILE"),
            // TODO
            lrat_file: File::open("/dev/null").unwrap(),
        };
        if config.lrat {
            let filename = matches.value_of("LRAT_FILE").unwrap();
            config.lrat_file = File::create(filename)
                .map_err(|err| die!("failed to open LRAT file {}: {}", filename, err))
                .unwrap();
        }
        config
    }
}
