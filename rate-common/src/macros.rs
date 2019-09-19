//! Macros and other utility code.

/// This should be used for every write to stdout.
#[macro_export]
macro_rules! write_to_stdout {
    ($($arg:tt)*) => ({
        use std::io::Write;
        match write!(std::io::stdout(), $($arg)*) {
            Ok(()) => (),
            // Don't panic on SIGPIPE.
            Err(ref err) if err.kind() == std::io::ErrorKind::BrokenPipe =>  std::process::exit(141),
            Err(ref err) =>  panic!("{}", err),
        };
    })
}

/// Implementation of log.
#[macro_export]
macro_rules! _log {
    ($verbosity:expr, $level:expr, $($arg:tt)*) => {
        if $crate::config::ENABLE_LOGGING && $level <= $verbosity
        {
            write_to_stdout!($($arg)*);
            write_to_stdout!("\n");
        }
    }
}

/// Print a formatted message based on verbosity level
#[macro_export]
macro_rules! log {
    ($checker:expr, $level:expr, $($arg:tt)*) => {
        _log!($checker.flags.verbosity, $level, $($arg)*)
    };
}

/// Print something upon scope exit.
// We need this to be a macro to avoid borrowing $checker.
#[macro_export]
macro_rules! defer_log {
    ($checker:expr, $level:expr, $($arg:tt)*) => {
        let verbosity = $checker.flags.verbosity;
        defer!(
            _log!(verbosity, $level, $($arg)*)
            );
    }
}

/// Print to stdout with red font color.
#[macro_export]
macro_rules! warn {
    ($($arg:tt)*) => ({
        use ansi_term;
        let style = if $crate::output::is_a_tty() {
            ansi_term::Colour::Yellow.normal()
        } else {
            ansi_term::Style::default()
        };
        write_to_stdout!("{}", style.paint("Warning: "));
        write_to_stdout!("{}\n", style.paint(&format!($($arg)*)));
    })
}

/// Report a fatal error and exit.
#[macro_export]
macro_rules! die {
    ($($arg:tt)*) => ({
        use ansi_term;
        let style = if $crate::output::is_a_tty() {
            ansi_term::Colour::Red.normal()
        } else {
            ansi_term::Style::default()
        };
        write_to_stdout!("{}", style.paint("Error: "));
        write_to_stdout!("{}\n", style.paint(&format!($($arg)*)));
        std::process::exit(2);
    })
}

/// Native assertions cannot be disabled, that's why why prefer to use this
/// macro.
#[macro_export]
macro_rules! invariant {
    ($($arg:tt)*) => ({
        if $crate::config::CHECK_INVARIANTS {
            assert!($($arg)*);
        }
    })
}

/// Like invariant, but for preconditions.
#[macro_export]
macro_rules! requires {
    ($($arg:tt)*) => ({
        if $crate::config::CHECK_PRECONDITIONS {
            assert!($($arg)*);
        }
    })
}

/// Print to stdout, prefixed by "c ".
#[macro_export]
macro_rules! comment {
    ($($arg:tt)*) => ({
        write_to_stdout!("c ");
        write_to_stdout!($($arg)*);
        write_to_stdout!("\n");
    })
}
