//! Macros and other utility code

/// This should be used for every write to stdout.
#[macro_export]
macro_rules! puts {
    ($($arg:tt)*) => ({
        use std::io::Write;
        match write!(std::io::stdout(), $($arg)*) {
            Ok(()) => (),
            // Don't panic on SIGPIPE.
            Err(ref err) if err.kind() == std::io::ErrorKind::BrokenPipe => std::process::exit(141),
            Err(ref err) =>  panic!("{}", err),
        };
    })
}

/// Print to stdout, prefixed by "c ".
#[macro_export]
macro_rules! comment {
    ($($arg:tt)*) => ({
        $crate::puts!("c ");
        $crate::puts!($($arg)*);
        $crate::puts!("\n");
    })
}

/// Print to stdout with yellow font color.
#[macro_export]
macro_rules! as_warning {
    ($what:expr) => {{
        if $crate::output::is_a_tty() {
            $crate::puts!("\x1b[33;1m");
        }
        $what;
        if $crate::output::is_a_tty() {
            $crate::puts!("\x1b[0m");
        }
    }};
}

/// Print to stdout with red font color.
#[macro_export]
macro_rules! as_error {
    ($what:expr) => {{
        if $crate::output::is_a_tty() {
            $crate::puts!("\x1b[31;1m");
        }
        $what;
        if $crate::output::is_a_tty() {
            $crate::puts!("\x1b[0m");
        }
    }};
}

/// Report a fatal error and exit.
#[macro_export]
macro_rules! die {
    ($($arg:tt)*) => ({
        $crate::as_error!({
            $crate::puts!($($arg)*);
            $crate::puts!("\n");
        });
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
