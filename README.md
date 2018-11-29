# Rate

Rate <sup>[1](#1)</sup> is a DRAT proof checker written in Rust, it is
similar to [drat-trim](https://github.com/marijnheule/drat-trim) or the [GRAT
toolchain](http://www21.in.tum.de/~lammich/grat/). The notable difference is
that it does not [ignore deletion of unit
clauses](https://github.com/marijnheule/drat-trim#clause-deletion-details).

**Note**: This is in a very early stage of development and many features are
still missing.

# Building
Install [Rust](https://www.rust-lang.org/en-US/install.html) and switch to the
nightly channel using [rustup](https://rustup.rs/).  Then you should be able to
run Rate like this:

```sh
$ cargo run --release formula.cnf proof.drat
```
Refer to the [cargo documentation](https://doc.rust-lang.org/cargo/) for other use cases.

# Tests
Currently, there are some unit tests that can be run with `cargo test`.

Additionally, there is a system test suite, that compares the Rate to other
checkers, in particular [rupee](https://github.com/arpj-rebola/rupee) to make
sure we get the same result. Install `python3` (version 3.6 or above) and `pytest` and
run `pytest test.py`.

Currently, we provide a C reimplementation of Rate in [crate.c](crate.c) which
can be built with `make`.  It is useful to catch some bugs early and to measure
the performance of some language features.

# Roadmap
These features are planned to be implemented:

- [x] Specified DRAT
- [ ] Operational DRAT
- [ ] Double-sweep DRAT checking
- [ ] Two watched literals
- [x] Incremental prepropagation
- [ ] Core-first propagation
- [ ] Resolution candidate caching
- [ ] Comprehensive input validation
- [ ] Linearly computing propagation cones
- [ ] Storing deleted traces as permutations
- [ ] On-demand watch relocation
- [ ] On-the-fly decompression

<a name="1">1</a>: "Rate ain't trustworthy either" or "Recursive acronyms tire everyone"
