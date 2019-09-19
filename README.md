# rate

[![crates.io](https://img.shields.io/crates/v/rate.svg)](https://crates.io/crates/rate)
![](https://img.shields.io/crates/l/rate.svg)

This is a DRAT/DPR proof checker written in Rust, similar to
[`drat-trim`](https://github.com/marijnheule/drat-trim) or `gratgen` from the
[GRAT toolchain](http://www21.in.tum.de/~lammich/grat/). The notable
difference is that it does not [ignore deletions of unit
clauses](https://github.com/marijnheule/drat-trim#clause-deletion-details) by
default.

# Features
- check DRAT (default) and PR (file extension `.pr` or `.dpr`) proofs
- output core lemmas as DIMACS, LRAT or GRAT for verified proofs
- output certificate of unsatisfiability for rejected proofs
- competitive performance due to double-sweep checking with
  core-first unit propagation
- option to ignore unit deletions (`--skip-unit-deletions`)
- transparently read compressed input files (Gzip, Zstandard, Bzip2, XZ, LZ4)

# Installation

Install [Rust](https://www.rust-lang.org/en-US/install.html).  Recent versions
of stable Rust are supported (e.g. 1.36 or later).

## Stable version

Releases are hosted on [crates.io](https://crates.io/) and can be installed
using `cargo`, Rust's package manager.

```sh
$ cargo install rate --force
```

After this has finished compiling, it will place the `rate` binary in
`~/.cargo/bin/`.

## Building from source

Alternatively, you can install the development version from a checkout of this
repository:

```sh
$ cargo install --path rate --force
```

Other binaries are provided in the crates `rate-sick-check` and
`rate-proof-utils` and can be installed by substituting `rate` with the
crate name in above commands.

# Usage

Run the proof checker like this:
```sh
$ rate formula.cnf proof.drat
```

Whenever the proof is accepted, this will exit with code 0 after printing
`s VERIFIED` and some metrics. See `rate --help` for more options.

## SICK certificates

If `rate` rejects a proof, it can output a certificate of incorrectness that
tells you which proof step failed and why.  The certificate can also be
checked by the `sick-check` binary which tries to make sure that the rejection
of the proof is justified.

```sh
$ rate formula.cnf proof.drat --recheck failure.sick ||
  sick-check formula.cnf proof.drat failure.sick
```

If `rate` rejects the proof, it prints `s NOT VERIFIED` exits with status 1.
Subsequently, if `sick-check` prints `s VERIFIED`, it means that the proof is
also incorrect according to `sick-check`.  If `sick-check` prints `s NOT
VERIFIED`, that is likely a bug in either tool.

## Other utilities

Crate `rate-proof-utils` contains several binaries that can be useful when
working with clausal proofs:

- `drat2bdrat` and `bdrat2drat` convert a DRAT proof to the [Binary DRAT Format]
  and vice versa.
- `apply-proof` applies a proof up to a given proof step, and outputs the
  accumulated formula as well as the rest of the proof. This can be very
  useful for delta-debugging a tool that works with proofs

[Binary DRAT Format]: <https://github.com/marijnheule/drat-trim#binary-drat-format>

# Caveats

Please note that `rate` accepts proof that are technically not fully correct,
Just like other checkers, we perform some transformations on the proof before
actually verifying the individual steps.  This is done to improve performance.
Some transformations on the proof virtually ignore some clauses in the
formula and some instructions in the proof. They are effectively removed.
This means that `rate` might accept a proof that contains lemmas that are
not correct inferences, but this should never happen for satisfiable formulas.

Here are the transformations we do:
- If `--skip-unit-deletions` is specified, then deletions of clauses that
  are unit with respect to the accumulated formula are ignored, as in
  `drat-trim` and `gratgen`.
- When traversing the proof, we stop as soon as a conflict is inferred.
  Any proof steps thereafter are ignored.  This means that an explicit empty
  clause at the end of the proof is not required.
- Clauses and lemmas that are not part of the reason for above conflict
  are ignored, even if they could be resolution candidates, find an explanation
  why this is sound [here].
- RAT checks are done upon every possible pivot and not just the first literal
  in a clause.

[here]: <http://www21.in.tum.de/~lammich/grat/gratgen-doc/Unmarked_RAT_Candidates.html>

# Tests

Run unit tests and the system test suite, respectively:

```sh
cargo test && pytest test.py
```

If you're in a hurry use `pytest test.py -k quick` to only run the system
tests with small input files.

Above tests require
- `python3` (version 3.6 or above)
- `pytest`
- optionally any of the following executables:
  - [`lrat-check`](https://github.com/acl2/acl2/tree/master/books/projects/sat/lrat)
    to validate the produced LRAT proofs.
  - If any of `drat-trim`, `rupee`, or `gratgen` are executable they will be
    run on the benchmarks and their results will be compared to the output of
    `rate` in the respective compatibility mode.

# Documentation

Find some background information and a performance evaluation in the [master's thesis].

[master's thesis]: <https://github.com/krobelus/rate-experiments/blob/master/thesis.pdf>

The source code includes an abundance of doc comments. They can be turned
to developer documentation in `target/doc/rate*/index.html` like so:
```sh
$ cargo doc --document-private-items
```

# Contributing

Please let us know if `rate` behaves in a way that is unexpected to you,
or if you need some feature. Tools that work with clausal proofs can be
built on top of this. If this is desired we recommend to integrate that
in this repository since we do not guarantee stability of the library
modules crates (only the binaries are considered an API).

# Roadmap

Some things that might be useful.

- expose a subset of the library modules as Rust (and possibly C) API
- support other clausal proof formats
- compute other features about clausal proofs (e.g. the lifespan of clauses)
- speed up handling of reason clauses that do not shrink the trail
- speed up RAT checks by caching resolution candidates
- improve compilation times
