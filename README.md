# rate

[![crates.io](https://img.shields.io/crates/v/rate.svg)](https://crates.io/crates/rate)
[![CircleCI branch](https://img.shields.io/circleci/project/github/krobelus/rate/master.svg)](https://circleci.com/gh/krobelus/rate/tree/master)
![](https://img.shields.io/crates/l/rate.svg)

This is a proof checker that can verify proofs produced by a
[SAT](https://en.wikipedia.org/wiki/Boolean_satisfiability_problem)
solver.  It supports proofs in the
[DRAT](http://www.cs.cmu.edu/~mheule/publications/drat-trim.pdf)
or [DPR](http://www.cs.cmu.edu/~mheule/publications/spr.pdf)
format; `rate` is very similar to
[`drat-trim`](https://github.com/marijnheule/drat-trim),
[`dpr-trim`](https://www.cs.utexas.edu/~marijn/pr/) or
[`gratgen`](http://www21.in.tum.de/~lammich/grat/). The notable
difference is that `rate` does not [ignore deletions of unit
clauses](https://github.com/marijnheule/drat-trim#clause-deletion-details)
by default.

# Features
- check DRAT proofs (default) and DPR proofs (file extension`.pr` or `.dpr`)
- competitive performance (faster than `drat-trim` and `dpr-trim`, almost as
  fast as `gratgen`)
- output a trimmed proof as DRAT, DPR, LRAT or GRAT after verifying a proof
- check and output a SICK certificate of incorrectness after rejecting a proof
- optionally ignore unit deletions for compatibility with `drat-trim`
  (flag `--skip-unit-deletions`)
- transparently read compressed input files (Gzip, Zstandard, Bzip2, XZ, LZ4)
- detect and report many errors like numeric overflows
- mostly safe Rust, should not have any undefined behavior

# Installation

Install [Rust](https://www.rust-lang.org/en-US/install.html).  Recent versions
of stable Rust are supported (e.g. 1.36 or later).

## Stable version

Releases are hosted on [crates.io](https://crates.io/) and can be
installed using `cargo`, Rust's package manager.

```sh
$ cargo install rate --force
```

After this has finished compiling, it will place the `rate` binary in
`~/.cargo/bin/`.

## Building from source

Alternatively, you can install the development version from a checkout of this
repository:

```sh
$ git clone https://github.com/krobelus/rate
$ cd rate
$ cargo install --path ./rate --force
```

# Usage

Run the proof checker like this:
```sh
$ rate formula.cnf proof.drat
```

Whenever the proof is accepted, this will exit with code 0 after printing
`s VERIFIED` and some metrics. See `rate --help` for more options.

## SICK certificates

If `rate` rejects a proof, it outputs and checks a certificate
of incorrectness that tells you which proof step failed and why..
The certificate can also be checked again with the `sick-check` binary
which is much faster than a full proof checker (install `sick-check`
using `cargo install rate-sick-check` for a stable version, or `cargo
install --path rate-sick-check` to install from a local checkout). These
certificates are useful to protect against bugs in the checker code.

## Other utilities

Install the crate `rate-proof-utils` (just like `rate` or
`rate-sick-check`) for some binaries that can be useful when working
with clausal proofs:

- `drat2bdrat` and `bdrat2drat` convert a DRAT proof to the [Binary DRAT Format]
  and vice versa. Also works for DPR proofs.
- `apply-proof` applies a proof up to a given proof step, and outputs the
  accumulated formula as well as the rest of the proof. This can be very
  useful for delta-debugging a tool that works with proofs.

[Binary DRAT Format]: <https://github.com/marijnheule/drat-trim#binary-drat-format>

# Unexpected rejections

If you are using a solver based on
[MiniSat](https://github.com/niklasso/minisat), then your proof might
be rejected by `rate` while it is accepted by other checkers, like
`drat-trim`. This is because the proof can contain some clause deletions
that are ignored by other checkers. There are two options:

1. Use `rate --skip-unit-deletions` to make it behave like other checkers.

2. Alternatively, you can patch your solver to not generate those extra
deletions.  This will make the proof valid for every checker.  Look for
`reason deletions shrinking trail` in the output of `rate`; this is the
number of deletions in the proof that delete information - it should
probably be zero, unless you are using certain advanced inprocessing
techniques.  Example patches that avoid these deletions: Minisat
([1](https://github.com/krobelus/minisat/commit/keep-locked-clauses) or
[2](https://github.com/krobelus/minisat/commit/add-unit-before-deleting-locked-clause)),
and `MapleLCMDistChronoBT`
([1](https://github.com/krobelus/MapleLCMDistChronoBT/commit/keep-locked-clauses)
or
[2](https://github.com/krobelus/MapleLCMDistChronoBT/commit/add-unit-before-deleting-locked-clause)).

# Caveats

Please note that `rate` accepts proofs that are technically not fully
correct.  Just like other checkers, we perform some transformations
on the proof before actually verifying the proofs steps.  This is done
to improve performance.  These transformations can ignore unnecessary
clauses or proof steps.  These are effectively removed from the formula
or proof, respectively.  This means that `rate` might accept a proof
that contains lemmas that are not valid inferences, but this should
never happen for satisfiable formulas.

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
  in a clause, unless `--assume-pivot-is-first` is specified.

[here]: <http://www21.in.tum.de/~lammich/grat/gratgen-doc/Unmarked_RAT_Candidates.html>

# Tests

Run unit tests and the system test suite, respectively:

```sh
cargo test && ./test.py
```

You can also selectively run tests, for example use `./test.py -k default
benchmarks/crafted benchmarks/sadical/add4.cnf` to only run test functions
matching `default` on the crafted benchmarks and on `add4.{cnf,dpr}`.

Above tests require
- `python3` (version 3.6 or above)
- optionally any of the following executables:
  - [`lrat-check`](https://github.com/acl2/acl2/tree/master/books/projects/sat/lrat)
    to validate the produced LRAT proofs.
  - [`pr2drat`](https://github.com/marijnheule/pr2drat) to produce
    DRAT and LRAT proofs from PR proofs.
  - `gratchk` to validate produced GRAT proofs.
  - If any of `drat-trim`, `rupee`, or `gratgen` are executable they will be
    run on the benchmarks and their verdicts will be compared to the output of
    `rate`.

You can use the [docker
image](https://cloud.docker.com/repository/docker/krobelus/rate-test-environment)
used by our [CI](.circleci/config.yml) which contains [builds of above
dependencies](scripts/test-environment/).

# Documentation

Find some background information and a performance evaluation in my [thesis].

[thesis]: <https://github.com/krobelus/rate-experiments/blob/master/thesis.pdf>

The source code includes an abundance of doc comments. Use
this command to turn them into internal documentation at
`target/doc/{rate*,sick_check,apply_proof,bdrat2drat,drat2bdrat}/index.html`.
```sh
$ cargo doc --document-private-items --no-deps
```

# Contributing

Please let us know if `rate` behaves in a way that is unexpected to you,
or if you need some feature.  We currently do not guarantee stability of the
library modules in `rate-common` (only the binaries are considered an API),
but we can integrate more tools that work on proofs in this repository.

# Roadmap

Some possible improvements:

- expose a Rust (and possibly C) API
- support other clausal proof formats
- compute other features about clausal proofs (e.g. the lifespan of clauses)
- speed up handling of reason clause deletions that do not shrink the trail
- speed up RAT checks by caching resolution candidates
