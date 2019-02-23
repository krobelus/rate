# rate

This is a DRAT/DPR proof checker written in Rust, it is similar to
[`drat-trim`](https://github.com/marijnheule/drat-trim) or `gratgen`
from the [GRAT toolchain](http://www21.in.tum.de/~lammich/grat/). The
notable difference is that it does not [ignore deletions of unit
clauses](https://github.com/marijnheule/drat-trim#clause-deletion-details)
by default.

# Features
- check DRAT (default) and PR (file extension `.pr`) proofs
- output core lemmas as DIMACS or LRAT for accepted proofs
- output certificate of unsatisfiability for rejected proofs
- competitive performance due to double-sweep checking with
  core-first unit propagation
- option to ignore unit deletions (`--skip-unit-deletions`)

# Building
Install [Rust](https://www.rust-lang.org/en-US/install.html). Then you should be
able to run `rate` like this:

```sh
$ cargo run --release formula.cnf proof.drat
```
Refer to the [cargo documentation](https://doc.rust-lang.org/cargo/) for other use cases.

# Tests
There are some unit tests that can be run with `cargo test`.

Additionally, there is a system test suite, that compares the output of `rate` to
previous versions of itself, and to other checkers, in particular
[rupee](https://github.com/arpj-rebola/rupee).
This can be run with `pytest test.py`. The requirements are:

- `python3` (version 3.6 or above)
- `pytest`
- [`lrat-check`](https://github.com/acl2/acl2/tree/master/books/projects/sat/lrat),
  [`sick-check`](https://github.com/arpj-rebola/rupee/blob/master/src/check/sickchecker.cpp),
  `drat-trim`, `rupee`, and `gratgen` need to be executable on your system.

If you're in a hurry use `pytest test.py -k quick` to only run the tests on
small input files.

# Caveats

Please note that `rate` accepts proof that are technically not fully
correct, Just like other checkers, we perform some transformations
on the proof before actually verifying the individual steps.  This is
done to improve performance, and the unsatisfiability of a formula can
still be certified. This means that `rate` might accept a proof that
contains lemmas that are not redundant, but this should not happen for
satisfiable formulas.

Here are the transformations we do:
- When doing the forward pass through the proof, we stop as soon as a
  conflict is inferred.  Any clauses after a conflict are ignore.
  This means that an explicit empty clause at the end of the proof is
  not required.
- Lemmas that are not part of the reason for the above conflict are not
  checked, thus they are effectively removed from the proof.
- Clauses and lemmas that are not part of the reason for the conflict are not
  considered as resolution candidates for the RAT check, just like `gratgen`.
- If `--skip-unit-deletions` is specified, then deletions of clauses that are unit
  with respect to the current assignment are ignored, as in `drat-trim`.
- RAT checks are done upon every possible pivot and not just the first literal
  in a clause.

# Contributing

Please let us know if `rate` behaves in a way that is unexpected to you,
or if you need some feature. Possible features include:

- expose Rust (and possibly C) API
- On-the-fly decompression
- Resolution candidate caching (can speed up RAT checks)
- Strict input validation
