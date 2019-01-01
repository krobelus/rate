# Rate

Rate <sup>[1](#1)</sup> is a DRAT proof checker written in Rust, it is similar
to [drat-trim](https://github.com/marijnheule/drat-trim) or the [GRAT
toolchain](http://www21.in.tum.de/~lammich/grat/). The notable difference is
that it does not [ignore deletions of unit
clauses](https://github.com/marijnheule/drat-trim#clause-deletion-details) by
default.

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
There are some minor unit tests that can be run with `cargo test`.

Additionally, there is a system test suite, that compares the output of Rate to
previous versions of itself, and to other checkers, in particular
[rupee](https://github.com/arpj-rebola/rupee).
This can be run with `pytest test.py`. The requirements are:

- `python3` (version 3.6 or above)
- `pytest`
- `drat-trim` and `rupee` need to be executable on your system.

## Crate

Currently we provide a reimplementation of Rate in C (see [crate.c](crate.c)).
Note that it may be lagging behind in terms of features. Anyway, it is useful to
us to catch some bugs and measure the performance impact of some language
features. Build `./crate` by typing `make`.

# Contributing

We appreciate contributions. Please let us know if Rate behaves in a way that is
unexpected to you, or if you need some feature.

# Caveats

Please note that, Rate accepts proof that are technically not fully correct,
We perform some transformations on the proof before actually checking the
steps, mainly to improve performance, as do other checkers. So this might
result in a proof that contains some invalid instructions being accepted, but
this should only be possible for unsatisfiable formulas.

Here are the transformations we do:
- We discard any lemma or deletion after the first time the empty clause
  (conflict) is inferred. In particular this means that an explicit empty
  clause at the end of the proof is not required.
- Lemmas that are not part of the reason for the above conflict are not
  checked, thus they are effectively removed from the proof.
- Clauses and lemmas that are not part of the reason for the conflict are not
  considered as resolution candidates for the RAT check. The reason why this
  is sound is a bit tricky.
- If `--skip-deletions` is specified, then deletions of clauses that are unit
  with respect to the current assignment are ignored, as in drat-trim.
- RAT checks are done upon every possible pivot and not just the first literal
  in a clause.

# Roadmap
These features are planned to be implemented:

- [x] Specified DRAT
- [x] Operational DRAT
- [x] Double-sweep DRAT checking
- [x] Two watched literals
- [x] Incremental prepropagation
- [ ] Core-first propagation
- [ ] Resolution candidate caching
- [ ] Comprehensive input validation
- [x] Linearly computing propagation cones
- [x] Storing deleted traces as permutations
- [x] On-demand watch relocation
- [ ] On-the-fly decompression

<a name="1">1</a>: "Rate ain't trustworthy either" or "Recursive acronyms tire everyone"
