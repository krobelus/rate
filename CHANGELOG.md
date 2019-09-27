# Unreleased

- Deprecate options --drat-trim and --rupee, they can be replaced by
  --skip-unit-deletions and --assume-pivot-is-first respectively.
  Also, gratgen-like behavior can be simulated with --noncore-rat-candidates.
- Deprecate option -i/--recheck in favor of -S/--sick to produce a SICK
  certificate.
- Hide option -m/--memory-breakdown, it's probably not interesting to users.
- Report an error when the input proof is not seekable (e.g. a pipe). We
  require seekable proofs to support detecting whether it is a binary proof.

# 0.1.0 (2019-09-19)

Initial release
