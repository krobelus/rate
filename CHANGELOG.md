# Unreleased
- Fix PR check giving false positives given empty witnesses.
- Fix PR check giving false positives due to not adding clauses to the
  core (except for the root conflict).
- Fix PR checking with flag -d/--skip-unit-deletions.
- Incorrectness certificates are now always checked internally when a
  proof is rejected. In that case the formula and proof files are
  opened again when checking the certificate.
- Improve output for rejected proofs (print the line of failed step).
- Fix wrong literal order in --lemmas output for PR
- Make --lemmas print the optimized proof instead of simply all core
  lemmas (just like drat-trim); this makes the output a core also for
  non-monotonic proof formats RAT and PR.
- Remove metric "skipped tautologies".

# 0.2.3 (2019-10-09)

- Fix bug in PR check where deletions would be ignored.
- Rewrite logging (flag -v) to print one line for each processed lemma;
  see tracking issue at https://github.com/krobelus/rate/issues/9

# 0.2.2 (2019-09-30)

- Fix unsound rejections by `rate --forward`.
- Correctly implement flag `--noncore-rat-candidates`.

# 0.2.1 (2019-09-28)

- SICK certificates for proofs without an empty clause now must not contain
  the `proof_step` attribute (previously it was the size of the proof + 1).
- Deprecate option --no-terminating-empty-clause, now we explicitly handle
  rejected proofs without an empty clause (printing "no conflict").
- Deprecate options --drat-trim and --rupee, they should be replaced by
  --skip-unit-deletions and --assume-pivot-is-first respectively.
  Also, gratgen-like behavior can be simulated with --noncore-rat-candidates.
- Deprecate option -i/--recheck in favor of -S/--sick to produce a SICK
  certificate.
- Hide option -m/--memory-breakdown, it's probably not interesting to users.
- Report an error when the input proof is not seekable (e.g. a pipe). We
  require seekable proofs to support detecting whether it is a binary proof.

# 0.1.0 (2019-09-19)

Initial release
