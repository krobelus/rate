# Unreleased

- Fix PR check ignoring deletions

# 0.2.2 (2019-09-30)

- Fix unsound rejections by `rate --forward`
- Correctly implement flag `--noncore-rat-candidates`

# 0.2.1 (2019-09-28)

- Fix documentation of compatibility flag --drat-trim, error out when using it
  with --noncore-rat-candidates.
- Deprecate option -i/--recheck in favor of -S/--sick to produce a SICK
  certificate.
- Report an error when the input proof is not seekable (e.g. a pipe) because we
  don't want to jump through hoops to detect binary DRAT in those cases.
- Hide option -m/--memory-breakdown, it's probably not interesting to users.

# 0.1.0 (2019-09-19)

Initial release
