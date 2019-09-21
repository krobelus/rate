# Unreleased

- Fix documentation of compatibility flag --drat-trim, error out when using it
  with --noncore-rat-candidates.
- Deprecate option -i/--recheck in favor of -S/--sick to produce a SICK
  certificate.
- Report an error when the input proof is not seekable (e.g. a pipe) because we
  don't want to jump through hoops to detect binary DRAT in those cases.
- Hide option -m/--memory-breakdown, it's probably not interesting to users.

# 0.1.0 (2019-09-19)

Initial release
