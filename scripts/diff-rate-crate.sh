#!/bin/sh

set -u

die() {
  echo "*** error: $@"
  exit 1
}

cd "$(dirname "$0")"/..

./target/release/rate "$1" "$2" --trace > log.rate
test $? -gt 1 && die "rate exited abnormally"
./crate               "$1" "$2" --trace > log.crate
test $? -gt 1 && die "crate exited abnormally"

exec diff log.rate log.crate
