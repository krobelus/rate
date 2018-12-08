#!/bin/sh

set -e -u

cd "$(dirname "$0")/.."

root="$(pwd)"

cd benchmarks
mkdir -p random
cd random

while true
do
  "$root"/scripts/random-instance.py > tmp.cnf
  cadical tmp.cnf tmp.drat --binary=false | grep -q '^s UNSATISFIABLE' || {
    echo s SATISFIABLE; continue
  }
  sed 1q tmp.cnf
  rupee tmp.* | grep '^s ACCEPTED'
  rupee=$?
  rate tmp.* | grep '^s ACCEPTED'
  rate=$?
  test $rupee -eq $rate
done
