#!/usr/bin/env bash

set -u

name=`dirname "$1"`/`basename "$1" | sed 's/\.[^.]*$//'`
shift

test -f "$name".drat && {
    prext=drat
    args="-L $name.lrat -G $name.grat"
}
test -f "$name".dpr && {
    prext=dpr
    args=
}
rate="cargo run --bin rate -- $name.cnf $name."$prext" $@"

output="$($rate $args -S "$name".sick)"

echo "$output"

echo "$output" | grep -q '^s VERIFIED$' && test $prext = drat && {
  lrat-check "$name".{cnf,lrat} nil t | awk '{print} /^s VERIFIED$/ {ok=1} END{exit !ok}' && \
  exec gratchk unsat "$name".{cnf,grat}
}

echo "$output" | grep -q '^s NOT VERIFIED$' && {
    exec cargo run --bin sick-check "$name".{cnf,"$prext",sick}
}
