#!/usr/bin/env bash

set -u

name=`dirname "$1"`/`basename "$1" | sed 's/\.[^.]*$//'`
shift

test -f "$name".drat && prext=drat
test -f "$name".pr && prext=pr

rate="cargo run -- $name.cnf $name."$prext" --assume-pivot-is-first $@"

output="$($rate -L "$name".lrat -G "$name".grat -i "$name".sick)"

echo "$output"

echo "$output" | grep -q '^s VERIFIED$' && {
  lrat-check "$name".{cnf,lrat} nil t | awk '{print} /^s VERIFIED$/ {ok=1} END{exit !ok}' && \
  exec gratchk unsat "$name".{cnf,grat}
}

echo "$output" | grep -q '^s NOT VERIFIED$' && {
    exec cargo run --bin sickcheck "$name".{cnf,"$prext",sick}
}
