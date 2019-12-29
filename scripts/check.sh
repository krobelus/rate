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
    args="-l $name.core.pr"
}
cargo build
rate=target/debug/rate

echo $rate $args -S "$name".sick $@ -- "$name".cnf "$name"."$prext"
output="$($rate $args -S "$name".sick $@ -- "$name".cnf "$name"."$prext")"

echo "$output"

if echo "$output" | grep -q '^s VERIFIED$'; then
	if test $prext = drat; then
		lrat-check "$name".{cnf,lrat} nil t | awk '{print} /^s VERIFIED$/ {ok=1} END{exit !ok}' &&
		exec gratchk unsat "$name".{cnf,grat}
	elif test $prext = dpr; then
		pr2drat "$name".{cnf,core.pr} > "$name".core.drat &&
		$rate "$name".{cnf,core.drat} -L "$name.lrat" &&
		exec lrat-check "$name".{cnf,lrat} nil t | awk '{print} /^s VERIFIED$/ {ok=1} END{exit !ok}'
	fi
fi

echo "$output" | grep -q '^s NOT VERIFIED$' && {
    exec cargo run --bin sick-check "$name".{cnf,"$prext",sick}
}
