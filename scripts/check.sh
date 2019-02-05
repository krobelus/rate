#!/usr/bin/env bash

set -u

name=`dirname "$1"`/`basename "$1" | sed 's/\.[^.]*$//'`
shift

rate="cargo run --release -- $name.cnf $name.drat --assume-pivot-is-first $@"

output="$($rate -L "$name".lrat -i "$name".sick)"
echo "$output" | grep -q '^s VERIFIED$' && {
  exec lrat-check-acl2 "$name".{cnf,lrat}
}

echo "$output" | grep -q '^s NOT VERIFIED$' && {
    echo SICK witness
    cat "$name".sick
    echo sickcheck
    sickcheck_output="$(sickcheck "$name".{cnf,drat,sick})"
    echo "$sickcheck_output"
    echo "$sickcheck_output" | grep -qE '(^e|REJECTED)' && {
        echo
        echo RUPEE
        rupee "$name".{cnf,drat} -i rupee.sick
        echo SICK WITNESS
        cat rupee.sick
        exec sickcheck "$name".{cnf,drat} rupee.sick
    } || exit 1
}

echo "$output"
