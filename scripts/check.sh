#!/bin/sh

set -u

name=`dirname "$1"`/`basename "$1" .`

cargo run --release "$name".{cnf,drat} -L "$name".lrat -i "$name".sick --assume-pivot-is-first && {
  echo
  echo LRAT PROOF
  cat "$name".lrat
  echo
  echo lratcheck
  lratcheck "$name".{cnf,lrat}
  echo
  echo lrat-check
  exec lrat-check "$name".{cnf,lrat}
} || {
  echo
  echo SICK WITNESS
  cat "$name".sick
  echo sickcheck
  sickcheck "$name".{cnf,drat,sick}
  sickcheck "$name".{cnf,drat,sick} | grep -qE '(^e|REJECTED)' && {
    echo
    echo RUPEE
    rupee "$name".{cnf,drat} -i rupee.sick
    echo SICK WITNESS
    cat rupee.sick
    exec sickcheck "$name".{cnf,drat} rupee.sick
  }
}
