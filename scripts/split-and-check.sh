#!/bin/sh

set -eu

formula="$1"
proof="$2"

ext="${proof##*.}"

N="${3:-2}"


logN="$(python3 -c "from math import log, ceil; print(ceil(log($N, 10)))")"

echo $logN

split "$proof" "$proof" \
	--additional-suffix=".$ext" \
	--number=l/$N --suffix-length=$logN --numeric-suffixes

# produces "$proof".XXX.sed
split-proof "$formula" "$proof" "$N"

check_part() {
	part="$1"
	lastpart="$2"
	patched_cnf="cat $formula "
	for i in $(seq 1 "$((part - 1))")
	do
		i4="$(printf %0${logN}d $i)"
		patched_cnf="$patched_cnf | sed -f $proof-$i4.diff"
		:
	done
	part2="$(printf %02d $part)"
	sh -c "$patched_cnf" > $formula.part.$part2
	echo drat-trim "$name".cnf.part.$part2 "$name".drat.part.$part2
	# bat "$name".cnf.part.$part2 "$name".drat.part.$part2
	sh -c "$patched_cnf" | drat-trim /dev/stdin "$name".drat.part.$part2 -f |
	(if test $part = "$lastpart"; then
	    grep -q 's VERIFIED'
	else
            grep -q 'c ERROR: all lemmas verified'
	fi
	)
}

for part in $(seq 1 $N)
do
    check_part $part $N
done
