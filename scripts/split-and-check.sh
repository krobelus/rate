#!/bin/sh

set -eu

formula="$1"
proof="$2"
ext="${proof##*.}"

N="${3:-2}"
verbose="${4:-}"
logN="$(python3 -c "from math import log, ceil; print(ceil(log($N, 10)))")"

checker() {
	drat-trim "$@" -f -I
}

log() {
	test -z "$verbose" && return
	printf "# " >/dev/stderr
	echo "$@" >/dev/stderr
}

log "Splitting proof in $N chunks"

split-proof "$formula" "$proof" "$N"

check_part() {
	part="$1"
	log "Checking part $part"
	patched_formula="grep -v '^c' $formula "
	for i in $(seq 0 "$((part - 1))")
	do
		id="$(printf %0${logN}d $i)"
		patched_formula="$patched_formula | sed -f $proof.$id.sed"
		:
	done
	id="$(printf %0${logN}d $part)"
	proof_chunk="$proof.$id.$ext"
	log "patched formula: $patched_formula"
	log "stored in: $proof.$id.xcnf"
	log "proof chunk: $proof_chunk"
	sh -c "$patched_formula" | checker /dev/stdin "$proof_chunk"
}

# TODO use env_parallel.sh
. "$(which env_parallel.bash)"

(
    for part in $(seq 0 $((N - 2)))
    do
	printf %s\\n "check_part $part | \
            	grep -q -E '(c ERROR: all lemmas verified|s VERIFIED)'"
    done
    printf %s\\n "check_part $((N - 1)) | grep -q 's VERIFIED'"
) | env_parallel
