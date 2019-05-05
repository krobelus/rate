#!/usr/bin/env bash

set -eu

formula="$1"
proof="$2"
ext="${proof##*.}"

N="${3:-2}"
verbose="${4:-}"
logN="$(python3 -c "from math import log, ceil; print(ceil(log($N, 10)))")"

checker() {
	# force textual proof with -I (needs patch)
	# drat-trim "$@" -f -I
	rate --forward "$@"
}

log() {
	test -z "$verbose" && return
	printf "# $@\n" >> /dev/stderr
}

log "Splitting proof in $N chunks"

split-proof "$formula" "$proof" "$N"

check_part() {
	part="$1"
	shift
	log
	log "Checking part $part"
	patched_formula="grep -v '^c' $formula "
	for i in $(seq 0 "$((part - 1))")
	do
		id="$(printf %0${logN}d $i)"
		patched_formula="$patched_formula | sed -f $proof.$id.sed"
	done
	id="$(printf %0${logN}d $part)"
	proof_chunk="$proof.$id.$ext"
	log "patched formula: $patched_formula"
	log "proof chunk: $proof_chunk"
	sh -c "$patched_formula" | checker "$@" /dev/stdin "$proof_chunk"
}

# TODO make it work for sh
. "$(which env_parallel.bash)"

(
    for part in $(seq 0 $((N - 2)))
    do
	printf %s\\n \
		"check_part $part --no-terminating-empty-clause"
    done
    printf %s\\n "check_part $((N - 1))"
) |
env_parallel --group --keep-order |
awk "
					{ if(\"$verbose\") print \$0 }
/all lemmas verified, but no conflict/	{ ok=1 }
/s NOT VERIFIED/			{ if(ok) ok=0; else exit }
/s VERIFIED/				{ verified=1; exit }
END					{ exit !verified }
"
# tee $output |
