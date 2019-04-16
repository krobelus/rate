#!/bin/sh

set -eu

# TODO this assumes the proof is textual

formula="$1"
proof="$2"
ext="${proof##*.}"

N="${3:-2}"
verbose="${4:-}"
logN="$(python3 -c "from math import log, ceil; print(ceil(log($N, 10)))")"
lines="$(wc -l < "$proof")"
lines_per_chunk="$(python3 -c "from math import floor; print(floor($lines / $N))")"

checker() {
	drat-trim "$@" -f -I
}

log() {
	test -z "$verbose" && return
	printf "# " >/dev/stderr
	echo "$@" >/dev/stderr
}

log "Splitting proof in $N chunks"

# produces "$proof".XXX.drat
#TODO
# split "$proof" "$proof". \
# 	--additional-suffix=".$ext" \
# 	--suffix-length=$logN --numeric-suffixes \
# 	--lines="$lines_per_chunk"
	# --number=l/$N 

# produces "$proof".XXX.sed
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
        # TODO remove this
        sh -c "$patched_formula" > "$proof".$id.xcnf
	sh -c "$patched_formula" | checker /dev/stdin "$proof_chunk"
}

for part in $(seq 0 $((N - 2)))
do
        # out="$(check_part $part ||:)"
        # echo "$out"
	# echo "$out" | grep 'early EOF' && exit 123 ||:
	check_part $part |
	grep -q -E '(c ERROR: all lemmas verified|s VERIFIED)'
done
check_part $((N - 1)) |
	tee /dev/stderr |
grep -q 's VERIFIED'
