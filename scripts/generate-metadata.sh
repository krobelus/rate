#!/bin/sh

set -eu

cd "$(dirname "$0")"/..

rate="Clausal proof checker (DRAT, DPR) for certifying SAT solvers' unsatisfiability results"
rate_common="Internal modules for rate"
rate_proof_utils="Utilities for clausal proofs (DRAT, DPR)"
rate_macros="Internal macros for rate"
rate_sick_check="Verify SICK certificates of proof incorrectness produced by rate"

for crate in rate*
do
	id="$(echo $crate | sed s/-/_/g)"
	description="$(eval echo \$$id)"
	sed "s/^description = .*/description = \"$description\"/" -i $crate/Cargo.toml
	cat > $crate/README.md << EOF
# $crate

$description
EOF
done

sed 1c"//! $rate"		-i rate/rate.rs
sed 1c"//! $rate_common"	-i rate-common/src/lib.rs
sed 1c"//! $rate_macros"	-i rate-macros/lib.rs
sed 1c"//! $rate_sick_check"	-i rate-sick-check/sick-check.rs

# This will break when we include another crate using `version = ...` syntax.
our_version="0.1.0"
sed -E -i 's/version = "[0-9]+\.[0-9]+\.[0-9]+"/version = "'$our_version'"/' */Cargo.toml

(
	script='sed -i rate*/Cargo.toml'
	while read package equals version
	do
		script="$script -e 's/^$package .*/$package = $version/'"
		:
	done
	eval $script
) << EOF
ansi_term = "0.11"
atty = "0.2"
bitfield = "0.13"
bzip2 = "0.3"
clap = "2.32"
derive_more = "0.15"
flate2 = "1.0"
libc = "0.2"
lz4 = "1.23"
proc-macro2 = "0.4"
quote = "0.6"
scopeguard = "1.0"
serde = "1.0"
serde_derive = "1.0"
static_assertions = "0.3"
syn = "0.15"
toml = "0.5"
xz2 = "0.1"
zstd = "0.4"
EOF