#!/usr/bin/env bash

set -e

cd "$(dirname "$0")"/..

./scripts/generate-metadata.sh
./scripts/format.sh
git --no-pager diff
git --no-pager diff | grep . && exit 1 ||:

source <(grep '^our_version=' scripts/generate-metadata.sh)
git tag "$our_version"
git push --tags


for crate in rate-macros rate-common rate rate-sick-check rate-proof-utils
do
	(
		cd $crate
		cargo publish
	)
	sleep 10
done
