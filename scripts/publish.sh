#!/bin/sh

set -eu

cd "$(dirname "$0")"/..

version="$1"

# require clean worktree
git --no-pager diff
git --no-pager diff | grep . && exit 1 ||:

./scripts/generate-metadata.sh "$version"
git commit -am "release $version"
git tag "$version"
git push
git push --tags

for crate in rate-macros rate-common rate rate-sick-check rate-proof-utils
do
	(
		cd $crate
		cargo publish
	)
	sleep 10
done
