#!/bin/sh

# execute a given command at a version of this repository.
#
# usage: exec-in-version.sh <commit-ish> command ...
#
# the versions used by this script will be stored in checkouts/
#
# stdout will be exactly the one of the given command but this script may print to stderr

set -e -u

die() {
  echo "*** error: $@" >/dev/stderr
  exit 1
}

cd "$(dirname "$0")"/..

commit="$(git rev-parse "$1")"
shift

checkouts=checkouts

mkdir -p "$checkouts"

dest="$checkouts"/"$commit"
test -d "$dest" || {
  git clone .git "$dest" &&
    git -C "$dest" checkout "$commit"
  }

cd "$dest"
exec "$@"
