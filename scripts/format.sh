#!/bin/sh

cd "$(dirname "$0")"/..

cargo fmt
git ls-files | grep '\.py$' | xargs autopep8 --in-place --aggressive --aggressive
checkbashisms scripts/*.sh
