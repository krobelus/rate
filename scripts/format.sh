#!/bin/bash

cd "$(dirname "$0")"/..

cargo fmt
autopep8 --in-place --aggressive --aggressive *.py scripts/*.py
checkbashisms scripts/*.sh
