.PHONY: format lint
format:
	cargo fmt
	autopep8 --in-place --aggressive --aggressive *.py scripts/*.py

lint:
	checkbashisms scripts/*.sh
