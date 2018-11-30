CFLAGS += -Wno-format
CFLAGS += -O3 -ggdb

crate: crate.c crate-stacks.h
	gcc $< -o $@ $(CFLAGS)

.PHONY: format
format:
	cargo fmt
	clang-format -i *.[ch]
	autopep8 --in-place --aggressive --aggressive *.py

lint:
	checkbashisms scripts/*.sh
