.PHONY: build install run

build:
		idris2 --build

install:
		idris2 --install
		idris2 --install-with-src

run:
		rlwrap ./build/exec/nova
