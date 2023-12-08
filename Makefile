.PHONY: build install run

clean:
		rm -rf build

build:
		idris2 --build

install:
		idris2 --install-with-src

run:
		rlwrap ./build/exec/nova
