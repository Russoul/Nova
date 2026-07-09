.PHONY: build install run test clean

clean:
		rm -rf build

build:
		pack build nova-foundation.ipkg

install:
		idris2 --install-with-src nova-foundation.ipkg

run:
		rlwrap ./build/exec/nova-foundation-app

test:
		./test.sh
