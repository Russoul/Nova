.PHONY: build install run

clean:
		rm -rf build

build-api:
		idris2 --build nova-api.ipkg

build-bin:
		idris2 --build nova-bin.ipkg

install-api:
		idris2 --install-with-src nova-api.ipkg

install-bin:
		idris2 --install nova-bin.ipkg

run:
		rlwrap ./build/exec/nova

test:
		./build/exec/nova
