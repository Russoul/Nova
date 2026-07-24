.PHONY: build install test clean

build:
	pack build nova.ipkg

install:
	pack install-app nova.ipkg

test:
	./test.sh

clean:
	rm -rf build
