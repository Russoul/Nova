.PHONY: build install test normalize clean

build:
	pack build nova.ipkg

install:
	pack install-app nova.ipkg

test:
	./test.sh

normalize:
	./normalize-corpus.sh

clean:
	rm -rf build
