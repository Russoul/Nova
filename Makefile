.PHONY: build install test normalize check-roles clean

build:
	pack build nova.ipkg

install:
	pack install-app nova.ipkg

test:
	./test.sh

normalize:
	./normalize-corpus.sh

check-roles:
	./check-roles.sh

clean:
	rm -rf build
