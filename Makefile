.PHONY: build install test normalize check-roles check-distill dev ci clean

build:
	pack build nova.ipkg
	pack build nova-tests.ipkg
	pack build nova-lsp.ipkg

install:
	pack install-app nova.ipkg

test:
	./test.sh

normalize:
	./normalize-corpus.sh

check-roles:
	./check-roles.sh

check-distill:
	./check-distill.sh

# The FAST pipeline (the local dev loop): build once, then the corpus,
# the golden suite and the roles audit against the built binaries —
# no distill round trip. About a minute on a laptop.
dev: build
	NOVA_BIN=$(CURDIR)/build/exec/nova ./check-elaborations.sh
	NOVA_BIN=$(CURDIR)/build/exec/nova NOVA_LSP_BIN=$(CURDIR)/build/exec/nova-lsp NOVA_TESTS_BIN=$(CURDIR)/build/exec/nova-tests ./test.sh
	./check-roles.sh
	python3 tools/render-specs.py --check > /dev/null

# The FULL pipeline (what CI runs): every flake check, the distill
# round trip and the docs render included.
ci:
	nix flake check

clean:
	rm -rf build
