.PHONY: build dev test promote ci clean

build:
	dune build

# The local dev loop: build, then the spec-rules check.
dev: build
	python3 tools/render-specs.py --check > /dev/null

# The unit tests and the golden tests of the kernel.
test:
	dune test

# Rewrite the golden tests' expected outputs from the current binary;
# review the diff before committing.
promote: build
	bash tests/kernel/run.sh _build/default/src/ocaml/bin/main.exe --promote tests/kernel

# Every flake check.
ci:
	nix flake check

clean:
	dune clean
