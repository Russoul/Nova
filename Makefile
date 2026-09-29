.PHONY: build dev ci clean

build:
	dune build

# The local dev loop: build, then the spec-rules check.
dev: build
	python3 tools/render-specs.py --check > /dev/null

# Every flake check.
ci:
	nix flake check

clean:
	dune clean
