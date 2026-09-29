.PHONY: build dev ci clean

build:
	pack build nova.ipkg

# The local dev loop: build, then the spec-rules check.
dev: build
	python3 tools/render-specs.py --check > /dev/null

# Every flake check.
ci:
	nix flake check

clean:
	rm -rf build
