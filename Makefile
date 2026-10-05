.PHONY: build dev test promote ci clean

# tools/nspec.lua runs under luajit, or under Neovim's own Lua.
LUA := $(shell command -v luajit >/dev/null 2>&1 && echo luajit || echo nvim -l)

build:
	dune build

# The local dev loop: build, then the spec check.
dev: build
	$(LUA) tools/nspec.lua

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
