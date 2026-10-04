{ pkgs }:
let
  op = pkgs.ocamlPackages;
in
{
  # A shell where `dune build` works straight away, with the editor
  # tooling that goes with it.
  default = pkgs.mkShell {
    packages = [
      op.ocaml
      op.dune_3
      op.ocaml-lsp
      op.ocamlformat
      op.utop
      pkgs.python3 # tools/render-specs.py
      pkgs.luajit # tools/nspec.lua
    ];

    # Written to stderr so `nix develop -c ...` output stays clean.
    shellHook = ''
      exec 3>&1 1>&2
      echo "Nova dev shell — OCaml ${op.ocaml.version}, dune ${op.dune_3.version}"
      echo "  dune build                   build nova"
      echo "  dune exec -- nova            run it"
      echo "  nix flake check              run every gate"
      exec 1>&3 3>&-
    '';
  };
}
