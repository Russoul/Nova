{ pkgs, inputs }:
let
  inherit (pkgs) lib;
  deps = import ./deps.nix { inherit pkgs inputs; };

  # With source, so the editor and `idris2 --repl` can jump into them.
  libs = map (l: l.library { withSource = true; }) [
    deps.just-a-parser
    deps.lsp-lib
  ];
in
{
  # A shell where `idris2 --build nova.ipkg` works straight away: the
  # pinned dependencies are already on IDRIS2_PACKAGE_PATH, so nothing
  # is fetched or bootstrapped.
  default = pkgs.mkShell {
    packages = [
      pkgs.idris2
      pkgs.python3 # tools/render-specs.py
    ];

    IDRIS2_PACKAGE_PATH = lib.makeSearchPath "lib/idris2-${pkgs.idris2.version}" libs;

    # Written to stderr so `nix develop -c ...` output stays clean.
    shellHook = ''
      exec 3>&1 1>&2
      echo "Nova dev shell — idris2 ${pkgs.idris2.version}"
      echo "  idris2 --build nova.ipkg     build the elaborator"
      echo "  nix flake check              run every CI gate"
      exec 1>&3 3>&-
    '';
  };
}
