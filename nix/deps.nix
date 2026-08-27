# The Idris2 libraries pack.toml pins under [custom.all.*], built with
# nixpkgs' buildIdris. `contrib` and `test` need no derivation here:
# they ship with the compiler, and the idris2 wrapper already puts them
# on the package path.
#
# Each attribute is a buildIdris result — a {executable, library,
# library'} set, which is what `idrisLibraries` expects.
{ pkgs, inputs }:

let
  buildIdris = pkgs.idris2Packages.buildIdris;
in
{
  just-a-parser = buildIdris {
    ipkgName = "just-a-parser";
    version = "0.1.1";
    src = inputs.just-a-parser;
    idrisLibraries = [ ];
  };

  lsp-lib = buildIdris {
    ipkgName = "lsp-lib";
    version = "0.5.0";
    src = inputs.lsp-lib;
    idrisLibraries = [ ];
  };
}
