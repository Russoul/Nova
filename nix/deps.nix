# The Idris2 library pack.toml pins under [custom.all.*], built with
# nixpkgs' buildIdris. `contrib` needs no derivation here: it ships
# with the compiler, and the idris2 wrapper already puts it on the
# package path.
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
}
