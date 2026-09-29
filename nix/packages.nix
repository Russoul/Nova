# The Nova package set: the Idris2 dependency pinned by pack.toml,
# built with nixpkgs' buildIdris, and the nova library.
{ pkgs, inputs }:

let
  inherit (pkgs) lib;

  buildIdris = pkgs.idris2Packages.buildIdris;

  deps = import ./deps.nix { inherit pkgs inputs; };
  inherit (deps) just-a-parser;

  fs = lib.fileset;

  # The library sees only what it compiles from, so an edit to the
  # corpus or the docs does not rebuild it.
  src = fs.toSource {
    root = ../.;
    fileset = fs.unions [
      (fs.fileFilter (f: f.hasExt "idr") ../src/idris)
      ../nova.ipkg
    ];
  };

in
{
  # The pinned dependency, as a plain derivation so `nix build` can
  # name it.
  idris-just-a-parser = just-a-parser.library';

  # nova.ipkg: the library.
  nova =
    (buildIdris {
      ipkgName = "nova";
      version = "0.1.0";
      inherit src;
      idrisLibraries = [ just-a-parser ];
    }).library';
}
