# The Nova package set: the nova executable, built with dune.
{ pkgs }:

let
  inherit (pkgs) lib;
  fs = lib.fileset;

  # The build sees only what it compiles from, so an edit to the
  # corpus or the docs does not rebuild it.
  src = fs.toSource {
    root = ../.;
    fileset = fs.unions [
      ../dune-project
      ../src/ocaml
    ];
  };

in
{
  nova = pkgs.ocamlPackages.buildDunePackage {
    pname = "nova";
    version = "0.1.0";
    inherit src;
    duneVersion = "3";
  };
}
