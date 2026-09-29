# The gates, as flake checks.
{ pkgs }:

let
  inherit (pkgs) lib;
  fs = lib.fileset;
  novaPkgs = import ./packages.nix { inherit pkgs; };

  specs = fs.toSource {
    root = ../.;
    fileset = fs.unions [
      ../docs
      ../tools
      ../src/ocaml
    ];
  };

  mkCheck =
    name:
    {
      src,
      nativeBuildInputs ? [ ],
      script,
    }:
    pkgs.runCommand "nova-check-${name}"
      {
        nativeBuildInputs = [ pkgs.bash ] ++ nativeBuildInputs;
      }
      ''
        cp -r ${src} ./repo
        chmod -R u+w ./repo
        cd ./repo
        patchShebangs . > /dev/null
        ${script}
        touch $out
      '';

in
{
  # The executable builds.
  nova = novaPkgs.nova;

  # Rule-shaped citations in src/ocaml must all be defined by a spec,
  # and rule names must be unique.
  spec-rules = mkCheck "spec-rules" {
    src = specs;
    nativeBuildInputs = [ pkgs.python3 ];
    script = ''
      python3 tools/render-specs.py --check
    '';
  };
}
