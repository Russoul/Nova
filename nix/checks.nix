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

  # The .nspec specs are well-formed: every formal line is a judgement of
  # the grammar, every rule name is the foundation's and defined once, and
  # so is every rule-shaped citation in src/ocaml.
  spec-format = mkCheck "spec-format" {
    src = specs;
    nativeBuildInputs = [ pkgs.luajit ];
    script = ''
      luajit tools/nspec.lua
    '';
  };
}
