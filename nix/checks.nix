# The gates, as flake checks.
{ pkgs, inputs }:

let
  inherit (pkgs) lib;
  fs = lib.fileset;

  specs = fs.toSource {
    root = ../.;
    fileset = fs.unions [
      ../docs
      ../tools
      (fs.fileFilter (f: f.hasExt "idr") ../src/idris)
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
  # Rule-shaped citations in src/idris must all be defined by a spec,
  # and rule names must be unique.
  spec-rules = mkCheck "spec-rules" {
    src = specs;
    nativeBuildInputs = [ pkgs.python3 ];
    script = ''
      python3 tools/render-specs.py --check
    '';
  };
}
