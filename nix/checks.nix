# The CI gates of .github/workflows/nova.yml, as flake checks.
{ pkgs, inputs }:

let
  inherit (pkgs) lib;
  novaPkgs = import ./packages.nix { inherit pkgs inputs; };

  root = ../.;
  fs = lib.fileset;

  # Everything the gates read at runtime: the surface corpus, the
  # golden tests and the scripts that drive them.
  corpus = fs.toSource {
    inherit root;
    fileset = fs.unions [
      ../src/nova
      ../tests
      ../check-distill.sh
      ../check-elaborations.sh
      ../test.sh
    ];
  };

  specs = fs.toSource {
    inherit root;
    fileset = fs.unions [
      ../docs
      ../tools
      (fs.fileFilter (f: f.hasExt "idr") ../src/idris)
    ];
  };

  mkCheck =
    name:
    {
      src ? corpus,
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
  # Every src/nova module elaborates with zero obligations, under both
  # the searchless discipline and NOVA_GLOBAL_STORE=1.
  elaborations = mkCheck "elaborations" {
    script = ''
      NOVA_BIN=${novaPkgs.nova}/bin/nova ./check-elaborations.sh
    '';
  };

  # The corpus round-trips through distill and src/nova is in canonical
  # distill form.
  distill = mkCheck "distill" {
    nativeBuildInputs = [ pkgs.diffutils ];
    script = ''
      NOVA_BIN=${novaPkgs.nova}/bin/nova ./check-distill.sh
    '';
  };

  # The golden test suite (parser, derivation, elaboration, evaluation,
  # distill, survey, implicitize and LSP pools), then the elaboration
  # gate — i.e. exactly what ./test.sh runs.
  tests = mkCheck "tests" {
    nativeBuildInputs = [ pkgs.diffutils ];
    script = ''
      export NOVA_TESTS_BIN=${novaPkgs.nova-tests}/bin/nova-tests
      export NOVA_LSP_BIN=${novaPkgs.nova-lsp}/bin/nova-lsp
      export NOVA_BIN=${novaPkgs.nova}/bin/nova
      ./test.sh
    '';
  };

  # The docs site builds: the specs render and every corpus module
  # renders to HTML.
  site = novaPkgs.site;

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
