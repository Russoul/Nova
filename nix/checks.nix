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

  # The headless neovim test, plus a corpus file for it to open.
  nvimSrc = fs.toSource {
    inherit root;
    fileset = fs.unions [
      ../editors/nvim/test
      ../src/nova
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

  # The reference QUOTES the corpus and the goldens rather than copying
  # them, so its check reads both on top of what the specs check needs.
  reference = fs.toSource {
    inherit root;
    fileset = fs.unions [
      ../docs
      ../tools
      ../src/nova
      ../tests
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

  # The VS Code extension packages, which also proves the nova-lsp path
  # substitution still finds its placeholder in extension.js.
  vscode-extension = (import ./vscode.nix { inherit pkgs inputs; }).extension;

  # Drives a real (headless) neovim with only this plugin on the
  # runtimepath: filetype detection, the baked server path, a live
  # nova-lsp attached to the buffer, the capabilities it advertises,
  # and an actual documentSymbol round trip.
  nvim-plugin =
    let
      nvim = import ./nvim.nix { inherit pkgs inputs; };
    in
    mkCheck "nvim-plugin" {
      src = nvimSrc;
      nativeBuildInputs = [ pkgs.neovim ];
      script = ''
        export HOME=$TMPDIR
        export NOVA_NVIM_PLUGIN=${nvim.plugin}
        nvim --headless -u editors/nvim/test/attach.lua src/nova/nat.nova
      '';
    };

  # Every ```nova block in docs/reference occurs verbatim in src/nova or
  # a golden's input, every ```report block in a golden's expected
  # output, every cited path exists, and every rule-shaped citation
  # names a rule the specs define. Also run by ./test.sh (the Nova Docs
  # pool); repeated here because it needs no Idris build.
  reference = mkCheck "reference" {
    src = reference;
    nativeBuildInputs = [ pkgs.python3 ];
    script = ''
      python3 tools/render-reference.py --check
    '';
  };

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
