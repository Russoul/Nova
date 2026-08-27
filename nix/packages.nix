# The Nova package set: the Idris2 dependencies pinned by pack.toml,
# built with nixpkgs' buildIdris, and the four executables of the repo.
{ pkgs, inputs }:

let
  inherit (pkgs) lib;

  buildIdris = pkgs.idris2Packages.buildIdris;

  deps = import ./deps.nix { inherit pkgs inputs; };
  inherit (deps) just-a-parser lsp-lib;

  # ===== Sources =====
  # Each executable sees only what it compiles from, so an edit to the
  # corpus or the docs tooling does not rebuild the compiler.

  root = ../.;
  fs = lib.fileset;

  idrisSources = fs.fileFilter (f: f.hasExt "idr") ../src/idris;

  mkSrc =
    extra:
    fs.toSource {
      inherit root;
      fileset = fs.unions ([ idrisSources ] ++ extra);
    };

  # The docs site: everything the Pages job of the CI workflow uploads.
  siteSrc = fs.toSource {
    inherit root;
    fileset = fs.unions [
      ../docs
      ../tools
      ../src/nova
      idrisSources
    ];
  };

  mkNova =
    {
      name,
      ipkg,
      extraSrc ? [ ],
      idrisLibraries,
    }:
    (buildIdris {
      ipkgName = name;
      version = "0.1.0";
      src = mkSrc ([ ipkg ] ++ extraSrc);
      inherit idrisLibraries;
    }).executable;

in
rec {
  # The pinned dependencies, as plain derivations so `nix build` can
  # name them.
  idris-just-a-parser = just-a-parser.library';
  idris-lsp-lib = lsp-lib.library';

  # The elaborator/kernel driver: `nova elab`, `nova distill`, ...
  nova = mkNova {
    name = "nova";
    ipkg = ../nova.ipkg;
    idrisLibraries = [ just-a-parser ];
  };

  # The language server.
  nova-lsp = mkNova {
    name = "nova-lsp";
    ipkg = ../nova-lsp.ipkg;
    idrisLibraries = [
      just-a-parser
      lsp-lib
    ];
  };

  # The golden-test driver. Needs the repo's `tests/` tree at runtime.
  nova-tests = mkNova {
    name = "nova-tests";
    ipkg = ../nova-tests.ipkg;
    idrisLibraries = [
      just-a-parser
      lsp-lib
    ];
  };

  # Renders .nova sources to HTML for the docs site.
  nova-docs = mkNova {
    name = "nova-docs";
    ipkg = ../nova-docs.ipkg;
    idrisLibraries = [
      just-a-parser
      lsp-lib
    ];
  };

  # The GitHub Pages site: the rendered specs, the rendered corpus and
  # the landing page — the artifact .github/workflows/nova.yml deploys.
  site = pkgs.runCommand "nova-site" { nativeBuildInputs = [ pkgs.python3 ]; } ''
    cd ${siteSrc}
    mkdir -p $out/nova
    python3 tools/render-specs.py --out $out/specs.html
    ${nova-docs}/bin/nova-docs $out/nova src/nova/*.nova
    cp tools/nova-docs.css $out/nova/
    cp tools/pages-index.html $out/index.html
  '';
}
