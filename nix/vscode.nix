# The VS Code extension (editors/vscode) and its installer.
#
# The extension is a thin client for nova-lsp, and the point of
# building it here is that the server's store path is baked into it: an
# extension installed from this flake needs no `nova.lsp.path` setting
# and cannot drift out of sync with the server it talks to, because
# both come from the same commit.
{ pkgs, inputs }:

let
  inherit (pkgs) lib;
  novaPkgs = import ./packages.nix { inherit pkgs inputs; };

  version = "0.1.0";

  extension = pkgs.buildNpmPackage {
    pname = "nova-vscode";
    inherit version;

    src = lib.fileset.toSource {
      root = ../editors/vscode;
      fileset = lib.fileset.unions [
        ../editors/vscode/package.json
        ../editors/vscode/package-lock.json
        ../editors/vscode/extension.js
        ../editors/vscode/language-configuration.json
        ../editors/vscode/syntaxes
        ../editors/vscode/README.md
        ../editors/vscode/LICENSE
        ../editors/vscode/.vscodeignore
      ];
    };

    # Regenerate after any package-lock.json change with:
    #   nix run nixpkgs#prefetch-npm-deps -- editors/vscode/package-lock.json
    npmDepsHash = "sha256-zruurSCLe1UGuvI+WunXLl6QYEXU6XjKTbjZGNYEcmw=";

    nativeBuildInputs = [ pkgs.vsce ];

    # Plain JavaScript — there is no compile step to run.
    dontNpmBuild = true;

    # The whole reason this derivation exists. `--replace-fail` so that
    # renaming the placeholder in extension.js breaks the build loudly
    # instead of shipping an extension that silently falls back to PATH.
    postPatch = ''
      substituteInPlace extension.js \
        --replace-fail "@novaLspPath@" "${novaPkgs.nova-lsp}/bin/nova-lsp"
    '';

    # vsce bundles the production node_modules that npm ci just
    # installed, so the packaged extension carries its one dependency.
    installPhase = ''
      runHook preInstall
      mkdir -p $out
      vsce package --out $out/nova.vsix
      runHook postInstall
    '';

    meta = {
      description = "VS Code support for Nova, backed by nova-lsp";
      homepage = "https://github.com/Russoul/Nova";
      license = lib.licenses.unlicense;
      platforms = lib.platforms.all;
    };
  };

  # Shape (C): install explicitly, rather than a devShell that writes
  # into the user's ~/.vscode or a wrapped editor that hides their own
  # extensions. `nix run .#install-vscode-extension`.
  installer = pkgs.writeShellApplication {
    name = "install-nova-vscode-extension";
    runtimeInputs = [ pkgs.coreutils ];
    text = ''
      vsix="${extension}/nova.vsix"

      # $VSCODE_BIN first, so a fork or a non-standard install can be
      # named explicitly. The macOS .app path is worth probing because
      # the `code` shell command there is opt-in — installed from the
      # command palette — and is missing on a fresh install.
      candidates=(
        "''${VSCODE_BIN:-}"
        code
        codium
        code-insiders
        cursor
        "/Applications/Visual Studio Code.app/Contents/Resources/app/bin/code"
        "/Applications/VSCodium.app/Contents/Resources/app/bin/codium"
      )

      editor=""
      for candidate in "''${candidates[@]}"; do
        [ -n "$candidate" ] || continue
        if command -v "$candidate" > /dev/null 2>&1; then
          editor="$candidate"
          break
        fi
      done

      if [ -z "$editor" ]; then
        echo "no VS Code found on PATH (tried: code, codium, code-insiders, cursor)." >&2
        echo "Set VSCODE_BIN=/path/to/code, or install the vsix by hand:" >&2
        echo "  $vsix" >&2
        exit 1
      fi

      echo "installing $vsix into $editor"
      "$editor" --install-extension "$vsix" --force

      echo
      echo "Installed. Reload VS Code to activate it."
      echo "The extension talks to:"
      echo "  ${novaPkgs.nova-lsp}/bin/nova-lsp"
      echo "Override with the nova.lsp.path setting or \$NOVA_LSP_BIN."
    '';
  };

in
{
  inherit extension installer;
}
