{
  description = "Nova — a type theory with its kernel, elaborator and surface language";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

    # The Idris2 libraries pack.toml pins under [custom.all.*]. The
    # compiler itself, and the `contrib`/`test` libraries that ship with
    # it, come from nixpkgs.
    just-a-parser = {
      url = "github:Russoul/Just-a-Parser/bd6acd473ef0f3fcd1bdc5fba0032b96a7b9313b";
      flake = false;
    };
    lsp-lib = {
      url = "github:idris-community/lsp-lib/512504c6680f9ee45d82f1cc06c596cc0be7c4ea";
      flake = false;
    };
  };

  outputs =
    { self, nixpkgs, ... }@inputs:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
    in
    {
      packages = forAllSystems (
        pkgs:
        let
          novaPkgs = import ./nix/packages.nix { inherit pkgs inputs; };
          vscode = import ./nix/vscode.nix { inherit pkgs inputs; };
        in
        novaPkgs
        // {
          default = novaPkgs.nova;
          vscode-extension = vscode.extension;
        }
      );

      checks = forAllSystems (pkgs: import ./nix/checks.nix { inherit pkgs inputs; });

      devShells = forAllSystems (pkgs: import ./nix/shell.nix { inherit pkgs inputs; });

      apps = forAllSystems (
        pkgs:
        let
          novaPkgs = import ./nix/packages.nix { inherit pkgs inputs; };
          vscode = import ./nix/vscode.nix { inherit pkgs inputs; };
          app = name: {
            type = "app";
            program = "${novaPkgs.${name}}/bin/${name}";
          };
        in
        {
          default = app "nova";
          nova = app "nova";
          nova-lsp = app "nova-lsp";
          nova-docs = app "nova-docs";
          nova-tests = app "nova-tests";

          install-vscode-extension = {
            type = "app";
            program = "${pkgs.lib.getExe vscode.installer}";
          };

          # `packages.vscode-extension` is a .vsix, which contains no
          # executable — so `nix run .#vscode-extension` would fail with
          # a bare "No such file or directory" that reads like a broken
          # build rather than a wrong attribute. Say so instead. It
          # deliberately does NOT just install: a `run` that silently
          # modified the user's editor would be a worse surprise than
          # the error it replaces.
          vscode-extension = {
            type = "app";
            program = "${pkgs.writeShellScript "nova-vscode-extension-hint" ''
              echo "'.#vscode-extension' is a package (a .vsix), not a runnable program." >&2
              echo >&2
              echo "  nix run   .#install-vscode-extension   install it into VS Code" >&2
              echo "  nix build .#vscode-extension           build the .vsix only" >&2
              exit 2
            ''}";
          };
        }
      );

      formatter = forAllSystems (pkgs: pkgs.nixfmt-tree);
    };
}
