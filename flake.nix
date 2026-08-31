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
        in
        novaPkgs // { default = novaPkgs.nova; }
      );

      checks = forAllSystems (pkgs: import ./nix/checks.nix { inherit pkgs inputs; });

      devShells = forAllSystems (pkgs: import ./nix/shell.nix { inherit pkgs inputs; });

      apps = forAllSystems (
        pkgs:
        let
          novaPkgs = import ./nix/packages.nix { inherit pkgs inputs; };
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
        }
      );

      formatter = forAllSystems (pkgs: pkgs.nixfmt-tree);
    };
}
