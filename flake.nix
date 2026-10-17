{
  description = "Nova — a type theory with its kernel, elaborator and surface language";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
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
          novaPkgs = import ./nix/packages.nix { inherit pkgs; };
        in
        novaPkgs // { default = novaPkgs.nova; }
      );

      apps = forAllSystems (
        pkgs:
        let
          novaPkgs = import ./nix/packages.nix { inherit pkgs; };
          nova = {
            type = "app";
            program = "${novaPkgs.nova}/bin/nova";
          };
        in
        {
          default = nova;
          inherit nova;
        }
      );

      checks = forAllSystems (pkgs: import ./nix/checks.nix { inherit pkgs; });

      devShells = forAllSystems (pkgs: import ./nix/shell.nix { inherit pkgs; });

      formatter = forAllSystems (pkgs: pkgs.nixfmt-tree);
    };
}
