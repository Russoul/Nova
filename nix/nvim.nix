# The neovim plugin (editors/nvim) and its installer.
#
# Same bargain as nix/vscode.nix: the server's store path is baked into
# the plugin, so an install from this flake needs no configuration and
# cannot drift out of sync with the nova-lsp it talks to. For neovim
# the drift that matters most is the semantic-token legend — a Lua copy
# of it rots silently when Nova.LSP.Capabilities changes, which is why
# the plugin has no copy and leans on neovim's native support instead.
{ pkgs, inputs }:

let
  inherit (pkgs) lib;
  novaPkgs = import ./packages.nix { inherit pkgs inputs; };

  plugin =
    pkgs.runCommand "nova-nvim-0.1.0"
      {
        src = lib.fileset.toSource {
          root = ../editors/nvim;
          fileset = lib.fileset.unions [
            ../editors/nvim/lua
            ../editors/nvim/ftdetect
            ../editors/nvim/plugin
            ../editors/nvim/README.md
          ];
        };

        nativeBuildInputs = [ pkgs.luajit ];

        meta = {
          description = "Neovim support for Nova, backed by nova-lsp";
          homepage = "https://github.com/Russoul/Nova";
          license = lib.licenses.unlicense;
          platforms = lib.platforms.all;
        };
      }
      ''
        cp -r $src $out
        chmod -R u+w $out

        # `--replace-fail` so that renaming the placeholder breaks the
        # build loudly instead of shipping a plugin that silently falls
        # back to PATH.
        substituteInPlace $out/lua/nova/init.lua \
          --replace-fail "@novaLspPath@" "${novaPkgs.nova-lsp}/bin/nova-lsp"

        # Neovim runs LuaJIT, so a syntax error here would only surface
        # when a user opened a .nova file. Compile every module instead.
        for f in $(find $out -name '*.lua'); do
          luajit -bl "$f" /dev/null
        done
      '';

  # Neovim loads anything under pack/*/start automatically, no plugin
  # manager involved — the closest analogue to `code --install-extension`.
  # NOVA_NVIM_PACK_DIR overrides the target, which is what the flake
  # check uses to install somewhere disposable.
  installer = pkgs.writeShellApplication {
    name = "install-nova-nvim-plugin";
    runtimeInputs = [ pkgs.coreutils ];
    text = ''
      pack_dir="''${NOVA_NVIM_PACK_DIR:-''${XDG_DATA_HOME:-$HOME/.local/share}/nvim/site/pack/nova/start}"
      target="$pack_dir/nova"

      mkdir -p "$pack_dir"
      # A symlink rather than a copy, so `nix store gc` cannot leave a
      # stale half-copy behind and a reinstall is atomic.
      ln -sfn "${plugin}" "$target"

      echo "linked $target -> ${plugin}"
      echo
      echo "Plain neovim loads pack/*/start on its own and the plugin sets"
      echo "itself up — nothing to add. Options go in vim.g.nova = { ... }."
      echo
      echo "With lazy.nvim, or anything else that resets 'packpath', neovim"
      echo "never scans that directory. Add it explicitly in init.lua:"
      echo "    vim.opt.rtp:append(vim.fn.stdpath(\"data\") .. \"/site/pack/nova/start/nova\")"
      echo "    require(\"nova\").setup()"
      echo
      echo "The plugin talks to:"
      echo "  ${novaPkgs.nova-lsp}/bin/nova-lsp"
      echo "Override with setup{ cmd = ... } or \$NOVA_LSP_BIN."
    '';
  };

in
{
  inherit plugin installer;
}
