// A thin LSP client for nova-lsp.
//
// Everything the editor shows — diagnostics, hover, go-to-definition,
// document symbols, semantic highlighting — comes from the server
// (src/idris/Nova/LSP). This file only starts it, points it at the
// right binary, and renders the one Nova-specific extension to the
// protocol: the `nova/elabTime` notification.
//
// Plain JavaScript on purpose. The single runtime dependency is
// vscode-languageclient, which keeps the dependency tree — and the
// npmDepsHash that nix/vscode.nix pins to it — small and stable.

const fs = require("fs");
const vscode = require("vscode");
const { LanguageClient, TransportKind } = require("vscode-languageclient/node");

// Replaced at build time with the store path of the nova-lsp this
// extension was built against (nix/vscode.nix). Left as the literal
// placeholder in the source tree, where it means "nothing was baked in"
// — hence the `@` test in resolveServer rather than a truthiness test.
const BAKED_SERVER_PATH = "@novaLspPath@";

let client = null;
let statusItem = null;

// uri string -> { millis, modules }, the last load reported for each
// document. Kept per-uri rather than as a single "latest", so switching
// tabs shows that tab's timing instead of whichever file was saved last.
const elabTimes = new Map();

// ===== server resolution =====

// Four sources, most explicit first. NOVA_LSP_BIN outranks the baked
// path so that `nix develop` and the test suite — which both already
// set it (test.sh, nix/checks.nix) — can point the editor at a
// freshly-built server without editing settings.
function resolveServer() {
  const configured = vscode.workspace
    .getConfiguration("nova")
    .get("lsp.path", "")
    .trim();
  if (configured !== "") {
    return { command: configured, source: "the nova.lsp.path setting" };
  }

  const fromEnv = (process.env.NOVA_LSP_BIN || "").trim();
  if (fromEnv !== "") {
    return { command: fromEnv, source: "$NOVA_LSP_BIN" };
  }

  if (!BAKED_SERVER_PATH.startsWith("@")) {
    return { command: BAKED_SERVER_PATH, source: "the Nix build" };
  }

  return { command: "nova-lsp", source: "PATH" };
}

// ===== elaboration time =====

// Matches tools/nova-elabtime.lua, so the two editors report the same
// number the same way.
function formatMillis(millis) {
  return millis >= 1000 ? `${(millis / 1000).toFixed(1)}s` : `${millis}ms`;
}

function refreshStatusItem() {
  if (statusItem === null) {
    return;
  }

  const show = vscode.workspace
    .getConfiguration("nova")
    .get("elabTime.show", true);
  const editor = vscode.window.activeTextEditor;
  if (!show || !editor || editor.document.languageId !== "nova") {
    statusItem.hide();
    return;
  }

  const report = elabTimes.get(editor.document.uri.toString());
  if (report === undefined) {
    statusItem.hide();
    return;
  }

  const time = formatMillis(report.millis);
  statusItem.text = `$(watch) ${time}`;
  statusItem.tooltip = `Nova: type checked in ${time} (${report.modules} modules)`;
  statusItem.show();
}

// ===== lifecycle =====

async function startClient(context) {
  const server = resolveServer();

  // An absolute path that is not there is worth catching here: the
  // client's own failure is a spawn ENOENT deep in an output channel,
  // which does not say which of the four sources produced the path.
  if (server.command.includes("/") && !fs.existsSync(server.command)) {
    vscode.window.showErrorMessage(
      `Nova: no nova-lsp at ${server.command} (from ${server.source}). ` +
        `Build one with \`nix build .#nova-lsp\` or \`pack build nova-lsp.ipkg\`, ` +
        `or set nova.lsp.path.`,
    );
    return;
  }

  const serverOptions = {
    command: server.command,
    transport: TransportKind.stdio,
  };

  const clientOptions = {
    documentSelector: [{ scheme: "file", language: "nova" }],
    outputChannelName: "Nova Language Server",
  };

  client = new LanguageClient(
    "nova",
    "Nova Language Server",
    serverOptions,
    clientOptions,
  );

  // Registered before start() so the first load's report is not missed:
  // the server sends nova/elabTime immediately after the diagnostics of
  // the didOpen that start() triggers.
  client.onNotification("nova/elabTime", (params) => {
    if (!params || typeof params.uri !== "string") {
      return;
    }
    elabTimes.set(vscode.Uri.parse(params.uri).toString(), {
      millis: params.millis || 0,
      modules: params.modules || 0,
    });
    refreshStatusItem();
  });

  await client.start();
  context.subscriptions.push(client);
}

async function stopClient() {
  if (client === null) {
    return;
  }
  const stopping = client;
  client = null;
  await stopping.stop();
}

async function activate(context) {
  statusItem = vscode.window.createStatusBarItem(
    vscode.StatusBarAlignment.Right,
    100,
  );
  context.subscriptions.push(statusItem);

  context.subscriptions.push(
    vscode.window.onDidChangeActiveTextEditor(refreshStatusItem),
    vscode.workspace.onDidChangeConfiguration((event) => {
      if (event.affectsConfiguration("nova.elabTime.show")) {
        refreshStatusItem();
      }
    }),
  );

  context.subscriptions.push(
    vscode.commands.registerCommand("nova.restartServer", async () => {
      await stopClient();
      // Stale timings would otherwise survive a restart and be shown
      // against a server that never produced them.
      elabTimes.clear();
      refreshStatusItem();
      await startClient(context);
    }),
    vscode.commands.registerCommand("nova.showServerLog", () => {
      if (client !== null) {
        client.outputChannel.show();
      }
    }),
  );

  await startClient(context);
}

async function deactivate() {
  await stopClient();
}

module.exports = { activate, deactivate };
