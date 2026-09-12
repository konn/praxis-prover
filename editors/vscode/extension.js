// The Praxis extension: starts praxis-lsp for .pra and .prf documents.
const { workspace } = require("vscode");
const { LanguageClient, TransportKind } = require("vscode-languageclient/node");

let client;

function activate(context) {
  const command = workspace.getConfiguration("praxis").get("server.path", "praxis-lsp");
  const serverOptions = { command, args: [], transport: TransportKind.stdio };
  const clientOptions = {
    documentSelector: [
      { scheme: "file", language: "pra" },
      { scheme: "file", language: "prf" },
    ],
  };
  client = new LanguageClient("praxis", "Praxis", serverOptions, clientOptions);
  context.subscriptions.push({ dispose: () => deactivate() });
  return client.start();
}

function deactivate() {
  if (!client) {
    return undefined;
  }
  const stopping = client.stop();
  client = undefined;
  return stopping;
}

module.exports = { activate, deactivate };
