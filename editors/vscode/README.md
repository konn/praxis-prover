# Praxis for VS Code

Language support for the files of the Praxis prover: `.pra` files of
theorems and rules, and `.prf` files of definitions. The extension
highlights them and runs `praxis-lsp`, which checks every declaration as it
is edited, reports a failing tactic at its position and a `sorry` with the
goal it stopped at, and shows the goal a tactic faces on hover.

## Installing

Build the server and put it on the path, then package and install the
extension:

```bash
cabal install praxis-lsp
cd editors/vscode
npm install
npx @vscode/vsce package
code --install-extension praxis-0.1.0.vsix
```

The setting `praxis.server.path` names the server when it is not on the
path, such as the executable `cabal list-bin praxis-lsp` prints.
