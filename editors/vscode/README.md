# Praxis for VS Code

Language support for the files of the Praxis prover: `.px` modules of the
surface language, `.pra` files of theorems and rules, and `.prf` files of
definitions. The extension highlights them and runs `praxis-lsp`, which
checks every declaration as it is edited, reports a failing tactic at its
position and a `sorry` with the goal it stopped at, colours every name by
what it is, goes to definitions, and shows the goal a tactic faces on hover
in `.pra` files.

The grammars know the names of the languages, `append-nil` and
`Semigroup-List.(<>).unfold-Nil` dashes and all, the keywords of imports,
data types in the GADT style, classes and instances, and the words of the
tactic language. The server refines the colours with semantic tokens: a
data type, a constructor, a function, a theorem, a class, a method, a
module, a type variable, a value or a variable each in its own colour, and
a tactic word a keyword only where it is one. Semantic highlighting is
turned on for the three languages whatever the theme says.

## Installing

Build the server and put it on the path, then package and install the
extension:

```bash
cabal install praxis-lsp
cd editors/vscode
npm install
npx @vscode/vsce package
code --install-extension praxis-0.3.0.vsix
```

The setting `praxis.server.path` names the server when it is not on the
path, such as the executable `cabal list-bin praxis-lsp` prints.
