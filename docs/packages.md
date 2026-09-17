# Packages, projects and modules

A module of the surface language ([surface.md](surface.md)) rarely stands
alone. This document describes how modules are grouped into libraries,
libraries into packages and packages into projects, how modules import one
another, and how names are resolved across them. The code is in
`praxis/src/Language/Praxis/Package/` (manifests, versions, the build) and
`praxis/src/Language/Praxis/Surface/Rename.hs` (scope).

```
project        project.toml          several packages, and the constraints on versions
└─ package     package.toml          metadata, and its components
   └─ library  [[lib]]               a source directory of modules, and its dependencies
      └─ module  src/Data/List.px    one top-level module per file, named by its path
```

## Packages: `package.toml`

A package is a directory holding `package.toml`: a header of metadata, and
a section per component. Only libraries exist so far; tests, benchmarks and
executables are planned.

```toml
[package]
name = "lists"
version = "0.1.2.0"
synopsis = "lists, their append, and its lemmas"   # optional

[[lib]]                       # the main library: unnamed
source-dir = "src"

[[lib]]                       # a sublibrary: named
name = "extra"
source-dir = "src-extra"
dependencies = ["lists"]
```

A package has exactly one main library, the `[[lib]]` without a `name`; a
package with the main library alone may write it as a single `[lib]` table.
`source-dir` defaults to `src`. Every `.px` file under a library's source
directory is a module of it, named by its path: `src/Data/List.px` is
`Data.List`. There are no hidden modules: a library exposes all of them.

Components are referred to by paths, `[package]:[kind]:[name]`. The main
library is named as its package, `lists`, or in full, `lists:lib:lists`; a
sublibrary is `lists:lib:extra`, or, in an import and in a dependency,
`lists:extra`. A sublibrary cannot be named `lib`, `exe`, `test` or `bench`.

A package name is words of letters and digits joined by dashes, each with a
letter, as in Cabal. A version follows the Package Versioning Policy: a
dot-separated sequence of naturals, compared as sequences (`1` before
`1.0`), whose first two components are its major version.

### Dependencies

`dependencies` lists, per library, the libraries it may import from: a
package, meaning its main library, or a sublibrary, each with the versions
of the package accepted, in Cabal's syntax:

```toml
dependencies = ["lists ^>= 0.1", "lists:extra", "other >= 1 && < 2"]
```

A range omitted accepts every version. The syntax is comparisons — `>=`,
`>`, `<=`, `<`, `==` — the major bound `^>= A.B.C` (from `A.B.C` below
`A.(B+1)`), the wildcard `== A.B.*`, `-any` and `-none`, joined by `&&` and
`||`, `&&` binding tighter, grouped by parentheses.

There is no repository of packages yet: a dependency must be a package of
the same project, at a version its range accepts.

## Projects: `project.toml`

A project is several packages, as a Cabal project is: the directories
holding them, and the constraints on versions which hold throughout.

```toml
[project]
packages = ["packages/*", "core"]
constraints = ["lists >= 0.1", "other == 1.*"]
```

A path ending in `*` stands for every subdirectory holding a
`package.toml`. A constraint is on a package, never on a library, and is
declared here and nowhere else: a package declares what *it* depends on,
with the versions it accepts; a project declares what holds for all of its
packages together. A package whose version violates a constraint, or a
dependency whose range no package of the project satisfies, is refused
before anything is checked. A `package.toml` alone, with no `project.toml`
above it, is a project of that package.

## Modules and files

A file is one top-level module, named by its path within the library's
source directory. Its header, `module Data.List where`, is optional; when
written it must name the module the path does. Outside any package a file
is checked on its own, its header naming it, or `Main`.

A module may contain modules, as in Agda: `module N where` and its
declarations, laid out deeper than the enclosing ones or in braces. A
nested module is a namespace of the enclosing one holding what it exports,
`Data.List.Length.length`; inside it, the declarations of the enclosing
modules are in scope. After it, its members are reached qualified,
`Length.length`, or by `open Length`.

```
module Data.List where

data List a = Nil | a : List a

(<>) : List a -> List a -> List a
…

private
  append-nil-aux : {a : Type} -> (xs : List a) -> xs <> Nil ≡ xs
  …

append-nil : {a : Type} -> (xs : List a) -> xs <> Nil ≡ xs
append-nil {a} xs = append-nil-aux xs

module Length where
  length : List a -> Nat
  …
```

What a module declares it exports, unless declared under `private`, which
takes a block of declarations: a private name is in scope in its module,
and in the modules nested in it, and nowhere else, not even qualified. A
module also exports what it opens `public`.

A module exports its names: its data types, functions, theorems, classes,
methods, laws, instances and nested modules. Constructors live in the
namespace of their type, not of the module: after `import Data.List`, the
constructor is `Data.List.List.Nil`, after `open Data.List` it is
`List.Nil`, and it is `Nil` after `open List` — or, as within a module,
where its type is expected of it (see § Names).

## Imports

```
import Data.List                              -- Data.List.append-nil, Data.List.List.Nil
import Data.List as L                         -- L.append-nil
import Data.List using (List, append-nil)     -- these members only
import Data.List hiding (append-nil)
import Data.List renaming ((<>) to (++))      -- Data.List.(++)
open Data.List                                -- append-nil, List, unqualified
open Data.List using (List) renaming ((<>) to (++)) public   -- and exported
open import Data.List                         -- imported, and opened
```

`import M` brings the exports of `M` into scope qualified, by the name of
`M` or by the one after `as`; imports may stand anywhere among the
declarations, and are in scope from where they stand. `open N` brings the
members of a namespace into unqualified scope: a module in scope, imported
or nested; a data type, its constructors; a class, its methods and laws; an
instance, its functions. `open N public` also exports them, so that a
module may gather several. `open import M …` imports and opens at once.

The directives follow Agda. `using (a, b)` takes the members named and no
other; `hiding (a)` leaves those named out; `renaming (a to b; c to d)`
takes each by its new name, whether or not `using` names it. `using` and
`hiding` exclude one another; a name none of the members has is an error.
An operator among the names is written in parentheses, `(<>)`.

The fixities of a module's operators travel with them: an imported
operator has the fixity its module declares, unless the importing module
declares one itself. An operator renamed keeps no fixity.

### Which library

An import names a module of the library itself, or of one of its
dependencies. Where two dependencies expose a module of one name, the
import must say which, in the syntax of Haskell's `PackageImports`:

```
import "lists" Data.List as L
import "other" Data.List as O
import "lists:extra" Data.List.Extra
```

The string names a package, meaning its main library, or a sublibrary,
`pkg:name`. A module of the library itself shadows a dependency's of the
same name.

Two libraries may expose modules of one name, and both may be in scope:
their globals are distinct, by the library heading their canonical names
(§ Names), down to the core, where `u_lists_sData_sList_sList_sis` and
`u_other_sData_sList_sList_sis` are two predicates.

### Order

A project is checked library by library, each after those it depends on,
and within a library module by module, each after those it imports. Modules
importing one another, directly or through others, are refused, at their
imports. The whole project is checked against one core: each module's
definitions and certified lemmas extend it for the modules after, and a
module names another's only through its imports.

## Names

Name resolution is a pass of its own, the renamer (`Rename.hs`), between
the association of operators and elaboration. It reads the scope —
declarations, imports, openings, nesting, privacy — and rewrites every
reference to a global as its canonical name: the library, the module, the
namespaces, then the name, which elaboration looks up in one table without
any scope. Scope errors are reported there, before any typing, each failing
the declaration it is in.

An unqualified name is resolved, in order, as

1. a variable bound around it — a pattern's, a binder's, a hypothesis
   named in a tactic;
2. a name declared by the module or by one enclosing it — a data type, a
   function, a theorem, a class, a method, a law, an instance, a nested
   module;
3. a member of an opened namespace; two opened namespaces giving it
   distinct globals which are not all constructors make it ambiguous;
4. otherwise as written: a constructor found by the type expected of it,
   among the constructors of the data types of the file and of the modules
   imported, or the only one of that name among them; a builtin, `S`,
   `absurd`; a lemma of the core's library, by its name; a hypothesis; a
   type variable in a signature; or nothing, which elaboration reports.

A qualified name is resolved through its first segments: a namespace in
unqualified scope, `List.Nil`, `Length.length`; the longest name of an
imported module which starts it, `Data.List.Length.length`, `L.List.Nil`;
or the module's own name or an enclosing one, written out. The rest of its
segments navigate namespaces: through those whose members the renamer
knows — modules, data types, classes, instances — a missing member is an
error; through a function's, the generated lemmas, `(<>).unfold-Nil`, the
segments are kept as written for elaboration to find.

A name which resolves to a declaration elaboration rejected is reported by
elaboration or by the engine, by its canonical name: `not a hypothesis or a
lemma: Data.List.bad`.

## Tooling

- `praxis check [TARGET…]` checks a `project.toml`, a `package.toml`, a
  directory holding one, or a `.px` file — as a module of the package
  enclosing it, its imports first, or, outside any package or with
  `--alone`, on its own; the current directory when no target is given.
  Every report is printed with its file, and the exit status is nonzero
  when one is an error. `--dump-core` prints each module's core text.
- `praxis-lsp` checks a `.px` document as a module of the package
  enclosing its path, with what it imports, and reports the document's own
  findings.

## Scope of the current implementation

Implemented: libraries and sublibraries, `package.toml` and
`project.toml`, PVP versions and Cabal's ranges with project-wide
constraints, the renamer with imports, openings, nesting, privacy and the
three directives, library-qualified imports, the build in dependency and
import order, `praxis check` over projects, and the language server within
packages. Planned: executables, tests and benchmarks as components; a
repository of packages, with a solver; hidden modules; parameterised
modules; and imports of the core's `.pra` and `.prf` files as modules.
