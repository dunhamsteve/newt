
# Newt

Newt is a dependently typed programming language that compiles to javascript. It is
my first attempt to write a dependent typed language. It is inspired by Idris,
Elaboration Zoo, pi-forall, and various tutorials.

I'm still learning how this stuff is done, so it's a bit of a mess. But I'm going to
work with the garage door up.

The goal is to have inductive types, pattern matching, compile to javascript, and be
self hosted. Ideally I could build a little browser "playground" to compile, view
output, and run code.

The repository is tagging `.newt` files as Agda to convince github to highlight them.

There is a web playground at https://dunhamsteve.github.io/newt. The top left corner
has a dropdown with some samples. At the moment, it shows generated code, but doesn't
execute it.

## Building

There is a `Makefile` that builds both chez and javascript versions.  They end up in
`build/exec` as usual.  I've also added a `pack.toml`, so `pack build` also works.

There is a vscode extension in `newt-vscode`. Running `make vscode` will build and install it. The extension expects `build/exec/newt` to exist in the workspace. And `make test` will run a few black box tests. Currently it simply checks return codes, since the output format is in flux.

The web playground is in playground.
- `npm install` will pull down dependencies.
- `./build` will build the web workers and install sample files (`make` must be run in root first).
- `npx vite` will run the dev server.

## Overview

I'm doing Type in Type for now.

The type checking and implicits are based on elaboration zoo. I'm using normalization
by evaluation with closure objects rather than HOAS.  When going under binders in the
typechecking, I follow Kovács example and place a `VVar` into the environment instead of
doing `subst`.

The raw syntax is `Raw`. This is elaborated to `Tm`. There is a top level context and a
context during checking. The top level context uses names, and type checking uses deBruijn
indices for `Tm` and levels for `Val`.  For compilation, this is converted to `CExp`, which works out how arity and closures will work, and then `JSExp` which is javascript AST.

I have `Let` in the core language. Partly because I'd like this to make it into javascript (only compute once), but also because it's being leveraged by the casetree stuff.

I also have `Case` in the core language.

## Case Tree

I've got no idea what I'm doing here. I worked off of Jesper Cockx "Elaborating Dependent (Co)pattern Matching", leaving out codata for now.  I've now added matching primitives, requiring a default case. When splitting on inductive types it will break out all of the remaining cases and doesn't emit a default case.

I'm essentially putting the constraints into the environment like `let`. This is a problem when stuff is already in `Val` form. Substitution into types in the context is done via quote/eval. I plan to revisit this.

I intend to add the codata / copatterns from the paper, but haven't gotten to that yet.

## Evaluation

Following kovacs, I'm putting `VVar` into context env when I go under binders in type-checking. This avoids substitution.

## Autos

Newt has primitive auto implicits. They are denoted by double braces `{{}}` as in Agda. Newt will search for a function that returns a type in the same family, only has implicit and auto-implicit arguments, and unifies (satisfying any relevant constraints).

This search can be used to manually create typeclasses.  `do` blocks are supported, desugaring to `>>=`, which it expects to be the `bind` of a Monad typeclass.

## References

"Elaborating Dependent (Co)pattern Matching" by Jesper Cockx and Andreas Abel describes building case trees. Section 5.2 describes the algorithm.

"A prettier printer" by Philip Wadler was the basis of the pretty printer.

"Elaboration Zoo" by András Kovács was my primary resource for typechecking and elaboration. In particular pattern unification and handling of implicits is based on it.

There were many other resources and papers that I used to learn how dependent typed languages are built.
