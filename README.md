
# Newt

Newt is a dependently typed programming language that compiles to javascript. It is
my first attempt to write a dependent typed language. It is inspired by Idris,
Elaboration Zoo, pi-forall, and other tutorials.

It has inductive types, dependent pattern matching, a typeclass-like mechanism, compiles
to javascript, and is now written in itself. There is a browser playground and vscode extension.

The web playground can be at https://dunhamsteve.github.io/newt. The top left corner
has a dropdown with some samples. Currently the web playground is using the Idris-built
version of newt because most browsers lack tail call optimization.

The directory `port` contains a port of newt to itself. Currently it needs to be run by `bun` rather than `node` because `bun` does tail call optimization.

## Sample code

- `port` contains a copy of newt written in newt
- `newt` contains miscellaneous files
- `aoc2024` contains solutions for 2024 Advent of Code in newt
- `tests` contains some test cases.

## Building

There is a `Makefile` that builds both chez and javascript versions.  They end up in
`build/exec` as usual.  I've also added a `pack.toml`, so `pack build` also works.

There is a vscode extension in `newt-vscode`. Running `make vscode` will build and install it. The extension expects `build/exec/newt` to exist in the workspace. And `make test` will run a few black box tests. Currently it simply checks return codes, since the output format is in flux.

The web playground is in playground.
- `npm install` will pull down dependencies.
- `./build` will build the web workers and install sample files (`make` must be run in root first).
- `npx vite` will run the dev server.

# Implementation details

## Overview

I'm doing Type in Type for now.

The type checking and implicits are based on elaboration zoo. I'm using normalization
by evaluation with closure objects rather than HOAS.  When going under binders in the
typechecking, I follow Kovács example and place a `VVar` into the environment instead of
doing `subst`.

The raw syntax is `Raw`. This is elaborated to `Tm`. There is a top level context and a
context during checking. The top level context uses names, and type checking uses deBruijn
indices for `Tm` and levels for `Val`.  For compilation, this is converted to `CExp`, which works out how arity and closures will work, and then into `JSExp` which is javascript AST.

I have `Let` in the core language. Partly because I'd like this to make it into javascript (only compute once), but also because it's being leveraged by the casetree stuff. The `where` clauses are turned into `LetRec` and locally defined functions, so I'm punting the lambda-lifting to javascript for now.

`Case` is in the core language `Tm` and it can appear anywhere in the syntax tree.

## Case Tree

This is inspired by Jesper Cockx "Elaborating Dependent (Co)pattern Matching". I've left off codata for now, and I'm trying to do indexes on the types rather than having explicit equalities as arguments. I've also added matching on primitives, which require a default case. And when matching on inductive types, I collect the unmentioned, but relevant constructors into a single default case. This greatly improved performance and reduced the size of the emitted code.


I'm essentially putting the constraints into the environment like `let`. This is a problem when stuff is already in `Val` form. Substitution into types in the context is done via quote/eval. I plan to revisit this.

## Evaluation

Following kovacs, I'm putting `VVar` into context env when I go under binders in type-checking. This avoids substitution.

## Autos

Auto implicits are denoted by double braces `{{}}`.  They are solved by searching for functions that return a type heading by the same type constructor and have only implicit and auto implicit arguments. It tries to solve the implicit with each candidate by checking it against the type, allowing one level of constraint to be checked. If exactly one works, it will take that as a solution and proceed.

Otherwise, we rarely solve the type because it contains metas with constraints that don't work with pattern unification (they have extra arguments).  I stop at one constraint to try to handle cases where a type mismatch gets turned into an auto failing to be solved.

The sugar for `do` blocks uses the `>>=` operator, which is defined on the `Monad` interface in the `Prelude`.

## References

"Elaborating Dependent (Co)pattern Matching" by Jesper Cockx and Andreas Abel describes building case trees. Section 5.2 describes the algorithm.

"A prettier printer" by Philip Wadler was the basis of the pretty printer.

"Elaboration Zoo" by András Kovács was my primary resource for typechecking and elaboration. In particular pattern unification and handling of implicits is based on it.

There were many other resources and papers that I used to learn how dependent typed languages are built.
