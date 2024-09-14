
# Newt

Newt is a dependently typed programming language that compiles to javascript. It is
my first attempt to write a dependent typed language. It is inspired by Idris,
Elaboration Zoo, pi-forall, and various tutorials.

The goal is to have inductive types, pattern matching, compile to javascript, and be self hosted. At the very least though, I'd like to be able to build a little browser "playground" to compile and run code.

## Building

There is a `Makefile` that builds both chez and javascript versions.  They end up in
`build/exec` as usual.  I've also added a `pack.toml`, so `pack build`

There is a vscode extension in `newt-vscode`. Running `make vscode` will build and install it. The extension expects `build/exec/newt` to exist in the workspace.

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

## Case Tree

I've got no idea what I'm doing here. I worked off of Jesper Cockx "Elaborating Dependent (Co)pattern Matching", leaving out codata for now.

For the dependent thing, I've change unify to return `VVar` constraints. I think this is an error typechecking on
RHS (meta solutions are handled separately). On the LHS, I'm rewriting the environment to turn the var from a bind
to a define. Unification has been tweaked to look up `VVar` in environment. Bind will hand back the same `VVar`.

Some of this I could probably do with subst, but the RHS is `Raw`, it takes typechecking to turn it into a clean `Tm`,
and I need this information for the typechecking.

## Issues

- I need to do some erasure of values unused at runtime
- I'm a little fuzzy on the "right way" to deal with constraints from unification
- I'm a little fuzzy on how much to evaluate and when
- I'm not postponing anything, and I suspect I will need to

## References

"Unifiers as Equivalences" has unification with types.  Look into adapting some of that (or at least read/understand it).  Indexed types are mentioned here.

"Elaborating Dependent (Co)pattern Matching" describes building case trees. Section 5.2 has the algorithm.

"A prettier printer" was the basis of the pretty printer.

"Elaboration Zoo" was a resource for typechecking and elaboration. In particular pattern unification and handling of implicits is based on that.
