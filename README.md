
"Unifiers as Equivalences" has unification with types.  Look into adapting some of that (or at least read/understand it).  Indexed types are mentioned here.

"Elaborating Dependent (Co)pattern Matching" describes building case trees. Section 5.2 has the algorithm.

"A prettier printer" was the basis of the pretty printer.

"Elaboration Zoo" was a resource for typechecking and elaboration. In particular pattern unification and handling of implicits is based on that.


- [x] Support primitives
- Make DCon/TCon separate from Ref? (Or add flavor to VRef/Ref? If processing is often the same. I think I want arity though. I don't think a checked DCon can be overapplied, but it could be underapplied without special form. And special form is possibly difficult if not collecting a stack on the way down...


Need to typecheck case - learning stuff like `n = S k` is not happening and the final bit of the data constructor doesn't unify with the data type, because we're not handling `Bnd n =?= Val`. Cockx collects a list of constraints.  We might want flags on unification to enable that?

I may want to collect a telescope instead of a type.

Cockx lecture suggests something about going backwards. I'm thinking unifying the codomain of the DCon with the type of the TCon will give us some constraints like `n =?= S k`.


Cockx paper §5.2 builds type-correct case trees. It doesn't have indicies, but they can be mapped to additional equality arguments. We can follow suit, or try to do the translation on the fly.

Proceed by:

context is snoc, telescope is cons

- [x] Add eval for case
  - These are just neutral for now
- [x] Check data constructors
  - I'm checking pi type, then checking codomain is application of appropriate type constructor
- [ ] Build case trees (Section 5.2)
  Write this for a function, but start with `case` statement and singleton list. We'll end up with a longer list when we hit `Just x :: xs` etc.
  Then add

- [ ] Add primitives
- [ ] Compile and run something
- [ ] Add modules

- [ ] Start translating self?

v1 of cases requires a constructor and vars, var, or default.

narya has a `with_loc`

> with_loc loc f runs the thunk f with loc as the new default location for val:emit and val:fatal. Note that with_loc None will clear the current default location, while merge_loc None will keep it. See val:merge_loc.

So it's using ocaml `algaeff` package, with a reader effect for the location.  I think it's accumulating a stack of them. Additionally `asai` has functions to emit messages that can pick up the location from context.

This is interesting in that we could include location in context or the monad for cases where we have an error say unifying, and want to know what we were processing when it happened (either instead of or in addition to reporting some FC of the terms being unified).

## Now

- Eval case
- constraints from case

### Main

- [x] flag for debug?

### Data

- [x] typecheck `plus`
- [x] don't leave extra "Axiom" entries for incomplete `data` (switch to a map or drop the order)
- [ ] Check types when declaring data (collect telescope and check final type against type constructor)
- [ ] Learn stuff like `n = S k` in case trees.
  - Need test case, but existing plus case fails unification if we try.
  - I guess I need to let these pattern vars unify/match and learn equalities
  - If this is all var = tm, I could mutate the local env, so var is now a let. (Would it need to be `let` to be used in unification?)
  - I could subst into something (environment / goal?)
  - I could carry around extra stuff for unification
  - With names, I could dump a `let` into the env
- [ ] Handle default cases (non-constructor)
- [ ] When we do impossible, take agda approach
- [ ] test cases. Maybe from pi-forall
- [ ] coverage checking
- [ ] case tree builder

### Primitives

Maybe we can declare primitive ops and not hardwire a list in the codegen?

- [ ] Add primitive strings
- [ ] Add primitive numbers
- [ ] Wire through compilation
- [ ] Magic Nat in compilation

### Erasure

We need some erasure for runtime. The pi-forall notation isn't compatible with implicits. Maybe use Idris2 or Agda notation. Prop is another option.

- [ ] Erased values?
  - pi-forall handles this, so it's probably not too crazy. She won't go near implicits and I think I understand why.
  - I don't think I Want to go full QTT at the moment
  - Is erased different from 0/many?

### Compilation

Code generation is partially done.

- [ ] Handle meta in compile (inline solved metas?)
- [ ] Default case (need to process list to cases and maybe default)
- [ ] Arity for top level functions (and lambda for partial application)
     - I can do this here, but I'll have to wire in M, otherwise maybe a transform
       before this (we could pull out default case too)
- [ ] Javascript operators / primitives
- [x] Don't do assign var to fresh var
- [ ] Write output file

### Parsing / Language

- [x] switch to FC
- [ ] add operators to parser state (Are we going to run this on LHS too?)
- [ ] Modules and namespaces
- [ ] List sugar

### Editor

- [ ] Type at point for the editor

### Unification

We're stopping at zoo4 for now.


### Typecheck / Elaboration

- [ ] think about whether there needs to be a desugar step separate from check/infer
- [x] Code Gen #partial
- [ ] Less expansion
  - Look at smallTT rules
  - Can we not expand top level - expand in unification and matching pi types?
  - should the environment be lazy?
- [ ] look into Lennart.newt issues
- [ ] figure out how to add laziness (might have to be via the monad)

So smalltt has TopVar with a Level. typechecking binders end up as top too.

Also delayed unfolded values for top or solved metas. This looks like glue - all the bits for the top and a cached value (it's keeping top as values).

REVIEW the delayed unfolding, we're being aggressive for now. This may have been necessary until unification was in place, now we can decide to further unfold during unification.

metas are assoc list, can probably just be list, but we'd need to do level/index math for the lookup.

They are in separate MetaContext wrapped in an IORef. I'm reluctant to copy Idris because resolved names are not compatible with query based, but everybody is using an array...

Idris has a common array for metas and defs but that might be a problem if I go query based someday.

Prettier was missing a Lazy.  I'm still fairly faithful to the paper, but might want to refactor that to push the computation down into the `if`.

Zoo3 runs now, I had to fix meta / meta unification.

I've added a bunch of info logs for the editor support.

Zoo4 examples run now.

When I generate code, I'll eventually run up against the erased thing. (I'll want to erase some of the stuff that is compile time.)  But we'll generate code and decide how far we need to take this.  It's probably pointless to just reproduce Idris.

When I self host, I'll have to drop or implement typeclasses. I do understand auto enough to make it happen.

Ok, for code gen, I think I'll need something like primitive values and definitely primitive functions. For v0, I could leave the holes as undefined and if there is a function with that name, it's magically FFI.

Questions:
- [ ] Should I write this up properly?

Parser:
- [x] parser for block comments
- [x] import statement
- [x] def
- [x] simple decl
- [ ] %check (either check at _ or infer and let it throw)
  - Lean checks (λ x => x) to ?m.249 → ?m.249
- [ ] %nf (ditto, but print value. WHNF for now, eval in lean?)
- [ ] operators / mixfix
  - Maybe put operators in parser state and update, ideally we'd have mixfix though
  - how does agda handle clashes between names and mixfix?
  - it seems to allow overlap: if, if_then, if_then_else_

Testing:

- [ ] black box testing
  - [ ] Proper exit code
  - [ ] bug.newt should fail with a certain parse error, but there will be noise, so look for specific error?
  - [ ] zoo?.newt should complete successfully

Misc:
- [x] vscode support for .newt
- [x] Error object like pi-forall
  - [ ] I think I'll need to go with non-generic error type once I need to do something other than print them
- [x] Get unification working (zoo3)
- [x] Get implicits working (zoo4)
- [x] Replace on define
- [x] more sugar on lambdas
- [ ] tests for parsing and pretty printing
- [ ] white box tests for internals
  - Maybe look at narya for examples of what I should be testing
- [ ] inductive types
  - read data definitions 1/2 done
- [x] read files
- [x] process a file
- [x] figure out context representation - Global context?
- [x] type checking / elab
  - What does this represent? The basics, implicits? pattern unification?
- [x] check for unsolved metas (after each def or at end?)
- [ ] compilation
- [ ] repl
- [ ] write tests
- [ ] Split up code better

Forward:

- [ ] Switch to query-based?
- [ ] LSP?
- [ ] white box testing
- [ ] switches on logging
- [ ] Add PRINTME / ? - Does it check and fake success? I don't think we can infer.

----

pi-forall sticks equality into scope as something like let. Not sure if this is compatible with deBruijn.  Possibly if we have everything at elab time?  But if `x = y` then previous stuff has a different `x`?



## Dep Ty Check

### pi-forall

unify returns a list of Entry, but "either term is "ambiguous" (i.e. neutral), give up and succeed with an empty list" seems wrong. fine for case refinement I guess, but wrong for conversion checking?  I suppose conv check could look for `[]`.

TODO find out what it does for conv checking

### idris / tiny idris

TODO how does idris mnage this?


### narya

TODO how does narya handle it?

Mybe a Conor paper or a Cockx paper would also shed some light.  And do ny "tutorial implementation" handle if properly?

