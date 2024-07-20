
We're stopping at zoo4.


- [ ] look into Lennart.newt issues
- [ ] Type at point for the editor
- [ ] add operators to parser state
  - (Are we going to run this on LHS too?)

- [ ] Data
  - [ ] Read data as real constructors
  - [ ] Typecheck / eval the same
  - [ ] Add elimination / case
    - [ ] Maybe some test cases from pi-forall
- [ ] Code Gen
- [ ] Less expansion
  - Can we not expand top level - expand in unification and matching pi types?

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

Maybe do `data` next.  There is a crude version in place, we'll want to fix that, typecheck the new stuff, and then add cases. (Maybe introduce eliminators.)

When I generate code, I'll eventually run up against the erased thing. (I'll want to erase some of the stuff that is compile time.)  But we'll generate code and decide how far we need to take this.  It's probably pointless to just reproduce Idris.

When I self host, I'll have to drop or implement typeclasses. I do understand auto enough to make it happen.

Ok, for code gen, I think I'll need something like primitive values and definitely primitive functions. For v0, I could leave the holes as undefined and if there is a function with that name, it's magically FFI.

Questions:
- [ ] Code gen or data next?
- [ ] Should I write this up properly?
- [ ] Erased values?
  - pi-forall handles this, so it's probably not too crazy. She won't go near implicits and I think I understand why.
  - I don't think I Want to go full QTT at the moment
  - Is erased different from 0/many?

Parser:
- [x] parser for block comments
- [x] import statement
- [x] def
- [x] simple decl
- [ ] check (either check at _ or infer and let it throw)
- [ ] nf (ditto, but print value. WHNF for now    )
- [ ] operators / mixfix
  - Maybe put operators in parser state and update, ideally we'd have mixfix though
  - how does agda handle clashes between names and mixfix?
  - it seems to allow overlap: if, if_then, if_then_else_

Testing:

- [ ] black box testing
  - [ ] bug.newt should fail with a certain parse error, but there will be noise, so look for specific error?
  - [ ] zoo?.newt should complete successfully
  - [ ]

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
- [ ] check for unsolved metas (after each def or at end?)
- [ ] compilation
  - I'm thinking I get data working first
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

