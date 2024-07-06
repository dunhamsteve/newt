
Parser is in place. 
Ditched well-scoped for now.

Fixed more issues, started processing stuff, we need real example code.

Need to sort out eval. Currently List doesn't get substituted. We should make sure we're CBV. I guess I could always subst (or glue?) since we're head normal form. We need actual values (∏) for checking.

ok, our kovacs eval puts the arg in the environment and continues. So CBN, but maybe duplicate work (for our version).

So smalltt has TopVar with a Level. typechecking binders end up as top too.

Also delayed unfolded values for top or solved metas. This looks like glue - all the bits for the top and a cached value (it's keeping top as values).

We need metas next.  SmallTT has a metactx in context as a mutable array.

We extend the context and then drop it, so we need soemthing mutable.

It's in top context and he pulls stuff down to context as needed. I'm overthinking this. I'm reluctant to copy Idris because resolved names are not compatible with query based, but everybody is using an array...

I'd kinda like to see array run in js...

Idris does a common array for metas and defs. 



Parser:
- [x] import statement
- [x] def
- [x] simple decl
- [x] List not in scope
- [x] vscode support for .newt
- [ ] Should I switch this back over to the App monad?
- [x] Error object like pi-forall
- [ ] Get implicits working
- [x] Replace on define
- [x] more sugar on lambdas
- [ ] tests for parsing and pretty printing
- [ ] inductive types
  - [ ] read data definitions 1/2 done
- [x] read files
- [x] process a file
- [x] figure out context representation - Global context?
- [x] type checking / elab
  - What does this represent? The basics, implicits? pattern unification?
- [ ] symbolic execution
- [ ] compilation

- [ ] write tests

Forward:

- [ ] Switch to query-based?
- [ ] LSP?
- [ ] white box testing

----

pi-forall sticks equality into scope as something like let. Not sure if this is compatible with deBruijn.  Possibly if we have everything at elab time?  But if `x = y` then previous stuff has a different `x`?

