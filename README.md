
Parser is in place. 
Ditched well-scoped for now.

Fixed more issues, started processing stuff, we need real example code.

Need to sort out eval. Currently List doesn't get substituted. We should make sure we're CBV. I guess I could always subst (or glue?) since we're head normal form. We need actual values (∏) for checking.

ok, our kovacs eval puts the arg in the environment and continues. So CBN, but maybe duplicate work (for our version).

So smalltt has TopVar with a Level. typechecking binders end up as top too.

Also delayed unfolded values for top or solved metas. This looks like glue - all the bits for the top and a cached value (it's keeping top as values).




Parser:
- [x] import statement
- [x] def
- [x] simple decl
- [x] List not in scope
- [ ] vscode support for .newt
- [ ] Should I switch this back over to the App monad?
- [ ] Error object like pi-forall
- [ ] Get implicits working
- [x] Replace on define
- [x] more sugar on lambdas
- [ ] tests for parsing and pretty printing
- [ ] inductive types
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
- 
f
