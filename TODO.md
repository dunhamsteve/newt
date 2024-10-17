
## TODO

- [ ] unsolved meta errors repeat (need to freeze at some point)
- [x] Sanitize JS idents, e.g. `_+_`
- [ ] Generate some programs that do stuff
- [x] import
- [ ] consider making meta application implicit in term, so its more readable when printed
  - Currently we have explicit `App` surrounding `Meta` when inserting metas. Some people
    leave that implicit for efficiency. I think it would also make printing more readable.
  - When printing `Value`, I now print the spine size instead of spine.
- [x] eval for case (see order.newt)
- [ ] dynamic pattern unification (add test case first)
  - Possibly the cause of issue in code commented out in `TestCase4.newt`
- [x] switch from commit/mustWork to checking progress
- [x] type constructors are no longer generated?  And seem to have 0 arity.
- [x] raw let is not yet implemented (although define used by case tree building)
- [x] there is some zero argument application in generated code
- [x] get equality.newt to work
  - [x] broken again because I added J, probably need to constrain scrutinee to value
- [x] inline metas.  Maybe zonk after TC/elab
- [x] implicit patterns
- [x] operators
- [x] pair syntax (via comma operator)
- [x] matching on operators
  - [x] top level
  - [x] case statements
- [x] SKIP list syntax
  - Agda doesn't have it, clashes with pair syntax
- [ ] autos / typeclass resolution
  - We need special handling in unification to make this possible
  - options
    - keep as implicit and do auto if the type constructor is flagged auto
    - keep as implicit and mark auto, behavior overlaps a lot with implicit
    - have separate type of implict with `{{}}`
    - `TypeClass.newt` is the exercise for this
- [ ] do blocks
- [ ] some solution for `+` problem (classes? ambiguity?)
- [x] show compiler failure in the editor (exit code != 0)
- [x] write output to file
  - uses `-o` option
- [ ] detect extra clauses in case statements
- [ ] add test framework
- [ ] decide what to do for erasure
- [ ] type at point in vscode
- [ ] repl
- [ ] LSP
- [x] don't match forced constructors at runtime
  - I think we got this by not switching for single cases
- [ ] magic nat (codegen as number with appropriate pattern matching)
- [ ] magic tuple? (codegen as array)
- [ ] magic newtype? (drop in codegen)
- [ ] records / copatterns
- [ ] vscode: syntax highlighting for String

### Parsing

- [ ] consider allowing σ etc in identifiers
  - Probably need to merge oper / ident first and sort out mixfix in parsing.

### Background

- [ ] Read Ulf Norell thesis


