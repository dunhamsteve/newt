
## TODO

I may be done with `U` - I keep typing `Type`.

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
- [ ] import
- [ ] autos / typeclass resolution
  - Can we solve right away when creating the implicit, or do we need postpone?
  - options
    - keep as implicit and do auto if the type constructor is flagged auto
    - keep as implicit and mark auto, behavior overlaps a lot with implicit
    - have separate type of implict with `{{}}`
- [ ] do blocks
- [ ] some solution for `+` problem (classes? ambiguity?)
- [x] show compiler failure in the editor (exit code != 0)
- [ ] write js files into `out` directory
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

- [ ] Read Ulf Norell thesis
