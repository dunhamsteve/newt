
## TODO

- [ ] Allow unicode operators/names
  - refactored parser to prep for this
- [ ] get rid of stray INFO from auto resolution
- [ ] handle if_then_else_j
- [x] Remember operators from imports
- [ ] Default cases for non-primitives (currently gets expanded to all constructors)
- [x] Case for primitives
- [ ] aoc2023 translation
  - [x] day1
  - [x] day2
  - some "real world" examples -v
- [x] Maybe Eq and stuff would work for typeclass without dealing with unification issues yet
- [x] unsolved meta errors repeat (need to freeze or only report at end)
- [x] Sanitize JS idents, e.g. `_+_`
- [x] Generate some programs that do stuff
- [x] import
- [ ] consider making meta application implicit in term, so its more readable when printed
  - Currently we have explicit `App` surrounding `Meta` when inserting metas. Some people
    leave that implicit for efficiency. I think it would also make printing more readable.
  - When printing `Value`, I now print the spine size instead of spine.
- [x] eval for case (see order.newt)
- [ ] dynamic pattern unification (add test case first)
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
- [ ] `data` sugar: `data Maybe a = Nothing | Just a`
- [x] matching on operators
  - [x] top level
  - [x] case statements
- [ ] Lean / Agda ⟨ ⟩
- [ ] Lean-like .map, etc? (resolve name in namespace of target type, etc)
- [x] ~~SKIP list syntax~~
  - Agda doesn't have it, clashes with pair syntax
- [ ] autos / typeclass resolution
  - [x] very primitive version in place, not higher order, search at end
  - [x] monad is now working
- [x] do blocks (needs typeclass, overloaded functions, or constrain to IO)
- [x] some solution for `+` problem (classes? ambiguity?)
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
- [ ] magic newtype? (drop them in codegen)
- [ ] records / copatterns
- [x] vscode: syntax highlighting for String
- [ ] add `pop` or variant of `pfunc` that maps to an operator, giving the js operator and precedence on RHS

### Parsing

- [ ] consider allowing σ etc in identifiers
  - Probably need to merge oper / ident first and sort out mixfix in parsing.

### Background

- [ ] Read Ulf Norell thesis


