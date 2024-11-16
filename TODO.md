
## TODO

- [ ] accepting DCon for another type (skipping case, but should be an error)
- [ ] don't allow (or dot) duplicate names on LHS
- [ ] improve test driver
  - maybe a file listing jobs, whether they are known broken, optional expected output, optional expected JS execution output.
- [x] forall / ∀ sugar (Maybe drop this, issues with `.` and `{A}` works fine)
- [x] Bad module name error has FC 0,0 instead of the module or name
- [x] I've made `{x}` be `{x : _}` instead of `{_ : x}`. Change this.
- [ ] Remove context lambdas when printing solutions (show names from context)
  - maybe build list of names and strip λ, then call pprint with names
- [ ] Revisit substitution in case building
- [x] Check for shadowing when declaring dcon
  - Handles the forward decl in `Zoo1.newt`, but we'll need different syntax if
    we have different core terms for TCon/DCon/Function
- [ ] Require infix decl before declaring names with `_` (helps find bugs)
- [ ] sugar for typeclasses
- [ ] maybe add implicits in core to help resugar operators?
  - There is also a bit where kovacs uses the implicit on the type (a value) to decide to insert
- [ ] consider binders in environment, like Idris, to better mark `let` and to provide names
- [ ] move some top-level chattiness to `debug`
- [ ] consider optionally compiling to eliminators for a second type-checking pass to help catch bugs.
- [x] Allow unicode operators/names
- Web playground
  - [x] editor
  - [x] view output
  - [x] view javascript
  - [ ] run javascript
  - [x] need to shim out Buffer
- [x] get rid of stray INFO from auto resolution
- [x] handle `if_then_else_` style mixfix
  - [x] equational reasoning sample (maybe PLFA "Lists")
  - actual `if_then_else_` isn't practical because the language is strict
- [x] Search should look at context
- [ ] records
- [ ] copattern matching
- [ ] Support @ on the LHS
- [ ] Get `Combinatory.newt` to work
- [x] Remember operators from imports
- [ ] Default cases for non-primitives (currently gets expanded to all constructors)
  - This may need a little care. But I think I could collect all constructors that only match wildcards into a single case. This would lose any information from breaking out the individual, unnamed cases though.
  - There are cases where we have  `_` and then `Foo` on the next line, but they should all get collected into the `Foo` case. I think I sorted all of this out for primitives.
- [x] Case for primitives
- [ ] aoc2023 translation
  - [x] day1
  - [x] day2
  - some "real world" examples
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
- [ ] Lean / Agda ⟨ ⟩ (does agda do this or just lean?)
- [ ] Lean-like .map, etc? (resolve name in namespace of target type, etc)
- [x] autos / typeclass resolution
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
- [x] vscode: syntax highlighting for String
- [ ] add `pop` or variant of `pfunc` that maps to an operator, giving the js operator and precedence on RHS

### Parsing

- [ ] consider allowing σ etc in identifiers
  - Probably need to merge oper / ident first and sort out mixfix in parsing
  - The mixfix parsing can handle this now, need to update lexing.
- [ ] Parse error not ideal for `\x y z b=> b` (points to lambda)

### Background

- [ ] Read Ulf Norell thesis
- [ ] Finish reading dynamic pattern unification paper to see what is missing/wrong with the current implementation
- [ ] Read "Unifiers as Equivalences" has unification with types.  Look into adapting some of that (or at least read/understand it).  Indexed types are mentioned here.

### Other issues

- [ ] Name space flattening makes it a bit more subtle when a misspelled (or shadowed) constructor turns into a variable.

