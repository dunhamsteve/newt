
## TODO

Syntax -> Parser.Impl ?

- [ ] implement tail call optimization
- [ ] `Def` is shadowed between Types and Syntax (TCon vs DCon), detect this
- [ ] review pattern matching. goal is to have a sane context on the other end. secondary goal - bring it closer to the paper.

- [ ] rename for top level functions (and maybe stuff in scope, probably need LSP first)
- [ ] warn on unused imports?
- [x] redo code to determine base path
- [x] emit only one branch for default case when splitting inductives
- [ ] save/load results of processing a module
  - [x] keep each module separate in context
  - [x] search would include imported modules, collect ops into and from modules
  - [x] serialize modules
  - [ ] deserialize modules if up to date
    - should I allow the idris cross module assignment hack?
    - >>> sort out metas (maybe push them up to the main list)
    - eventually we may want to support resuming halfway through a file

- [x] get port to run
  - [x] something goes terribly wrong with traverse_ and for_ (related to erasure, I think)
- [ ] sort through issues that came up during port
- [x] ~~don't use `take` - it's not stack safe~~ The newt version is stack safe
- [ ] move idris version into a bootstrap directory
  - (Need Idris/chez or newt-in-newt to bootstrap!)

More comments in code! This is getting big enough that I need to re-find my bearings when fixing stuff.

- [ ] report info in case of error
- [x] tokenizer that can be ported to newt
- [ ] Add default path for library, so we don't need symlinks everywhere and can write tests for the library
- [x] string interpolation?
  - The tricky part here is the `}` - I need to run the normal tokenizer in a way that treats `}` specially.
  - Idris handles `putStrLn "done \{ show $ add {x=1} 2}"` - it recurses for `{` `}` pairs.  Do we want that complexity?
  - The mini version would be recurse on `{`, pop on `}` (and expect caller to handle), fail if we get to the top with a tokens remaining.
- [ ] mutual recursion in where?
  - need to scan sigs and then defs, will have to make sure Compile.idr puts them all in scope before processing each.
- [x] Move on to next decl in case of error
- [x] for parse error, seek to col 0 token and process next decl
- [ ] record update sugar, syntax TBD
  - I think I'm going to hold off on this for now as it requires the type to elaborate. This ends up at the head of an app, which typically is inferred. We'd need a special case somewhere that infers its argument instead.
- [x] Change `Ord` to be more like Idris - LT / EQ / GT (and entail equality)
- [ ] Keep a `compare` function on `SortedMap` (like lean)
- [x] keymap for monaco
- [x] SortedMap.newt issue in `where`
- [x] fix "insufficient patterns", wire in M or Either String
- [x] Matching _,_ when Maybe is expected should be an error
- [ ] There are issues with matching inside do blocks
    - I may have handled a lot of this by reworking autos to check just one level of constraints (with a 20% speedup)
    - Do we need to guess scrutinee? Or we could refine a meta scrutinee type to match the constructor being split. This happens during checking for pi, where we create ?m -> ?m and unifiy it with the meta. Could we do the same in a case, where `Just ...` says the meta must be `Maybe ?m`?
  - ~~`newt/Fixme.newt` - I can drop `do` _and_ put `bind {IO}` to push it along. It may need to try to solve autos earlier and better.~~
  - Also, the root cause is tough to track down if there is a type error (this happens with `do` in Idris, too).
  - Part of it is the auto solutions are getting discarded because of an unrelated unification failure. Either auto shouldn't go as deep or should run earlier. Forgetting that lookupMap returns a (k,v) pair is a good example.
  - I've gotten it to the point where things are solved for good code, but it still does poorly when there is an error. (Auto fails to solve and it doesn't get far enough to report error.)
- [ ] add error for non-linear pattern
- [ ] typeclass dependencies
  - need to flag internal functions to not search (or flag functions for search). I need to decide on syntax for this.
  - for something like an `isEq` field in `Ord`, auto-search is picking up the function being defined.
- [ ] default implementations (use them if nothing is defined, where do we store them?) e.g. Ord compare, <, etc in Idris
  - I may need to actually store some details on interfaces rather than reverse engineer from type.
- [x] syntax for negative integers
- [ ] White box tests in `test` directory (I can't get this to work right with pack et al)
- [x] Put worker in iframe on safari
- [ ] Warnings or errors for missing definitions (e.g. on `Axiom` in codegen)
- [ ] Add the type name to dcon so confusion detection in case split is simpler
- [ ] Warnings or errors for unused cases
  - This is important when misspelled constructors become pattern vars
- [ ] if we're staying with this version of auto, we might need to list candidates and why they're rejected. e.g. I had a bifunctor fail to solve because the right answer unblocked a Foo vs IO Foo mismatch
- [ ] literals for double
- [ ] add default failing case for constructor matching to catch errors
- [x] Add icit to Lam
- [ ] add jump to definition magic to vscode extension
  - [x] Cheap dump to def - dump context
- [ ] TCO? Probably needed in browser, since v8 doesn't do it. bun and JavaScriptCore do support it.
- [x] deconstructing `let` (and do arrows)
- [x] Fix string printing to be js instead of weird Idris strings
- [x] make $ special
  - Makes inference easier, cleaner output, and allows `foo $ \ x => ...`
  - [ ] `$` no longer works inside ≡⟨ ⟩ sort out how to support both that and `$ \ x => ...` (or don't bother)
    - We'd either need to blacklist all non-initial mixfix bits at the appropriate spots or always pass around a terminating token.
- [ ] **Translate newt to newt**
  - [x] Support @ on the LHS
  - [x] if / then / else sugar
  - [x] `data Foo = A | B` sugar
  - [x] records
  - [ ] record sugar? (detailed above)
  - [x] where
  - [ ] add namespaces
  - [ ] magic nat?
- [x] rework `unify` case tree
  - Idris needs help with the case tree to keep code size down, do it in stages, one dcon at a time.
  - I'm not sure it can go a few steps deep and have a default hanging off the side, so we may need to put the default case in another function ourselves.
- [x] Strategy to avoid three copies of `Prelude.newt` in this source tree
- [ ] `mapM` needs inference help when scrutinee (see Day2.newt)
  - Meta hasn't been solved yet. It's Normal, but maybe our delayed solving of Auto plays into it. Idris will peek at LHS of CaseAlts to guess the type if it doesn't have one.
- [ ] Can't skip an auto. We need `{{_}}` to be auto or have a `%search` syntax.
- [x] add filenames to FC
- [ ] Add full ranges to FC
- [x] maybe use backtick for javascript so we don't highlight strings as JS
- [x] dead code elimination
- [x] imported files leak info messages everywhere
  - For now, take the start ix for the file and report at end starting there
- [x] update node shim to include idris2-playground changes
- [x] refactor playground to better share code with idris2-playground
- [x] accepting DCon for another type (skipping case, but should be an error)
- [ ] don't allow (or dot) duplicate names on LHS
- [x] remove metas from context, M has TopContext
- [ ] improve test driver
  - maybe a file listing jobs, whether they are known broken, optional expected output, optional expected JS execution output.
- [x] forall / ∀ sugar (Maybe drop this, issues with `.` and `{A}` works fine)
- [x] Bad module name error has FC 0,0 instead of the module or name
- [ ] Revisit substitution in case building
- [x] Check for shadowing when declaring dcon
  - Handles the forward decl in `Zoo1.newt`, but we'll need different syntax if
    we have different core terms for TCon/DCon/Function
- [ ] Require infix decl before declaring names with `_` (helps find bugs) or implicitly define infixl something if it's missing
- [x] sugar for typeclasses
- [x] maybe add implicits in core to help resugar operators?
- [ ] consider putting binders in environment, like Idris, to better mark `let` and to provide names
- [x] move some top-level chattiness to `debug`
- [ ] consider optionally compiling to eliminators for a second type-checking pass to help catch bugs.
- [x] Allow unicode operators/names
- Web playground
  - [x] editor
  - [x] view output
  - [x] view javascript
  - [x] run javascript
  - [x] need to shim out Buffer
- [x] get rid of stray INFO from auto resolution
- [x] handle `if_then_else_` style mixfix
  - [x] equational reasoning sample (maybe PLFA "Lists")
  - actual `if_then_else_` isn't practical because the language is strict
- [x] Search should look at context
- [ ] copattern matching
- [ ] Get `Combinatory.newt` to work
- [x] Remember operators from imports
- [ ] Default cases for non-primitives (currently gets expanded to all constructors)
  - This may need a little care. But I think I could collect all constructors that only match wildcards into a single case. This would lose any information from breaking out the individual, unnamed cases though.
  - There are cases where we have  `_` and then `Foo` on the next line, but they should all get collected into the `Foo` case. I think I sorted all of this out for primitives.
- [x] Case for primitives
- [ ] aoc2023 translation
  - [x] day1
  - [x] day2 - day6
  - some "real world" examples
- [x] Maybe Eq and stuff would work for typeclass without dealing with unification issues yet
- [x] unsolved meta errors repeat (need to freeze or only report at end)
- [x] Sanitize JS idents, e.g. `_+_`
- [x] Generate some programs that do stuff
- [x] import
- [ ] consider making meta application implicit in term, so it's more readable when printed
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
- [x] Bad FC for missing case in where clause (probably from ctx)
- [x] inline metas.  Maybe zonk after TC/elab
- [x] implicit patterns
- [x] operators
- [x] pair syntax (via comma operator)
- [x] `data` sugar: `data Maybe a = Nothing | Just a`
- [x] matching on operators
  - [x] top level
  - [x] case statements
- [ ] Lean ⟨ ⟩ anonymous constructors
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
  - I'm going to try explicit annotation, forall/∀ is erased
  - [x] Parser side
  - [x] push down to value/term
  - [x] check quantity
  - [x] erase in output
  - [ ] remove erased top level arguments
- [x] top level at point in vscode
- [ ] in-scope type at point in vscode
- [ ] repl
- [ ] LSP
- [x] don't match forced constructors at runtime
  - I think we got this by not switching for single cases
- [ ] magic nat (codegen as number with appropriate pattern matching)
- [ ] magic tuple? (codegen as array)
- [ ] magic newtype? (drop them in codegen)
- [x] vscode: syntax highlighting for String
- [ ] add `pop` or variant of `pfunc` that maps to an operator, giving the js operator and precedence on RHS
- [ ] consider moving caselet, etc. desugaring out of the parser
- [ ] pattern matching lambda
  - I kept wanting this in AoC and use it a lot in the newt code
  - This conflicts with current code (unused?) that allows telescope information in lambdas
  - For now, I'll implement `\case`

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

### Error Messages

Missing `Monad Maybe` looks like:
```
Unsolved meta 358 Normal type U 0 constraints
Unsolved meta 356 Auto type Monad (?m:355 s:0) 0 constraints
Unsolved meta 355 Normal type U -> U 2 constraints
  * (m355 (%var0 (List (%meta 358 [1 sp]))) =?= (Maybe (List Card))
  * (m355 (%var0 (%meta 358 [1 sp])) =?= (Maybe Card)
```
There is some information here, but it's obtuse.  One issue is that I'm taking an Agda-inspired approach to search (try every option and see if exactly one works with our constraints) rather than Idris (assume the determinant on an interface is injective and solve `m344 %var0` with `Maybe`).

