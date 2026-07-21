
## TODO

- [ ] Build single name map on import
  - Check performance - cost to build the map vs not walking $n$ maps
  - This will likely be needed for qualified / partial imports
  - [ ] Add `export` keywords
- [ ] code formatter
  - [ ] consider moving caselet, etc. desugaring out of the parser
  - comments stored aside (location, whether it is a tail or standalone) and re-integrated
  - how do we want to handle `$` and parens?
- [ ] consider postponing `case` if scrutinee type is an unsolved meta
- [ ] in batch mode, stop at first erroring module
  - We could also gain performance by not collecting LSP data in batch mode
- [ ] maybe `let case` instead of `let (...)` (which is a little subtle)
  - Or simply put a term in there and treat as a variable iff it is lowercase and non-applied
- [x] Use while-TCO for mutual recursion, drop `bouncer`
- [ ] Importing Prelude twice should be an error (currently it causes double hints and breaks auto)
  - or relax to no-op to aid repl usage
- [ ] maybe allow "Main" module name for any file
  - possibly allow eliding `module` for Main?
- [ ] preserve information on record / class / instance for LSP "document symbols" kind
  - We will want some of this for default implementations in class
  - It may help avoid reverse-engineering the class when processing implementation
- [ ] Put a copy of the `Def` on `Ref` terms
  - It may be Axiom for forward/recursive functions, but it would get us DCon and TCon info without lookup - and may save passing around the Ref2 (+lookup) during Compilation.
  - We can do lookup for Axiom via helper
- [ ] Improve handling of names:
  - We need FC on names in a lot of places
  - [x] FC for duplicate `data`, `record`, `class` name is wrong (points to `data`)
  - [x] FC on bad import should point to the name
  - [x] Current module overrides imports
  - [ ] Duplicate data constructor errors point to `data`
  - [ ] Allow Qualified names in surface syntax
  - Don't disambiguate on type for now
- [ ] Suppress code actions in `derive` statements
- [ ] Could we disambiguate just Data constructors on type?
- [ ] maybe add fat arrows, I keep wanting to type them, `{{...}}` is a little ugly
  - There may be ambiguity issues at the parsing level, but we don't have typecase, so.
  - It's less to type, too.
- [ ] Maybe return constraints instead of solving metas during unification
  - We already return non-meta constraints for work on the LHS.
  - We might get into a situation where solving immediately would have gotten us more progress?
  - Idris had a couple of bugs where they were accidentally dropped
- [ ] Delay checking
  - We have things like `foldr (\ x acc => case x : ...`, where the lambda doesn't have a good type, so we have to be explicit. If we could defer the checking of that expression until more things are solved, we might not need the annotation (e.g. checking the other arguments). Some `case` statements may have a similar situation.
  - One idea is to throw the checks onto some sort of TODO list and run whatever works. (I think Idris may have a heuristic where it checks arguments backwards in some cases.)
- [ ] see if we can get a better error if `for` is used instead of `for_` in do blocks
- [ ] consider moving primitive functions to a support file
  - Downside here is that we lose some dead code elimination
  - it better supports bootstrapping when calling convention changes.
- [ ] allow declaration of primitive operators
  - Removes assumptions of hack in Compile.newt, but might not support other backends
  - Alternate solution would be to pull from Prelude and hard code for all backends
  - POper added to physical syntax types, but not implemented
- [ ] See if we can split up `Elab.newt`
  - Unify, checking, and case builder have circular references.
  - Perhaps unify should return constraints instead of calling solve directly.
  - passing a pointer to `check` in the context may suffice
- [ ] Functions with erased-only arguments still get called with `()` - do we want this or should they be constants?
  - Is this still the case?
- [ ] Lifted closures could elide unused arguments (LiftWhere / LiftLambda)
- [-] Look into using holes for errors (https://types.pl/@AndrasKovacs/115401455046442009)
  - This is done in some places
  - This would let us hit more cases in a function when we hit an error.
  - I've been wanting to try holes for parse errors too.
  - Does softening up check errors break `auto`?
  - [ ] Missing `∀ k` in type is error -> no declaration for, if we insert a hole, we can get the declaration.
- [ ] in-scope type at point in vscode
  - So the idea here is that the references will be via FC, we remember the type at declaration and then point the usage back to the declaration (FC -> FC). We could dump all of this. (If we're still doing json.)
  - This information _could_ support renaming, too (but there may be indentation issues).
  - Do we want to (maybe later) keep the scope as a FC? We could do scope at point then.
- [ ] LSP and/or more editor support
  - [ ] refactor to query based?  E.g. importing a module
  - [ ] restart mid file (we could save state per top level decl)
  - [ ] rename in editor (need to accumulate all names and what they reference)
  - [ ] who calls X?  We can only do this scoped to the current context for now. Someday whole source dir. #lsp
- [ ] Pretty print
  - Can we format code? Maybe pull nearby comments or attach them like FC to tokens?
  - We would need to address stack and laziness issues in prettier printer (or make it merely pretty)
- [ ] Add info to Ref/VRef (is dcon, arity, etc)
  - To save lookups during compilation and it might make eval faster
- [ ] Consider splitting desugar/check
  - We can only check physical syntax at the moment, which has been inconvenient in a couple of spots where we want to check generated code. E.g. solutions to auto implicits.
  - case let for do, list syntax, and tuple syntax are desugared in the parser. operators are run in the parser.
- [ ] Eq Nat does things the hard way, can we turn it into `==`?
  - We could have a compile time substitution for the function
  - Maybe this could reify how we're hard coding functions to js operators
- Improve `auto`
  - [ ] Improve cases where the auto isn't solved because of a type error
  - [ ] Handle `Foo Blah`, `Foo a => Bar a` vs `Bar Blah`
- [ ] Add some optimizations
  - It would be nice if IO looked like imperative JS, but that might be a bit of a stretch.
- [ ] warn on unused imports?
  - Probably have to mark on name lookup, maybe wait until we have query-based
- [ ] Add default path for library, so we don't need symlinks everywhere and can write tests for the library
  - We need this to work for tests / dev and for installed newt.
  - The new `FileSource` mechanism might help here.
- [ ] mutual recursion in where?
  - need to scan sigs and then defs, will have to make sure Compile.idr puts them all in scope before processing each.
  - we probably want this, just haven't gotten around to it.
  - LetRec would have to be extended to have multiple names.
- [ ] Consider making `<` independent of `Ord`, so we get the `<` oper in the javascript.
  - Or a "default implementation" deal.
- [ ] There are issues with matching inside do blocks
    - I may have handled a lot of this by reworking autos to check just one level of constraints (with a 20% speedup)
    - Do we need to guess scrutinee? Or we could refine a meta scrutinee type to match the constructor being split. This happens during checking for pi, where we create ?m -> ?m and unifiy it with the meta. Could we do the same in a case, where `Just ...` says the meta must be `Maybe ?m`?
  - ~~`newt/Fixme.newt` - I can drop `do` _and_ put `bind {IO}` to push it along. It may need to try to solve autos earlier and better.~~

### Error messages

- [ ] "Failed to unify %var0 and %var1" - get names in there
  - Need fancier `Env` or the index on the type of `Tm`
  - Or the name on the VVar?
  - Also we should render %pi, etc more readably (bonus points for _×_)
- [ ] Better FC for parse errors (both EOF and the ones that show up just after the error)

### Documentation

- [ ] Document syntax
- [ ] Document case building

### Language

- [ ] add something like `rewrite` to make replace easier to use
  - look at Idris and pi-forall
  - consider something interactive (what would Ask do?)
- [ ] play with documentation extraction?
  - lean uses `/--` and `/-!` I think I prefer something like this over the `|||` in Idris.
- [ ] Idris `!` / Lean `<-` notation.
- [ ] Maybe `letcase` for case `let` statements (the "must have parens" rule is subtle - we might get away with "is it capital or app" though.
- [ ] Maybe `local` for `where`-like `let` clauses? (I want a `where` that closes over more stuff)
- [ ] Maybe allow `{x}` to skip over auto and vice-versa
  - I think we print a mismatch here. Not sure how useful it would be though.
  - I can do `let f : ... = \ a b c => ...`. But it doesn't work for recursion and cases are awkward.

### Case building

- [ ] Warnings or errors for unused cases
  - This is important when misspelled constructors become pattern vars
- [ ] Support pattern matching on `Lazy x`
  - e.g. change second arg of `<|>` to lazy, Parser.Impl doesn't compile
    complaining that `Lazy` is not a type constructor.
  - Put a match on `Delay` there (add `Delay` to surface syntax). Eliminator forces the function
  - Can be manually done today by breaking out another `case` for the lazy value (scrutinee is forced)
- [ ] Collect remaining cases on default / variable patterns for more precise case split

### Type classes

- [ ] typeclass dependencies
  - need to flag internal functions to not search (or flag functions for search). I need to decide on syntax for this.
  - for something like an `isEq` field in `Ord`, auto-search is picking up the function being defined.
- [ ] default implementations (use them if nothing is defined, where do we store them?) e.g. Ord compare, <, etc in Idris
  - I may need to actually store some details on interfaces rather than reverse engineer from type.
- [x] syntax for negative integers
- [ ] if we're staying with this version of auto, we might need to list candidates and why they're rejected. e.g. I had a bifunctor fail to solve because the right answer unblocked a Foo vs IO Foo mismatch

### Parser

- [ ] Qualified names
- [ ] Improve FC
  - [ ] mechanism to capture the range for a production
  - [ ] FC on more names (rather than relying on the expression FC
- [ ] Parse error not ideal for `\x y z b=> b` (points to lambda)
- [ ] Consider `.newt.md` support.

### LSP

- [ ] add jump to definition for non-top-level functions
- [ ] Maybe run whole project for completion search and "all errors in project"
- [x] code action to add clause
- [ ] Add missing args code action?
  - when a constructor is underapplied
  - is this useful? we would probably have to add at the end
- [x] case split
  - We could fake this up:
    - given a name and a point in the editor
    - walk through the function looking for the binder
    - get its type
    - enumerate valid constructors (and their arity)
    - Repeat the line with each, applied to args
    - For `<-` or `let` we'd want to fudge some `|` lines
    - [ ] `let` has issues for multiline split / add missing
    - [ ] `derive` has phantom split actions in it

### Code generation

- [ ] add default failing case for constructor matching to catch errors
- [ ] C backend
  - [x] Rework the Javascript AST to be more generic semi-A-Normal form (WIP)
  - [x] Generated code accepted by C compiler
  - [ ] Check in C code generation
  - [ ] Implement runtime for C code generation
  - [ ] Runtime implementation

### Misc

- [ ] White box tests in `test` directory (I can't get this to work right with pack et al)
- [x] Put worker in iframe on safari
- [ ] Warnings or errors for missing definitions (e.g. on `Axiom` in codegen)
- [ ] literals for double
- [ ] add unit test framework
- [ ] Require infix decl before declaring mixfix names with `_` (helps find bugs) or implicitly define as infixl if it is missing
- [ ] consider putting binders in environment, like Idris, to better mark `let` and to provide names for printing
  - I might want to distinguish `let` from pattern vars from user-`let`.
- [x] move some top-level chattiness to `debug`
- [ ] consider optionally compiling to eliminators for a second type-checking pass to help catch bugs.
- [ ] copattern matching
- [ ] consider making meta application implicit in term, so it's more readable when printed
  - Currently we have explicit `App` surrounding `Meta` when inserting metas. Some people
    leave that implicit for efficiency. I think it would also make printing more readable.
  - When printing `Value`, I now print the spine size instead of spine.
- [ ] Lean ⟨ ⟩ anonymous constructors
  - This would only work for `check` and we might need to revisit how `,` is handled.
- [ ] Lean-like `#eval`
- [ ] Lean-like .map, etc? (resolve name in namespace of target type, etc)
- [ ] detect extra clauses in case statements
- [ ] add test framework
- [ ] magic tuple? (codegen as array)
  - Seems like this would be tricky as soon as the user starts peeling off the tail or consing them
- [ ] magic newtype? (drop them in codegen)
  - Needed before we switch IO to newtype, so the tail recursion still works
- [ ] Maybe a rollup plugin? (So web apps can be rolled up from newt.)
- [-] pattern matching lambda
  - `\case` is sufficient
  - I kept wanting this in AoC and use it a lot in the newt code
  - This conflicts with current code (unused?) that allows telescope information in lambdas

### Background

- [ ] Read Ulf Norell thesis
- [ ] Finish reading dynamic pattern unification paper to see what is missing/wrong with the current implementation
- [ ] Read "Unifiers as Equivalences" has unification with types.  Look into adapting some of that (or at least read/understand it).  Indexed types are mentioned here.

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
