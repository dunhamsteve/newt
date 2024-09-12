
## TODO

- [ ] there is some zero argument application in generated code
  - possibly the fancy "apply arity then curry the rest" bit
- [x] inline metas.  Maybe zonk after TC/elab
- [x] implicit patterns
- [ ] pair syntax
- [ ] list syntax
- [ ] operators
- [ ] import
- [ ] add {{ }} and solving autos
  - considering various solutions.  Perhaps marking the data type as solvable, if we had types on metas.
- [ ] do blocks
- [ ] some solution for `+` (classes? ambiguity?)
- [ ] show compiler failure in the editor (exit code != 0)
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
