syn keyword newtInfix infix infixl infixr
syn keyword newtKW data where let in case of
syn keyword newtLet let in
syn match newtIdentifier "[a-zA-Z][a-zA-Z]*" contained
syn keyword newtStructure data import module where
syn region newtBlockComment start="/-" end="-/" contained
syn match newtLineComment "--.*$" contains=@Spell

" no idea why this works for idris but not here
"highlight dev link newtIdentifier Identifier
highlight def link newtInfix PreProc
highlight def link newtBlockComment Comment
highlight def link newtLineComment Comment
highlight def link newtLet Structure
highlight def link newtStructure Structure

let b:current_syntax = "newt"
