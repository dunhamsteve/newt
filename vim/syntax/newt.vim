syn keyword newtInfix infix infixl infixr
syn keyword newtKW data where let in case of derive module import if then else
syn match newtType "\<[A-Z][a-zA-Z]*\>"
syn region newtBlockComment start="/-" end="-/"
syn match newtLineComment "--.*$" contains=@Spell

" no idea why this works for idris but not here
highlight def link newtType Identifier
highlight def link newtInfix PreProc
highlight def link newtBlockComment Comment
highlight def link newtLineComment Comment
highlight def link newtStructure Keyword
highlight def link newtKW Keyword

let b:current_syntax = "newt"
