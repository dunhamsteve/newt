
" This can load for newt files or be loaded for code blocks in markdown.newt,
" but not for the entire markdown.newt file
if exists("b:current_syntax") && !exists("main_syntax")
  finish
endif
syn keyword newtInfix infix infixl infixr
syn keyword newtKW data where let in case of derive module import if then else alias class instance record constructor pfunc ptype uses do
syn match newtType "\<[A-Z][a-zA-Z0-9]*\>"
syn region newtBlockComment start="/-" end="-/"
syn match newtLineComment "--.*$" contains=@Spell

syn region newtInterp matchgroup=String start='\\{' end='}' contained contains=ALL
syn region newtString start='"' skip='\\["\\]' end='"' contains=@Spell,newtInterp

syn match newtChar "'\([^'\\]\|\\.\)'"

highlight def link newtType Identifier
highlight def link newtInfix PreProc
highlight def link newtBlockComment Comment
highlight def link newtLineComment Comment
highlight def link newtStructure Keyword
highlight def link newtKW Keyword
highlight def link newtString String
highlight def link newtChar Character

let b:current_syntax = "newt"
