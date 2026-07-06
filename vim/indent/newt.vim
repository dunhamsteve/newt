" indentation for newt
"
" Based on haskell indentation by motemen <motemen@gmail.com>
"

if exists('b:did_indent')
  finish
endif

let b:did_indent = 1

setlocal indentexpr=GetNewtIndent()
setlocal indentkeys=!^F,o,O,0=of,0=where,0==

function! GetNewtIndent()
  let l:pline = prevnonblank(v:lnum - 1)
  if l:pline == 0
    return 0
  endif

  let prevline = getline(v:lnum - 1)
  let l:prevIndent = indent(l:pline)
  let l:prevLine = getline(l:pline)

  if l:prevLine =~# '\<\(of\|where\|do\|=\)\s*$'
    return l:prevIndent + 2
  endif

  " return on a blank line outdents
  if l:prevLine =~ '^\s*$'
    return 0
  endif

  return l:prevIndent
endfunction

