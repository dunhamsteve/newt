

let current_compiler = 'newt'
if exists(":CompilerSet") != 2
  command -nargs=* CompilerSet setlocal <args>
endif

CompilerSet makeprg=newt
" doesn't work
CompilerSet errorformat=ERROR\ at\ (%l,\ %c)
