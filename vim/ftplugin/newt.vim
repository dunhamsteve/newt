setlocal syntax=newt
setlocal comments=s1:/-,mb:*,ex:-/,:--
setlocal commentstring=--\ %s
setlocal expandtab
setlocal tabstop=2
" run make so we get project-wide errors LSP picks up the local ones
setlocal makeprg=make
" setlocal makeprg=newt\ %
setlocal errorformat=ERROR\ at\ %f:%l:%c--%e:%k:\ %m
