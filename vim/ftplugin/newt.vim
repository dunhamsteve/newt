setlocal syntax=newt
setlocal comments=s1:/-,mb:*,ex:-/,:--
setlocal commentstring=--\ %s
setlocal expandtab
setlocal tabstop=2
" run make so we get project-wide errors LSP picks up the local ones
setlocal makeprg=make
" setlocal makeprg=newt\ %
setlocal errorformat=ERROR\ at\ %f:%l:%c--%e:%k:\ %m

" Single-character sequences
inoremap <buffer> \r  →
inoremap <buffer> \x  ×
inoremap <buffer> \0  ₀
inoremap <buffer> \1  ₁
inoremap <buffer> \2  ₂
inoremap <buffer> \3  ₃

" Multi-character sequences
inoremap <buffer> \all ∀
inoremap <buffer> \==  ≡
inoremap <buffer> \=?  ≟
inoremap <buffer> \neg  ¬
inoremap <buffer> \[[  ⟦
inoremap <buffer> \]]  ⟧
inoremap <buffer> \circ ∘
inoremap <buffer> \cuL ⌈
inoremap <buffer> \cuR ⌉

" Sets and Types
inoremap <buffer> \bN  ℕ
inoremap <buffer> \bZ  ℤ

" Greek/Logic Prefixes
inoremap <buffer> \GP  ∏
inoremap <buffer> \GS  Σ
inoremap <buffer> \GD  Δ
inoremap <buffer> \GG  Γ
inoremap <buffer> \Gl  λ
inoremap <buffer> \Gs  σ
inoremap <buffer> \Gt  τ
inoremap <buffer> \Ga  α
inoremap <buffer> \Gd  δ
inoremap <buffer> \Ge  ε


