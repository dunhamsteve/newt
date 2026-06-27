augroup NewtUnicode
autocmd!

autocmd FileType newt inoremap <buffer> \\ \

" Single-character sequences
autocmd FileType newt inoremap <buffer> \r  →
autocmd FileType newt inoremap <buffer> \x  ×
autocmd FileType newt inoremap <buffer> \0  ₀
autocmd FileType newt inoremap <buffer> \1  ₁
autocmd FileType newt inoremap <buffer> \2  ₂
autocmd FileType newt inoremap <buffer> \3  ₃

" Multi-character sequences
autocmd FileType newt inoremap <buffer> \all ∀
autocmd FileType newt inoremap <buffer> \==  ≡
autocmd FileType newt inoremap <buffer> \neg  ¬
autocmd FileType newt inoremap <buffer> \[[  ⟦
autocmd FileType newt inoremap <buffer> \]]  ⟧
autocmd FileType newt inoremap <buffer> \circ ∘

" Sets and Types
autocmd FileType newt inoremap <buffer> \bN  ℕ
autocmd FileType newt inoremap <buffer> \bZ  ℤ

" Greek/Logic Prefixes
autocmd FileType newt inoremap <buffer> \GP  ∏
autocmd FileType newt inoremap <buffer> \GS  Σ
autocmd FileType newt inoremap <buffer> \GD  Δ
autocmd FileType newt inoremap <buffer> \GG  Γ
autocmd FileType newt inoremap <buffer> \Gl  λ
autocmd FileType newt inoremap <buffer> \Gs  σ
autocmd FileType newt inoremap <buffer> \Gt  τ
augroup END

