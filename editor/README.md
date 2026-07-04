



## Editor support for Newt


### BBEdit

I had to write a "code-less" extension as an XML plist to specify highlighting and point to the LSP. (The keys for setting the LSP in the plist were undocumented.) The highlighting is crude. I didn't get it to fully support the strings, but I don't think I spent much time on it.

In settings, choose "Languages" on the left, click "Install Language Module...", and choose the `NewtLanguageModule.plist` file.

### Nova

Nova needs tree-sitter parser, and you have to build it with their build script to link with their framework. The LSP works with it. I could not get unicode shortcuts to work, and I don't like that the project-wide search doesn't support regex.

### Nvim / Vim

The vim support is one directory up, in `/vim`. Link it as `~/.config/nvim/pack/dev/start/newt`. It includes syntax rules in `syntax/newt.vim`, but lsp is also supported in nvim by putting `newt.dylib` in `~/.config/nvim/parser` and the queries in `~/.config/nvim/queries/newt`.

I was able to get the unicode shortcuts to work in both vim and nvim.

### Emacs

Emacs now has tree-sitter support, which I haven't tried. I also implemented simple syntax highlighting. For the unicode characters, I use the agda-mode input method. I have LSP working there.

### Helix

I was able to get the unicode and LSP working.

### Zed / Gram

I got it to work with the LSP.

### Sublime / bat / typst

The `bat` utility and typst use sublime text highlighting files. It looks like I got the strings working in syntax highlighting.


### github

Github doesn't support custom highlighting, but you can borrow a similar language's highlighter with the following in `.gitattributes`:
```
*.newt linguist-language=agda linguist-detectable
```

## Misc

### topiary

Topiary lets you define a pretty printer based on a tree-sitter grammar, but it won't work for newt:

- Topiary appears to ignore `append_indent_end` on nodes of 0 length, like end.
- doBlock ends with `(end)`, and putting an `append_indent_end` on the `doBlock` will put it on the `(end)` and it will be dropped.
- putting it on something like `(_) @append_indent_end . (end)` will tag some of them, but not `(end) (end)`
- even in that case, we can't find a physical node to tag _multiple_ `append_indent_end` onto.

