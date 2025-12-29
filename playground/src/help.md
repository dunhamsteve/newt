# Newt Playground

Newt is a dependent typed programming language that compiles to javascript. This playground embeds the newt compiler and a codemirror based editor.

The editor will typecheck the file with newt and render errors as the file is changed. The current file is saved to localStorage and will be restored if there is no data in the URL. Cmd-s or Ctrl-s will create a url embedding the file contents.

## Tabs

**Output** - Displays the compiler output, which is also used to render errors and info annotations in the editor.

**JS** - Displays the javascript translation of the file

**Console** - Displays the console output from running the javascript

**Help** - Displays this help file

## Buttons

:play: Compile and run the current file in an iframe, console output is collected to the console tab.

:share: Embed the current file in the URL and copy to clipboard.

## Keyboard

*C-s or M-s* - Embed the current file in the URL and copy to clipboard


