

# Web framework experiment

Work in progress of a DOM-patching web framework, like Elm.

In the root, you can do:

```sh
newt src/Todo.newt -o dist/main.js
esbuild dist/main.js --bundle --servedir=web --outdir=web --alias:fs=./dist/empty.js --watch
```
