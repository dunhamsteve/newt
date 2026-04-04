# Newt "Spruce" framework • [TodoMVC](http://todomvc.com)

## Implementation

An implementation of TodoMVC, using the official CSS and DOM structure. I threw together an Elm-like framework that I'm calling "spruce" for now. It's lacking features, but works.

I don't have a good story for javascript imports yet, so I'm embedding the DOM patcher in [Spruce.newt](../src/Web/Spruce.newt).

## Dev

If you background vite, you can rerun the newt command and reload the browser.  Hot reload is not implemented.

```
newt src/Todo.newt -o public/app.js
vite public
```

## Build

```
newt src/Todo.newt -o public/app.js
vite build --minify public
```
