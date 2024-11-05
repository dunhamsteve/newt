import './style.css'
import {newtLanguage} from './monarch.ts'

import * as monaco from 'monaco-editor'


monaco.languages.setMonarchTokensProvider("newt", newtLanguage);

let container = document.getElementById('editor')!
let result = document.getElementById('result')!
const editor = monaco.editor.create(container, {
  value: "module Main\n\n",
  language: "newt",
  theme: "vs",

  automaticLayout: true,
})

let timeout : number | undefined

function run(s: string) {
  console.log('run', s)
  process.argv = ['','', 'src/Main.newt']
  files['src/Main.newt'] = s
  result.innerHTML = ''
  __mainExpression_0()
}


// We'll want to collect and put info in the monaco
process.stdout.write = (s) => {
  console.log('write', s)
  let div = document.createElement('div')
  div.className = 'log'
  div.textContent = s
  result.appendChild(div)
}

editor.onDidChangeModelContent((ev) => {
  console.log('mc', ev)
  let value = editor.getValue()
  clearTimeout(timeout)
  timeout = setTimeout(() => run(value), 1000)
})
console.log('REGISTER')
