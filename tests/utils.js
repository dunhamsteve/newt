import { LSP_codeActionInfo, LSP_checkFile } from '../build/lsp.js'

export let clog = console.log
console.log = () => { }

let LEVEL = ["0", "ERROR", "WARN", "INFO"]
const showRange = (range) => `${range.start.line}:${range.start.character}--${range.end.line}:${range.end.character}`
const jstr = (obj) => JSON.stringify(obj)

export function checkFile(fn) {
  const urn = `file://${process.cwd()}/tests/${fn}`
  clog(`*** Check ${fn}`)
  let res = LSP_checkFile(urn)
  for (let error of res) {
    clog(`${LEVEL[error.severity]} ${showRange(error.range)} ${jstr(error.message)}`)
  }
  clog()
}
export function showActions(fn, row, col) {
  const urn = `file://${process.cwd()}/tests/${fn}`
  clog(`*** Actions ${fn} ${row} ${col}`)
  let actions = LSP_codeActionInfo(urn, row, col)
  for (let {title, edit} of actions) {
    clog(`* ${title}`)
    for (let fn in edit.changes) {
      for (let change of edit.changes[fn]) {
        let base = fn.split('/').at(-1)
        clog(`- ${base} ${showRange(change.range)} ${jstr(change.newText)}`)
      }
    }
  }
  clog()
}

