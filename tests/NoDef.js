import { LSP_codeActionInfo, LSP_checkFile } from '../build/lsp.js'

let clog = console.log
console.log = () => { }
function showActions(urn) {
  LSP_checkFile(urn)
  let actions = LSP_codeActionInfo(urn, 6, 0)
  for (let {title, edit} of actions) {
    clog(`*** ${title}`)
    for (let fn in edit.changes) {
      for (let change of edit.changes[fn]) {
        let base = fn.split('/').at(-1)
        clog(`${base} ${change.range.start.line}:${change.range.start.character}--${change.range.end.line}:${change.range.end.character} ${JSON.stringify(change.newText)}`)
      }
    }
  }
}

async function main() {
  const urn = `file://${process.cwd()}/tests/NoDef.newt`
  showActions(urn)
}
main()
