/**
 * WIP
 *
 * Wraps newt.js (compiled from src/LSP.newt with some tweaks to `export`) with the
 * vscode LSP server module.
 */

import { LSP_checkFile, LSP_updateFile, LSP_hoverInfo } from './newt.js'

import {
  createConnection,
  TextDocuments,
  ProposedFeatures,
  Hover,
  InitializeParams,
  InitializeResult,
  TextDocumentSyncKind,
  Location,
} from "vscode-languageserver/node";
import { TextDocument } from "vscode-languageserver-textdocument";

const connection = createConnection(ProposedFeatures.all);
const documents = new TextDocuments(TextDocument);

// the last is the most important to the user, but we run FIFO
// to ensure dependencies are seen in causal order
let changes: TextDocument[] = []
let running = false
let lastChange = 0
function addChange(doc: TextDocument) {
  console.log('enqueue', doc.uri)
  // drop stale pending changes
  let before = changes.length
  changes = changes.filter(ch => ch.uri != doc.uri)
  console.log('DROPPED', before - changes.length);
  changes.push(doc)
  lastChange = +new Date()
  if (!running) runChange()
}

const sleep = (ms: number) => new Promise(resolve => setTimeout(resolve, ms));

async function runChange() {
  try {
    running = true;
    while (changes.length) {
      console.log('LOOP TOP')
      // Wait until things stop changing
      let prev = lastChange
      while (1) {
        await sleep(100)
        if (prev == lastChange) break
        prev = lastChange
        console.log('DELAY')
      }
      let doc = changes.shift()
      if (!doc) {
        running = false
        return
      }
      const uri = doc.uri
      const start = +new Date()
      const diagnostics = LSP_checkFile(doc.uri)
      const end = +new Date()
      console.log('CHECK', doc.uri, 'in', end - start);
      await sleep(1);
      if (!changes.find(ch => ch.uri === uri)) {
        connection.sendDiagnostics({ uri, diagnostics })
      } else {
        console.log('STALE result not sent for', uri)
      }
    }
  } finally {
    running = false;
  }
}

documents.onDidChangeContent(async (change) => {
  console.log('DIDCHANGE', change.document.uri)
  const uri = change.document.uri;
  const text = change.document.getText();
  // update/invalidate happens now, check happens on quiesce.
  LSP_updateFile(uri, text);
  addChange(change.document);
});

connection.onHover((params): Hover | null => {
  // wait until quiesced (REVIEW after query-based)
  if (running) return null

  const uri = params.textDocument.uri;
  const pos = params.position;
  console.log('HOVER', uri, pos)
  let res = LSP_hoverInfo(uri, pos.line, pos.character)
  if (!res) return null
  console.log('HOVER is ', res)
  return { contents: { kind: "plaintext", value: res.info } };
});

connection.onDefinition((params): Location | null => {
  const uri = params.textDocument.uri;
  const pos = params.position;
  let value = LSP_hoverInfo(uri, pos.line, pos.character)
  if (!value) return null;
  return value.location
})

connection.onInitialize((_params: InitializeParams): InitializeResult => ({
  capabilities: {
    textDocumentSync: TextDocumentSyncKind.Incremental,
    hoverProvider: true,
    definitionProvider: true,
  },
}));

documents.listen(connection);
connection.listen();
console.log('STARTED')