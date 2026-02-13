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

// waiting for whomever to send accumulated changes
const DELAY_AFTER_SEND = 200
// waiting for typing to quiesce (and it seems accumulated changes have a delay between them)
const DELAY_AFTER_CHANGE = 100

// the last is the most important to the user, but we run FIFO
// to ensure dependencies are seen in causal order
let changes: TextDocument[] = []
let running: NodeJS.Timeout | undefined
let lastChange = 0
function addChange(doc: TextDocument) {
  console.log('enqueue', doc.uri)
  // drop stale pending changes
  let before = changes.length
  changes = changes.filter(ch => ch.uri != doc.uri)
  console.log('DROP', before - changes.length);
  changes.push(doc)
  lastChange = +new Date()
  // I'm not sure if this timeout is a big deal
  if (!running) running = setTimeout(runChange, DELAY_AFTER_CHANGE)
}


function runChange() {
  let now = +new Date()
  if ( now - lastChange < DELAY_AFTER_CHANGE) running = setTimeout(runChange, DELAY_AFTER_CHANGE);
  let doc = changes.shift()
  if (!doc) {
    running = undefined
    return
  }
  const uri = doc.uri
  const start = +new Date()
  const diagnostics = LSP_checkFile(doc.uri)
  const end = +new Date()
  connection.sendDiagnostics({uri,diagnostics})
  console.log('CHECK', doc.uri, 'in', end-start);
  running = undefined
  // If we just sent one, it seems that we need to give vscode some time to send the rest
  // Otherwise, for Elab.newt, we hit 1.8s for each character typed.
  // 1 ms doesn't work, so I guess we don't have the changes accumulated locally.
  running = setTimeout(runChange, DELAY_AFTER_SEND)
}

documents.onDidChangeContent(async (change) => {
  console.log('DIDCHANGE', change.document.uri)
  const uri = change.document.uri;
  const text = change.document.getText();
  LSP_updateFile(uri, text);
  // we defer the check to let all of the changes file in.
  addChange(change.document);
  // const diagnostics = LSP_checkFile(uri);
  // console.log(`Got ${JSON.stringify(diagnostics, null, '  ')}`)
  // connection.sendDiagnostics({ uri, diagnostics })
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