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
} from "vscode-languageserver/node";
import { TextDocument } from "vscode-languageserver-textdocument";

const connection = createConnection(ProposedFeatures.all);
const documents = new TextDocuments(TextDocument);

// the last is the most important to the user, but we run FIFO
// to ensure dependencies are seen in causal order
let changes: TextDocument[] = []
let running: NodeJS.Timeout | undefined
function addChange(doc: TextDocument) {
  console.log('enqueue', doc.uri)
  // drop stale pending changes
  let before = changes.length
  changes = changes.filter(ch => ch.uri != doc.uri)
  console.log('DROP', changes.length - before);
  changes.push(doc)
  if (!running) running = setTimeout(runChange, 1)
}

function runChange() {
  let doc = changes.shift()
  if (!doc) {
    running = undefined
    return
  }
  const uri = doc.uri
  const diagnostics = LSP_checkFile(doc.uri)
  connection.sendDiagnostics({uri,diagnostics})
  console.log('SENT', doc.uri);
  running = undefined
  // give more a chance to file in.
  running = setTimeout(runChange,1)
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
  let value = LSP_hoverInfo(uri, pos.line, pos.character)
  if (!value) return null
  console.log('HOVER is ', value)
  return { contents: { kind: "plaintext", value } };
});

connection.onInitialize((_params: InitializeParams): InitializeResult => ({
  capabilities: {
    textDocumentSync: TextDocumentSyncKind.Incremental,
    hoverProvider: true,
  },
}));

documents.listen(connection);
connection.listen();
console.log('STARTED')