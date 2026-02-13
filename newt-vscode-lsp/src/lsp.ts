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

documents.onDidChangeContent(async (change) => {
  console.log('DIDCHANGE', change.document.uri)
  const uri = change.document.uri;
  const text = change.document.getText();
  LSP_updateFile(uri, text);
  const diagnostics = LSP_checkFile(uri);
  console.log(`Got ${JSON.stringify(diagnostics, null, '  ')}`)
  connection.sendDiagnostics({ uri, diagnostics })
});

connection.onHover((params): Hover | null => {
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