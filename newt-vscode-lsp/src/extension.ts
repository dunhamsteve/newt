import * as vscode from "vscode";
import { ABBREV } from "./abbrev";
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
  TransportKind
} from 'vscode-languageclient/node';

// They put this at module level for deactivate below.
let client: LanguageClient

export function activate(context: vscode.ExtensionContext) {
  const serverModule = context.asAbsolutePath('./dist/lsp.js')
  console.log('*** servervModule', serverModule)
  const config = vscode.workspace.getConfiguration("newt");
  const cmd = config.get<string | null>("lspPath");

  let serverOptions: ServerOptions
  if (cmd) {
    serverOptions = {
      run: { command: "node", args: [cmd], transport: TransportKind.pipe },
      debug: { command: "node", args: [cmd], transport: TransportKind.pipe },
    }
  } else {
    serverOptions = {
      run: { module: serverModule, transport: TransportKind.ipc },
      debug: { module: serverModule, transport: TransportKind.ipc },
    }
  }

  const clientOptions: LanguageClientOptions = {
    documentSelector: [{ scheme: 'file', language: 'newt' }],
    synchronize: {
      fileEvents: vscode.workspace.createFileSystemWatcher('*.newt')
    }
  }

  client = new LanguageClient(
    'NewtLanguageServer',
    'Newt Language Server',
    serverOptions,
    clientOptions
  )

  client.start();
  console.log('CLIENT started')

  vscode.workspace.onDidChangeTextDocument((event) => {
    const editor = vscode.window.activeTextEditor;
    if (!editor || event.document !== editor.document) return;

    const changes = event.contentChanges;
    if (changes.length === 0) return;

    // TODO - agda input mode does the replacement as soon as possible
    // but if the sequence is a prefix, it will change for subsequent characters
    // The latter would require keeping state, but if we don't allow sequences to prefix
    // each other, we could activate quicker.
    const lastChange = changes[changes.length - 1];
    const text = lastChange.text;
    // Check if the last change is a potential shortcut trigger
    if (!text || !(" ')\\_".includes(text) || text.startsWith('\n'))) return;

    const document = editor.document;
    const position = lastChange.range.end;
    const lineText = document.lineAt(position.line).text;
    const start = Math.max(0, position.character - 10);
    const snippet = lineText.slice(start, position.character);
    const m = snippet.match(/(\\[^ ]+)$/);
    if (m) {
      const cand = m[0];
      console.log("cand", cand);
      const replacement = ABBREV[cand];
      console.log("repl", replacement);
      if (replacement) {
        const range = new vscode.Range(
          position.line,
          position.character - cand.length,
          position.line,
          position.character
        );
        editor.edit((editBuilder) => {
          editBuilder.replace(range, replacement);
        });
      }
    }
  });
  return;

}

export function deactivate() {
  if (client) client.stop();
}
