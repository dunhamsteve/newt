import * as vscode from "vscode";
import { ABBREV } from "./abbrev";
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
  TransportKind
} from 'vscode-languageclient/node';

function getIndent(text: string) {
  return text.match(/\S/)?.index ?? 0
}

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

  // HACK Temporarily copied from non-LSP version, until code actions are implemented
  context.subscriptions.push(
    vscode.languages.registerCodeActionsProvider(
      { language: "newt" },
      {
        provideCodeActions(document, range, context, token) {
          const actions: vscode.CodeAction[] = [];
          for (const diagnostic of context.diagnostics) {
            let {message,range} = diagnostic;
            let m = message.match(/missing cases: \[(.*)\]/);
            if (m) {
              // A lot of this logic would also apply to case split.
              let cons = m[1].split(', ');
              let line = range.start.line;
              let lineText = document.lineAt(line).text;
              // this isn't going to work for let.
              // and I think I relaxed the indent for `|`
              const indent = getIndent(lineText)
              let m2 = lineText.match(/(.*=>?)/);
              if (!m2) continue;
              let s = range.start.character;
              let e = range.end.character;
              let a = lineText.slice(0,s);
              let b = lineText.slice(e,m2[0].length);
              let parens = a.endsWith('(') && b.startsWith(')');
              let lines = cons.map(con =>
                !parens && con.includes('_')
                ? `${a}(${con})${b} ?`
                : `${a}${con}${b} ?`);
                const fix = new vscode.CodeAction(
                  "Add missing cases",
                  vscode.CodeActionKind.QuickFix
                );
                fix.edit = new vscode.WorkspaceEdit();
                // skip indented lines
                while (1) {
                  line = line + 1
                  lineText = document.lineAt(line).text
                  if (!lineText.trim() || getIndent(lineText) <= indent) break
                }
                const insertPos = new vscode.Position(line, 0);
                let text = lines.join('\n') + '\n';
                if (insertPos.line === document.lineCount) {
                  text = "\n" + text;
                }
                fix.edit.insert(document.uri, insertPos, text);
                fix.diagnostics = [diagnostic];
                fix.isPreferred = true;
                actions.push(fix);
            }
            m = message.match(/try importing: (.*)/);
            if (m) {
              let mods = m[1].split(', ')
              let insertLine = 0;
              for (let i = 0; i < document.lineCount; i++) {
                const line = document.lineAt(i).text;
                if (/^(import|module)\b/.test(line)) insertLine = i + 1;
              }
              const insertPos = new vscode.Position(insertLine, 0);
              for (let mod of mods) {
                const fix = new vscode.CodeAction(
                  `Import ${mod}`,
                  vscode.CodeActionKind.QuickFix
                );
                fix.edit = new vscode.WorkspaceEdit();
                fix.edit.insert(document.uri, insertPos, `import ${mod}\n`);
                fix.diagnostics = [diagnostic];
                // fix.isPreferred = true;  // they're all preferred?
                actions.push(fix);
              }
            }
          }
          return actions;
        }
      }
    )
  );
  return;

}

export function deactivate() {
  if (client) client.stop();
}
