import * as vscode from "vscode";
import { exec } from "child_process";
import path from "path";
import { ABBREV } from "./abbrev";

interface FC {
  file: string;
  line: number;
  col: number;
}

interface TopEntry {
  fc: FC;
  name: string;
  type: string;
}
interface TopData {
  context: TopEntry[];
}

export function activate(context: vscode.ExtensionContext) {
  let topData: undefined | TopData;
  const diagnosticCollection =
    vscode.languages.createDiagnosticCollection("newt");

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
    if (!text || !( " ')\\_".includes(text) || text.startsWith('\n'))) return;

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

  function checkDocument(document: vscode.TextDocument) {
    const fileName = document.fileName;
    if (!fileName.endsWith(".newt")) return;

    // Is there a better way to do this? It will get fussy with quoting and all plus it's not visible to the user.
    const workspaceFolder = vscode.workspace.getWorkspaceFolder(document.uri);
    const cwd = workspaceFolder
      ? workspaceFolder.uri.fsPath
      : path.dirname(fileName);
    const config = vscode.workspace.getConfiguration("newt");
    const cmd = config.get<string>("path", "node bootstrap/newt.js");
    const command = `${cmd} --top ${fileName}`;
    let st = +new Date();
    exec(
      command,
      { cwd, maxBuffer: 1024 * 1024 * 10 },
      (err, stdout, _stderr) => {
        console.log(`newt took ${+new Date() - st}`);
        // I think I ignored 1 here because I wanted failure to launch
        if (err && err.code !== 1)
          vscode.window.showErrorMessage(`newt error: ${err}`);

        // extract errors and messages from stdout
        const lines = stdout.split("\n");
        const diagnostics: vscode.Diagnostic[] = [];

        if (err) {
          let start = new vscode.Position(0, 0);
          let end = new vscode.Position(0, 1);
          let range =
            document.getWordRangeAtPosition(start) ??
            new vscode.Range(start, end);
          const diag = new vscode.Diagnostic(
            range,
            "newt execution failed",
            vscode.DiagnosticSeverity.Error
          );
          diagnostics.push(diag);
        }

        for (let i = 0; i < lines.length; i++) {
          const line = lines[i];
          if (line.startsWith("TOP:")) {
            try {
              topData = JSON.parse(line.slice(4));
            } catch (e) {
              console.error("Bad top data", e);
            }
            console.log("top data", topData);
          }
            const match = line.match(
            /(INFO|WARN|ERROR) at (.*):(\d+):(\d+)--(\d+):(\d+):\s*(.*)/
            );
          if (match) {
            let [_full, kind, file, line, column, eline, ecol, message] = match;
            let lnum = +line - 1;
            let cnum = +column - 1;
            let elnum = +eline - 1;
            let ecnum = +ecol - 1;
            let start = new vscode.Position(lnum, cnum);
            let end = new vscode.Position(elnum, ecnum);
            let range = new vscode.Range(start, end);
            if (file !== fileName) {
              range = new vscode.Range(new vscode.Position(0,0), new vscode.Position(0,0));
            }
            // anything indented after the ERROR/INFO line are part of
            // the message
            while (lines[i + 1]?.match(/^(  )/)) message += "\n" + lines[++i];

            let severity;

            if (kind === "ERROR") severity = vscode.DiagnosticSeverity.Error;
            else if (kind === "WARN")
              severity = vscode.DiagnosticSeverity.Warning;
            else severity = vscode.DiagnosticSeverity.Information;
            const diag = new vscode.Diagnostic(range, message, severity);
            if (kind === "ERROR" || lnum > 0) diagnostics.push(diag);
          }
        }
        diagnosticCollection.set(vscode.Uri.file(fileName), diagnostics);
      }
    );
  }

  const runNewt = vscode.commands.registerCommand("newt-vscode.check", () => {
    const editor = vscode.window.activeTextEditor;
    if (editor) checkDocument(editor.document);
  });

  context.subscriptions.push(
    vscode.languages.registerDefinitionProvider(
      { language: "newt" },
      {
        provideDefinition(document, position, cancelToken) {
          if (!topData) return null;
          const wordRange = document.getWordRangeAtPosition(position);
          if (!wordRange) return null;
          const name = document.getText(wordRange);
          let entry = topData.context.find((entry) => entry.name === name);
          if (!entry) {
            console.log(`entry ${name} not found`);
            return null;
          }
          const root = vscode.workspace.getWorkspaceFolder(document.uri);
          if (!root) {
            console.error("Workspace folder not found");
            return null;
          }
          // let uri = vscode.Uri.file(path.join(root.uri.fsPath, entry.fc.file));
          let fileName = entry.fc.file;
          if (!fileName.startsWith('/')) fileName = path.join(root.uri.fsPath, fileName);
          let uri = vscode.Uri.file(fileName);
          console.log('root', root.uri.fsPath, 'file', entry.fc.file, 'uri', uri);
          let start = new vscode.Position(entry.fc.line, entry.fc.col);
          let range = new vscode.Range(start, start);
          return new vscode.Location(uri, range);
        },
      }
    )
  );
  context.subscriptions.push(
    vscode.languages.registerCompletionItemProvider(
      { language: "newt" },
      {
        provideCompletionItems(document, position, token, context) {
          if (!topData) return [];
          const wordRange = document.getWordRangeAtPosition(position);
          const prefix = wordRange ? document.getText(wordRange) : "";
          const items: vscode.CompletionItem[] = [];
          for (const entry of topData.context) {
            if (entry.name.startsWith(prefix)) {
              const item = new vscode.CompletionItem(entry.name, vscode.CompletionItemKind.Function);
              item.detail = entry.type;
              items.push(item);
            }
          }
          return items;
        }
      },
      ...'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_'.split('')
    )
  );
  context.subscriptions.push(
    vscode.languages.registerHoverProvider(
      { language: "newt" },
      {
        provideHover(document, position, token) {
          if (!topData) return null;
          const wordRange = document.getWordRangeAtPosition(position);
          if (!wordRange) return null;
          const name = document.getText(wordRange);
          let entry = topData.context.find((entry) => entry.name === name);
          if (!entry) {
            console.log(`entry ${name} not found`);
            return null;
          }
          return new vscode.Hover(`${entry.name} : ${entry.type}`);
        },
      }
    )
  );

  context.subscriptions.push(
    vscode.languages.registerDocumentSymbolProvider(
      { language: "newt" },
      {
        provideDocumentSymbols(document, token) {
          console.log("DSP!!");
          const symbols: vscode.DocumentSymbol[] = [];
          // we should ask the compiler
          const RE_FUNC = /^(|data|record|class|instance)\s*([\d\w']+)\s*:/;

          for (let i = 0; i < document.lineCount; i++) {
            const line = document.lineAt(i);
            const match = line.text.match(RE_FUNC);
            if (match) {
              const prefix = match[1];
              const functionName = match[2];
              const range = new vscode.Range(
                new vscode.Position(i, 0),
                new vscode.Position(i, line.text.length)
              );
              let type = vscode.SymbolKind.Function;
              let details = "Function";
              if (prefix === "class") type = vscode.SymbolKind.Interface;
              if (prefix === "instance") type = vscode.SymbolKind.Class;
              if (prefix === "record") type = vscode.SymbolKind.Struct;
              if (prefix === "data") type = vscode.SymbolKind.Struct;

              const symbol = new vscode.DocumentSymbol(
                functionName,
                details,
                type,
                range, // full range
                range  // selection
              );
              symbols.push(symbol);
            }
          }
          console.log("SYMBOLS", symbols);
          return symbols;
        },
      }
    )
  );

  context.subscriptions.push(runNewt);
  vscode.window.onDidChangeActiveTextEditor((editor) => {
    if (editor?.document.fileName.endsWith(".newt") && !editor.document.isDirty) {
      checkDocument(editor.document);
    }
  });
  vscode.workspace.onDidSaveTextDocument(checkDocument);
  vscode.workspace.onDidOpenTextDocument(checkDocument);
  vscode.workspace.textDocuments.forEach(checkDocument);

  context.subscriptions.push(diagnosticCollection);
  context.subscriptions.push(
    vscode.languages.registerCodeActionsProvider(
      { language: "newt" },
      {
        provideCodeActions(document, range, context, token) {
          const actions: vscode.CodeAction[] = [];
          for (const diagnostic of context.diagnostics) {
            let {message,range} = diagnostic;
            let m = message.match(/missing cases: (.*)/);
            if (m) {
              // A lot of this logic would also apply to case split.
              let cons = m[1].split(', ');
              const line = range.start.line;
              const lineText = document.lineAt(line).text;
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
                // TODO - we should skip over subsequent lines that are indented more than the current.
                const insertPos = new vscode.Position(line + 1, 0);
                fix.edit.insert(document.uri, insertPos, lines.join('\n') + '\n');
                fix.diagnostics = [diagnostic];
                fix.isPreferred = true;
                actions.push(fix);
            }
          }
          return actions;
        }
      }
    )
  );
}

export function deactivate() {}
