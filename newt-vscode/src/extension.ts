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
  name: String;
  type: String;
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

    const lastChange = changes[changes.length - 1];
    const text = lastChange.text;
    // Check if the last change is a potential shortcut trigger
    if (!text || !( " ')\\".includes(text) || text.startsWith('\n'))) return;

    const document = editor.document;
    const position = lastChange.range.end;
    const lineText = document.lineAt(position.line).text;
    const start = Math.max(0, position.character - 10);
    const snippet = lineText.slice(start, position.character);
    console.log(`change '${text}' snippet ${snippet}`);
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
            /(INFO|WARN|ERROR) at (.*):\((\d+), (\d+)\):\s*(.*)/
          );
          if (match) {
            let [_full, kind, file, line, column, message] = match;
            let lnum = Number(line) - 1;
            let cnum = Number(column) - 1;
            if (file !== fileName) lnum = cnum = 0;

            let start = new vscode.Position(lnum, cnum);
            // we don't have the full range, so grab the surrounding word
            let end = new vscode.Position(lnum, cnum + 1);
            let range =
              document.getWordRangeAtPosition(start) ??
              new vscode.Range(start, end);
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
    if (editor) {
      const document = editor.document;
      if (document.fileName.endsWith(".newt")) checkDocument(document);
    }
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

  vscode.workspace.onDidSaveTextDocument((document) => {
    if (document.fileName.endsWith(".newt"))
      vscode.commands.executeCommand("newt-vscode.check");
  });
  vscode.workspace.onDidOpenTextDocument((document) => {
    if (document.fileName.endsWith(".newt"))
      vscode.commands.executeCommand("newt-vscode.check");
  });
  for (let document of vscode.workspace.textDocuments)
    if (document.fileName.endsWith(".newt")) checkDocument(document);

  context.subscriptions.push(diagnosticCollection);
}

export function deactivate() {}
