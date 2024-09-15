import * as vscode from "vscode";
import { exec } from "child_process";
import path from "path";

export function activate(context: vscode.ExtensionContext) {
  const diagnosticCollection =
    vscode.languages.createDiagnosticCollection("newt");

  function checkDocument(document: vscode.TextDocument) {
    const fileName = document.fileName;
    // Is there a better way to do this? It will get fussy with quoting and all plus it's not visible to the user.
    const workspaceFolder = vscode.workspace.getWorkspaceFolder(document.uri);
    const cwd = workspaceFolder
      ? workspaceFolder.uri.fsPath
      : path.dirname(fileName);
    const config = vscode.workspace.getConfiguration("newt");
    const cmd = config.get<string>("path", "build/exec/newt");
    const command = `${cmd} ${fileName}`;
    exec(command, { cwd }, (err, stdout, _stderr) => {
      // I think I ignored 1 here because I wanted failure to launch
      if (err && err.code !== 1) {
        vscode.window.showErrorMessage(`newt error: ${err}`);
      }

      // extract errors and messages from stdout
      const lines = stdout.split("\n");
      const diagnostics: vscode.Diagnostic[] = [];

      if (err) {
        let start = new vscode.Position(0,0)
        let end = new vscode.Position(0,1)
        let range = document.getWordRangeAtPosition(start) ?? new vscode.Range(start,end)
        const diag = new vscode.Diagnostic(range, "newt execution failed", vscode.DiagnosticSeverity.Error)
        diagnostics.push(diag)
      }

      for (let i = 0; i < lines.length; i++) {
        const line = lines[i];
        const match = line.match(/(INFO|ERROR) at \((\d+), (\d+)\): (.*)/);
        if (match) {
          let [_full, kind, line, column, message] = match;
          let lnum = Number(line);
          let cnum = Number(column);
          let start = new vscode.Position(lnum, cnum);
          // we don't have the full range, so grab the surrounding word
          let end = new vscode.Position(lnum, cnum+1);
          let range =
            document.getWordRangeAtPosition(start) ??
            new vscode.Range(start, end);
          // heuristics to grab the entire message:
          // anything indented
          // Context:, or Goal: are part of PRINTME
          // unexpected / expecting appear in parse errors
          while (
            lines[i + 1]?.match(/^(  )/)
          ) {
            message += "\n" + lines[++i];
          }
          const severity = kind === 'ERROR' ? vscode.DiagnosticSeverity.Error : vscode.DiagnosticSeverity.Information;
          const diag = new vscode.Diagnostic(range, message, severity);
          diagnostics.push(diag);
        }
      }
      diagnosticCollection.set(vscode.Uri.file(fileName), diagnostics);
    });
  }

  const runPiForall = vscode.commands.registerCommand(
    "newt-vscode.check",
    () => {
      const editor = vscode.window.activeTextEditor;
      if (editor) {
        const document = editor.document;
        if (document.fileName.endsWith(".newt")) {
          checkDocument(document);
        }
      }
    }
  );
  context.subscriptions.push(runPiForall);

  vscode.workspace.onDidSaveTextDocument((document) => {
    if (document.fileName.endsWith(".newt")) {
      vscode.commands.executeCommand("newt-vscode.check");
    }
  });
  vscode.workspace.onDidOpenTextDocument((document) => {
    if (document.fileName.endsWith(".newt")) {
      vscode.commands.executeCommand("newt-vscode.check");
    }
  });
  for (let document of vscode.workspace.textDocuments) {
    if (document.fileName.endsWith(".newt")) {
      checkDocument(document);
    }
  }
  context.subscriptions.push(diagnosticCollection);
}

export function deactivate() {}
