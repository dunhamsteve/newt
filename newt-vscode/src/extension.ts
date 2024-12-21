import * as vscode from "vscode";
import { exec } from "child_process";
import path from "path";

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

  function checkDocument(document: vscode.TextDocument) {
    const fileName = document.fileName;
    // Is there a better way to do this? It will get fussy with quoting and all plus it's not visible to the user.
    const workspaceFolder = vscode.workspace.getWorkspaceFolder(document.uri);
    const cwd = workspaceFolder
      ? workspaceFolder.uri.fsPath
      : path.dirname(fileName);
    const config = vscode.workspace.getConfiguration("newt");
    const cmd = config.get<string>("path", "build/exec/newt");
    const command = `${cmd} --top ${fileName}`;
    exec(
      command,
      { cwd, maxBuffer: 1024 * 1024 * 10 },
      (err, stdout, _stderr) => {
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
            /(INFO|ERROR) at (.*):\((\d+), (\d+)\):\s*(.*)/
          );
          if (match) {
            let [_full, kind, file, line, column, message] = match;
            // FIXME - check filename against current
            console.log("********", file, fileName);

            let lnum = Number(line);
            let cnum = Number(column);
            if (file !== fileName)
              lnum = cnum = 0;

            let start = new vscode.Position(lnum, cnum);
            // we don't have the full range, so grab the surrounding word
            let end = new vscode.Position(lnum, cnum + 1);
            let range =
              document.getWordRangeAtPosition(start) ??
              new vscode.Range(start, end);
            // heuristics to grab the entire message:
            // anything indented
            // Context:, or Goal: are part of PRINTME
            // unexpected / expecting appear in parse errors
            while (lines[i + 1]?.match(/^(  )/))
              message += "\n" + lines[++i];

            const severity =
              kind === "ERROR"
                ? vscode.DiagnosticSeverity.Error
                : vscode.DiagnosticSeverity.Information;
            const diag = new vscode.Diagnostic(range, message, severity);
            if (kind === "ERROR" || lnum > 0)
              diagnostics.push(diag);

          }
        }
        diagnosticCollection.set(vscode.Uri.file(fileName), diagnostics);
      }
    );
  }

  const runPiForall = vscode.commands.registerCommand(
    "newt-vscode.check",
    () => {
      const editor = vscode.window.activeTextEditor;
      if (editor) {
        const document = editor.document;
        if (document.fileName.endsWith(".newt"))
          checkDocument(document);

      }
    }
  );

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
          let uri = vscode.Uri.file(entry.fc.file);
          let start = new vscode.Position(entry.fc.line, entry.fc.col);
          let range = new vscode.Range(start, start);
          return new vscode.Location(uri, range);
        },
      }
    )
  );

  context.subscriptions.push(
    vscode.languages.registerHoverProvider(
      {language: 'newt'},
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
        }
      }
    )
  );

  context.subscriptions.push(runPiForall);

  vscode.workspace.onDidSaveTextDocument((document) => {
    if (document.fileName.endsWith(".newt"))
      vscode.commands.executeCommand("newt-vscode.check");

  });
  vscode.workspace.onDidOpenTextDocument((document) => {
    if (document.fileName.endsWith(".newt"))
      vscode.commands.executeCommand("newt-vscode.check");

  });
  for (let document of vscode.workspace.textDocuments)
    if (document.fileName.endsWith(".newt"))
      checkDocument(document);


  context.subscriptions.push(diagnosticCollection);
}

export function deactivate() {}
