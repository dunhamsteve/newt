import { newtConfig, newtTokens } from "./monarch.ts";
import * as monaco from "monaco-editor";

monaco.languages.register({ id: "newt" });
monaco.languages.setMonarchTokensProvider("newt", newtTokens);
monaco.languages.setLanguageConfiguration("newt", newtConfig);

const newtWorker = new Worker("worker.js")//new URL("worker.js", import.meta.url))

self.MonacoEnvironment = {
  getWorkerUrl(moduleId, label) {
    console.log("Get worker", moduleId);
    return moduleId;
  },
};

// I keep pressing this.
document.addEventListener('keydown', (ev) => {
  if (ev.metaKey && ev.code == 'KeyS') ev.preventDefault();
})

let value = localStorage.code || "module Main\n";

let container = document.getElementById("editor")!;
let result = document.getElementById("result")!;
const editor = monaco.editor.create(container, {
  value,
  language: "newt",
  theme: "vs",
  automaticLayout: true,
  minimap: { enabled: false },
});

let timeout: number | undefined;

function run(src: string) {
  newtWorker.postMessage({src})
}

newtWorker.onmessage = (ev) => {
  console.log('worker sent', ev.data)
  let {output, javascript} = ev.data
  processOutput(output);
}

// Adapted from the vscode extension, but types are slightly different
// and positions are 1-based.
const processOutput = (output: string) => {
  result.innerText = output

  let model = editor.getModel()!
  let markers: monaco.editor.IMarkerData[] = []
  let lines = output.split('\n')
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    const match = line.match(/(INFO|ERROR) at \((\d+), (\d+)\):\s*(.*)/);
    if (match) {
      let [_full, kind, line, col, message] = match;
      let lineNumber = +line+1
      let column = +col+1;
      let start = {column, lineNumber};
      // we don't have the full range, so grab the surrounding word
      let endColumn = column + 1
      let word = model.getWordAtPosition(start)
      if (word) endColumn = word.endColumn

      // heuristics to grab the entire message:
      // anything indented
      // Context:, or Goal: are part of PRINTME
      // unexpected / expecting appear in parse errors
      while (
        lines[i + 1]?.match(/^(  )/)
      ) {
        message += "\n" + lines[++i];
      }
      const severity = kind === 'ERROR' ? monaco.MarkerSeverity.Error : monaco.MarkerSeverity.Info

      markers.push({
        severity,
        message,
        startLineNumber: lineNumber,
        endLineNumber: lineNumber,
        startColumn: column,
        endColumn,
      })
    }
  }
  console.log('setMarkers', markers)
  monaco.editor.setModelMarkers(model, 'newt', markers)
}

editor.onDidChangeModelContent((ev) => {
  console.log("mc", ev);
  let value = editor.getValue();
  clearTimeout(timeout);
  timeout = setTimeout(() => run(value), 1000);
  localStorage.code = value;
});

run(value);
