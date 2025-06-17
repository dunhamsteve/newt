import { ABBREV } from "./abbrev.ts";
import { newtConfig, newtTokens } from "./monarch.ts";
import * as monaco from "monaco-editor";
import { AbstractEditor, EditorDelegate, Marker } from "./types.ts";

// we need to fix the definition of word
monaco.languages.register({ id: "newt" });
monaco.languages.setMonarchTokensProvider("newt", newtTokens);
monaco.languages.setLanguageConfiguration("newt", newtConfig);

self.MonacoEnvironment = {
  getWorkerUrl(moduleId, _label) {
    console.log("Get worker", moduleId);
    return moduleId;
  },
};

export class MonacoEditor implements AbstractEditor {
  editor: monaco.editor.IStandaloneCodeEditor;
  delegate: EditorDelegate;

  constructor(container: HTMLElement, value: string, language: EditorDelegate) {
    this.delegate = language;
    let editor = (this.editor = monaco.editor.create(container, {
      value,
      language: "newt",
      fontFamily: "Comic Code, Menlo, Monaco, Courier New, sans",
      automaticLayout: true,
      acceptSuggestionOnEnter: "off",
      unicodeHighlight: { ambiguousCharacters: false },
      minimap: { enabled: false },
    }));
    monaco.languages.registerDefinitionProvider("newt", {
      provideDefinition(model, position, token) {
        const info = model.getWordAtPosition(position);
        if (!info) return;
        let entry = language.getEntry(
          info.word,
          position.lineNumber,
          info.startColumn
        );
        if (!entry) return;

        // HACK - we don't know our filename which was generated from `module` decl, so
        // assume the last context entry is in our file.

        let file = language.getFileName();
        if (!entry || entry.fc.file !== file) return;
        let lineNumber = entry.fc.line + 1;
        let column = entry.fc.col + 1;
        let word = model.getWordAtPosition({ lineNumber, column });
        let range = new monaco.Range(lineNumber, column, lineNumber, column);
        if (word) {
          range = new monaco.Range(
            lineNumber,
            word.startColumn,
            lineNumber,
            word.endColumn
          );
        }
        return { uri: model.uri, range };
      },
    });
    monaco.languages.registerHoverProvider("newt", {
      provideHover(model, position, token, context) {
        const info = model.getWordAtPosition(position);
        if (!info) return;
        let entry = language.getEntry(
          info.word,
          position.lineNumber,
          info.startColumn
        );
        if (!entry) return;
        return {
          range: new monaco.Range(
            position.lineNumber,
            info.startColumn,
            position.lineNumber,
            info.endColumn
          ),
          contents: [{ value: `${entry.name} : ${entry.type}` }],
        };
      },
    });
    editor.onDidChangeModelContent((ev) => {
      this.delegate.onChange(editor.getValue());

      let last = ev.changes[ev.changes.length - 1];
      const model = editor.getModel();
      // figure out heuristics here, what chars do we want to trigger?
      // the lean one will only be active if it sees you type \
      // and bail if it decides you've gone elsewhere
      // it maintains an underline annotation, too.
      if (model && last.text && " ')\\".includes(last.text)) {
        console.log("LAST", last);
        let { startLineNumber, startColumn } = last.range;
        const text = model.getValueInRange(
          new monaco.Range(
            startLineNumber,
            Math.max(1, startColumn - 10),
            startLineNumber,
            startColumn
          )
        );
        const m = text.match(/(\\[^ ]+)$/);
        if (m) {
          let cand = m[0];
          console.log("GOT", cand);
          let text = ABBREV[cand];
          if (text) {
            const range = new monaco.Range(
              startLineNumber,
              startColumn - cand.length,
              startLineNumber,
              startColumn
            );
            editor.executeEdits("replaceSequence", [{ range, text: text }]);
          }
        }
      }
    });
  }
  setValue(value: string) {
    this.editor.setValue(value);
  }
  getValue() {
    return this.editor.getValue();
  }
  setMarkers(markers: Marker[]) {
    let model = this.editor.getModel()!;
    const mapMarker = (marker: Marker): monaco.editor.IMarkerData => {
      let severity =
        marker.severity === "ERROR"
          ? monaco.MarkerSeverity.Error
          : monaco.MarkerSeverity.Info;
      // translate to surrounding word
      // FIXME - we have `getWord` in monaco, but probably belongs to the delegate
      // and eventually we have better FC
      let { message, startColumn, endColumn, startLineNumber, endLineNumber } =
        marker;
      let word = model.getWordAtPosition({
        column: startColumn,
        lineNumber: startLineNumber,
      });
      if (word) endColumn = word.endColumn;
      return {
        message,
        startColumn,
        endColumn,
        startLineNumber,
        endLineNumber,
        severity,
      };
    };
    monaco.editor.setModelMarkers(model, "newt", markers.map(mapMarker));
  }
}

// scratch
const processOutput = (
  editor: monaco.editor.IStandaloneCodeEditor,
  output: string
) => {
  let model = editor.getModel()!;
  let markers: monaco.editor.IMarkerData[] = [];
  let lines = output.split("\n");
  let m = lines[0].match(/.*Process (.*)/);
  let fn = "";
  if (m) fn = m[1];
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    const match = line.match(/(INFO|ERROR) at (.*):\((\d+), (\d+)\):\s*(.*)/);
    if (match) {
      let [_full, kind, file, line, col, message] = match;
      let lineNumber = +line + 1;
      let column = +col + 1;
      // FIXME - pass the real path in
      if (fn && fn !== file) {
        lineNumber = column = 0;
      }
      let start = { column, lineNumber };
      // we don't have the full range, so grab the surrounding word
      let endColumn = column + 1;
      let word = model.getWordAtPosition(start);
      if (word) endColumn = word.endColumn;

      // heuristics to grab the entire message:
      // anything indented
      // Context:, or Goal: are part of PRINTME
      // unexpected / expecting appear in parse errors
      while (lines[i + 1]?.match(/^(  )/)) {
        message += "\n" + lines[++i];
      }
      const severity =
        kind === "ERROR"
          ? monaco.MarkerSeverity.Error
          : monaco.MarkerSeverity.Info;
      if (kind === "ERROR" || lineNumber)
        markers.push({
          severity,
          message,
          startLineNumber: lineNumber,
          endLineNumber: lineNumber,
          startColumn: column,
          endColumn,
        });
    }
  }
  monaco.editor.setModelMarkers(model, "newt", markers);
};
