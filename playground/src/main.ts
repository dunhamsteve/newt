import { effect, signal } from "@preact/signals";
import { newtConfig, newtTokens } from "./monarch.ts";
import * as monaco from "monaco-editor";
import { useEffect, useRef, useState } from "preact/hooks";
import { h, render, VNode } from "preact";
import { ChangeEvent } from "preact/compat";

monaco.languages.register({ id: "newt" });
monaco.languages.setMonarchTokensProvider("newt", newtTokens);
monaco.languages.setLanguageConfiguration("newt", newtConfig);

const newtWorker = new Worker("worker.js"); //new URL("worker.js", import.meta.url))

function run(src: string) {
  newtWorker.postMessage({ src });
}

newtWorker.onmessage = (ev) => {
  state.output.value = ev.data.output;
  state.javascript.value = ev.data.javascript;
};

self.MonacoEnvironment = {
  getWorkerUrl(moduleId, _label) {
    console.log("Get worker", moduleId);
    return moduleId;
  },
};

const state = {
  output: signal(""),
  javascript: signal(""),
  editor: signal<monaco.editor.IStandaloneCodeEditor | null>(null),
};

// I keep pressing this.
document.addEventListener("keydown", (ev) => {
  if (ev.metaKey && ev.code == "KeyS") ev.preventDefault();
});

let value = localStorage.code || "module Main\n";

// let result = document.getElementById("result")!;

// the editor might handle this itself with the right prodding.
effect(() => {
  let text = state.output.value;
  let editor = state.editor.value;
  if (editor) processOutput(editor, text);
});

interface EditorProps {
  initialValue: string;
}

function Editor({ initialValue }: EditorProps) {
  const ref = useRef<HTMLDivElement>(null);
  useEffect(() => {
    const container = ref.current!;
    const editor = monaco.editor.create(container, {
      value,
      language: "newt",
      theme: "vs",
      automaticLayout: true,
      minimap: { enabled: false },
    });
    state.editor.value = editor;

    editor.onDidChangeModelContent((ev) => {
      clearTimeout(timeout);
      timeout = setTimeout(() => {
        let value = editor.getValue();
        run(value);
        localStorage.code = value;
      }, 1000);
    });
    run(initialValue);
  }, []);

  return h("div", { id: "editor", ref });
}

// for extra credit, we could have a read-only monaco
function JavaScript() {
  const text = state.javascript.value;
  return h("div", { id: "javascript" }, text);
}

function Result() {
  const text = state.output.value;
  return h("div", { id: "result" }, text);
}

const RESULTS = "Output";
const JAVASCRIPT = "JS";

function Tabs() {
  const [selected, setSelected] = useState(RESULTS);

  const Tab = (label: string) => {
    let onClick = () => setSelected(label);
    let className = "tab";
    if (label == selected) className += " selected";
    return h("div", { className, onClick }, label);
  };

  let body;
  switch (selected) {
    case RESULTS:
      body = h(Result, {});
      break;
    case JAVASCRIPT:
      body = h(JavaScript, {});
      break;
    default:
      body = h("div", {});
  }

  return h(
    "div",
    { className: "tabPanel" },
    h("div", { className: "tabBar" }, Tab(RESULTS), Tab(JAVASCRIPT)),
    h("div", { className: "tabBody" }, body)
  );
}

const SAMPLES = [
  "Tree.newt",
  // "Prelude.newt",
  "Lib.newt",
  "Day1.newt",
  "Day2.newt",
  "TypeClass.newt",

];

function EditWrap() {
  const options = SAMPLES.map((value) => h("option", { value }, value));

  const onChange = async (ev: ChangeEvent) => {
    if (ev.target instanceof HTMLSelectElement) {
      let fn = ev.target.value;
      ev.target.value = "";
      if (fn) {
        const res = await fetch(fn);
        const text = await res.text();
        state.editor.value!.setValue(text);
      } else {
        state.editor.value!.setValue("module Main\n");
      }
    }
  };
  return h(
    "div",
    { className: "tabPanel" },
    h(
      "div",
      { className: "tabBar" },
      h(
        "select",
        { onChange },
        h("option", { value: "" }, "choose sample"),
        options
      )
    ),
    h("div", { className: "tabBody" }, h(Editor, { initialValue: value }))
  );
}

function App() {
  return h(
    "div",
    { className: "wrapper" },
    h(EditWrap, {}),
    h(Tabs, {})
  );
}

render(h(App, {}), document.getElementById("app")!);

let timeout: number | undefined;

// Adapted from the vscode extension, but types are slightly different
// and positions are 1-based.
const processOutput = (
  editor: monaco.editor.IStandaloneCodeEditor,
  output: string
) => {
  let model = editor.getModel()!;
  let markers: monaco.editor.IMarkerData[] = [];
  let lines = output.split("\n");
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    const match = line.match(/(INFO|ERROR) at \((\d+), (\d+)\):\s*(.*)/);
    if (match) {
      let [_full, kind, line, col, message] = match;
      let lineNumber = +line + 1;
      let column = +col + 1;
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
