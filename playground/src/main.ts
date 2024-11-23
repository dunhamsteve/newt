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
const iframe = document.createElement("iframe");
iframe.src = "frame.html";
iframe.style.display = "none";
document.body.appendChild(iframe);

function run(src: string) {
  newtWorker.postMessage({ src });
}

function runOutput() {
  const src = state.javascript.value
  console.log("RUN", iframe.contentWindow);
  try {
    iframe.contentWindow?.postMessage({ cmd: "exec", src }, "*");
  } catch (e) {
    console.error(e);
  }
}

window.onmessage = (ev) => {
  console.log("window got", ev.data);
  if (ev.data.messages)
    state.messages.value = ev.data.messages;
};

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
  messages: signal<string[]>([]),
  editor: signal<monaco.editor.IStandaloneCodeEditor | null>(null),
};

async function loadFile(fn: string) {
  if (fn) {
    const res = await fetch(fn);
    const text = await res.text();
    state.editor.value!.setValue(text);
  } else {
    state.editor.value!.setValue("module Main\n");
  }
}

// I keep pressing this.
document.addEventListener("keydown", (ev) => {
  if (ev.metaKey && ev.code == "KeyS") ev.preventDefault();
});

const LOADING = "module Loading\n"

let value = localStorage.code || LOADING;
let initialVertical = localStorage.vertical == 'true'

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
      fontFamily: "Comic Code, Menlo, Monaco, Courier New, sans",
      automaticLayout: true,
      acceptSuggestionOnEnter: "off",
      unicodeHighlight: { ambiguousCharacters: false },
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
    if (initialValue === LOADING)
      loadFile("Tour.newt")
    else
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

function Console() {
  const messages = state.messages.value ?? []
  return h(
    "div",
    { id: "console" },
    messages.map((msg) => h("div", { className: "message" }, msg))
  );
}

const RESULTS = "Output";
const JAVASCRIPT = "JS";
const CONSOLE = "Console";

function Tabs() {
  const [selected, setSelected] = useState(localStorage.tab ?? RESULTS);
  const Tab = (label: string) => {
    let onClick = () => {
      setSelected(label);
      localStorage.tab = label
    }
    let className = "tab";
    if (label == selected) className += " selected";
    return h("div", { className, onClick }, label);
  };

  useEffect(() => {
    if (state.messages.value) setSelected(CONSOLE)
  }, [state.messages.value])

  let body;
  switch (selected) {
    case RESULTS:
      body = h(Result, {});
      break;
    case JAVASCRIPT:
      body = h(JavaScript, {});
      break;
    case CONSOLE:
      body = h(Console, {});
      break;
    default:
      body = h("div", {});
  }

  return h(
    "div",
    { className: "tabPanel right" },
    h("div", { className: "tabBar" }, Tab(RESULTS), Tab(JAVASCRIPT), Tab(CONSOLE)),
    h("div", { className: "tabBody" }, body)
  );
}

const SAMPLES = [
  "Tour.newt",
  "Hello.newt",
  "DSL.newt",
  "Tree.newt",
  "Reasoning.newt",
  "Lists.newt",
  "Day1.newt",
  "Day2.newt",
  "Lib.newt",
  "TypeClass.newt",
  "Combinatory.newt",
];

function EditWrap({vertical, toggle}: {vertical: boolean, toggle: () => void}) {
  const options = SAMPLES.map((value) => h("option", { value }, value));

  const onChange = async (ev: ChangeEvent) => {
    if (ev.target instanceof HTMLSelectElement) {
      let fn = ev.target.value;
      ev.target.value = "";
      loadFile(fn)

    }
  };
  let d = vertical ?  "M0 0 h20 v20 h-20 z M0 10 h20" : "M0 0 h20 v20 h-20 z M10 0 v20"
  return h(
    "div",
    { className: "tabPanel left" },
    h(
      "div",
      { className: "tabBar" },
      h(
        "select",
        { onChange },
        h("option", { value: "" }, "choose sample"),
        options
      ),
      h("div", { style: { flex: "1 1" } }),
      h("button", { onClick: runOutput
       }, "⏵"),
      h(
        "button",
        { onClick: toggle },
        h(
          "svg",
          { width: 20, height: 20 },
          h("path", { d, fill: "none", stroke: "black" })
        )
      )
    ),
    h("div", { className: "tabBody" }, h(Editor, { initialValue: value }))
  );
}

function App() {
  let [vertical,setVertical] = useState(initialVertical)
  let toggle = () => {
    setVertical(!vertical)
    localStorage.vertical = !vertical
  }
  let className = `wrapper ${vertical?"vertical":"horizontal"}`
  return h(
    "div",
    { className },
    h(EditWrap, {vertical, toggle}),
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
