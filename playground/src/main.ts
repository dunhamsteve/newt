import { effect, signal } from "@preact/signals";
import { newtConfig, newtTokens } from "./monarch.ts";
import * as monaco from "monaco-editor";
import { useEffect, useRef, useState } from "preact/hooks";
import { h, render } from "preact";
import { ChangeEvent } from "preact/compat";
import { archive, preload } from "./preload.ts";
import { CompileReq, CompileRes, Message } from "./types.ts";

// editor.(createModel / setModel / getModels) to switch files

// TODO - remember files and allow switching?

// static zip filesystem with user changes overlaid via localStorage
// download individual files (we could use the cheap compression from the pdflib or no compression to make zip download)
// would need way to reset/delete

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

let topData: undefined | TopData;

// we need to fix the definition of word
monaco.languages.register({ id: "newt" });
monaco.languages.setMonarchTokensProvider("newt", newtTokens);
monaco.languages.setLanguageConfiguration("newt", newtConfig);
monaco.languages.registerDefinitionProvider("newt", {
  provideDefinition(model, position, token) {
    if (!topData) return;
    // HACK - we don't know our filename which was generated from `module` decl, so
    // assume the last context entry is in our file.
    let last = topData.context[topData.context.length - 1];
    let file = last.fc.file;

    const info = model.getWordAtPosition(position);
    if (!info) return;
    let entry = topData.context.find((entry) => entry.name === info.word);
    // we can't switch files at the moment
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
    if (!topData) return;
    const info = model.getWordAtPosition(position);
    if (!info) return;
    let entry = topData.context.find((entry) => entry.name === info.word);
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
const newtWorker = new Worker("worker.js");
let postMessage = (msg: CompileReq) => newtWorker.postMessage(msg);

// Safari/MobileSafari have small stacks in webworkers.
if (navigator.vendor.includes("Apple")) {
  const workerFrame = document.createElement("iframe");
  workerFrame.src = "worker.html";
  workerFrame.style.display = "none";
  document.body.appendChild(workerFrame);
  postMessage = (msg: any) => workerFrame.contentWindow?.postMessage(msg, "*");
}

// iframe for running newt output
const iframe = document.createElement("iframe");
iframe.src = "frame.html";
iframe.style.display = "none";
document.body.appendChild(iframe);

function run(src: string) {
  console.log("SEND TO", iframe.contentWindow);
  const fileName = state.currentFile.value;
  postMessage({ type: "compileRequest", fileName, src });
}

function runOutput() {
  const src = state.javascript.value;
  console.log("RUN", iframe.contentWindow);
  try {
    iframe.contentWindow?.postMessage({ type: "exec", src }, "*");
  } catch (e) {
    console.error(e);
  }
}

function setOutput(output: string) {
  let lines = output.split("\n");
  output = lines.filter((l) => !l.startsWith("TOP:")).join("\n");
  let data = lines.find((l) => l.startsWith("TOP:"));
  if (data) {
    try {
      topData = JSON.parse(data.slice(4));
      console.log({ topData });
    } catch (e) {
      console.error(e);
    }
  } else {
    topData = undefined;
  }
  state.output.value = output;
}

window.onmessage = (ev: MessageEvent<Message>) => {
  console.log("window got", ev.data);
  if ("messages" in ev.data) state.messages.value = ev.data.messages;
  if ("message" in ev.data) {
    state.messages.value = [...state.messages.value, ev.data.message];
  }
  // safari callback
  if ("output" in ev.data) {
    setOutput(ev.data.output);
    state.javascript.value = ev.data.javascript;
  }
};

newtWorker.onmessage = (ev: MessageEvent<CompileRes>) => {
  setOutput(ev.data.output);
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
  dark: signal(false),
  files: signal<string[]>(["Tour.newt"]),
  currentFile: signal<string>(localStorage.currentFile ?? "Tour.newt"),
};

// Monitor dark mode state (TODO - let user override system setting)
if (window.matchMedia) {
  function checkDark(ev: { matches: boolean }) {
    console.log("CHANGE", ev);
    if (ev.matches) {
      monaco.editor.setTheme("vs-dark");
      document.body.className = "dark";
      state.dark.value = true;
    } else {
      monaco.editor.setTheme("vs");
      document.body.className = "light";
      state.dark.value = false;
    }
  }
  let query = window.matchMedia("(prefers-color-scheme: dark)");
  query.addEventListener("change", checkDark);
  checkDark(query);
}

async function loadFile(fn: string) {
  await preload;
  let data = archive?.getData(fn);
  if (data) {
    let text = new TextDecoder().decode(data);
    state.editor.value!.setValue(text);
  } else {
    state.editor.value!.setValue("module Main\n\n-- File not found\n");
  }
  state.currentFile.value = fn;
  localStorage.currentFile = fn;
}

// I keep pressing this.
document.addEventListener("keydown", (ev) => {
  if (ev.metaKey && ev.code == "KeyS") ev.preventDefault();
});

const LOADING = "module Loading\n";

let value = localStorage.code || LOADING;
let initialVertical = localStorage.vertical == "true";

// the editor might handle this itself with the right prodding.
effect(() => {
  let text = state.output.value;
  let editor = state.editor.value;
  if (editor) processOutput(editor, text);
});

interface EditorProps {
  initialValue: string;
}

const ABBREV: Record<string, string> = {
    '\\x': '×',
    '\\r': '→',
    '\\all': '∀',
    '\\\\': '\\',
    '\\==': '≡',
    '\\circ': '∘',
    '\\1': '₁',
    '\\2': '₂',
  }

function Editor({ initialValue }: EditorProps) {
  const ref = useRef<HTMLDivElement>(null);
  useEffect(() => {
    const container = ref.current!;
    const editor = monaco.editor.create(container, {
      value,
      language: "newt",
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
      let last = ev.changes[ev.changes.length - 1];
      const model = editor.getModel();
      // figure out heuristics here, what chars do we want to trigger?
      // the lean one will only be active if it sees you type \
      // and bail if it decides you've gone elsewhere
      // it maintains an underline annotation, too.
      if (model && last.text && " ')\\".includes(last.text)) {
        console.log('LAST', last)
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
    if (initialValue === LOADING) loadFile("Tour.newt");
    else run(initialValue);
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
  const messages = state.messages.value ?? [];
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
      localStorage.tab = label;
    };
    let className = "tab";
    if (label == selected) className += " selected";
    return h("div", { className, onClick }, label);
  };

  useEffect(() => {
    if (state.messages.value.length) setSelected(CONSOLE);
  }, [state.messages.value]);

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
    h(
      "div",
      { className: "tabBar" },
      Tab(RESULTS),
      Tab(JAVASCRIPT),
      Tab(CONSOLE)
    ),
    h("div", { className: "tabBody" }, body)
  );
}

preload.then(() => {
  if (archive) {
    let files = [];
    for (let name in archive.entries) {
      if (name.endsWith(".newt")) files.push(name);
    }
    files.sort();
    state.files.value = files;
  }
});

function EditWrap({
  vertical,
  toggle,
}: {
  vertical: boolean;
  toggle: () => void;
}) {
  // const [file, setFile] = useState("Tour.newt");
  const options = state.files.value.map((value) =>
    h("option", { value }, value)
  );

  const selectFile = async (ev: ChangeEvent) => {
    if (ev.target instanceof HTMLSelectElement) {
      let fn = ev.target.value;
      ev.target.value = "";
      loadFile(fn);
    }
  };
  let d = vertical
    ? "M0 0 h20 v20 h-20 z M0 10 h20"
    : "M0 0 h20 v20 h-20 z M10 0 v20";
  let play = "M0 0 L20 10 L0 20 z";
  let svg = (d: string) =>
    h("svg", { width: 20, height: 20, className: "icon" }, h("path", { d }));
  return h(
    "div",
    { className: "tabPanel left" },
    h(
      "div",
      { className: "tabBar" },
      h(
        "select",
        { onChange: selectFile, value: state.currentFile.value },
        options
      ),
      h("div", { style: { flex: "1 1" } }),
      h("button", { onClick: runOutput }, svg(play)),
      h("button", { onClick: toggle }, svg(d))
    ),
    h("div", { className: "tabBody" }, h(Editor, { initialValue: value }))
  );
}

function App() {
  let [vertical, setVertical] = useState(initialVertical);
  let toggle = () => {
    setVertical(!vertical);
    localStorage.vertical = !vertical;
  };
  let className = `wrapper ${vertical ? "vertical" : "horizontal"}`;
  return h(
    "div",
    { className },
    h(EditWrap, { vertical, toggle }),
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
