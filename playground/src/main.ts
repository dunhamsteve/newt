import { effect, signal } from "@preact/signals";
import { Diagnostic } from "@codemirror/lint";
import { useEffect, useRef, useState } from "preact/hooks";
import { h, render } from "preact";
import { ChangeEvent } from "preact/compat";
import { archive, preload } from "./preload.ts";
import {
  AbstractEditor,
  EditorDelegate,
  CompileReq,
  CompileRes,
  Message,
  TopData,
  Marker,
} from "./types.ts";
import { CMEditor } from "./cmeditor.ts";

let topData: undefined | TopData;

const newtWorker = new Worker("worker.js");
// :FIXME use because Safari
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
  // postMessage({ type: "compileRequest", fileName, src });
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

let lastID = 0;
const nextID = () => "" + lastID++;

window.onmessage = (ev: MessageEvent<Message>) => {
  console.log("window got", ev.data);
  if ("messages" in ev.data) state.messages.value = ev.data.messages;
  if ("message" in ev.data) {
    state.messages.value = [...state.messages.value, ev.data.message];
  }
  // safari callback
  if ("output" in ev.data) {
    newtWorker.onmessage?.(ev)
    setOutput(ev.data.output);
    state.javascript.value = ev.data.javascript;
  }
};

// TODO wrap up IPC

type Suspense<T> = {
  resolve: (value: T | PromiseLike<T>) => void;
  reject: (reason?: any) => void;
};

const callbacks: Record<string, Suspense<string>> = {};

newtWorker.onmessage = (ev: MessageEvent<CompileRes>) => {
  let suspense = callbacks[ev.data.id];
  if (suspense) {
    suspense.resolve(ev.data.output);
    delete callbacks[ev.data.id];
  }
  console.log('result', ev.data, 'suspense', suspense)
  // FIXME - we want to have the callback take a response for its command
  setOutput(ev.data.output);
  state.javascript.value = ev.data.javascript;
};

function runCommand(req: CompileReq) {
  return new Promise<string>(
    (resolve, reject) => {
      callbacks[req.id] = { resolve, reject }
      postMessage(req);
    }
  );
}

const state = {
  output: signal(""),
  javascript: signal(""),
  messages: signal<string[]>([]),
  editor: signal<AbstractEditor | null>(null),
  dark: signal(false),
  files: signal<string[]>(["Tour.newt"]),
  currentFile: signal<string>(localStorage.currentFile ?? "Tour.newt"),
};

// Monitor dark mode state (TODO - let user override system setting)
if (window.matchMedia) {
  function checkDark(ev: { matches: boolean }) {
    console.log("CHANGE", ev);
    if (ev.matches) {
      // monaco.editor.setTheme("vs-dark");
      document.body.className = "dark";
      state.dark.value = true;
      state.editor.value?.setDark(true);
    } else {
      // monaco.editor.setTheme("vs");
      document.body.className = "light";
      state.dark.value = false;
      state.editor.value?.setDark(false);
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
  // TODO - abstract this for both editors
  // if (editor) processOutput(editor, text);
});

interface EditorProps {
  initialValue: string;
}
const language: EditorDelegate = {
  getEntry(word, _row, _col) {
    return topData?.context.find((entry) => entry.name === word);
  },
  onChange(value) {
    // clearTimeout(timeout);
    //   timeout = setTimeout(() => {
    //     run(value);
    //     localStorage.code = value;
    //   }, 1000);
  },
  getFileName() {
    if (!topData) return "";
    let last = topData.context[topData.context.length - 1];
    return last.fc.file;
  },
  async lint(view) {
    console.log("LINT");
    let src = view.state.doc.toString();
    const fileName = state.currentFile.value;
    console.log("FN", fileName);
    // console.log("SRC", src);
    try {
      let out = await runCommand({
        id: nextID(),
        type: "compileRequest",
        fileName,
        src,
      });
      console.log("OUT", out);
      let markers = processOutput(out);
      let diags: Diagnostic[] = []
      for (let marker of markers) {
        let col = marker.startColumn

        let line = view.state.doc.line(marker.startLineNumber)
        const pos = line.from + col - 1;
        let word = view.state.wordAt(pos)
        diags.push({
          from: word?.from ?? pos,
          to: word?.to ?? pos+1,
          severity: marker.severity,
          message: marker.message,
        })
      }
      return diags
    } catch (e) {
      console.log("ERR", e);
    }

    return [];
  },
};

function Editor({ initialValue }: EditorProps) {
  const ref = useRef<HTMLDivElement>(null);

  useEffect(() => {
    const container = ref.current!;
    const editor = new CMEditor(container, value, language);
    // const editor = new MonacoEditor(container, value, language)
    state.editor.value = editor;
    editor.setDark(state.dark.value);
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
  // editor: AbstractEditor,
  output: string
) => {
  // let model = editor.getModel()!;
  console.log('process output', output)
  let markers: Marker[] = [];
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
      // we don't have the full range, so grab the surrounding word
      let endColumn = column + 1;

      // heuristics to grab the entire message:
      // anything indented
      // Context:, or Goal: are part of PRINTME
      // unexpected / expecting appear in parse errors
      while (lines[i + 1]?.match(/^(  )/)) {
        message += "\n" + lines[++i];
      }
      if (kind === "ERROR" || lineNumber)
        markers.push({
          severity: kind === 'ERROR' ? 'error' : 'info',
          message,
          startLineNumber: lineNumber,
          endLineNumber: lineNumber,
          startColumn: column,
          endColumn,
        });
    }
  }
  console.log('markers', markers)
  // editor.setMarkers(markers)
  return markers;
};
