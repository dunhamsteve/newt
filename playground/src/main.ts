import { effect, signal } from "@preact/signals";
import { Diagnostic } from "@codemirror/lint";
import { useEffect, useRef, useState } from "preact/hooks";
import { h, render, VNode } from "preact";
import { ChangeEvent } from "preact/compat";
import { archive, preload } from "./preload.ts";
import { b64decode, b64encode } from "./base64";
import {
  AbstractEditor,
  EditorDelegate,
  TopData,
  Marker,
} from "./types.ts";
import { CMEditor } from "./cmeditor.ts";
import { deflate } from "./deflate.ts";
import { inflate } from "./inflate.ts";
import { IPC } from "./ipc.ts";

let topData: undefined | TopData;

const ipc = new IPC();

function mdline2nodes(s: string) {
  let cs: (VNode|string)[] = []
  let toks = s.matchAll(/(\*\*.*?\*\*)|(\*.*?\*)|(_.*?_)|[^*]+|\*/g)
  for (let tok of toks) {
    if (tok[1]) cs.push(h('b',{},tok[0].slice(2,-2)))
    else if (tok[2]) cs.push(h('em',{},tok[0].slice(1,-1)))
    else if (tok[3]) cs.push(h('em',{},tok[0].slice(1,-1)))
    else cs.push(tok[0])
  }
  return cs
}

function md2nodes(md: string)  {
  let rval: VNode[] = []
  let list: VNode[] | undefined
  for (let line of md.split("\n")) {
    if (line.startsWith('- ')) {
      list = list ?? []
      list.push(h('li', {}, mdline2nodes(line.slice(2))))
      continue
    }
    if (list) {
      rval.push(h('ul', {}, list))
      list = undefined
    }
    if (line.startsWith('# ')) {
      rval.push(h('h2', {}, mdline2nodes(line.slice(2))))
    } else if (line.startsWith('## ')) {
      rval.push(h('h3', {}, mdline2nodes(line.slice(3))))
    } else {
      rval.push(h('div', {}, mdline2nodes(line)))
    }
  }
  return rval
}

// iframe for running newt output
const iframe = document.createElement("iframe");
iframe.src = "frame.html";
iframe.style.display = "none";
document.body.appendChild(iframe);

async function refreshJS() {
if (!state.javascript.value) {
    let src = state.editor.value!.getValue();
    console.log("SEND TO", iframe.contentWindow);
    const fileName = state.currentFile.value;
    // maybe send fileName, src?
    await ipc.sendMessage("save", [fileName, src]);
    let js = await ipc.sendMessage("compile", [fileName]);
    state.javascript.value = js;
  }
}

async function runOutput() {
  await refreshJS()
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

window.addEventListener("message", (ev) => {
  if (ev.data.id) return;
  console.log("window got", ev.data);
  if ("messages" in ev.data) state.messages.value = ev.data.messages;
  if ("message" in ev.data) {
    state.messages.value = [...state.messages.value, ev.data.message];
  }
});

async function copyToClipboard(ev: Event) {
ev.preventDefault();
    let src = state.editor.value!.getValue();
    let hash = `#code/${b64encode(deflate(new TextEncoder().encode(src)))}`;
    window.location.hash = hash;
    await navigator.clipboard.writeText(window.location.href);
    state.toast.value = "URL copied to clipboard";
    setTimeout(() => (state.toast.value = ""), 2_000);
}

// We could push this into the editor
document.addEventListener("keydown", (ev) => {
  if ((ev.metaKey || ev.ctrlKey) && ev.code == "KeyS")
    copyToClipboard(ev);
});

function getSavedCode() {
  let value: string = localStorage.idrisCode || LOADING;
  let hash = window.location.hash;
  if (hash.startsWith("#code/")) {
    try {
      value = new TextDecoder().decode(inflate(b64decode(hash.slice(6))));
    } catch (e) {
      console.error(e);
    }
  }
  return value;
}

const state = {
  output: signal(""),
  toast: signal(""),
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

let value = getSavedCode() || LOADING;
let initialVertical = localStorage.vertical == "true";

interface EditorProps {
  initialValue: string;
}
const language: EditorDelegate = {
  getEntry(word, _row, _col) {
    return topData?.context.find((entry) => entry.name === word);
  },
  onChange(_value) {
    // we're using lint() now
  },
  getFileName() {
    if (!topData) return "";
    let last = topData.context[topData.context.length - 1];
    return last.fc.file;
  },
  async lint(view) {
    console.log("LINT");
    let src = view.state.doc.toString();
    localStorage.code = src;
    let module = src.match(/module\s+([^\s]+)/)?.[1];
    if (module) {
      // This causes problems with stuff like aoc/...
      state.currentFile.value = module.replace(".", "/") + ".newt";
    }
    state.javascript.value = ''
    let fileName = state.currentFile.value;
    console.log("FN", fileName);
    try {
      await ipc.sendMessage("save", [fileName, src]);
      let out = await ipc.sendMessage("typeCheck", [fileName]);
      setOutput(out);
      let markers = processOutput(out);
      let diags: Diagnostic[] = [];
      for (let marker of markers) {
        let col = marker.startColumn;

        let line = view.state.doc.line(marker.startLineNumber);
        const pos = line.from + col - 1;
        let word = view.state.wordAt(pos);
        diags.push({
          from: word?.from ?? pos,
          to: word?.to ?? pos + 1,
          severity: marker.severity,
          message: marker.message,
        });
      }
      return diags;
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

function Help() {
  return h("div", { id: "help" },
    md2nodes(`
# Newt Playground

The editor will typecheck the file with newt and render errors as the file is changed. The current file is saved to localStorage and will be restored if there is no data in the URL. Cmd-s / Ctrl-s will create a url embedding the file contents. There is a layout toggle for phone use.

## Tabs

**Output** - Displays the compiler output, which is also used to render errors and info annotations in the editor.

**JS** - Displays the javascript translation of the file

**Console** - Displays the console output from running the javascript

**Help** - Displays this help file

## Buttons

▶ Compile and run the current file in an iframe, console output is collected to the console tab.

📋 Embed the current file in the URL and copy to clipboard

↕ or ↔ Toggle vertical or horziontal layout (for mobile)

## Keyboard

*C-s or M-s* - Embed the current file in the URL and copy to clipboard
`)
  )
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
const HELP = "Help";

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

  useEffect(() => {
    if (selected === JAVASCRIPT && !state.javascript.value) refreshJS();
  }, [selected, state.javascript.value]);

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
    case HELP:
      body = h(Help, {});
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
      Tab(CONSOLE),
      Tab(HELP),
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

  const char = vertical ? "↕" : "↔"

  // let d = vertical
  //   ? "M0 0 h20 v20 h-20 z M0 10 h20"
  //   : "M0 0 h20 v20 h-20 z M10 0 v20";
  // let play = "M0 0 L20 10 L0 20 z";
  // let svg = (d: string) =>
  //   h("svg", { width: 20, height: 20, className: "icon" }, h("path", { d }));
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
      h("button", { onClick: copyToClipboard, title: "copy url" }, "📋"),
      h("button", { onClick: runOutput, title: "run program" }, "▶"),
      h("button", { onClick: toggle, title: "change layout" }, char),
      // h("button", { onClick: toggle }, svg(d))
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
  let toast;
  if (state.toast.value) {
    toast = h("p", { className: "toast" }, h("div", {}, state.toast.value));
  }
  let className = `wrapper ${vertical ? "vertical" : "horizontal"}`;
  return h(
    "div",
    { className },
    toast,
    h(EditWrap, { vertical, toggle }),
    h(Tabs, {})
  );
}

render(h(App, {}), document.getElementById("app")!);

const processOutput = (
  output: string
) => {
  console.log("process output", output);
  let markers: Marker[] = [];
  let lines = output.split("\n");
  let m = lines[0].match(/.*Process (.*)/);
  let fn = "";
  if (m) fn = m[1];
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    const match = line.match(
      /(INFO|ERROR) at ([^:]+):\((\d+), (\d+)\):\s*(.*)/
    );
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
          severity: kind === "ERROR" ? "error" : "info",
          message,
          startLineNumber: lineNumber,
          endLineNumber: lineNumber,
          startColumn: column,
          endColumn,
        });
    }
  }
  console.log("markers", markers);
  // editor.setMarkers(markers)
  return markers;
};
