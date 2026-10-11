import { signal } from "@preact/signals";
import { Diagnostic } from "@codemirror/lint";
import { useEffect, useRef } from "preact/hooks";
import { h, render, TargetedEvent, VNode } from "preact";
import { archive, preload } from "./preload.ts";
import { b64decode, b64encode } from "./base64";
import { AbstractEditor, EditorDelegate, TopData } from "./types.ts";
import { CMEditor, scheme } from "./cmeditor.ts";
import { deflate } from "./deflate.ts";
import { inflate } from "./inflate.ts";
import { IPC, Range, Position, Diagnostic as Diag } from "./ipc.ts";
import helpText from "./help.md?raw";
import { basicSetup, EditorView } from "codemirror";
import { Compartment, EditorState } from "@codemirror/state";
import { javascript } from "@codemirror/lang-javascript";
import { oneDark } from "@codemirror/theme-one-dark";

let topData: undefined | TopData;

const ipc = new IPC();

// TODO double check the last two are right
const SEVERITY: Diagnostic["severity"][] = [
  "error",
  "error",
  "warning",
  "info",
  "hint",
];

function mdline2nodes(s: string) {
  let cs: (VNode<any> | string)[] = [];
  let toks = s.matchAll(
    /\*\*(.*?)\*\*|\*(.*?)\*|_(.*?)_|!\[(.*?)\]\((.*?)\)|:(\w+):|[^*]+|\*/g,
  );
  for (let tok of toks) {
    // oxlint-disable-next-line no-unused-expressions
    (tok[1] && cs.push(h("b", {}, tok[1]))) ||
      (tok[2] && cs.push(h("em", {}, tok[2]))) ||
      (tok[3] && cs.push(h("em", {}, tok[0].slice(1, -1)))) ||
      (tok[5] && cs.push(h("img", { src: tok[5], alt: tok[4] }))) ||
      (tok[6] && cs.push(h(Icon, { name: tok[6] }))) ||
      cs.push(tok[0]);
  }
  return cs;
}

function bundle(js: string) {
  js = js.replace(/^import.*\n/g, "");
  js = js.replace(/\nexport /g, "\n");
  return js;
}

function md2nodes(md: string) {
  let rval: VNode[] = [];
  let list: VNode[] | undefined;
  for (let line of md.split("\n")) {
    if (line.startsWith("- ")) {
      if (!list) {
        list = [];
        rval.push(h("ul", {}, list));
      }
      list.push(h("li", {}, mdline2nodes(line.slice(2))));
      continue;
    }
    list = undefined;
    if (line.startsWith("# ")) {
      rval.push(h("h2", {}, mdline2nodes(line.slice(2))));
    } else if (line.startsWith("## ")) {
      rval.push(h("h3", {}, mdline2nodes(line.slice(3))));
    } else {
      rval.push(h("div", {}, mdline2nodes(line)));
    }
  }
  return rval;
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
    await ipc.sendMessage("updateFile", [fileName, src]);
    let js = await ipc.sendMessage("compile", [fileName, "javascript"]);
    state.javascript.value = bundle(js);
  }
}

async function refreshScheme() {
  if (!state.scheme.value) {
    let src = state.editor.value!.getValue();
    console.log("SEND TO", iframe.contentWindow);
    const fileName = state.currentFile.value;
    // maybe send fileName, src?
    await ipc.sendMessage("updateFile", [fileName, src]);
    let scheme = await ipc.sendMessage("compile", [fileName, "scheme"]);
    state.scheme.value = scheme;
  }
}

async function runOutput() {
  await refreshJS();
  const src = state.javascript.value;
  console.log("RUN", iframe.contentWindow);
  try {
    iframe.contentWindow?.postMessage({ type: "exec", src }, "*");
  } catch (e) {
    console.error(e);
  }
}

// deprecated, we're getting nothing from res.output now
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
  if ((ev.metaKey || ev.ctrlKey) && ev.code == "KeyS") copyToClipboard(ev);
});

function getSavedCode() {
  let value: string = localStorage.code || LOADING;
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

const RESULTS = "Output";
const JAVASCRIPT = "JS";
const SCHEME = "Scheme";
const CONSOLE = "Console";
const HELP = "Help";

const state = {
  output: signal(""),
  toast: signal(""),
  javascript: signal(""),
  scheme: signal(""),
  messages: signal<string[]>([]),
  editor: signal<AbstractEditor | null>(null),
  dark: signal(false),
  files: signal<string[]>(["Tour.newt"]),
  currentFile: signal<string>(localStorage.currentFile ?? "Tour.newt"),
  viMode: signal(false),
  // this should go away and work off of filename
  markdown: signal(false),
  selected: signal(localStorage.tab ?? RESULTS),
  diags: signal<Diag[]>([]),
};

// Monitor dark mode state (TODO - let user override system setting)
if (window.matchMedia) {
  function checkDark(ev: { matches: boolean }) {
    console.log("CHANGE", ev.matches, ev);
    if (ev.matches) {
      document.body.className = "dark";
      state.dark.value = true;
      state.editor.value?.setDark(true);
    } else {
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
  async getEntry(_, row, col) {
    let fileName = state.currentFile.value;
    let res = await ipc.sendMessage("hoverInfo", [fileName, row, col]);
    console.log("HOVER", res, "for", row, col);
    if (res == true) return null;
    return res || null;
  },
  async getActions(_, row, col) {
    let fileName = state.currentFile.value;
    let res = await ipc.sendMessage("codeActionInfo", [fileName, row, col]);
    console.log("ACTIONS", res, "for", row, col);
    return res;
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
    // FIXME we need a better way to manage the file name
    let module = src.match(/module\s+([^\s]+)/)?.[1];
    if (module) {
      // This causes problems with stuff like aoc/...
      let filename = "./" + module.replace(".", "/") + ".newt";
      // fragile..
      let isMarkdown = !!src.match(/```/)
      if (isMarkdown) filename += '.md'
      state.currentFile.value = filename
      state.markdown.value = isMarkdown
      state.editor.value?.setMarkdown(isMarkdown)
    }
    // This is a little flashy
    // state.javascript.value = ''
    let fileName = state.currentFile.value;
    console.log("FN", fileName);
    try {
      await ipc.sendMessage("updateFile", [fileName, src]);
      let res = await ipc.sendMessage("typeCheck", [fileName]);
      let diags: Diagnostic[] = [];
      state.diags.value = res.diags
      for (let marker of res.diags) {
        let { start, end } = marker.range;
        let xlate = (pos: Position): number =>
          view.state.doc.line(pos.line + 1).from + pos.character;

        diags.push({
          from: xlate(start),
          to: xlate(end),
          severity: SEVERITY[marker.severity ?? 1],
          message: marker.message,
        });
      }
      setOutput(res.output);
      state.javascript.value = "";
      state.scheme.value = "";
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
    state.editor.value = editor;
    editor.setDark(state.dark.value);
    if (initialValue === LOADING) loadFile("Tour.newt");
  }, []);
  return h("div", { id: "editor", ref });
}

interface ViewerProps {
  language: "javascript" | "scheme";
}
function SourceViewer({ language }: ViewerProps) {
  const text = state[language].value;

  const ref = useRef<HTMLDivElement>(null);
  const editorView = useRef<EditorView>(null);
  const themeRef = useRef<Compartment>(null);
  useEffect(() => {
    const container = ref.current!;
    themeRef.current = new Compartment();
    const editor = new EditorView({
      doc: text,
      parent: container,
      extensions: [
        basicSetup,
        themeRef.current.of(
          state.dark.value ? oneDark : EditorView.baseTheme({}),
        ),
        language == "javascript" ? javascript() : scheme(),
        EditorState.readOnly.of(true),
        EditorView.editable.of(false),
      ],
    });
    editorView.current = editor;
  }, []);
  let isDark = state.dark.value;
  let ev = editorView.current;
  if (ev) {
    ev.dispatch({
      effects: themeRef.current?.reconfigure(
        isDark ? oneDark : EditorView.baseTheme({}),
      ),
      changes: { from: 0, to: ev.state.doc.length, insert: text },
    });
  }
  return h("div", { id: "javascript", ref });
}

function Result() {
  const text = state.output.value;
  const diags = state.diags.value;
  const showRange = (range: Range) => h('div', { className: 'range' }, `${range.start.line}:${range.start.character}--${range.end.line}:${range.end.character}`)
  return h("div", { id: "result" }, ...diags.map(diag =>
    h("div", { className: 'diag' }, showRange(diag.range), diag.message)
  ));
}

function Help() {
  return h("div", { id: "help" }, md2nodes(helpText));
}

function Console() {
  const messages = state.messages.value ?? [];
  return h(
    "div",
    { id: "console" },
    messages.map((msg) => h("div", { className: "message" }, msg)),
  );
}

function Tabs() {
  const selected = state.selected.value;
  const Tab = (label: string) => {
    let onClick = () => {
      state.selected.value = label;
      localStorage.tab = label;
    };
    let className = "tab";
    if (label == selected) className += " selected";
    return h("div", { className, onClick }, label);
  };

  useEffect(() => {
    if (state.messages.value.length) state.selected.value = CONSOLE;
  }, [state.messages.value]);

  useEffect(() => {
    if (selected === JAVASCRIPT && !state.javascript.value) refreshJS();
    if (selected === SCHEME && !state.scheme.value) refreshScheme();
  }, [selected, state.javascript.value, state.scheme.value]);

  let body;
  switch (selected) {
    case RESULTS:
      body = h(Result, {});
      break;
    case SCHEME:
      body = h(SourceViewer, { language: "scheme" });
      break;
    case JAVASCRIPT:
      body = h(SourceViewer, { language: "javascript" });
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
      Tab(SCHEME),
      Tab(CONSOLE),
      Tab(HELP),
    ),
    h("div", { className: "tabBody" }, body),
  );
}

preload.then(() => {
  if (archive) {
    let files = [];
    for (let name in archive.entries) {
      if (name.endsWith(".newt")) files.push(name);
      if (name.endsWith(".newt.md")) files.push(name);
    }
    files.sort();
    state.files.value = files;
  }
});

function Icon({ name }: { name: string }) {
  return h("svg", { class: "icon" }, h("use", { href: `#${name}` }));
}

function EditWrap() {
  const options = state.files.value.map((value) =>
    h("option", { value }, value),
  );

  const selectFile = async (ev: TargetedEvent<HTMLSelectElement>) => {
    let fn = ev.currentTarget.value;
    ev.currentTarget.value = "";
    loadFile(fn);
  };
  const toggleViMode = (ev: MouseEvent) => {
    state.viMode.value = !state.viMode.value
    state.editor.value?.setVim(state.viMode.value)
    state.editor.value?.focus()
  };
  const doEscape = (ev: MouseEvent) => {
    state.editor.value?.escape()
    ev.preventDefault();
    ev.stopPropagation();
  }

  return h(
    "div",
    { className: "tabPanel left" },
    h(
      "div",
      { className: "tabBar" },
      h(
        "select",
        { onChange: selectFile, value: "" },
        h("option", { value: "" }, "-- load sample --"),
        options,
      ),
      // h("a", { href: 'https://github.com/dunhamsteve/newt', target: '_blank', title: "github" }, h('img', {src: state.dark.value ? github : github_light})),
      h(
        "a",
        {
          href: "https://github.com/dunhamsteve/newt",
          target: "_blank",
          title: "github",
        },
        h("svg", { class: "icon" }, h("use", { href: "#github" })),
      ),
      h('div', { onClick: toggleViMode, className: state.viMode.value ? 'vimon' : 'vimoff' }, "vi"),
      // Maybe add an "ESC" button, with preventDefault for mobile
      h('div', { onMouseDown: doEscape, className: state.viMode.value ? 'vimon' : 'vimoff', style: {display: state.viMode.value ? 'block' : 'none'} }, "esc"),
      h('div', { className: 'fileName' }, state.currentFile.value),
      h("div", { style: { flex: "1 1" } }),
      h(
        "div",
        {},
        h(
          "button",
          { onClick: copyToClipboard, title: "copy url" },
          h("svg", { class: "icon" }, h("use", { href: "#share" })),
        ),
        h(
          "button",
          { onClick: runOutput, title: "run program" },
          h("svg", { class: "icon" }, h("use", { href: "#play" })),
        ),
      ),
    ),
    h("div", { className: "tabBody" }, h(Editor, { initialValue: value })),
  );
}

function App() {
  let toast;
  if (state.toast.value) {
    toast = h("p", { className: "toast" }, h("div", {}, state.toast.value));
  }
  let className = `wrapper`;
  return h("div", { className }, toast, h(EditWrap, {}), h(Tabs, {}));
}

render(h(App, {}), document.getElementById("app")!);

