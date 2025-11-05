import { AbstractEditor, EditorDelegate, Marker } from "./types";
import { basicSetup } from "codemirror";
import {
  indentMore,
  indentLess,
  toggleLineComment,
} from "@codemirror/commands";
import { EditorView, hoverTooltip, keymap, Tooltip } from "@codemirror/view";
import { Compartment, Prec } from "@codemirror/state";
import { oneDark } from "@codemirror/theme-one-dark";
import { linter } from "@codemirror/lint";
import {
  bracketMatching,
  indentService,
  LanguageSupport,
  StreamLanguage,
  StringStream,
} from "@codemirror/language";
import { ABBREV } from "./abbrev.js";

// prettier flattened this...
const keywords = [
  "let",
  "in",
  "where",
  "case",
  "of",
  "data",
  "U",
  "do",
  "ptype",
  "pfunc",
  "module",
  "infixl",
  "infixr",
  "infix",
  "∀",
  "forall",
  "import",
  "uses",
  "class",
  "instance",
  "record",
  "constructor",
  "if",
  "then",
  "else",
  "$",
  "λ",
  "?",
  "@",
  ".",
  "->",
  "→",
  ":",
  "=>",
  ":=",
  "$=",
  "=",
  "<-",
  "\\",
  "_",
  "|",
];

// a stack of tokenizers, current is first
// we need to push / pop {} so we can parse strings correctly
interface State {
  tokenizers: Tokenizer[];
}
type Tokenizer = (stream: StringStream, state: State) => string | null;

function tokenizer(stream: StringStream, state: State): string | null {
  if (stream.eatSpace()) return null;
  if (stream.match("--")) {
    stream.skipToEnd();
    return "comment";
  }
  // maybe keyword?
  if (stream.match(/{/)) {
    state.tokenizers.unshift(tokenizer);
    return null;
  }
  if (stream.match(/}/) && state.tokenizers.length > 1) {
    state.tokenizers.shift();
    return state.tokenizers[0] === stringTokenizer ? "keyword" : null;
  }
  if (stream.match(/^[/]-/)) {
    state.tokenizers.unshift(commentTokenizer);
    return state.tokenizers[0](stream, state);
  }
  if (stream.match(/"/)) {
    state.tokenizers.unshift(stringTokenizer);
    return stringTokenizer(stream, state);
  }
  // TODO match tokenizer better..
  if (stream.match(/[^\\(){}[\],.@;\s][^()\\{}\[\],.@;\s]*/)) {
    let word = stream.current();
    if (keywords.includes(word)) return "keyword";
    if (word[0] >= "A" && word[0] <= "Z") return "typeName";
    return "variableName";
  }
  // unhandled
  stream.next();
  return null;
}

function stringTokenizer(stream: StringStream, state: State) {
  while (true) {
    if (stream.current() && stream.match(/^\\{/, false)) {
      return "string";
    }
    if (stream.match(/^\\{/)) {
      state.tokenizers.unshift(tokenizer);
      return "keyword";
    }
    let ch = stream.next();
    if (!ch) return "string";
    if (ch === '"') {
      state.tokenizers.shift();
      return "string";
    }
  }
}

// We have a tokenizer for this because codemirror processes a line at a time.
// So we may need to end the line in `comment` state and see the -/ later
function commentTokenizer(stream: StringStream, state: State): string | null {
  console.log("ctok");
  let dash = false;
  let ch;
  while ((ch = stream.next())) {
    if (dash && ch === "/") {
      state.tokenizers.shift();
      return "comment";
    }
    dash = ch === "-";
  }
  return "comment";
}

const newtLanguage2: StreamLanguage<State> = StreamLanguage.define({
  startState: () => ({ tokenizers: [tokenizer] }),
  token(stream, st) {
    return st.tokenizers[0](stream, st);
  },
  languageData: {
    commentTokens: {
      line: "--",
    },
    // The real list would include almost every character.
    wordChars: "!#$%^&*_+-=<>|",
  },
});

function newt() {
  return new LanguageSupport(newtLanguage2);
}

export class CMEditor implements AbstractEditor {
  view: EditorView;
  delegate: EditorDelegate;
  theme: Compartment;
  constructor(container: HTMLElement, doc: string, delegate: EditorDelegate) {
    this.delegate = delegate;
    this.theme = new Compartment();

    this.view = new EditorView({
      doc,
      parent: container,
      extensions: [
        basicSetup,
        linter((view) => this.delegate.lint(view)),
        // For indent on return
        indentService.of((ctx, pos) => {
          let line = ctx.lineAt(pos);
          if (!line || !line.from) return null;
          let prevLine = ctx.lineAt(line.from - 1);
          if (prevLine.text.trimEnd().match(/\b(of|where|do)\s*$/)) {
            let pindent = prevLine.text.match(/^\s*/)?.[0].length ?? 0;
            return pindent + 2;
          }
          return null;
        }),
        Prec.highest(
          keymap.of([
            {
              key: "Tab",
              preventDefault: true,
              run: indentMore,
            },
            {
              key: "Cmd-/",
              run: toggleLineComment,
            },
            // ok, we can do multiple keys (we'll want this for Idris)
            {
              key: "c-c c-s",
              run: () => {
                console.log("C-c C-s");
                return false;
              },
            },
            {
              key: "Shift-Tab",
              preventDefault: true,
              run: indentLess,
            },
          ])
        ),
        EditorView.updateListener.of((update) => {
          let doc = update.state.doc;
          update.changes.iterChanges((fromA, toA, fromB, toB, inserted) => {
            if (" ')\\_".includes(inserted.toString()) || inserted.lines > 1) {
              console.log("changes", update.changes, update.changes.desc);
              let line = doc.lineAt(fromA);
              let e = fromA - line.from;
              const m = line.text.slice(0, e).match(/(\\[^ ]+)$/);
              if (m) {
                let s = e - m[0].length;
                let key = line.text.slice(s, e);
                if (ABBREV[key]) {
                  this.view.dispatch({
                    changes: {
                      from: line.from + s,
                      to: fromA,
                      insert: ABBREV[key],
                    },
                  });
                }
              }
            }
          });
        }),
          this.theme.of(EditorView.baseTheme({})),
          hoverTooltip((view, pos) => {
            let cursor = this.view.state.doc.lineAt(pos);
            let line = cursor.number;
            let range = this.view.state.wordAt(pos);
            console.log(range);
            if (range) {
              let col = range.from - cursor.from;
              let word = this.view.state.doc.sliceString(range.from, range.to);
              let entry = this.delegate.getEntry(word, line, col);
              if (!entry)
                entry = this.delegate.getEntry("_" + word + "_", line, col);
              console.log("entry for", word, "is", entry);
              if (entry) {
                let rval: Tooltip = {
                  pos: range.head,
                  above: true,
                  create: () => {
                    let dom = document.createElement("div");
                    dom.className = "tooltip";
                    dom.textContent = entry.type;
                    return { dom };
                  },
                };
                return rval;
              }
            }
            // we'll iterate the syntax tree for word.
            // let entry = delegate.getEntry(word, line, col)
            return null;
          }),
        newt(),
      ],
    });
  }
  setDark(isDark: boolean) {
    this.view.dispatch({
      effects: this.theme.reconfigure(
        isDark ? oneDark : EditorView.baseTheme({})
      ),
    });
  }
  setValue(_doc: string) {
    // Is this all we can do?
    this.view.dispatch({
      changes: { from: 0, to: this.view.state.doc.length, insert: _doc },
    });
  }
  getValue() {
    // maybe?
    return this.view.state.doc.toString();
  }
  setMarkers(_: Marker[]) {}
}
