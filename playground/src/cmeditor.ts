import { AbstractEditor, EditorDelegate, Marker } from "./types";
import { basicSetup } from "codemirror";
import { defaultKeymap, indentMore, indentLess, toggleLineComment } from "@codemirror/commands";
import { EditorView, hoverTooltip, keymap, Tooltip } from "@codemirror/view";
import { Compartment, Prec } from "@codemirror/state";
import { oneDark } from "@codemirror/theme-one-dark";
import { linter } from "@codemirror/lint";
import {
  indentService,
  LanguageSupport,
  StreamLanguage,
  StringStream,
} from "@codemirror/language";
import { ABBREV } from "./abbrev.js";

// maybe use https://github.com/codemirror/legacy-modes/blob/main/mode/simple-mode.js instead.
// @codemirror/legacy-modes/mode/simple-mode.js

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

interface State {
  tokenizer(stream: StringStream, state: State): string | null;
}

function tokenizer(stream: StringStream, state: State): string | null {
  if (stream.eatSpace()) return null
  if (stream.match("--")) {
    stream.skipToEnd();
    return "comment";
  }
  if (stream.match(/^[/]-/)) {
    state.tokenizer = commentTokenizer;
    return state.tokenizer(stream, state);
  }

  // TODO match tokenizer better..
  if (stream.match(/[^\\(){}[\],.@;\s][^()\\{}\[\],.@;\s]*/)) {
    let word = stream.current();
    if (keywords.includes(word)) return "keyword";
    if (word[0] >= "A" && word[0] <= "Z") return "typename";
    return "identifier";
  }
  // unhandled
  stream.next()
  return null;
}
function commentTokenizer(stream: StringStream, state: State): string | null {
  console.log("ctok");
  let dash = false;
  let ch;
  while ((ch = stream.next())) {
    if (dash && ch === "/") {
      state.tokenizer = tokenizer;
      return "comment";
    }
    dash = ch === "-";
  }
  return "comment";
}

const newtLanguage2 = StreamLanguage.define({
  startState: () => ({ tokenizer }),
  token(stream, st) {
    return st.tokenizer(stream, st);
  },
  languageData: {
    commentTokens: {
      line: "--"
    },
    wordChars: "!#$%^&*_+-=<>|",
  }
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
          let line = ctx.lineAt(pos)
          if (!line || !line.from) return null
            let prevLine = ctx.lineAt(line.from - 1);
            if (prevLine.text.trimEnd().match(/\b(of|where|do)\s*$/)) {
              let pindent = prevLine.text.match(/^\s*/)?.[0].length ?? 0
              return pindent + 2
            }
          return null
        }),
        Prec.highest(keymap.of([
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
              console.log("C-c C-s")
              return false
            }
          },
          {
            key: "Shift-Tab",
            preventDefault: true,
            run: indentLess,
          },
        ])),
        EditorView.updateListener.of((update) => {
          let doc = update.state.doc;

          update.changes.iterChanges((fromA, toA, fromB, toB, inserted) => {
            if (" ')\\_".includes(inserted.toString())) {
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
            if (!entry) entry = this.delegate.getEntry('_'+word+'_', line, col);
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
