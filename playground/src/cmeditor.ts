import { AbstractEditor, EditorDelegate, Marker } from "./types";
import { basicSetup } from "codemirror";
import { EditorView, hoverTooltip, Tooltip } from "@codemirror/view";
import { Compartment } from "@codemirror/state";
import { parser } from "./parser.js";
import { oneDark, oneDark as themeOneDark } from "@codemirror/theme-one-dark";
import { styleTags, tags as t } from "@lezer/highlight";
import { linter, Diagnostic } from "@codemirror/lint";
import {
  LanguageSupport,
  LRLanguage,
  StreamLanguage,
  StringStream,
} from "@codemirror/language";

let parserWithMetadata = parser.configure({
  props: [
    styleTags({
      Identifier: t.variableName,
      LineComment: t.lineComment,
      "if then else data where": t.keyword,
    }),
    // indentNodeProp, foldNodeProp
  ],
});

const newtLanguage = LRLanguage.define({
  parser: parserWithMetadata,
  languageData: {
    commentTokens: {
      line: "--",
    },
  },
});
// prettier did this...
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
  stream.eatSpace();
  if (stream.match("--")) {
    stream.skipToEnd();
    return "comment";
  }
  if (stream.match(/^[/]-/)) {
    state.tokenizer = commentTokenizer;
    return state.tokenizer(stream, state);
  }
  if (stream.match(/^[\w_][\w\d_']*/)) {
    let word = stream.current();
    if (keywords.includes(word)) return "keyword";
    if (word[0] >= "A" && word[0] <= "Z") return "typename";
    return "identifier";
  }
  // unhandled
  stream.next();
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
  console.log("XX", stream.current());
  return "comment";
}

const newtLanguage2 = StreamLanguage.define({
  startState: () => ({ tokenizer }),
  token(stream, st) {
    return st.tokenizer(stream, st);
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
            console.log("entry", entry);
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
