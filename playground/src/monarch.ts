import * as monaco from "monaco-editor";

export let newtConfig: monaco.languages.LanguageConfiguration = {
  // see singleton in Tokenizer.idr
  wordPattern: /[^()\\{}\[\],.@\s]+/,
  comments: {
    // symbol used for single line comment. Remove this entry if your language does not support line comments
    lineComment: "--",
    // symbols used for start and end a block comment. Remove this entry if your language does not support block comments
    blockComment: ["/-", "-/"],
  },
  // symbols used as brackets
  brackets: [
    ["{", "}"],
    ["[", "]"],
    ["(", ")"],
  ],
  // symbols that are auto closed when typing
  autoClosingPairs: [
    { open: "{", close: "}" },
    { open: "[", close: "]" },
    { open: "(", close: ")" },
    { open: '"', close: '"' },
    // { open: "'", close: "'" }, causes problems with foo''
    { open: "/-", close: "-/" },
  ],
  // symbols that can be used to surround a selection
  surroundingPairs: [
    { open: "{", close: "}" },
    { open: "[", close: "]" },
    { open: "(", close: ")" },
    { open: '"', close: '"' },
    { open: "'", close: "'" },
  ],
  onEnterRules: [
    {
      beforeText: /^\s+$/,
      action: {
        indentAction: monaco.languages.IndentAction.Outdent,
      },
    },
    {
      beforeText: /\bwhere$/,
      action: {
        indentAction: monaco.languages.IndentAction.Indent,
      },
    },
    {
      beforeText: /\bof$/,
      action: {
        indentAction: monaco.languages.IndentAction.Indent,
      },
    },
    {
      beforeText: /\/-/,
      afterText: /-\//,
      action: {
        indentAction: monaco.languages.IndentAction.IndentOutdent,
      },
    },
  ],
};

export let newtTokens: monaco.languages.IMonarchLanguage = {
  // Set defaultToken to invalid to see what you do not tokenize yet
  // defaultToken: "invalid",

  keywords: [
    "let",
    "in",
    "where",
    "case",
    "record",
    "of",
    "data",
    "forall",
    "∀",
    "U",
    "module",
    "ptype",
    "pfunc",
    "if",
    "uses",
    "then",
    "else",
    "class",
    "instance",
    "module",
    "infixl",
    "infixr",
    "infix",
  ],
  specialOps: ["=>", "->", ":", "=", ":=", "<-"],
  tokenizer: {
    root: [
      [
        /[a-z_$'][\w$]*/,
        { cases: { "@keywords": "keyword", "@default": "identifier" } },
      ],
      [/[A-Z][\w\$]*/, "type.identifier"],
      [/\\|λ/, "keyword"],
      { include: "@whitespace" },
      [/[{}()\[\]]/, "@brackets"],
      [
        /[:!#$%&*+.<=>?@\\^|~\/-]+/,
        {
          cases: {
            "@specialOps": "keyword",
            "@default": "operator",
          },
        },
      ],
      // char literal, but I don't think there is a class for that.
      [/'\\?.'/, "string"],
      [/\d+/, "number"],

      // strings
      [/"([^"\\]|\\.)*$/, "string.invalid"], // non-teminated string
      [/"/, { token: "string.quote", bracket: "@open", next: "@string" }],
    ],
    comment: [
      [/[^-]+/, "comment"],
      ["-/", "comment", "@pop"],
      ["-", "comment"],
    ],
    string: [
      [/[^\\"]+/, "string"],
      // [/@escapes/, "string.escape"],
      // [/\\./, "string.escape.invalid"],
      [/"/, { token: "string.quote", bracket: "@close", next: "@pop" }],
    ],
    whitespace: [
      [/[ \t\r\n]+/, "white"],
      ["/-", "comment", "@comment"],
      [/--.*$/, "comment"],
    ],
  },
};
