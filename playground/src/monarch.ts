import * as monaco from 'monaco-editor'

export let newtLanguage: monaco.languages.IMonarchLanguage = {
  // Set defaultToken to invalid to see what you do not tokenize yet
  // defaultToken: 'invalid',

  keywords: [
    "let",
    "in",
    "where",
    "case",
    "of",
    "data",
    "U",
    "module",
    "ptype",
    "pfunc",
    "module",
    "infixl",
    "infixr",
    "infix",
  ],
  specialOps: ["=>", "->", ":", "=", ":="],
  tokenizer: {
    root: [
      [
        /[a-z_$][\w$]*/,
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
      [/\\./, "string.escape.invalid"],
      [/"/, { token: "string.quote", bracket: "@close", next: "@pop" }],
    ],
    whitespace: [
      [/[ \t\r\n]+/, "white"],
      ["/-", "comment", "@comment"],
      [/--.*$/, "comment"],
    ],
  },
};
