import js from "@eslint/js";

export default [
  js.configs.recommended,
  {
    rules: {
      "no-shadow": ["error", { "builtinGlobals": true, "hoist": "all" }]
    }
  }
];
