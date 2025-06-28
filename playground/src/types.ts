import { EditorView } from "codemirror";
import { linter, Diagnostic } from "@codemirror/lint";

export interface CompileReq {
  id: string
  type: "compileRequest";
  fileName: string;
  src: string;
  compile: boolean;
}

export interface CompileRes {
  id: string
  type: "compileResult";
  output: string;
  javascript: string;
  duration: number;
}

export interface ConsoleList {
  type: 'setConsole'
  messages: string[];
}
export interface ConsoleItem {
  type: 'pushConsole'
  message: string;
}

export interface ExecCode {
  type: 'exec'
  src: string
}

export type Message = CompileReq | CompileRes | ConsoleList | ConsoleItem | ExecCode
// editor.(createModel / setModel / getModels) to switch files
// TODO - remember files and allow switching?
// static zip filesystem with user changes overlaid via localStorage
// download individual files (we could use the cheap compression from the pdflib or no compression to make zip download)
// would need way to reset/delete
export interface FC {
  file: string;
  line: number;
  col: number;
}

interface TopEntry {
  fc: FC;
  name: string;
  type: string;
}

export interface TopData {
  context: TopEntry[];
}
export interface EditorDelegate {
  getEntry(word: string, row: number, col: number): TopEntry | undefined
  onChange(value: string): unknown
  getFileName(): string
  lint(view: EditorView): Promise<Diagnostic[]> | Diagnostic[]
}
export interface Marker {
  severity: 'error' | 'info' | 'warning'
  message: string
  startColumn: number
  startLineNumber: number
  endColumn: number
  endLineNumber: number
}
export interface AbstractEditor {
  setValue: (_: string) => unknown;
  getValue: () => string;
  setMarkers: (_: Marker[]) => unknown
  setDark(isDark: boolean): unknown
}

