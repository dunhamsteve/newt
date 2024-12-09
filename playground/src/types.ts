export interface CompileReq {
  type: "compileRequest";
  fileName: string;
  src: string;
}

export interface CompileRes {
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
