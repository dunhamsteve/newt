export interface CompileReq {
  src: string;
}

export interface CompileRes {
  output: string
  javascript: string
  duration: number
}
