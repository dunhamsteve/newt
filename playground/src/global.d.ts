export {}
declare global {
  interface Process {
    stdout: {
      write(s: string): void
    },
    argv: string[]

  }
  let files : Record<string,string>
  let process : Process
  let __mainExpression_0 : () => unknown
}
