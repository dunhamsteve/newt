declare module "*.css";
export {};
declare global {
  interface Process {
    platform: string;
    stdout: {
      write(s: string): void;
    };
    argv: string[];
    exit(_: number): void;
  }
  let files: Record<string, string>;
  let process: Process;
  let newtMain: () => unknown;
}
