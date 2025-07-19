/// <reference types="vite/client" />
declare module "*.css";
export {};
declare global {
  // typescript doesn't know worker.ts is a worker
  function importScripts(...scripts: string[]): void;

  // let files: Record<string, string>;
  // let process: Process;
  let Main_main: () => unknown;
}
