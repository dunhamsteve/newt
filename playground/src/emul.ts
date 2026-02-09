import { ZipFile } from "./zipfile";

export interface Handle {
  name: string;
  mode: string;
  pos: number;
  buf: Uint8Array;
}

interface Process {
  argv: string[];
  platform: string;
  exit(_: number): void;
  stdout: {
    write(s: string): unknown
  };
  cwd(): string;
  env: Record<string,string>
  __lasterr: {errno: number}
}
export interface NodeShim {
  stdout: string;
  archive?: ZipFile;
  process: Process;
  files: Record<string, Uint8Array>;
  fs: any;
}
export let shim: NodeShim = {
  // these three and process are poked at externally
  archive: undefined,
  stdout: "",
  files: {},
  fs: {
    readFileSync(name: string, encoding: string, enc?: string) {
      if (name.startsWith("./")) name = name.slice(2);
      let data: Uint8Array | undefined = shim.files[name]
      if (!data && shim.archive?.entries[name]) {
        // keep a copy of the uncompressed version for speed
        data = shim.files[name] = shim.archive.getData(name)!;
      }
      if (data) {
        return new TextDecoder().decode(data);
      } else {
        throw new Error(`${name} not found`);
      }
    },
    writeFileSync(name: string, data: string, enc?: string) {
      shim.files[name] = new TextEncoder().encode(data)
    },
    writeSync(fd: number, data: string) {
      shim.stdout += data;
    }
  },
  process: {
    argv: ["", ""],
    exit(v: number) {
      throw new Error(`exit ${v}`)
    },
  }
};

// we intercept require to return our fake node modules
declare global {
  interface Window {
    require: (x: string) => any;
    process: Process;
  }
}
const requireStub: any = (x: string) => (shim as any)[x];
self.require = requireStub;
self.process = shim.process;
