import { ZipFile } from "./zipfile";

class Buffer extends DataView {
  static alloc(n: number) {
    return new Buffer(new Uint8Array(n).buffer);
  }
  indexOf(n: number) {
    return new Uint8Array(this.buffer).indexOf(n);
  }
  get length() {
    return this.byteLength;
  }
  slice(start: number, end: number) {
    return new Buffer(this.buffer.slice(start, end));
  }
  readUInt8(i: number) {
    return this.getUint8(i);
  }
  writeUInt8(val: number, i: number) {
    this.setUint8(i, val);
  }
  write(value: string, start: number, len: number, enc: string) {
    // console.log("write", value, start, len, enc);
    let buf = new TextEncoder().encode(value);
    let ss = 0;
    let se = Math.min(len, buf.length);
    let ts = start;
    for (; ss < se; ss++, ts++) this.setInt8(ts, buf[ss]);
    shim.process.__lasterr.errno = 0;
    return se;
  }
  readDoubleLE(i: number) {
    return this.getFloat64(i, true);
  }
  readInt32LE(i: number) {
    return this.getInt32(i, true);
  }
  writeInt32LE(val: number, i: number) {
    return this.setInt32(i, val, true);
  }
  copy(target: Buffer, ts: number, ss: number, se: number) {
    for (; ss < se; ss++, ts++) target.setInt8(ts, this.getInt8(ss));
  }
  static concat(bufs: Buffer[]) {
    let size = bufs.reduce((a, b) => (a += b.byteLength), 0);
    let rval = Buffer.alloc(size);
    let off = 0;
    for (let buf of bufs) {
      const view = new Int8Array(rval.buffer);
      view.set(new Uint8Array(buf.buffer), off);
      off += buf.byteLength;
    }
    return rval;
  }
  toString() {
    return new TextDecoder().decode(this);
  }
}

export interface Handle {
  name: string;
  mode: string;
  pos: number;
  buf: Uint8Array;
}

interface Process {
  platform: string;
  stdout: {
    write(s: string): void;
  };
  argv: string[];
  exit(_: number): void;
  cwd(): string;
  env: Record<string, string>;
  __lasterr: { errno: number };
}
export interface NodeShim {
  stdout: string;
  archive?: ZipFile;
  process: Process;
  files: Record<string, Uint8Array>;
  fds: Handle[];
  tty: {
    isatty(): number;
  };
  os: {
    platform(): string;
  };
  fs: any;
}
export let shim: NodeShim = {
  // these three and process are poked at externally
  archive: undefined,
  stdout: "",
  files: {},
  fds: [],
  tty: {
    isatty() {
      return 0;
    },
  },
  os: {
    platform() {
      return "linux";
    },
  },
  fs: {
    // TODO - Idris is doing readdir, we should implement that
    opendirSync(name: string) {
      let fd = shim.fds.findIndex((x) => !x);
      if (fd < 0) fd = shim.fds.length;
      console.log("openDir", name);
      shim.process.__lasterr.errno = 0;
      return fd;
    },
    mkdirSync(name: string) {
      console.log("mkdir", name);
      shim.process.__lasterr.errno = 0;
      return 0;
    },
    openSync(name: string, mode: string) {
      console.log("open", name, mode);
      let te = new TextEncoder();

      let fd = shim.fds.findIndex((x) => !x);
      if (fd < 0) fd = shim.fds.length;
      let buf: Uint8Array;
      let pos = 0;
      if (mode == "w") {
        buf = new Uint8Array(0);
      } else {
        // TODO, we need to involve localStorage when the window does multiple files and persists
        if (shim.files[name]) {
          buf = shim.files[name];
        } else if (shim.archive?.entries[name]) {
          // keep a copy of the uncompressed version for speed
          buf = shim.files[name] = shim.archive.getData(name);
        } else {
          shim.process.__lasterr.errno = 1;
          throw new Error(`${name} not found`);
        }
      }
      shim.process.__lasterr.errno = 0;
      shim.fds[fd] = { buf, pos, mode, name };
      // we'll mutate the pointer as stuff is read
      return fd;
    },
    writeSync(fd: number, line: string | Buffer) {
      try {
        let handle = shim.fds[fd];
        if (!handle) throw new Error(`bad fd ${fd}`);

        let buf2: ArrayBuffer;
        if (typeof line === "string") {
          buf2 = new TextEncoder().encode(line);
          let newbuf = new Uint8Array(handle.buf.byteLength + buf2.byteLength);
          newbuf.set(new Uint8Array(handle.buf));
          newbuf.set(new Uint8Array(buf2), handle.buf.byteLength);
          handle.buf = newbuf;
          shim.process.__lasterr.errno = 0;
        } else if (line instanceof Buffer) {
          let start = arguments[2];
          let len = arguments[3];
          buf2 = line.buffer.slice(start, start + len);
          let newbuf = new Uint8Array(handle.buf.byteLength + buf2.byteLength);
          newbuf.set(new Uint8Array(handle.buf));
          newbuf.set(new Uint8Array(buf2), handle.buf.byteLength);
          handle.buf = newbuf;
          shim.process.__lasterr.errno = 0;
          return len;
        } else {
          debugger;
          throw new Error(`write ${typeof line} not implemented`);
        }
      } catch (e) {
        debugger;
        throw e;
      }
    },
    chmodSync(fn: string, mode: number) {},
    fstatSync(fd: number) {
      let hand = shim.fds[fd];
      return { size: hand.buf.byteLength };
    },
    readSync(fd: number, buf: Buffer, start: number, len: number) {
      let hand = shim.fds[fd];
      let avail = hand.buf.length - hand.pos;
      let rd = Math.min(avail, len);
      let src = hand.buf;
      let dest = new Uint8Array(buf.buffer);
      for (let i = 0; i < rd; i++) dest[start + i] = src[hand.pos++];
      return rd;
    },
    closeSync(fd: number) {
      let handle = shim.fds[fd];
      // console.log("close", handle.name);
      if (handle.mode == "w") {
        shim.files[handle.name] = handle.buf;
      }
      delete shim.fds[fd];
    },
  },
  process: {
    platform: "linux",
    argv: ["", ""],
    stdout: {
      // We'll want to replace this one
      write(s) {
        console.log("*", s);
        shim.stdout += s;
      },
    },
    exit(v: number) {
      console.log("exit", v);
    },
    cwd() {
      return "";
    },
    env: {
      NO_COLOR: "true",
      IDRIS2_CG: "javascript",
      IDRIS2_PREFIX: "",
    },
    __lasterr: {
      errno: 0,
    },
    // stdin: { fd: 0 },
  },
};

// Spy on Idris' calls to see what we need to fill in
shim.fs = new Proxy(shim.fs, {
  get(target, prop, receiver) {
    if (prop in target) {
      return (target as any)[prop];
    }
    let err = new Error(`IMPLEMENT fs.${String(prop)}`);
    // idris support eats the exception
    console.error(err);
    throw err;
  },
});

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
