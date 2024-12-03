class Buffer extends ArrayBuffer {
  static alloc(n: number) {
    return new Buffer(n);
  }
  indexOf(n: number) {
    let view = new Uint8Array(this);
    return view.indexOf(n);
  }

  static concat(bufs: Buffer[]) {
    let size = bufs.reduce((a, b) => (a += b.byteLength), 0);
    let rval = new Buffer(size);
    let view = new Uint8Array(rval);
    let off = 0;
    for (let buf of bufs) {
      view.set(new Uint8Array(buf), off);
      off += buf.byteLength;
    }
    return rval;
  }
  toString() {
    return new TextDecoder().decode(this);
  }
}

let files: Record<string, string> = {};
interface Handle {
  name: string;
  mode: string;
  pos: number;
  buf: Buffer;
}
let fds: Handle[] = [];

let shim: any = {
  os: {
    platform() {
      return "linux";
    },
  },
  fs: {
    openSync(name: string, mode: string) {
      console.log("open", name, arguments);
      let te = new TextEncoder();

      let fd = fds.findIndex((x) => !x);
      if (fd < 0) fd = fds.length;
      let buf;
      let pos = 0;
      if (mode == "w") {
        buf = new Buffer(0);
      } else {
        if (!files[name]) throw new Error(`${name} not found`);
        buf = te.encode(files[name]);
      }
      fds[fd] = { buf, pos, mode, name };
      // we'll mutate the pointer as stuff is read
      return fd;
    },
    writeSync(fd: number, line: string) {
      if (typeof line !== "string") throw new Error("not implemented");
      let handle = fds[fd];
      if (!handle) throw new Error(`bad fd ${fd}`)
      let buf2 = new TextEncoder().encode(line);
      handle.buf =  Buffer.concat([handle.buf, buf2])
    },
    chmodSync(fn: string, mode: number) { },
    readSync(fd: number, buf: Buffer, start: number, len: number) {
      let hand = fds[fd];
      let avail = hand.buf.byteLength - hand.pos;
      let rd = Math.min(avail, len);
      let src = new Uint8Array(hand.buf);
      let dest = new Uint8Array(buf);
      for (let i = 0; i < rd; i++) dest[start + i] = src[hand.pos++];
      return rd;
    },
    closeSync(fd: number) {
      let handle = fds[fd];
      if (handle.mode == "w") {
        files[handle.name] = new TextDecoder().decode(handle.buf);
      }
      delete fds[fd];
    },
  },
};

// Spy on Idris' calls to see what we need to fill in
shim.fs = new Proxy(shim.fs, {
  get(target, prop, receiver) {
    if (prop in target) {
      return (target as any)[prop];
    }
    throw new Error(`implement fs.${String(prop)}`)
  },
});

const process: Process = {
  platform: "linux",
  argv: ["", ""],
  stdout: {
    // We'll want to replace this one
    write: console.log,
  },
  exit(v: number) {
    console.log("exit", v);
  },
  // stdin: { fd: 0 },
};

const require = (x: string) => shim[x];

// Maybe the shim goes here and we append newt...

let stdout = ''
// We'll want to collect and put info in the monaco
process.stdout.write = (s) => {
  stdout += s
};
// hack for now
const preload = [
  "Prelude.newt",
  "Web.newt",
  "aoc2023/day1/eg.txt",
  "aoc2023/day1/eg2.txt",
]
const handleMessage = async function (e) {
  console.log('message for you sir', e.data)
  for (let fn of preload) {

    if (!files[fn]) {
      console.log('preload', fn)
      let res = await fetch(fn)
      let text = await res.text()
      files[fn] = text
    }
  }
  let {src} = e.data
  let module = 'Main'
  let m = src.match(/module (\w+)/)
  if (m) module = m[1]
  let fn = `${module}.newt`
  process.argv = ["", "", fn, "-o", "out.js"];
  console.log("args", process.argv);
  files[fn] = src;
  files['out.js'] = 'No JS output';
  stdout = ''
  const start = +new Date()
  try {
    newtMain();
  } catch (e) {
    // make it clickable
    console.error(e)
    // make it visable
    stdout += '\n' + String(e)
  }
  let duration = +new Date() - start
  console.log(`process ${fn} in ${duration} ms`)
  let javascript = files['out.js']
  let output = stdout
  sendResponse({javascript, output, duration})
}
let sendResponse = postMessage
onmessage = handleMessage

importScripts('newt.js')
