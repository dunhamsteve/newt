class Buffer extends ArrayBuffer {
  static alloc(n) {

    return new Buffer(n);
  }
  indexOf(n) {
    let view = new Uint8Array(this);
    return view.indexOf(n);
  }

  static concat(bufs) {
    let size = bufs.reduce((a, b) => (a += b.byteLength), 0);
    console.log('concat', size, bufs);
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
    return dec.decode(this)
  }
}
let dec = new TextDecoder();
let enc = new TextEncoder();
let files = {
};

let fds = [];

let shim = {
  os: {
    platform() {
      return "linux";
    },
  },
  fs: {
    openSync(fn) {
      console.log("openSync", fn);
      let te = new TextEncoder();
      let fd = fds.length;
      if (!files[fn]) throw new Error(`${fn} not found`)
      let buf = te.encode(files[fn]);
      let pos = 0;
      fds.push({ buf, pos });
      // we'll mutate the pointer as stuff is read
      return fd;
    },
    readSync(fd, buf, start, len) {
      let hand = fds[fd]
      let avail = hand.buf.byteLength - hand.pos
      let rd = Math.min(avail, len)
      let src = new Uint8Array(hand.buf)
      let dest = new Uint8Array(buf)
      for (let i=0;i<rd;i++)
        dest[start+i] = src[hand.pos++]
      console.log('read', rd)
      return rd
    },
    closeSync(fd) {
      delete fds[fd]
    }
  },
};

shim.fs = new Proxy(shim.fs, {
  get(target, prop, receiver) {
    console.log("fs get", prop);
    return target[prop];
  },
});

const process = {
  platform: "linux",
  argv: ["", ""],
  stdout: {
    // We'll want to replace this one
    write: console.log,
  },
  exit(v) {
    console.log("exit", v);
  },
  // stdin: { fd: 0 },
};

const require = (x) => shim[x];
