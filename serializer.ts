// Experimental serializer / deserializer for modules
// not completely wired in yet, serialization is running, deserialization is not

const END = 0;
const LIST = 1;
const TUPLE = 2;
const INDUCT = 3;
const STRING = 4;
const NUMBER = 5;
const NULL = 6;
const te = new TextEncoder();

class DeserializationStream {
  pos = 0;
  buf: Uint8Array;

  constructor(buf: Uint8Array) {
    this.buf = buf;
  }

  readByte() {
    return this.buf[this.pos++];
  }

  readVarint() {
    let shift = 0;
    let result = 0;
    while (true) {
      const byte = this.readByte();
      result |= (byte & 0x7f) << shift;
      if ((byte & 0x80) === 0) break;
      shift += 7;
    }
    return result;
  }

  readSignedVarint() {
    const n = this.readVarint();
    return (n >>> 1) ^ -(n & 1);
  }

  readString() {
    const length = this.readVarint();
    const bytes = this.buf.slice(this.pos, this.pos + length);
    this.pos += length;
    return new TextDecoder().decode(bytes);
  }
}

export class DecFile {
  pool: string[] = [""];
  buf: DeserializationStream;
  static decode(encoded: Uint8Array) {
    return new DecFile(encoded).read()
  }
  constructor(data: Uint8Array) {
    this.buf = new DeserializationStream(data);
    this.readPool();
  }

  readPool() {
    while (true) {
      let str = this.buf.readString();
      if (!str.length) break
      this.pool.push(str);
    }
    console.log('read pool', this.buf.pos)
  }

  read(): any {
    const type = this.buf.readByte();
    switch (type) {
      case NULL:
        return null;
      case LIST: {
        const list: any[] = [];
        while (this.buf.buf[this.buf.pos] !== END) {
          list.push(this.read());
        }
        this.buf.pos++;
        let rval: any = { tag: "Nil", 'h0': null };
        while (list.length)
          rval = { tag: "_::_", h0: null, h1: list.pop(), h2: rval };
        return rval;
      }
      case TUPLE: {
        const tuple: any[] = [];
        while (this.buf.buf[this.buf.pos] !== END) {
          tuple.push(this.read());
        }
        this.buf.pos++;
        let rval: any = tuple.pop();
        while (tuple.length)
          rval = { tag: "_,_", h0: null, h1: null, h2: tuple.pop(), h3: rval };
        return rval;
      }
      case STRING:
        return this.pool[this.buf.readVarint()];
      case NUMBER:
        return this.buf.readSignedVarint();
      case INDUCT:
        const tag = this.pool[this.buf.readVarint()];
        const obj: any = { tag };
        let i = 0;
        while (this.buf.buf[this.buf.pos] !== END) {
          obj[`h${i++}`] = this.read();
        }
        this.buf.pos++;
        return obj;
      default:
        debugger
        throw new Error(`Unknown type: ${type}`);
    }
  }
}

class SerializationStream {
  pos = 0;
  buf = new Uint8Array(1024 * 1024);

  ensure(size: number) {
    if (this.buf.length - this.pos < size) {
      const tmp = new Uint8Array(this.buf.length * 1.5);
      tmp.set(this.buf);
      this.buf = tmp;
    }
  }

  writeByte(n: number) {
    this.ensure(1);
    this.buf[this.pos++] = n % 256;
  }

  writeVarint(n: number) {
    while (n > 127) {
      this.writeByte((n & 0x7f) | 0x80);
      n >>= 7;
    }
    this.writeByte(n & 0x7f);
  }

  writeSignedVarint(n: number) {
    const zigzag = (n << 1) ^ (n >> 31);
    this.writeVarint(zigzag);
  }

  writeString(s: string) {
    let data = te.encode(s);
    this.ensure(data.byteLength + 4);
    this.writeVarint(data.byteLength);
    this.buf.set(data, this.pos);
    this.pos += data.byteLength;
  }
  toUint8Array() {
    return this.buf.slice(0, this.pos);
  }
}

export class EncFile {
  poollen = 1;
  pool = new SerializationStream();
  buf = new SerializationStream();
  pmap: Record<string, number> = { "": 0 };

  static encode(data: any) {
    let f = new EncFile()
    f.write(data)
    f.pool.writeVarint(0)
    return f.toUint8Array()
  }

  writeString(s: string) {
    let n = this.pmap[s];
    if (n === undefined) {
      n = this.poollen++;
      this.pool.writeString(s);
      this.pmap[s] = n;
    }
    this.buf.writeVarint(n);
  }

  write(a: any) {
    // shouldn't happen?
    if (a == null) {
      this.buf.writeByte(NULL);
    } else if (a.tag == "_::_") {
      this.buf.writeByte(LIST);
      for (; a.tag === "_::_"; a = a.h2) {
        this.write(a.h1);
      }
      this.buf.writeByte(END);
    } else if (a.tag == "_,_") {
      this.buf.writeByte(TUPLE);
      for (; a.tag === "_,_"; a = a.h3) {
        this.write(a.h2);
      }
      this.write(a);
      this.buf.writeByte(END);
    } else if (typeof a === "string") {
      this.buf.writeByte(STRING);
      this.writeString(a);
    } else if (typeof a === "number") {
      this.buf.writeByte(NUMBER);
      this.buf.writeSignedVarint(a);
    } else if (a.tag) {
      this.buf.writeByte(INDUCT);
      this.writeString(a.tag);
      // we're actually missing a bunch of data here...
      // with null, hack is not needed.
      let i = 0
      for (; i <= 20; i++) {
        let key = 'h' + i
        let v = a[key]
        if (v === undefined) break
        this.write(v);
      }
      if (a['h' + (i + 1)] !== undefined) {
        throw new Error("BOOM")
      }
    this.buf.writeByte(END);
    } else {
      throw new Error(`handle ${typeof a} ${a} ${Object.keys(a)}`);
    }
  }
  toUint8Array() {
    const poolArray = this.pool.toUint8Array();
    const bufArray = this.buf.toUint8Array();
    const rval = new Uint8Array(poolArray.length + bufArray.length);
    // console.log('psize', poolArray.byteLength, poolArray.length)
    rval.set(poolArray);
    rval.set(bufArray, poolArray.length);
    return rval;
  }
}

function deepEqual(a: any, b: any): boolean {
  if (a === b) return true;
  if (typeof a !== typeof b) return false;
  if (a == null || b == null) return false;
  if (typeof a !== "object") return false;

  if (Array.isArray(a)) {
    if (!Array.isArray(b) || a.length !== b.length) return false;
    for (let i = 0; i < a.length; i++) {
      if (!deepEqual(a[i], b[i])) return false;
    }
    return true;
  }

  const keysA = Object.keys(a);
  const keysB = Object.keys(b);
  if (keysA.length !== keysB.length) return false;

  for (const key of keysA) {
    if (!deepEqual(a[key], b[key])) return false;
  }

  return true;
}
