import { inflate } from "./inflate";


interface Entry {
  size: number;
  start: number;
  end: number;
  method: number;
}

export class ZipFile {
  data: Uint8Array;
  entries: Record<string, Entry>;
  constructor(data: Uint8Array) {
    this.data = data;
    this.entries = {};
    let td = new TextDecoder();
    let error = (msg: string) => {
      throw new Error(`${msg} at ${pos}`);
    };

    let view = new DataView(data.buffer);
    let pos = 0;
    while (pos < view.byteLength) {
      let sig = view.getUint32(pos, true);
      if (sig == 0x02014b50) break;
      if (sig != 0x04034b50) error(`bad sig ${sig.toString(16)}`);
      let method = view.getUint16(pos + 8, true);
      let csize = view.getUint32(pos + 18, true);
      let size = view.getUint32(pos + 22, true);
      let fnlen = view.getUint16(pos + 26, true);
      let eflen = view.getUint16(pos + 28, true);
      let fn = td.decode(data.slice(pos + 30, pos + 30 + fnlen));
      if (size) {
        let start = pos + 30 + fnlen + eflen;
        let end = start + csize;
        this.entries[fn] = { size, start, end, method };
      }
      pos = pos + 30 + fnlen + eflen + csize;
    }
  }
  getData(name: string) {
    let { start, end, size } = this.entries[name];
    return inflate(new Uint8Array(this.data.slice(start, end)));
  }
}

