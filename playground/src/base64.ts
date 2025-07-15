// tables
const i2c = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_";
const c2i: Record<string, number> = {};
i2c.split("").forEach((c, i) => (c2i[c] = i));

export function b64encode(data: Uint8Array): string {
  let rval = "";
  let i = 0;
  while (i < data.length) {
    let v = data[i++];
    // aaaaaa aa
    rval += i2c[v >> 2];
    // aabbbb bbbb
    v = ((v & 3) << 8) | data[i++];
    rval += i2c[v >> 4];
    if (i > data.length) break;
    // bbbbcc cccccc
    v = ((v & 15) << 8) | data[i++];
    rval += i2c[v >> 6];
    if (i > data.length) break;
    // cccccc
    rval += i2c[v & 63];
  }
  return rval;
}

export function b64decode(s: string) {
  let i = 0;
  let arr: number[] = [];
  while (i < s.length) {
    // aaaaaabb bbbb
    let acc = (c2i[s[i++]] << 6) | c2i[s[i++]];
    arr.push(acc >> 4);
    if (i >= s.length) break;
    // bbbbcccc cc
    acc = ((acc & 15) << 6) | c2i[s[i++]];
    arr.push(acc >> 2);
    if (i >= s.length) break;
    // ccdddddd
    acc = ((acc & 3) << 6) | c2i[s[i++]];
    arr.push(acc);
    if (i >= s.length) break;
  }
  return Uint8Array.from(arr);
}
