import test from "node:test";
import assert from "node:assert";
import { b64decode, b64encode } from "./base64.ts";

test("round trip", () => {
  for (let s of ["", "a", "aa", "aaa", "aaaa", "aaaaa", "aaaaaa"]) {
    let t = new TextEncoder().encode(s);
    console.log(t, t + "");
    let enc = b64encode(t);
    assert.equal(enc.length, Math.ceil((t.length * 8) / 6));
    assert.equal(b64decode(b64encode(t)) + "", t + "");
    console.log("---");
  }
});
