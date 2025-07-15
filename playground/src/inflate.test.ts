
import test from "node:test";
import assert from "node:assert";
import { readFileSync } from "node:fs";
import { deflate } from "./deflate.ts";
import { inflate } from "./inflate.ts";
import { b64encode } from "./base64.ts";


test('round trip', ()=>{
  let src = readFileSync('src/inflate.ts','utf8')
  let smol = deflate(new TextEncoder().encode(src))
  let big = inflate(smol)
  assert.equal(src, new TextDecoder().decode(big))
  console.log(src.length, smol.length, b64encode(smol).length)
})
