import { shim } from "./emul";
import { archive, preload } from "./preload";
import { CompileReq, CompileRes } from "./types";

const handleMessage = async function (ev: { data: CompileReq }) {
  console.log("message", ev.data);
  await preload;
  shim.archive = archive;
  let { src } = ev.data;
  let module = "Main";
  let m = src.match(/module (\w+)/);
  if (m) module = m[1];
  let fn = `${module}.newt`;
  const outfile = "out.js";
  shim.process.argv = ["", "", fn, "-o", outfile, "--top"];
  console.log("Using args", shim.process.argv);
  shim.files[fn] = new TextEncoder().encode(src);
  shim.files[outfile] = new TextEncoder().encode("No JS output");
  shim.stdout = "";
  const start = +new Date();
  try {
    newtMain();
  } catch (e) {
    // make it clickable in console
    console.error(e);
    // make it visable on page
    shim.stdout += "\n" + String(e);
  }
  let duration = +new Date() - start;
  console.log(`process ${fn} in ${duration} ms`);
  let javascript = new TextDecoder().decode(shim.files[outfile]);
  let output = shim.stdout;
  sendResponse({ javascript, output, duration });
};

// hooks for worker.html to override
let sendResponse: (_: CompileRes) => void = postMessage;
onmessage = handleMessage;
importScripts("newt.js");
