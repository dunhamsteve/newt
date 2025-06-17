import { shim } from "./emul";
import { archive, preload } from "./preload";
import { CompileReq, CompileRes } from "./types";

console.log = (m) => {
  shim.stdout += '\n' + m
}

const handleMessage = async function (ev: { data: CompileReq }) {
  console.log("message", ev.data);
  await preload;
  shim.archive = archive;
  let { id, src, fileName } = ev.data;
  const outfile = "out.js";
  shim.process.argv = ["browser", "newt", fileName, "-o", outfile, "--top"];
  shim.files[fileName] = new TextEncoder().encode(src);
  shim.files[outfile] = new TextEncoder().encode("No JS output");
  shim.stdout = "";
  const start = +new Date();
  try {
    Main_main();
  } catch (e) {
    // make it clickable in console
    console.error(e);
    // make it visable on page
    shim.stdout += "\n" + String(e);
  }
  let duration = +new Date() - start;
  console.log(`process ${fileName} in ${duration} ms`);
  let javascript = new TextDecoder().decode(shim.files[outfile]);
  let output = shim.stdout;
  sendResponse({ id, type: 'compileResult', javascript, output, duration });
};

// hooks for worker.html to override
let sendResponse: (_: CompileRes) => void = postMessage;
onmessage = handleMessage;
importScripts("newt.js");
