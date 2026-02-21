import { shim } from "./emul";
import { API, Message, ResponseMSG } from "./ipc";
import { archive, preload } from "./preload";
import { Main_main } from './newt';

const LOG = console.log

console.log = (m) => {
  LOG(m)
  shim.stdout += "\n" + m;
};

const handleMessage = async function <K extends keyof API>(ev: { data: Message<K> }) {
  LOG("HANDLE", ev.data);
  await preload;
  shim.archive = archive;
  let key = ev.data.key
  if (key === 'typeCheck' || key === 'compile') {
    let {id, args: [fileName]} = ev.data
    LOG(key, fileName)
    const outfile = "out.js";
    const isCompile = key === 'compile';
    if (isCompile)
      shim.process.argv = ["browser", "newt", fileName, "-o", outfile, "--top"];
    else
      shim.process.argv = ["browser", "newt", fileName, "--top"];
    shim.stdout = "";
    shim.files[outfile] = new TextEncoder().encode("No JS output");

    try {
      Main_main();
    } catch (e) {
      // make it clickable in console
      console.error(e);
      // make it visable on page
      shim.stdout += "\n" + String(e);
    }
    let result = isCompile ? new TextDecoder().decode(shim.files[outfile]) : shim.stdout
    sendResponse({id, result})
  } else if (key === 'save') {
    let {id, args: [fileName, content]} = ev.data
    LOG(`SAVE ${content?.length} to ${fileName}`)
    shim.files[fileName] = new TextEncoder().encode(content)
    LOG('send', {id, result: ''})
    sendResponse({id, result: ''})
  }

};

// hooks for worker.html to override
let sendResponse: <K extends keyof API>(_: ResponseMSG) => void = postMessage;
onmessage = handleMessage;
