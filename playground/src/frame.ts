import { archive } from "./preload";
import { Message } from "./types";

// fs emulation for frame
const shim = {
  stdout: "",
  fs: {
    // made just for Node.newt...
    readFileSync(fn: string, encoding: string) {
      let data = archive?.getData(fn);
      if (data) {
        return new TextDecoder().decode(data);
      } else {
        throw new Error(`${fn} not found`);
      }
    },
  },
};
// we intercept require to return our fake node modules
declare global {
  interface Window {
    require: (x: string) => any;
  }
}
const requireStub: any = (x: string) => (shim as any)[x];
self.require = requireStub;
self.process = {
  platform: "linux",
  argv: ["", ""],
  stdout: {
    // We'll want to replace this one
    write(s) {
      console.log("*", s);
      shim.stdout += s;
    },
  },
  exit(v: number) {
    console.log("exit", v);
  },
  cwd() {
    return "";
  },
  env: {
    NO_COLOR: "true",
    IDRIS2_CG: "javascript",
    IDRIS2_PREFIX: "",
  },
  __lasterr: {
    errno: 0,
  },
  // stdin: { fd: 0 },
};
let realLog = console.log;
console.log = (...args) => {
  sendMessage({ type: "pushConsole", message: args.join(" ") });
  realLog(...args);
};

window.addEventListener("message", (ev: MessageEvent<Message>) => {
  realLog("got", ev.data);
  if (ev.data.type === "exec") {
    let { src } = ev.data;
    try {
      sendMessage({ type: "setConsole", messages: [] });
      (new Function(src))();
    } catch (e) {
      console.log(e);
    }
  }
});
const sendMessage = (msg: Message) => window.parent.postMessage(msg, "*");

realLog("IFRAME INITIALIZED");
if (shim) {
  realLog("shim imported for effect");
}
