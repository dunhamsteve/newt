export type Result<A> =
  | { status: "ok"; value: A }
  | { status: "err"; error: string };

export interface API {
  save(fileName: string, content: string): string;
  typeCheck(fileName: string): string;
  compile(fileName: string): string;
}

export interface Message<K extends keyof API> {
  id: number;
  key: K;
  args: Parameters<API[K]>;
}

export interface ResponseMSG {
  id: number;
  result: string;
}

type Suspense = {
  resolve: (value: any | PromiseLike<any>) => void;
  reject: (reason?: any) => void;
};

export class IPC {
  callbacks: Record<number, Suspense> = {};
  _postMessage: <K extends keyof API>(msg: Message<K>) => void;
  lastID = 1;
  constructor() {
    const newtWorker = new Worker("worker.js");
    this._postMessage = <K extends keyof API>(msg: Message<K>) =>
      newtWorker.postMessage(msg);
    // Safari/MobileSafari have small stacks in webworkers.
    if (navigator.vendor.includes("Apple")) {
      const workerFrame = document.createElement("iframe");
      workerFrame.src = "worker.html";
      workerFrame.style.display = "none";
      document.body.appendChild(workerFrame);
      this._postMessage = (msg: any) =>
        workerFrame.contentWindow?.postMessage(msg, "*");
      window.addEventListener("message", (ev) => this.onmessage(ev));
    } else {
      newtWorker.onmessage = this.onmessage
    }
    // Need to handle messages from the other iframe too? Or at least ignore them.
  }
  onmessage = (ev: MessageEvent<ResponseMSG>) => {
    console.log("GET", ev.data);
    // Maybe key off of type
    if (ev.data.id) {
      let suspense = this.callbacks[ev.data.id];
      if (suspense) {
        suspense.resolve(ev.data.result);
        delete this.callbacks[ev.data.id];
      }
      console.log("result", ev.data, "suspense", suspense);
    }
  }
  async sendMessage<K extends keyof API>(
    key: K,
    args: Parameters<API[K]>
  ): Promise<ReturnType<API[K]>> {
    return new Promise((resolve, reject) => {
      let id = this.lastID++;
      this.callbacks[id] = { resolve, reject };
      console.log("POST", { id, key, args });
      this._postMessage({ id, key, args });
    });
  }
}

class IPCClient {}
