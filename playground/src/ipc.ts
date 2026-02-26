
//// Copy of LSP types

export interface Location { uri: string; range: Range; }
export interface Position { line: number; character: number; }
export interface Range { start: Position; end: Position; }
export interface HoverResult { info: string; location: Location; }
export interface TextEdit { range: Range; newText: string; }
export type DiagnosticSeverity = 1 | 2 | 3 | 4
export interface DiagnosticRelatedInformation { location: Location; message: string; }
export interface Diagnostic {
    range: Range
    message: string
    severity?: DiagnosticSeverity
    source?: string
    // we don't emit this yet, but I think we will
    relatedInformation?: DiagnosticRelatedInformation[]
}

export interface WorkspaceEdit {
  changes?: {
    [uri: string]: TextEdit[];
  }
}

export interface CodeAction {
  title: string;
  edit?: WorkspaceEdit;
}

export interface BuildResult {
  diags: Diagnostic[]
  output: string
}

//// IPC Thinger

export type Result<A> =
  | { status: "ok"; value: A }
  | { status: "err"; error: string };

export interface API {
  // Invalidates stuff and writes to an internal cache that overlays the "filesystem"
  updateFile(fileName: string, content: string): unknown;
  // Run checking, return diagnostics
  typeCheck(fileName: string): BuildResult;
  // returns True if we need to recheck - usually for files invalidating other files
  // The playground rarely hits this situation at the moment
  hoverInfo(fileName: string, row: number, col: number): HoverResult | boolean | null;
  codeActionInfo(fileName: string, row: number, col: number): CodeAction[] | null;
  // we need to add this to the LSP build
  compile(fileName: string):  string;
}

export interface Message<K extends keyof API> {
  id: number;
  key: K;
  args: Parameters<API[K]>;
}

export interface ResponseMSG<K extends keyof API> {
  id: number;
  result: Awaited<ReturnType<API[K]>>;
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
    // But support for the frame needs to be fixed
    if (navigator.vendor.includes("Apple") && false) {
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
  onmessage = <K extends keyof API>(ev: MessageEvent<ResponseMSG<K>>) => {
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
