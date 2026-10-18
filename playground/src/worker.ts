import { shim } from "./emul";
import { API, Message, Range, ResponseMSG, WorkspaceEdit } from "./ipc";
import { archive, preload } from "./preload";
import { LSP_checkFile, LSP_codeActionInfo, LSP_compileJS, LSP_compileToScheme, LSP_hoverInfo, LSP_lspRename, LSP_prepareRename, LSP_updateFile } from './newt';
import { LSP_completions } from "./newt";

const LOG = console.log

// console.log = (m) => {
//   LOG(m)
//   shim.stdout += "\n" + m;
// };

const invoke = <T extends (...args: any[]) => any>(fun:T, args: Parameters<T>): ReturnType<T> => {
  return fun.apply(undefined, args)
}

const api: API = {
    // none of these are promises...
    updateFile: LSP_updateFile,
    typeCheck(filename) {
        shim.stdout = "";
        let diags = LSP_checkFile(filename);
        let output = shim.stdout;
        return { diags, output };
    },
    hoverInfo: LSP_hoverInfo,
    codeActionInfo: LSP_codeActionInfo,
    compile: (fn, lang) => {
        if (lang == 'scheme') return LSP_compileToScheme(fn);
        return LSP_compileJS(fn);
    },
    completions: (fn, row, col) => {
        console.log('RUN', fn, row, col);
        return LSP_completions(fn, row, col);
    },
    prepareRename: (filename: string, row: number, col: number): Range | null => {
        return LSP_prepareRename(filename, row, col)
    },
    lspRename: function(filename: string, row: number, col: number, newName: string): WorkspaceEdit | null {
      return LSP_lspRename(filename, row, col, newName);
    }
}

const handleMessage = async function <K extends keyof API>(ev: { data: Message<K> }) {
  LOG("HANDLE", ev.data);
  await preload;
  shim.archive = archive;
  try {
    shim.stdout = ''
    let {id, key, args} = ev.data
    let result = await invoke(api[key], args)
    LOG('got', result)
    sendResponse<typeof key>({id, result})
  } catch (e) {
    console.error(e)
  }
  console.log(shim.stdout)

};

// hooks for worker.html to override
let sendResponse: <K extends keyof API>(_: ResponseMSG<K>) => void = postMessage;
onmessage = handleMessage;
