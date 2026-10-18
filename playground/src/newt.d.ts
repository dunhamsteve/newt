import { Range, Diagnostic, HoverResult, CodeAction, Completion } from './ipc'

export function LSP_updateFile(name: string, content: string): any;
export function LSP_checkFile(name: string): Diagnostic[];
export function LSP_hoverInfo(name: string, row: number, col: number): HoverResult | boolean | null;
export function LSP_codeActionInfo(name: string, row: number, col: number): CodeAction[] | null;
export function LSP_compileJS(name: string): string;
export function LSP_compileToScheme(name: string): string;
export function LSP_completions(name: string, row: number, col: number): Completion[] | null;
export function LSP_lspRename(uri: string, row: number, col: number, newName: string): WorkspaceEdit | null
export function LSP_prepareRename(uri: string, row: number, col: number): Range | null

