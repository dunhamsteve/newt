import { CodeAction, Diagnostic, DocumentSymbol, Location, Range, WorkspaceEdit } from "vscode-languageserver";

export function LSP_updateFile(name: string, content: string): (eta: any) => any;
export function LSP_checkFile(name: string): Diagnostic[];
interface HoverResult {
    info: string
    location: Location
}
export function LSP_hoverInfo(name: string, row: number, col: number): HoverResult|boolean|null;
export function LSP_codeActionInfo(name: string, row: number, col: number): CodeAction[]|null;
export function LSP_docSymbols(name: string): DocumentSymbol[] | null;
export function LSP_lspRename(uri: string, row: number, col: number, newName: string): WorkspaceEdit | null
export function LSP_prepareRename(uri: string, row: number, col: number): Range | null
export function LSP_findReferences(uri: string, row: number, col: number): Location[] | null
