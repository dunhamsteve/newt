import { Diagnostic } from "vscode-languageserver";

export function LSP_updateFile(name: string, content: string): (eta: any) => any;
export function LSP_checkFile(name: string): Diagnostic[];
export function LSP_hoverInfo(name: string, row: number, col: number): string|null;
