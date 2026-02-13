import { Diagnostic, Location } from "vscode-languageserver";

export function LSP_updateFile(name: string, content: string): (eta: any) => any;
export function LSP_checkFile(name: string): Diagnostic[];
interface HoverResult {
    info: string
    location: Location
}
export function LSP_hoverInfo(name: string, row: number, col: number): HoverResult|null;
