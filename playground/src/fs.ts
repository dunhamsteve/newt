import {shim} from './emul';

// Shim was dumping stuff globally and we've shifted to imports, so I'm adapting it here for now.

export const {readFileSync, writeFileSync, writeFile, writeSync, readSync } = shim.fs;
export default {readFileSync, writeFileSync, writeFile, writeSync, readSync };
