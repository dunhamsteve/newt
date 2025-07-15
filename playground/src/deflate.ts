// This is a minimal deflate implementation.
//
// It writes data that zlib can decompress, but sticks to the built-in huffman tables
// and a simple search heuristic to keep the code size down.
//
// TODO
// - initialize offsets to something other than zero (MAXINT32)
// - offsets are all wrong.

const maxMatchOffset  = 1 << 14
const tableSize = 1 << 14
const lengthExtra = [0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0];
const distExtra = [0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13];
const lengthCode : number[] = []
const lengthBase : number[] = []
const distCode : number[] = [];
const distBase : number[] = [];

(function() {
    // see trees.c
    let code
    let length = 0
    for (code = 0; code < 28; code++) {
        lengthBase[code] = length;
        for (let n = 0; n < (1<<lengthExtra[code]); n++) {
            lengthCode[length++] = code
        }
    }
    lengthCode[length-1] = code

    // Initialize the mapping dist (0..32K) -> dist code (0..29)
    let dist = 0;
    for (code = 0 ; code < 16; code++) {
        distBase[code] = dist;
        for (let n = 0; n < (1<<distExtra[code]); n++) {
            distCode[dist++] = code;
        }
    }
    dist >>= 7; // from now on, all distances are divided by 128
    for ( ; code < 30; code++) {
        distBase[code] = dist << 7;
        for (let n = 0; n < (1<<(distExtra[code]-7)); n++) {
            distCode[256 + dist] = code;
            dist++
        }
    }
})()

export function deflate(buf: Uint8Array, raw = true) {
    let bitpos = 0
    let out = new Uint8Array(65536)
    function write(bits: number,value:number,backwards?: boolean) {
        for (let i = 0;i < bits;i++) {
            const bytepos = bitpos >> 3
            const mask = 1 << (bitpos&7)
            if (bytepos + 10 > out.length) {
                const tmp = new Uint8Array(out.length*1.5)
                tmp.set(out)
                out = tmp
            }
            let j = backwards ? i : bits - i - 1
            if (value & (1 << j)) out[bytepos] |= mask
            bitpos++
        }
    }

    function emit(value: number) {
        if (value < 144)      write(8, 48+value)
        else if (value < 256) write(9, value-144+400)
        else if (value < 280) write(7, value-256)
        else                  write(8, value-280+192)
    }
    if (!raw) {
        write(8,0x78,true)
        write(8,0x9c,true)
    }
    write(1,1)
    write(2,2)

    const src = new DataView(buf.buffer)

    const hash = (u:number) => (u * 0x1e35a7bd) >>> 18 // top 14 bits
    const values = new Int32Array(tableSize)
    const offsets = new Int32Array(tableSize)
    const sLimit = buf.length - 3

    let s = 0
    let nextEmit = 0
    while ( s < sLimit) {
        let cur_val = src.getUint32(s, true)
        let cur_hash = hash(cur_val)
        const cand_val = values[cur_hash]
        const cand_off = offsets[cur_hash]
        offsets[cur_hash] = s
        values[cur_hash] = cur_val

        let offset = s - cand_off
        if (0 < offset && offset < maxMatchOffset && cur_val == cand_val) {
            for (;nextEmit<s;nextEmit++) emit(buf[nextEmit])
            s += 4
            let t = cand_off + 4
            let l = 0
            while (s+l < buf.length && buf[s+l] === buf[t+l] && l<255) l++
            const l_code = lengthCode[l+1]
            emit(l_code+257)
            write(lengthExtra[l_code],l + 1 - lengthBase[l_code],true)

            const d_code = (offset<257) ? distCode[offset-1] : distCode[256+((offset-1)>>7)]
            write(5,d_code)
            write(distExtra[d_code],offset-1-distBase[d_code],true)
            s += l
            nextEmit = s
        } else {
            s++
        }
    }
    for (;nextEmit<buf.length;nextEmit++) emit(buf[nextEmit])
    emit(256)
    
    let adler = 1
    let s2 = 0
    for (let i=0;i<buf.length;i++) {
        adler = (adler + buf[i] % 65521)
        s2 = (s2 + adler) % 65521
    }
    adler |= (s2 << 16)
    let len = 1 + (bitpos >> 3)
    if (raw) return out.slice(0,len)
    new DataView(out.buffer).setInt32(len,adler,false)
    return out.slice(0, len+4)
}
