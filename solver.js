'use strict';

// Kesto solver.
//
// Board: 8x8. Every move (U/D/L/R) pushes ALL blocks one cell in that direction.
// A block that is blocked (wall, board edge, or a blocked block in front of it)
// stays put. The puzzle is solved when every block sits on a target.
//
// State = two signed 32-bit ints (lo = rows 0-3, hi = rows 4-7, one byte per row,
// bit c of a row byte = column c), which matches the old 64-bit bitboard layout
// (cell index = row * 8 + column).

const INF = 10000;
const EXACT_TIME_SHARE = 0.8;           // share of the time limit given to the exact search
const BEAM_WIDTHS = [1500, 6000, 24000, 96000];
const BEAM_MAX_DEPTH = 256;
const BEAM_DIR_ORDER = [1, 3, 0, 2];
const DIR_CHARS = ['U', 'D', 'L', 'R'];  // 0 = up, 1 = down, 2 = left, 3 = right

const packLo = (b) => (b[0] | (b[1] << 8) | (b[2] << 16) | (b[3] << 24)) | 0;
const packHi = (b) => (b[4] | (b[5] << 8) | (b[6] << 16) | (b[7] << 24)) | 0;

function popcountByte(x) {
    let n = 0;
    while (x) { n += x & 1; x >>= 1; }
    return n;
}

// One line of 8 cells moving toward lower (dir 2) or higher (dir 3) indices.
function stepLineBits(bits, walls, dir) {
    let moving = bits & ~walls;

    for (let iter = 0; iter < 8; iter++) {
        let blocked = 0;
        const stationary = bits ^ moving;

        for (let i = 0; i < 8; i++) {
            const bit = 1 << i;
            if ((moving & bit) === 0) continue;

            const next = dir === 2 ? i - 1 : i + 1;
            if (next < 0 || next >= 8) {
                blocked |= bit;
                continue;
            }

            const nextBit = 1 << next;
            if ((walls & nextBit) || (stationary & nextBit)) {
                blocked |= bit;
            }
        }

        if (blocked === 0) break;
        moving ^= blocked;
    }

    let out = bits ^ moving;
    for (let i = 0; i < 8; i++) {
        const bit = 1 << i;
        if ((moving & bit) === 0) continue;
        out |= 1 << (dir === 2 ? i - 1 : i + 1);
    }

    return out & 0xff;
}

// Lookup tables are built lazily, only for the wall patterns a board really uses.
const FORWARD_CACHE = [null, null, new Array(256).fill(null), new Array(256).fill(null)];
const REVERSE_CACHE = [null, null, new Array(256).fill(null), new Array(256).fill(null)];
let COLUMN_LO = null;
let COLUMN_HI = null;

function getForwardTable(dir, wall) {
    let table = FORWARD_CACHE[dir][wall];
    if (!table) {
        table = new Uint8Array(256);
        for (let bits = 0; bits < 256; bits++) {
            table[bits] = (bits & wall) ? bits : stepLineBits(bits, wall, dir);
        }
        FORWARD_CACHE[dir][wall] = table;
    }
    return table;
}

// reverse[result] = every line content that moves into `result`.
function getReverseTable(dir, wall) {
    let table = REVERSE_CACHE[dir][wall];
    if (!table) {
        table = Array.from({ length: 256 }, () => []);
        for (let bits = 0; bits < 256; bits++) {
            if (bits & wall) continue;
            table[stepLineBits(bits, wall, dir)].push(bits);
        }
        REVERSE_CACHE[dir][wall] = table;
    }
    return table;
}

// COLUMN_LO[c][mask] / COLUMN_HI[c][mask] = the board bits (as lo/hi words)
// of a column-c line whose row r is set when bit r of `mask` is set.
function getColumnTables() {
    if (!COLUMN_LO) {
        COLUMN_LO = [];
        COLUMN_HI = [];
        for (let c = 0; c < 8; c++) {
            const lo = new Int32Array(256);
            const hi = new Int32Array(256);
            for (let mask = 0; mask < 256; mask++) {
                let l = 0;
                let h = 0;
                for (let r = 0; r < 8; r++) {
                    if ((mask & (1 << r)) === 0) continue;
                    const bit = r * 8 + c;
                    if (bit < 32) l |= 1 << bit;
                    else h |= 1 << (bit - 32);
                }
                lo[mask] = l;
                hi[mask] = h;
            }
            COLUMN_LO.push(lo);
            COLUMN_HI.push(hi);
        }
    }
    return { lo: COLUMN_LO, hi: COLUMN_HI };
}

// Compact store of visited states with parent links and an open-addressing index.
// The index table stores [lo, hi, id + 1] together, so a lookup touches a single
// cache line instead of three scattered arrays (id + 1 === 0 marks an empty slot).
class StateStore {
    constructor(initialLog2 = 16) {
        this.cap = 1 << initialLog2;
        this.size = 0;
        this.lo = new Int32Array(this.cap);
        this.hi = new Int32Array(this.cap);
        this.parent = new Int32Array(this.cap);
        this.dir = new Uint8Array(this.cap);
        this.depth = new Uint16Array(this.cap);
        this.slots = this.cap * 2;
        this.mask = this.slots - 1;
        this.limit = Math.floor(this.slots * 0.7);
        this.table = new Int32Array(this.slots * 3);
    }

    hash(lo, hi) {
        let h = Math.imul(lo, 0x9E3779B1) ^ Math.imul(hi ^ (hi >>> 15), 0x85EBCA6B);
        h ^= h >>> 16;
        h = Math.imul(h, 0x7FEB352D);
        h ^= h >>> 15;
        return h & this.mask;
    }

    find(lo, hi) {
        const table = this.table;
        let slot = this.hash(lo, hi);
        while (true) {
            const t = slot * 3;
            const id = table[t + 2];
            if (id === 0) return -1;
            if (table[t] === lo && table[t + 1] === hi) return id - 1;
            slot = (slot + 1) & this.mask;
        }
    }

    // The caller guarantees the state is not stored yet.
    add(lo, hi, parent, dir, depth) {
        if (this.size === this.cap) this.growArrays();
        if (this.size + 1 > this.limit) this.growTable();
        const i = this.size++;
        this.lo[i] = lo;
        this.hi[i] = hi;
        this.parent[i] = parent;
        this.dir[i] = dir;
        this.depth[i] = depth;
        this.insert(lo, hi, i + 1);
        return i;
    }

    insert(lo, hi, idPlusOne) {
        const table = this.table;
        let slot = this.hash(lo, hi);
        while (table[slot * 3 + 2] !== 0) slot = (slot + 1) & this.mask;
        const t = slot * 3;
        table[t] = lo;
        table[t + 1] = hi;
        table[t + 2] = idPlusOne;
    }

    growArrays() {
        this.cap *= 2;
        const grown = (Type, old) => { const a = new Type(this.cap); a.set(old); return a; };
        this.lo = grown(Int32Array, this.lo);
        this.hi = grown(Int32Array, this.hi);
        this.parent = grown(Int32Array, this.parent);
        this.dir = grown(Uint8Array, this.dir);
        this.depth = grown(Uint16Array, this.depth);
    }

    growTable() {
        const old = this.table;
        this.slots *= 2;
        this.mask = this.slots - 1;
        this.limit = Math.floor(this.slots * 0.7);
        this.table = new Int32Array(this.slots * 3);
        for (let t = 0; t < old.length; t += 3) {
            if (old[t + 2] !== 0) this.insert(old[t], old[t + 1], old[t + 2]);
        }
    }
}

// Open-addressing set of states with their BFS depth. A state is stored as a
// (lo, hi) pair and the all-zero pair marks an empty slot (a real state always
// holds at least one block). About 10 bytes per slot, no parent pointers: paths
// are rebuilt from the depth labels.
class DepthSet {
    constructor(initialLog2 = 16) {
        this.slots = 1 << initialLog2;
        this.mask = this.slots - 1;
        this.limit = Math.floor(this.slots * 0.75);
        this.keys = new Int32Array(this.slots * 2);
        this.depth = new Uint16Array(this.slots);
        this.count = 0;
    }

    hash(lo, hi) {
        let h = Math.imul(lo, 0x9E3779B1) ^ Math.imul(hi ^ (hi >>> 15), 0x85EBCA6B);
        h ^= h >>> 16;
        h = Math.imul(h, 0x7FEB352D);
        h ^= h >>> 15;
        return h & this.mask;
    }

    // Depth of the state, or -1 when it is not in the set.
    get(lo, hi) {
        const keys = this.keys;
        let slot = this.hash(lo, hi);
        while (true) {
            const t = slot * 2;
            const a = keys[t];
            const b = keys[t + 1];
            if (a === 0 && b === 0) return -1;
            if (a === lo && b === hi) return this.depth[slot];
            slot = (slot + 1) & this.mask;
        }
    }

    // Adds the state when it is new and returns -1; otherwise returns the stored depth.
    insert(lo, hi, depth) {
        if (this.count >= this.limit) this.grow();
        const keys = this.keys;
        let slot = this.hash(lo, hi);
        while (true) {
            const t = slot * 2;
            const a = keys[t];
            const b = keys[t + 1];
            if (a === 0 && b === 0) {
                keys[t] = lo;
                keys[t + 1] = hi;
                this.depth[slot] = depth;
                this.count++;
                return -1;
            }
            if (a === lo && b === hi) return this.depth[slot];
            slot = (slot + 1) & this.mask;
        }
    }

    grow() {
        const oldKeys = this.keys;
        const oldDepth = this.depth;
        this.slots *= 2;
        this.mask = this.slots - 1;
        this.limit = Math.floor(this.slots * 0.75);
        this.keys = new Int32Array(this.slots * 2);
        this.depth = new Uint16Array(this.slots);
        const keys = this.keys;
        for (let s = 0; s < oldDepth.length; s++) {
            const lo = oldKeys[2 * s];
            const hi = oldKeys[2 * s + 1];
            if (lo === 0 && hi === 0) continue;
            let slot = this.hash(lo, hi);
            while (keys[2 * slot] !== 0 || keys[2 * slot + 1] !== 0) slot = (slot + 1) & this.mask;
            keys[2 * slot] = lo;
            keys[2 * slot + 1] = hi;
            this.depth[slot] = oldDepth[s];
        }
    }
}

// Growable list of (lo, hi) pairs: one BFS level.
class PairList {
    constructor(capacity = 1024) {
        this.buf = new Int32Array(capacity * 2);
        this.n = 0;
    }

    push(lo, hi) {
        if (this.n * 2 + 2 > this.buf.length) {
            const bigger = new Int32Array(this.buf.length * 2);
            bigger.set(this.buf);
            this.buf = bigger;
        }
        this.buf[this.n * 2] = lo;
        this.buf[this.n * 2 + 1] = hi;
        this.n++;
    }
}

class Solver {
    constructor(bgGrid, fgGrid) {
        this.bgGrid = bgGrid;
        this.fgGrid = fgGrid;

        this.rowWalls = new Uint8Array(8);
        this.colWalls = new Uint8Array(8);
        this.rowTargets = new Uint8Array(8);
        this.rowBlocks = new Uint8Array(8);
        for (let r = 0; r < 8; r++) {
            for (let c = 0; c < 8; c++) {
                if (bgGrid[r][c] === '#') {
                    this.rowWalls[r] |= 1 << c;
                    this.colWalls[c] |= 1 << r;
                }
                if (bgGrid[r][c] === 'T') this.rowTargets[r] |= 1 << c;
                if (fgGrid[r][c] === 'Y') this.rowBlocks[r] |= 1 << c;
            }
        }

        this.startLo = packLo(this.rowBlocks);
        this.startHi = packHi(this.rowBlocks);
        this.goalLo = packLo(this.rowTargets);
        this.goalHi = packHi(this.rowTargets);
        this.blockCount = 0;
        this.targetCount = 0;
        for (let r = 0; r < 8; r++) {
            this.blockCount += popcountByte(this.rowBlocks[r]);
            this.targetCount += popcountByte(this.rowTargets[r]);
        }

        this.fwdL = [];
        this.fwdR = [];
        this.revRows = [null, null, [], []];
        this.revCols = [null, null, [], []];
        for (let r = 0; r < 8; r++) {
            this.fwdL.push(getForwardTable(2, this.rowWalls[r]));
            this.fwdR.push(getForwardTable(3, this.rowWalls[r]));
            this.revRows[2].push(getReverseTable(2, this.rowWalls[r]));
            this.revRows[3].push(getReverseTable(3, this.rowWalls[r]));
        }
        for (let c = 0; c < 8; c++) {
            this.revCols[2].push(getReverseTable(2, this.colWalls[c]));
            this.revCols[3].push(getReverseTable(3, this.colWalls[c]));
        }
        const columnTables = getColumnTables();
        this.colLo = columnTables.lo;
        this.colHi = columnTables.hi;

        // scratch space
        this.rows = new Uint8Array(8);
        this.cols = new Uint8Array(8);
        this.out = new Uint8Array(8);
        this.stuck = new Uint8Array(8);
        this.lists = new Array(8);
        this.lens = new Int32Array(8);
        this.idx = new Int32Array(8);
        this.predBuf = new Int32Array(1 << 12);
        this.nlo = 0;
        this.nhi = 0;

        this.initDistances();
    }

    // dist[cell] = fewest single steps from the cell to the nearest target (walls respected).
    initDistances() {
        this.dist = new Int32Array(64).fill(INF);
        const queue = [];
        for (let r = 0; r < 8; r++) {
            for (let c = 0; c < 8; c++) {
                if (this.rowTargets[r] & (1 << c)) {
                    this.dist[r * 8 + c] = 0;
                    queue.push(r * 8 + c);
                }
            }
        }
        for (let head = 0; head < queue.length; head++) {
            const cur = queue[head];
            const r = cur >> 3;
            const c = cur & 7;
            const next = this.dist[cur] + 1;
            const neighbours = [];
            if (r > 0) neighbours.push(cur - 8);
            if (r < 7) neighbours.push(cur + 8);
            if (c > 0) neighbours.push(cur - 1);
            if (c < 7) neighbours.push(cur + 1);
            for (const n of neighbours) {
                if (this.rowWalls[n >> 3] & (1 << (n & 7))) continue;
                if (this.dist[n] <= next) continue;
                this.dist[n] = next;
                queue.push(n);
            }
        }
    }

    fail(message) {
        return { success: false, message, path: [], states: [] };
    }

    // Returns an error message when the board can never be solved, otherwise null.
    validate() {
        for (let r = 0; r < 8; r++) {
            if (this.rowBlocks[r] & this.rowWalls[r]) return 'Invalid board: a block is placed inside a wall.';
        }

        if (this.blockCount !== this.targetCount) {
            const blockWord = this.blockCount === 1 ? 'block' : 'blocks';
            const targetWord = this.targetCount === 1 ? 'target' : 'targets';
            return `Unsolvable: target count must equal block count (${this.blockCount} ${blockWord}, ${this.targetCount} ${targetWord}).`;
        }

        // Blocks can never leave the connected region they start in, so every
        // region needs exactly as many targets as blocks.
        const seen = new Uint8Array(64);
        for (let s = 0; s < 64; s++) {
            if (seen[s] || (this.rowWalls[s >> 3] & (1 << (s & 7)))) continue;
            let blocks = 0;
            let targets = 0;
            const stack = [s];
            seen[s] = 1;
            while (stack.length > 0) {
                const cur = stack.pop();
                const r = cur >> 3;
                const c = cur & 7;
                if (this.rowBlocks[r] & (1 << c)) blocks++;
                if (this.rowTargets[r] & (1 << c)) targets++;
                const neighbours = [];
                if (r > 0) neighbours.push(cur - 8);
                if (r < 7) neighbours.push(cur + 8);
                if (c > 0) neighbours.push(cur - 1);
                if (c < 7) neighbours.push(cur + 1);
                for (const n of neighbours) {
                    if (seen[n] || (this.rowWalls[n >> 3] & (1 << (n & 7)))) continue;
                    seen[n] = 1;
                    stack.push(n);
                }
            }
            if (blocks !== targets) {
                return `Unsolvable: a region walled off from the rest has ${blocks} ${blocks === 1 ? 'block' : 'blocks'} but ${targets} ${targets === 1 ? 'target' : 'targets'}.`;
            }
        }
        return null;
    }

    unpack(lo, hi) {
        const rows = this.rows;
        rows[0] = lo & 255;
        rows[1] = (lo >>> 8) & 255;
        rows[2] = (lo >>> 16) & 255;
        rows[3] = lo >>> 24;
        rows[4] = hi & 255;
        rows[5] = (hi >>> 8) & 255;
        rows[6] = (hi >>> 16) & 255;
        rows[7] = hi >>> 24;
    }

    // One move of every block. The result is left in this.nlo / this.nhi.
    move(lo, hi, dir) {
        this.unpack(lo, hi);
        const rows = this.rows;
        const out = this.out;

        if (dir === 2) {
            for (let r = 0; r < 8; r++) out[r] = this.fwdL[r][rows[r]];
        } else if (dir === 3) {
            for (let r = 0; r < 8; r++) out[r] = this.fwdR[r][rows[r]];
        } else {
            // Up/down: all 8 columns at once, one pass over the rows. A block is
            // stuck when the cell ahead is a wall or holds a stuck block.
            const stuck = this.stuck;
            const walls = this.rowWalls;
            if (dir === 0) {
                stuck[0] = rows[0];
                for (let r = 1; r < 8; r++) stuck[r] = rows[r] & (walls[r - 1] | stuck[r - 1]);
                for (let r = 0; r < 7; r++) out[r] = stuck[r] | (rows[r + 1] & ~stuck[r + 1]);
                out[7] = stuck[7];
            } else {
                stuck[7] = rows[7];
                for (let r = 6; r >= 0; r--) stuck[r] = rows[r] & (walls[r + 1] | stuck[r + 1]);
                for (let r = 1; r < 8; r++) out[r] = stuck[r] | (rows[r - 1] & ~stuck[r - 1]);
                out[0] = stuck[0];
            }
        }

        this.nlo = packLo(out);
        this.nhi = packHi(out);
    }

    // Fills this.predBuf with every state P where move(P, dir) equals the state in
    // this.rows / this.cols. Returns the count, or -1 when it would exceed `limit`.
    fillPredecessors(dir, limit) {
        const lists = this.lists;
        const lens = this.lens;
        const idx = this.idx;
        let total = 1;

        if (dir >= 2) {
            for (let r = 0; r < 8; r++) {
                const list = this.revRows[dir][r][this.rows[r]];
                if (list.length === 0) return 0;
                lists[r] = list;
                lens[r] = list.length;
                total *= list.length;
            }
        } else {
            const lineDir = dir === 0 ? 2 : 3;
            for (let c = 0; c < 8; c++) {
                const list = this.revCols[lineDir][c][this.cols[c]];
                if (list.length === 0) return 0;
                lists[c] = list;
                lens[c] = list.length;
                total *= list.length;
            }
        }

        if (total > limit) return -1;
        if (this.predBuf.length < total * 2) {
            let size = this.predBuf.length;
            while (size < total * 2) size *= 2;
            this.predBuf = new Int32Array(size);
        }
        const buf = this.predBuf;
        idx.fill(0);

        for (let k = 0; k < total; k++) {
            let lo;
            let hi;
            if (dir >= 2) {
                lo = lists[0][idx[0]] | (lists[1][idx[1]] << 8) | (lists[2][idx[2]] << 16) | (lists[3][idx[3]] << 24);
                hi = lists[4][idx[4]] | (lists[5][idx[5]] << 8) | (lists[6][idx[6]] << 16) | (lists[7][idx[7]] << 24);
            } else {
                lo = 0;
                hi = 0;
                for (let c = 0; c < 8; c++) {
                    const mask = lists[c][idx[c]];
                    lo |= this.colLo[c][mask];
                    hi |= this.colHi[c][mask];
                }
            }
            buf[2 * k] = lo | 0;
            buf[2 * k + 1] = hi | 0;

            let p = 7;
            while (p >= 0) {
                if (++idx[p] < lens[p]) break;
                idx[p] = 0;
                p--;
            }
        }
        return total;
    }

    prepareColumns() {
        for (let c = 0; c < 8; c++) {
            let m = 0;
            for (let r = 0; r < 8; r++) m |= ((this.rows[r] >> c) & 1) << r;
            this.cols[c] = m;
        }
    }

    toBigInt(lo, hi) {
        return (BigInt(hi >>> 0) << 32n) | BigInt(lo >>> 0);
    }

    // Replays `dirs` from the start, checks it ends on the goal, and builds the result object.
    makeResult(dirs, message) {
        let lo = this.startLo;
        let hi = this.startHi;
        const states = [this.toBigInt(lo, hi)];
        for (let i = 0; i < dirs.length; i++) {
            this.move(lo, hi, dirs[i]);
            lo = this.nlo;
            hi = this.nhi;
            states.push(this.toBigInt(lo, hi));
        }
        if (lo !== this.goalLo || hi !== this.goalHi) {
            return this.fail('Internal error: the reconstructed path does not reach the targets.');
        }
        return {
            success: true,
            message: message || `Solution in ${dirs.length} steps`,
            path: dirs.map((d) => DIR_CHARS[d]),
            states
        };
    }

    // Number of states that move into the state currently held in this.rows / this.cols,
    // for one direction (the size of the list fillPredecessors would produce).
    countPredecessors(dir) {
        let total = 1;
        if (dir >= 2) {
            for (let r = 0; r < 8; r++) {
                const len = this.revRows[dir][r][this.rows[r]].length;
                if (len === 0) return 0;
                total *= len;
            }
        } else {
            const lineDir = dir === 0 ? 2 : 3;
            for (let c = 0; c < 8; c++) {
                const len = this.revCols[lineDir][c][this.cols[c]].length;
                if (len === 0) return 0;
                total *= len;
            }
        }
        return total;
    }

    // Candidates a backward step over `front` would generate (counting stops once it passes `cap`).
    backwardLevelCost(front, cap) {
        let total = 0;
        for (let i = 0; i < front.n; i++) {
            this.unpack(front.buf[2 * i], front.buf[2 * i + 1]);
            this.prepareColumns();
            for (let d = 0; d < 4; d++) total += this.countPredecessors(d);
            if (total > cap) return total;
        }
        return total;
    }

    // Exact search: level-by-level BFS from the start and, in reverse, from the goal.
    // Each round expands the side whose next level is cheaper to generate, counted in
    // candidate states. Going backwards can branch into thousands of predecessors per
    // state while going forwards is at most 4, so the cheaper side is often the start.
    // Returns { done: true, result } or { done: false, reason: 'time' | 'states', stats }.
    solveBidirectional(deadline, maxStates) {
        const F = new DepthSet();
        const B = new DepthSet();
        F.insert(this.startLo, this.startHi, 0);
        B.insert(this.goalLo, this.goalHi, 0);

        let fFront = new PairList();
        let bFront = new PairList();
        fFront.push(this.startLo, this.startHi);
        bFront.push(this.goalLo, this.goalHi);
        let fDepth = 0;
        let bDepth = 0;

        let bestLen = Infinity;
        let bestLo = 0;
        let bestHi = 0;
        let bestF = 0;
        let bestB = 0;

        const stop = (reason) => ({
            done: false,
            reason,
            stats: { forwardDepth: fDepth, backwardDepth: bDepth, states: F.count + B.count }
        });

        while (fFront.n > 0 && bFront.n > 0) {
            // A path that has not been seen yet is at least fDepth + bDepth + 1 long.
            if (bestLen !== Infinity && fDepth + bDepth + 1 >= bestLen) break;
            if (Date.now() > deadline) return stop('time');
            if (F.count + B.count > maxStates) return stop('states');

            const forwardCost = fFront.n * 4;
            const backwardCost = this.backwardLevelCost(bFront, forwardCost);

            if (forwardCost <= backwardCost) {
                const nextDepth = fDepth + 1;
                const next = new PairList();
                for (let i = 0; i < fFront.n; i++) {
                    const lo = fFront.buf[2 * i];
                    const hi = fFront.buf[2 * i + 1];
                    for (let d = 0; d < 4; d++) {
                        this.move(lo, hi, d);
                        const nlo = this.nlo;
                        const nhi = this.nhi;
                        if (nlo === lo && nhi === hi) continue;
                        if (F.insert(nlo, nhi, nextDepth) !== -1) continue;
                        next.push(nlo, nhi);
                        const other = B.get(nlo, nhi);
                        if (other !== -1 && nextDepth + other < bestLen) {
                            bestLen = nextDepth + other;
                            bestLo = nlo; bestHi = nhi; bestF = nextDepth; bestB = other;
                        }
                    }
                    if ((i & 1023) === 1023) {
                        if (Date.now() > deadline) return stop('time');
                        if (F.count + B.count > maxStates) return stop('states');
                    }
                }
                fFront = next;
                fDepth = nextDepth;
            } else {
                const nextDepth = bDepth + 1;
                const next = new PairList();
                for (let i = 0; i < bFront.n; i++) {
                    const lo = bFront.buf[2 * i];
                    const hi = bFront.buf[2 * i + 1];
                    this.unpack(lo, hi);
                    this.prepareColumns();
                    for (let d = 0; d < 4; d++) {
                        const count = this.fillPredecessors(d, maxStates - (F.count + B.count));
                        if (count < 0) return stop('states');
                        const buf = this.predBuf;
                        for (let k = 0; k < count; k++) {
                            const plo = buf[2 * k];
                            const phi = buf[2 * k + 1];
                            if (plo === lo && phi === hi) continue;
                            if (B.insert(plo, phi, nextDepth) !== -1) continue;
                            next.push(plo, phi);
                            const other = F.get(plo, phi);
                            if (other !== -1 && nextDepth + other < bestLen) {
                                bestLen = nextDepth + other;
                                bestLo = plo; bestHi = phi; bestF = other; bestB = nextDepth;
                            }
                        }
                    }
                    if ((i & 255) === 255) {
                        if (Date.now() > deadline) return stop('time');
                        if (F.count + B.count > maxStates) return stop('states');
                    }
                }
                bFront = next;
                bDepth = nextDepth;
            }
        }

        if (bestLen === Infinity) {
            return { done: true, result: this.fail('No solution exists for this board.') };
        }
        return { done: true, result: this.rebuildExactPath(F, B, bestLo, bestHi, bestF, bestB) };
    }

    // Walks from the meeting state back to the start (using forward depths) and on to the goal
    // (using backward depths). No parent pointers are stored, so every step looks for a
    // neighbour whose depth label is exactly one smaller.
    rebuildExactPath(F, B, lo, hi, forwardDepth, backwardDepth) {
        const prefix = [];
        let curLo = lo;
        let curHi = hi;
        for (let level = forwardDepth; level > 0; level--) {
            this.unpack(curLo, curHi);
            this.prepareColumns();
            let found = false;
            for (let d = 0; d < 4 && !found; d++) {
                const count = this.fillPredecessors(d, 50000000);
                if (count < 0) return this.fail('Internal error: too many predecessors while rebuilding the path.');
                const buf = this.predBuf;
                for (let k = 0; k < count; k++) {
                    if (F.get(buf[2 * k], buf[2 * k + 1]) === level - 1) {
                        prefix.push(d);
                        curLo = buf[2 * k];
                        curHi = buf[2 * k + 1];
                        found = true;
                        break;
                    }
                }
            }
            if (!found) return this.fail('Internal error: could not rebuild the path from the start.');
        }
        prefix.reverse();

        const suffix = [];
        curLo = lo;
        curHi = hi;
        for (let level = backwardDepth; level > 0; level--) {
            let found = false;
            for (let d = 0; d < 4 && !found; d++) {
                this.move(curLo, curHi, d);
                if (B.get(this.nlo, this.nhi) === level - 1) {
                    suffix.push(d);
                    curLo = this.nlo;
                    curHi = this.nhi;
                    found = true;
                }
            }
            if (!found) return this.fail('Internal error: could not rebuild the path to the goal.');
        }

        const dirs = prefix.concat(suffix);
        return this.makeResult(dirs, `Optimal solution in ${dirs.length} steps`);
    }

    // Guidance for the beam: smaller is better. Not a lower bound.
    beamScore(lo, hi) {
        this.unpack(lo, hi);
        let sum = 0;
        let max = 0;
        for (let r = 0; r < 8; r++) {
            const bits = this.rows[r];
            if (bits === 0) continue;
            for (let c = 0; c < 8; c++) {
                if ((bits & (1 << c)) === 0) continue;
                const d = this.dist[r * 8 + c];
                if (d >= INF) return INF;
                sum += d;
                if (d > max) max = d;
            }
        }
        return sum * 4 + max;
    }

    // Keeps the `width` best states per level. Only states that were actually kept
    // are remembered, so a pruned state may come back by another route later.
    beamPass(width, deadline, maxStates) {
        const S = new StateStore(14);
        const root = S.add(this.startLo, this.startHi, -1, 0, 0);
        let beam = [root];

        const candCap = width * 4;
        const cLo = new Int32Array(candCap);
        const cHi = new Int32Array(candCap);
        const cParent = new Int32Array(candCap);
        const cDir = new Uint8Array(candCap);
        const cScore = new Int32Array(candCap);
        const order = new Int32Array(candCap);

        for (let depth = 0; depth < BEAM_MAX_DEPTH; depth++) {
            let n = 0;
            for (let b = 0; b < beam.length; b++) {
                const node = beam[b];
                const lo = S.lo[node];
                const hi = S.hi[node];
                for (let j = 0; j < 4; j++) {
                    const d = BEAM_DIR_ORDER[j];
                    this.move(lo, hi, d);
                    const nlo = this.nlo;
                    const nhi = this.nhi;
                    if (nlo === lo && nhi === hi) continue;

                    if (nlo === this.goalLo && nhi === this.goalHi) {
                        const dirs = [d];
                        for (let k = node; S.parent[k] !== -1; k = S.parent[k]) dirs.push(S.dir[k]);
                        dirs.reverse();
                        return this.makeResult(dirs, `Alternate solution in ${dirs.length} steps (not proven optimal)`);
                    }

                    if (S.find(nlo, nhi) !== -1) continue;
                    const score = this.beamScore(nlo, nhi);
                    if (score >= INF) continue;
                    cLo[n] = nlo;
                    cHi[n] = nhi;
                    cParent[n] = node;
                    cDir[n] = d;
                    cScore[n] = score;
                    n++;
                }
                if ((b & 255) === 255 && Date.now() > deadline) return { success: false, reason: 'time' };
            }

            if (n === 0) return { success: false, reason: 'no candidates left' };
            if (Date.now() > deadline) return { success: false, reason: 'time' };

            for (let i = 0; i < n; i++) order[i] = i;
            const view = order.subarray(0, n);
            view.sort((a, b) => (cScore[a] - cScore[b]) || (cLo[a] - cLo[b]) || (cHi[a] - cHi[b]));

            const next = [];
            let prev = -1;
            for (let i = 0; i < n && next.length < width; i++) {
                const c = view[i];
                if (prev !== -1 && cLo[prev] === cLo[c] && cHi[prev] === cHi[c]) continue;
                prev = c;
                next.push(S.add(cLo[c], cHi[c], cParent[c], cDir[c], depth + 1));
            }
            beam = next;
            if (S.size > maxStates) return { success: false, reason: 'states' };
        }
        return { success: false, reason: 'depth limit' };
    }

    // Heuristic fallback: wider and wider beams until the time or state budget runs out.
    solveBeam(deadline, maxStates) {
        let reason = 'no candidates left';
        for (let i = 0; i < BEAM_WIDTHS.length; i++) {
            if (Date.now() > deadline) return { success: false, reason: 'time' };
            const result = this.beamPass(BEAM_WIDTHS[i], deadline, maxStates);
            if (result.success) return result;
            reason = result.reason;
            if (reason === 'time' || reason === 'states') break;
        }
        return { success: false, reason };
    }

    solve(maxNodes = 3000000, maxMillis = 9500) {
        const t0 = Date.now();
        const hasLimit = maxMillis > 0;
        const finalDeadline = hasLimit ? t0 + maxMillis : Infinity;
        const exactDeadline = hasLimit ? t0 + maxMillis * EXACT_TIME_SHARE : Infinity;

        const problem = this.validate();
        if (problem) return this.fail(problem);

        if (this.startLo === this.goalLo && this.startHi === this.goalHi) {
            return this.makeResult([], 'Optimal solution in 0 steps');
        }

        const exact = this.solveBidirectional(exactDeadline, maxNodes);
        if (exact.done) return exact.result;

        const beam = this.solveBeam(finalDeadline, maxNodes);
        if (beam.success) return beam;

        const describe = (reason) => (reason === 'time' ? 'time limit reached'
            : reason === 'states' ? 'state budget reached' : reason);
        const progress = exact.stats
            ? ` after ${exact.stats.states.toLocaleString('en-US')} states (searched ${exact.stats.forwardDepth} steps from the start and ${exact.stats.backwardDepth} back from the targets)`
            : '';
        return this.fail(
            `No solution found. This does not mean the puzzle is unsolvable. Exact search stopped (${describe(exact.reason)})${progress}; ` +
            `beam search stopped (${describe(beam.reason)}). ` +
            'Try a longer time limit or a larger state budget.'
        );
    }
}
