// Tiny stack VM for the make.fun ISA: 32-bit wrapping ints, 256-value stack,
// 64-deep calls, 256 words of memory, ten traps.
// One run answers a whole set.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Opcode facts: [byte, immediate bytes, values popped, values pushed].
const O=[[0,0,0,0],[1,1,0,1],[2,4,0,1],[3,0,1,0],[4,0,1,2],[5,0,2,2],[6,0,2,3],[7,0,3,3],[16,0,2,1],[17,0,2,1],[18,0,2,1],[19,0,2,1],[20,0,2,1],[21,0,2,1],[22,0,2,1],[23,0,1,1],[24,0,2,1],[25,0,2,1],[26,0,2,1],[27,0,1,1],[28,0,2,1],[29,0,2,1],[30,0,2,1],[32,0,2,1],[33,0,2,1],[34,0,2,1],[48,2,0,0],[49,2,1,0],[50,2,1,0],[51,2,0,0],[52,0,0,0],[64,0,1,1],[65,0,2,0],[80,0,1,0],[81,0,1,0],[82,0,0,1],[83,0,1,0]];
const K = new Uint8Array(256), IM = new Uint8Array(256), PO = new Uint8Array(256), PU = new Uint8Array(256);
for (const [op, im, po, pu] of O) { K[op] = 1; IM[op] = im; PO[op] = po; PU[op] = pu; }

function run(p: Uint8Array, g: Uint8Array): { out: Uint8Array; code: number } {
  const n = p.length, D = new Int32Array(256), C = new Int32Array(64), M = new Int32Array(256);
  const o = new Uint8Array(65536), s = new Uint8Array(12);
  let sp = 0, cp = 0, ol = 0, ip = 0, pc = 0, st = 0;
  const done = (c: number) => ({ out: o.slice(0, ol), code: c });
  for (;;) {
    // Per-step checks, in the ISA's order: step limit, pc in range, known
    // opcode, immediate fully inside the program. Then the stack checks.
    if (st === 1e6) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = p[pc];
    if (!K[op]) return done(5);
    const im = IM[op];
    if (pc + im >= n) return done(9);
    st++;
    const nx = pc + 1 + im, po = PO[op], pu = PU[op];
    if (sp < po) return done(2);
    if (sp - po + pu > 256) return done(3);
    pc = nx;
    switch (op) {
      case 0: return done(0);
      case 1: D[sp++] = (p[nx - 1] << 24) >> 24; break;
      case 2: D[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break;
      case 3: sp--; break;
      case 4: D[sp] = D[sp - 1]; sp++; break;
      case 5: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; }
      case 6: D[sp] = D[sp - 2]; sp++; break;
      case 7: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; }
      case 23: D[sp - 1] = (-D[sp - 1]) | 0; break;
      case 27: D[sp - 1] = ~D[sp - 1]; break;
      case 16: case 17: case 18: case 19: case 20: case 21: case 22:
      case 24: case 25: case 26: case 28: case 29: case 30:
      case 32: case 33: case 34: {
        const b = D[sp - 1], a = D[sp - 2];
        let r: number;
        if (op === 16) r = (a + b) | 0;
        else if (op === 17) r = (a - b) | 0;
        else if (op === 18) r = Math.imul(a, b);
        else if (op === 19) { if (!b) return done(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
        else if (op === 20) { if (!b) return done(4); r = b === -1 ? 0 : (a % b) | 0; }
        else if (op === 21) { if (!b) return done(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
        else if (op === 22) { if (!b) return done(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
        else if (op === 24) r = a & b;
        else if (op === 25) r = a | b;
        else if (op === 26) r = a ^ b;
        else if (op === 28) r = a << (b & 31);
        else if (op === 29) r = a >> (b & 31);
        else if (op === 30) r = (a >>> (b & 31)) | 0;
        else if (op === 32) r = a === b ? 1 : 0;
        else if (op === 33) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2;
        D[sp++] = r;
        break;
      }
      case 48: case 49: case 50: {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let t = op === 48;
        if (!t) { const v = D[--sp]; t = op === 49 ? v === 0 : v !== 0; }
        if (t) pc = nx + rel; // a target outside the program traps at the next step
        break;
      }
      case 51:
        if (cp === 64) return done(7);
        C[cp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 52:
        if (!cp) return done(8);
        pc = C[--cp];
        break;
      case 64: { const a = D[sp - 1]; if (a < 0 || a > 255) return done(6); D[sp - 1] = M[a]; break; }
      case 65: { const a = D[sp - 1]; if (a < 0 || a > 255) return done(6); M[a] = D[sp - 2]; sp -= 2; break; }
      case 80: {
        let q = 12;
        const v = D[sp - 1];
        let x = v < 0 ? -v : v; // -INT_MIN is 2147483648, exact as a double
        if (!x) s[--q] = 48;
        while (x > 0) { s[--q] = 48 + (x % 10); x = Math.floor(x / 10); }
        if (v < 0) s[--q] = 45;
        const l = 12 - q;
        if (ol + l > 65536) return done(11); // writes none of its bytes
        sp--;
        o.set(s.subarray(q), ol);
        ol += l;
        break;
      }
      case 81:
        if (ol + 1 > 65536) return done(11);
        o[ol++] = D[--sp] & 255;
        break;
      case 82: D[sp++] = ip < g.length ? g[ip++] : -1; break;
      case 83: return done(D[--sp] & 255);
      default: return done(5); // unreachable: unknown opcodes were filtered above
    }
  }
}

// One run answers the whole set; env vars only exist for local runs.
const A = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const B = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(A).sort()) {
  let p: Buffer, g: Buffer;
  try { p = readFileSync(join(A, id, 'program.bin')); } catch { p = Buffer.alloc(0); }
  try { g = readFileSync(join(A, id, 'input.bin')); } catch { g = Buffer.alloc(0); }
  const r = run(new Uint8Array(p), new Uint8Array(g));
  mkdirSync(join(B, id), { recursive: true, mode: 0o755 });
  writeFileSync(join(B, id, 'stdout.bin'), r.out, { mode: 0o644 });
  writeFileSync(join(B, id, 'exit.txt'), `${r.code}\n`, { mode: 0o644 });
}
