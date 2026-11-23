// tiny-stack-vm-01: a spec-exact interpreter for make.fun's tiny stack ISA v1.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Per-opcode metadata: immediate bytes (-1 = unknown), pops, pushes.
const IMM = new Int8Array(256).fill(-1);
const POPS = new Uint8Array(256);
const PUSH = new Uint8Array(256);
const meta = (op, imm, pops, push) => { IMM[op] = imm; POPS[op] = pops; PUSH[op] = push; };
meta(0x00, 0, 0, 0); meta(0x01, 1, 0, 1); meta(0x02, 4, 0, 1); meta(0x03, 0, 1, 0);
meta(0x04, 0, 1, 2); meta(0x05, 0, 2, 2); meta(0x06, 0, 2, 3); meta(0x07, 0, 3, 3);
for (let op = 0x10; op <= 0x22; op++) meta(op, 0, 2, 1); // binary ops
meta(0x17, 0, 1, 1); meta(0x1b, 0, 1, 1); // NEG, NOT (unary)
IMM[0x1f] = -1; // not an opcode
meta(0x30, 2, 0, 0); meta(0x31, 2, 1, 0); meta(0x32, 2, 1, 0); meta(0x33, 2, 0, 0);
meta(0x34, 0, 0, 0); meta(0x40, 0, 1, 1); meta(0x41, 0, 2, 0); meta(0x50, 0, 1, 0);
meta(0x51, 0, 1, 0); meta(0x52, 0, 0, 1); meta(0x53, 0, 1, 0);

function run(prog, inp) {
  const n = prog.length;
  const st = new Int32Array(256);
  const cs = new Int32Array(64);
  const mem = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0, csp = 0, olen = 0, ip = 0, pc = 0, steps = 0;
  const fin = (code) => ({ out: out.subarray(0, olen), code });
  for (;;) {
    if (steps === 1000000) return fin(10); // step limit, first
    if (pc < 0 || pc >= n) return fin(9);
    const op = prog[pc];
    const imm = IMM[op];
    if (imm < 0) return fin(5); // unknown opcode
    if (pc + imm >= n) return fin(9); // immediate cut off
    steps++;
    if (sp < POPS[op]) return fin(2); // underflow
    if (sp - POPS[op] + PUSH[op] > 256) return fin(3); // overflow
    const nx = pc + 1 + imm;
    pc = nx;
    switch (op) {
      case 0x00: return fin(0);
      case 0x01: st[sp++] = (prog[nx - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 0x02: st[sp++] = prog[nx - 4] | (prog[nx - 3] << 8) | (prog[nx - 2] << 16) | (prog[nx - 1] << 24); break;
      case 0x03: sp--; break;
      case 0x04: st[sp] = st[sp - 1]; sp++; break;
      case 0x05: { const t = st[sp - 1]; st[sp - 1] = st[sp - 2]; st[sp - 2] = t; break; }
      case 0x06: st[sp] = st[sp - 2]; sp++; break;
      case 0x07: { const a = st[sp - 3]; st[sp - 3] = st[sp - 2]; st[sp - 2] = st[sp - 1]; st[sp - 1] = a; break; }
      case 0x10: st[sp - 2] = (st[sp - 2] + st[sp - 1]) | 0; sp--; break;
      case 0x11: st[sp - 2] = (st[sp - 2] - st[sp - 1]) | 0; sp--; break;
      case 0x12: st[sp - 2] = Math.imul(st[sp - 2], st[sp - 1]); sp--; break; // low 32 bits
      case 0x13: { // DIV, toward zero
        const b = st[sp - 1]; if (b === 0) return fin(4);
        const a = st[sp - 2];
        st[sp - 2] = a === -2147483648 && b === -1 ? a : (a / b) | 0; sp--; break;
      }
      case 0x14: { // MOD, sign of dividend
        const b = st[sp - 1]; if (b === 0) return fin(4);
        st[sp - 2] = b === -1 ? 0 : st[sp - 2] % b | 0; sp--; break;
      }
      case 0x15: { // DIVU
        const b = st[sp - 1]; if (b === 0) return fin(4);
        st[sp - 2] = Math.floor((st[sp - 2] >>> 0) / (b >>> 0)) | 0; sp--; break;
      }
      case 0x16: { // MODU
        const b = st[sp - 1]; if (b === 0) return fin(4);
        st[sp - 2] = (st[sp - 2] >>> 0) % (b >>> 0) | 0; sp--; break;
      }
      case 0x17: st[sp - 1] = -st[sp - 1] | 0; break;
      case 0x18: st[sp - 2] = st[sp - 2] & st[sp - 1]; sp--; break;
      case 0x19: st[sp - 2] = st[sp - 2] | st[sp - 1]; sp--; break;
      case 0x1a: st[sp - 2] = st[sp - 2] ^ st[sp - 1]; sp--; break;
      case 0x1b: st[sp - 1] = ~st[sp - 1]; break;
      case 0x1c: st[sp - 2] = st[sp - 2] << (st[sp - 1] & 31); sp--; break;
      case 0x1d: st[sp - 2] = st[sp - 2] >> (st[sp - 1] & 31); sp--; break; // arithmetic
      case 0x1e: st[sp - 2] = (st[sp - 2] >>> (st[sp - 1] & 31)) | 0; sp--; break; // logical
      case 0x20: st[sp - 2] = st[sp - 2] === st[sp - 1] ? 1 : 0; sp--; break;
      case 0x21: st[sp - 2] = st[sp - 2] < st[sp - 1] ? 1 : 0; sp--; break;
      case 0x22: st[sp - 2] = (st[sp - 2] >>> 0) < (st[sp - 1] >>> 0) ? 1 : 0; sp--; break; // unsigned
      case 0x30: pc = nx + (((prog[nx - 2] | (prog[nx - 1] << 8)) << 16) >> 16); break;
      case 0x31: if (st[--sp] === 0) pc = nx + (((prog[nx - 2] | (prog[nx - 1] << 8)) << 16) >> 16); break;
      case 0x32: if (st[--sp] !== 0) pc = nx + (((prog[nx - 2] | (prog[nx - 1] << 8)) << 16) >> 16); break;
      case 0x33: // CALL, absolute target
        if (csp === 64) return fin(7);
        cs[csp++] = nx;
        pc = prog[nx - 2] | (prog[nx - 1] << 8);
        break;
      case 0x34: if (csp === 0) return fin(8); pc = cs[--csp]; break;
      case 0x40: { // LOAD
        const addr = st[sp - 1];
        if (addr < 0 || addr > 255) return fin(6);
        st[sp - 1] = mem[addr]; break;
      }
      case 0x41: { // STORE ( v addr -- )
        const addr = st[sp - 1];
        if (addr < 0 || addr > 255) return fin(6);
        mem[addr] = st[sp - 2]; sp -= 2; break;
      }
      case 0x50: { // PRINT, decimal, no newline
        const s = String(st[sp - 1]);
        if (olen + s.length > 65536) return fin(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        break;
      }
      case 0x51:
        if (olen + 1 > 65536) return fin(11);
        out[olen++] = st[--sp] & 255;
        break;
      case 0x52: st[sp++] = ip < inp.length ? inp[ip++] : -1; break;
      case 0x53: return fin(st[sp - 1] & 255); // EXIT, low byte
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const read = (p) => { try { return new Uint8Array(readFileSync(p)); } catch { return new Uint8Array(0); } };
for (const id of readdirSync(I).sort()) {
  const r = run(read(join(I, id, 'program.bin')), read(join(I, id, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), r.code + '\n');
}
