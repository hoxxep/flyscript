"use strict";
// Runs a program compiled to WebAssembly for WASI: `node selfhost/wasm.js program.wasm args...`.
// The program's tasks are state machines (§11.3), which need no stack of their own: the host gives
// what WASI does, and its calls may suspend the program until they are done, by JavaScript promise
// integration.
const fs = require("node:fs");
const { WASI } = require("node:wasi");
// Every call the host makes runs on a stack of promise integration's, 984 KB unless told otherwise,
// however much stack Node itself was given. A program that recurses deeply, as the compiler does,
// needs as much room there as natively; and which frames are larger depends on when V8 compiles a
// function again, optimized, so too small a stack overflows only now and then.
require("node:v8").setFlagsFromString("--wasm-stack-switching-stack-size=65536");

async function main() {
  const [path, ...args] = process.argv.slice(2);
  const wasi = new WASI({ version: "preview1", args: [path, ...args], env: process.env, preopens: { ".": "." }, returnOnExit: true });
  let exports;
  // The program ends when it calls `proc_exit`, which throws what keys its status.
  const ended = (e) => {
    if (typeof e === "symbol" && typeof wasi[e] === "number") process.exit(wasi[e]);
    console.error(e);
    process.exit(1);
  };
  const module = await WebAssembly.compile(fs.readFileSync(path));
  // WASI's calls are made on Node's own stack, not promise integration's: Node's WASI tells V8 of
  // memory it allocates, which may start a collection that V8 runs only on its own stack.
  const host = {};
  for (const [name, f] of Object.entries(wasi.wasiImport)) {
    host[name] = name === "proc_exit" ? f : new WebAssembly.Suspending(async (...args) => f(...args));
  }
  const instance = await WebAssembly.instantiate(module, { wasi_snapshot_preview1: host, fly: { crypto: (...a) => crypto(exports.memory, ...a) } });
  exports = instance.exports;
  // WASI learns the memory from a command it starts: one that does nothing. `_start` itself runs
  // promising, so that the program may suspend in the host's calls.
  wasi.start({ exports: { memory: exports.memory, _start() {} } });
  await WebAssembly.promising(exports._start)().catch(ended);
}

// The runtime's cryptography (runtime.c's `crypto_op`), by Node's, which is OpenSSL's: operation
// `op` of up to four byte strings, written to `out`; how much it wrote, -1 if what it opened was
// forged or a signature is not one, -2 if its input cannot be what it takes.
function crypto(memory, op, a, na, b, nb, c, nc, d, nd, out, cap) {
  const nc_ = require("node:crypto");
  const m = () => new Uint8Array(memory.buffer);
  const at = (p, n) => Buffer.from(m().slice(p, p + n));
  const [A, B, C, D] = [at(a, na), at(b, nb), at(c, nc), at(d, nd)];
  const give = (bytes) => { m().set(bytes.subarray(0, cap), out); return Math.min(bytes.length, cap); };
  const edSecret = (k) => nc_.createPrivateKey({ key: Buffer.concat([Buffer.from("302e020100300506032b657004220420", "hex"), k]), format: "der", type: "pkcs8" });
  switch (op) {
    case 1: return give(nc_.createHash("sha256").update(A).digest());
    case 2: return give(nc_.createHash("sha384").update(A).digest());
    case 3: return give(nc_.createHash("sha512").update(A).digest());
    case 4: return give(nc_.createHmac("sha256", A).update(B).digest());
    case 5: return give(nc_.createHmac("sha512", A).update(B).digest());
    case 6: return cap === 0 ? 0 : give(Buffer.from(nc_.hkdfSync("sha256", A, B, C, cap)));
    case 7: case 8: {
      if (A.length !== 32 || B.length !== 12) return -2;
      if (op === 7) {
        const e = nc_.createCipheriv("aes-256-gcm", A, B);
        e.setAAD(D);
        return give(Buffer.concat([e.update(C), e.final(), e.getAuthTag()]));
      }
      if (C.length < 16) return -1;
      const dec = nc_.createDecipheriv("aes-256-gcm", A, B);
      dec.setAAD(D);
      dec.setAuthTag(C.subarray(C.length - 16));
      try { return give(Buffer.concat([dec.update(C.subarray(0, C.length - 16)), dec.final()])); } catch { return -1; }
    }
    case 9: return A.length !== 32 ? -2 : give(nc_.createPublicKey(edSecret(A)).export({ format: "der", type: "spki" }).subarray(12));
    case 10: return A.length !== 32 ? -2 : give(nc_.sign(null, B, edSecret(A)));
    case 11: {
      if (A.length !== 32 || C.length !== 64) return -1;
      try {
        const key = nc_.createPublicKey({ key: Buffer.concat([Buffer.from("302a300506032b6570032100", "hex"), A]), format: "der", type: "spki" });
        return nc_.verify(null, B, key, C) ? 0 : -1;
      } catch { return -1; }
    }
  }
  return -2;
}

main();
