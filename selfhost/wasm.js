"use strict";
// Runs a program compiled to WebAssembly for WASI: `node selfhost/wasm.js program.wasm args...`.
// The host gives what WebAssembly cannot do itself: switching between fibers, each running as a
// call of its own on a shadow stack of its own, by JavaScript promise integration.
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
  // Each fiber suspended in a switch, by its address: how to resume it.
  const waiting = new Map();
  const saved = new Map();
  let runFiber;
  // The program ends when any fiber calls `proc_exit`, which throws what keys its status.
  const ended = (e) => {
    if (typeof e === "symbol" && typeof wasi[e] === "number") process.exit(wasi[e]);
    console.error(e);
    process.exit(1);
  };
  const switchTo = new WebAssembly.Suspending(async (from, to) => {
    const sp = exports.__stack_pointer;
    saved.set(from, sp.value);
    const back = new Promise((resolve) => waiting.set(from, resolve));
    const resume = waiting.get(to);
    if (resume) {
      waiting.delete(to);
      resume();
    } else {
      sp.value = exports.fly_fiber_top(to);
      runFiber(to).catch(ended);
    }
    await back;
    sp.value = saved.get(from);
  });
  const module = await WebAssembly.compile(fs.readFileSync(path));
  // A fiber freed is forgotten: its memory may hold the next one.
  const free = (f) => {
    waiting.delete(f);
    saved.delete(f);
  };
  // WASI's calls are made on Node's own stack, not promise integration's: Node's WASI tells V8 of
  // memory it allocates, which may start a collection that V8 runs only on its own stack.
  const host = {};
  for (const [name, f] of Object.entries(wasi.wasiImport)) {
    host[name] = name === "proc_exit" ? f : new WebAssembly.Suspending(async (...args) => f(...args));
  }
  const instance = await WebAssembly.instantiate(module, { wasi_snapshot_preview1: host, fly: { switch: switchTo, free } });
  exports = instance.exports;
  runFiber = WebAssembly.promising(exports.fly_fiber_run);
  // WASI learns the memory from a command it starts: one that does nothing. `_start` itself runs
  // promising, so the main fiber may suspend too.
  wasi.start({ exports: { memory: exports.memory, _start() {} } });
  await WebAssembly.promising(exports._start)().catch(ended);
}

main();
