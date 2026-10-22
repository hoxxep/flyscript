# Roadmap

Flyscript compiles itself today, to JavaScript and to C. The next five steps take it from a self-hosted language to a systems platform: one intermediate form under every back end, kernels, LLVM, WebAssembly, every core of the machine, and a web framework that shows what all of it buys.

## 0. One core IR under every back end

The compiler lowers the checked program once, after specialization, into a small statement IR: every type a concrete layout, every temporary named in evaluation order, every block with its cleanup (drops, `defer`s, region arenas) explicit, every early exit naming the scopes it unwinds, closures as `{ code, environment, drop }`, region evidence as parameters, and each function classified by what it can do: nothing, fail, allocate in a region, or suspend.

The C and JavaScript back ends both become printers of this IR, so Flyscript's semantics — evaluation order, pattern matching, drops, unwinding — are lowered in exactly one place. Cleanup becomes lexical: a value is dropped where its scope ends, on every path out of it.

## 1. Foreign code and freestanding programs

The foreign interface of §8.2, built for real, and what a kernel needs beyond it:

- Raw pointers `T*`, used only inside `unsafe`: `read`, `write`, `add`, `readVolatile` and `writeVolatile` for memory-mapped devices, and atomics with explicit ordering (`loadAcquire`, `storeRelease`, `compareExchange`, `fetchAdd`, fences), which interrupt handlers need because they cannot perform `Io`. `Ptr.fromMut(mut x)` and `Ptr.fromRef(x)` take an address and say which kind; `Ptr.at(address)` names a device register, and address `0` is null.
- `extern "C"` functions, and `export extern "C"` functions that C or assembly can call.
- `sizeOf<T>()` and `alignOf<T>()`, `@layout(c, align = 4096)` for page tables and DMA rings, and `zeroed<T>()` for C structures filled in by a callee.
- Fallible allocation where it matters: `tryReserve(n)` on growable collections and `Box.tryNew(v)` fail with `#OutOfMemory`; everything else keeps its simple signature.
- A freestanding target: no `main`, no C library, no `Io`. The program supplies an allocator and a panic routine; regions, `defer`, failures, generators and effect handlers all work unchanged.

The proof is a small AArch64 kernel that boots under QEMU, drives a UART through volatile writes, allocates pages fallibly, and has an interrupt handler the type system keeps from sleeping.

## 2. WebAssembly

Through clang's `wasm32` target for WASI, with fibers in linear memory: each fiber keeps its own shadow stack, so a value lent `mut` across a suspension never moves, and the host switches between them by JavaScript promise integration. `Io` maps to the host: WASI, or promises in a browser. Every test program and the compiler itself run as WebAssembly.

## 3. LLVM

A back end that writes LLVM IR as text from the core IR, linked with the same runtime: exact integer semantics, debug information that maps to `.fly` source, and every target LLVM supports. The C back end stays as the portable, dependency-free bootstrap.

## 4. Every core

Tasks on all cores: a work-stealing scheduler over one worker thread per core, small pooled fiber stacks, atomic `Arc` counts, the unwind state kept per fiber, and `par` on a fork-join pool. The deterministic single-thread scheduler remains a separate implementation of the same `Io` interface, and is what tests run on, so every interleaving a test sees can be reproduced from its seed.

## 5. A web framework

A proof of concept of what Next.js and React do, in one Flyscript component tree:

- Components are functions that perform `Ui<Msg>`: elements, text, `keyed` children, and events as `Msg` values, with `onInput` taking a function from the input's text to a `Msg`. `if`, `for` and `match` work inside the tree.
- The server renders natively, streaming HTML from a per-request region; the client hydrates the same tree in WebAssembly and updates the DOM by a keyed diff of flat operation lists, with no virtual DOM objects.
- Server functions are an effect shared by both sides: handled against the database on the server, over `fetch` on the client, with typed failures re-raised where they were called.
- Routes are files, each its own WebAssembly module over a shared core.
