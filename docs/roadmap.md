# Roadmap

Flyscript compiled itself, to JavaScript and to C, when this roadmap was written. Its steps take it from a self-hosted language to a systems platform: one intermediate form under every back end, kernels, LLVM, WebAssembly, every core of the machine, and a web framework that shows what all of it buys. Steps 0 to 5 and 8 are done, and each says what was built; the others are next.

## 0. One core IR under every back end

*Done: `selfhost/ir.fly`, which the JavaScript, C and LLVM back ends all print.*

The compiler lowers the checked program once, after specialization, into a small statement IR: every type a concrete layout, every temporary named in evaluation order, every block with its cleanup (drops, `defer`s, region arenas) explicit, every early exit naming the scopes it unwinds, closures as `{ code, environment, drop }`, region evidence as parameters, and each function classified by what it can do: nothing, fail, allocate in a region, or suspend.

The C and JavaScript back ends both become printers of this IR, so Flyscript's semantics — evaluation order, pattern matching, drops, unwinding — are lowered in exactly one place. Cleanup becomes lexical: a value is dropped where its scope ends, on every path out of it.

## 1. Foreign code and freestanding programs

*Done: raw pointers, `Unsafe`, `extern "C"` both ways, `@layout(c, align = N)`, fallible allocation, and [a kernel](../examples/kernel/) that boots on QEMU.*

The foreign interface of §8.2, built for real, and what a kernel needs beyond it:

- Raw pointers `T*`, used only inside `unsafe`: `read`, `write`, `add`, `readVolatile` and `writeVolatile` for memory-mapped devices, and atomics with explicit ordering (`loadAcquire`, `storeRelease`, `compareExchange`, `fetchAdd`, fences), which interrupt handlers need because they cannot perform `Io`. `Ptr.fromMut(mut x)` and `Ptr.fromRef(x)` take an address and say which kind; `Ptr.at(address)` names a device register, and address `0` is null.
- `extern "C"` functions, and `export extern "C"` functions that C or assembly can call.
- `sizeOf<T>()` and `alignOf<T>()`, `@layout(c, align = 4096)` for page tables and DMA rings, and `zeroed<T>()` for C structures filled in by a callee.
- Fallible allocation where it matters: `tryReserve(n)` on growable collections and `Box.tryNew(v)` fail with `#OutOfMemory`; everything else keeps its simple signature.
- A freestanding target: no `main`, no C library, no `Io`. The program supplies an allocator and a panic routine; regions, `defer`, failures, generators and effect handlers all work unchanged.

The proof is a small AArch64 kernel that boots under QEMU, drives a UART through volatile writes, allocates pages fallibly, and has an interrupt handler the type system keeps from sleeping.

## 2. WebAssembly

*Done: every test program and the compiler itself run as WebAssembly; pages run it in browsers ([web](../web/)).*

Through LLVM, as native code is, for WASI: the program's LLVM IR made for 32-bit pointers and linked with the runtime's C for `wasm32`, smaller than through C for the same speed. Fibers live in linear memory: each fiber keeps its own shadow stack, so a value lent `mut` across a suspension never moves, and the host switches between them by JavaScript promise integration. `Io` maps to the host: WASI, or promises in a browser. Every test program and the compiler itself run as WebAssembly.

## 3. LLVM

*Done: `selfhost/llvm.fly`, with debug information for lldb and gdb; the compiler built through LLVM reproduces itself, and the kernel boots built through it.*

A back end that writes LLVM IR as text from the core IR, linked with the same runtime: exact integer semantics, debug information that maps to `.fly` source, and every target LLVM supports. The C back end stays as the portable, dependency-free bootstrap.

## 4. Every core

*Done: a work-stealing scheduler over a worker per core, and `par` over a work-stealing `join`, checked by the thread sanitizer; the deterministic scheduler runs every test.*

Tasks on all cores: a work-stealing scheduler over one worker thread per core, small pooled fiber stacks, atomic `Arc` counts, the unwind state kept per fiber, and `par` on a fork-join pool. The deterministic single-thread scheduler remains a separate implementation of the same `Io` interface, and is what tests run on, so every interleaving a test sees can be reproduced from its seed.

## 5. A web framework

*Done: [FlyNext](../web/) and [a site](../examples/todo/) built with it. Routes from files with parameters, nested layouts, data loaded on the server, pages streamed where part of them is slow and kept and revalidated where they are the same for everyone, server functions from an effect, links followed and the history stepped through without loading a page, components, a 404 page, and `web/flynext dev`; one WebAssembly program for the whole site.*

A proof of concept of what Next.js and React do, in one Flyscript component tree:

- Components are functions that perform `Ui<Msg>`: elements, text, `keyed` children, and events as `Msg` values, with `onInput` taking a function from the input's text to a `Msg`. `if`, `for` and `match` work inside the tree.
- The server renders natively, streaming HTML from a per-request region; the client hydrates the same tree in WebAssembly and updates the DOM by a keyed diff of flat operation lists, with no virtual DOM objects.
- Server functions are an effect shared by both sides: handled against the database on the server, over `fetch` on the client, with typed failures re-raised where they were called.
- Routes are files. The browser runs one WebAssembly program for the whole site; loading each route's code as it is needed is step 6.

## 6. Pages loaded by route

*Next.*

A page downloads the code it runs and no more, as a Next.js page does, while the server goes on rendering every page natively:

- The site compiles to a core module and a module per route. The core holds the runtime, the C library, the standard library, the DOM's handler of `Ui`, the layouts, and everything two routes or more use, generic instantiations among them; a route's module holds only what that route alone uses. The compiler makes the split after specialization, so each instantiation is in exactly one module.
- Route modules are linked dynamically, as WebAssembly side modules: position-independent code that imports the core's memory, function table and stack pointer, and its symbols through a table of offsets the loader fills in. The loader is part of `web/flynext.js`, and fibers switch across modules as within one, since every module shares the one memory and its shadow stacks.
- The server's HTML names the core and the page's own module, so the browser fetches both at once; following a link fetches the next route's module with its data, prefetched as the pointer nears the link, as data is now. Each module is cached on its own, so a change to one page leaves every other's cached code valid.
- Done when the example site's first page downloads only the core and its own module, every test of the site passes in a browser, and the cost is measured: what the first page downloads, before and after, and the speed of code built position-independent.

## 7. A smaller shared base

*Next.*

Every page downloads the core, so a byte saved there is saved for every page of every site. Of the example site's 165 KB program (48 KB compressed), a site of one page still needs 110 KB (37 KB); about 32 KB of that is the C library, the most of it `printf` and `dlmalloc`.

- Numbers formatted by the standard library in Flyscript, as the language already defines them, so that a page program links no `printf`.
- An allocator for one thread, made for the sizes Flyscript allocates — classes of small blocks and pages for large ones — in place of `dlmalloc` where there are no threads.
- Nothing else of the C library that a page program does not call: what a page links is measured symbol by symbol, and each part kept is there for a reason.
- Done when the core of the example site is measured smaller, the WebAssembly corpus and the site's browser tests still pass, and the compiler built for WebAssembly still compiles itself to the same output.

## 8. Compile speed

*Done: the native compiler checks and compiles itself in 0.88 seconds, from 4.0; `--watch` compiles a change to a function again in about 100 milliseconds; native builds through LLVM use every core.*

- `--time` reports each phase: loading, checking, ownership, and code generation, which lowers and prints.
- What the profile showed was fixed where it was. A nominal type's class, whether it hides a borrow and whether it has a `Drop` are worked out once for the program, as the least solution over types that hold each other, not by walking its fields at every question; a method is looked up among the methods of its name; a trial unification is undone along a trail of what it bound, rather than by copying every binding; declarations, receivers and arguments are lent rather than copied; and a native program allocates from the runtime's own allocator, in classes of sizes with a cache per thread, which made binary-trees faster than C's.
- The cores go where the time is. Compiling the compiler's own C took eighteen seconds against the front end's one, so `llvm.sh` splits a program's module into a part per core, compiles the parts apart and links them with ThinLTO, which optimizes across them as one module would: the compiler builds in six seconds rather than nineteen, and runs as fast. The front end stays on one core: the time a change costs it is what `--watch` saves.
- `--watch` keeps the program between builds. A change to the bodies of a module's functions is checked, lowered and printed again for those functions alone, what they now reach for the first time with them; any other change compiles from scratch. The test changes a program's bodies and declarations, breaks it and mends it, and runs each build.

## 9. The proof joined to the compiler

*Next.*

The proof covers λ-fly; the compiler's checker is held to it by tests alone. This step checks the compiler's work by the proof:

- A checker for λ-fly written in Lean, `check : Program → Bool`, proved sound: `check p = true` implies that `p` is well typed, and so has every guarantee the proof gives.
- `--core` prints a program as the compiler elaborated it, as a λ-fly term in Lean.
- Every test program in the part of the language λ-fly covers is certified on each build: Lean evaluates the proved checker on its term, in the kernel, with no `native_decide`. A disagreement is a bug on one side or the other.
- What remains trusted is said in §9.5 of the spec: the elaboration from the surface language to λ-fly, lowering and code generation, each held to the others by differential tests.
- Done when the corpus's programs in λ-fly's part of the language are certified on every build.

## 10. The standard library, filled out

*Next.*

What programs need beyond the core, each part an effect or a pure library, so that a test handles the clock, the files or the network itself, with no mocking library, and the browser and WASI map it to their host as they map `Io`:

- Files, directories and processes: paths, walking a directory, metadata, the environment, and child processes with pipes.
- Time: a monotonic clock, the time of day, durations, and time zones from the system's tz database, written and read as ISO 8601.
- Unicode: text that is always valid UTF-8, iterated by code point or by grapheme, normalized, and mapped between cases.
- Regular expressions that run in time linear in their input, as RE2's do, written in Flyscript: with no backtracking, no input makes one run for ever.
- An HTTP client over `std/net`, with TLS through bindings to an audited library.
- Cryptography through bindings to the same library: hashes, HMAC, authenticated encryption, signatures and secure random numbers.
- Done when each part is specified in [std.md](std.md), runs on every back end its host allows, and is tested against handlers of its own and against the real system.

## 11. Packages, a lockfile and `fly`

*Next.*

- One command, `fly`, in place of the scripts: `new`, `build`, `run`, `test` and `add`.
- `fly.toml` names a package and its dependencies, fetched from git by semantic version tag; a registry can come later.
- `fly.lock` records the exact commit and the hash of the content of every dependency, so that a build is the same wherever it is made.
- The lockfile also records the effects each dependency's exported functions perform, which their types already say: an update after which a package performs `Io` or `Unsafe` where it did not is shown, and stops the build, until it is accepted. A package's types are a statement of what it can do, and its lockfile holds it to that statement.
- Done when the example site and the compiler build with `fly` from their manifests, a dependency's update that adds an effect stops the build, and two builds from one lockfile are the same.

## 12. The runtime in Flyscript

*Next.*

The runtime's higher layers — the scheduler, channels, `Mutex`, buffered I/O and formatting — move from C into Flyscript, over a thin core of C and assembly that switches stacks, makes system calls and tells the sanitizers about fibers. The runtimes for JavaScript and the browser stay JavaScript; buffered I/O and formatting join the standard library step 10 fills out. Channels, `Mutex` and atomics are already proved as handlers (§9.5 of the spec); written in Flyscript, the code that runs them is checked by the same type system the proof is about. Every back end must still interleave tasks the same way under the deterministic scheduler, for every test, from its seed.
