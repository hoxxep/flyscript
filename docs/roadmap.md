# Roadmap

Flyscript compiled itself, to JavaScript and to C, when this roadmap was written. Its steps take it from a self-hosted language to a systems platform: one intermediate form under every back end, kernels, LLVM, WebAssembly, every core of the machine, and a web framework that shows what all of it buys. Steps 0 to 12 are done, and each says what was built.

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
- Routes are files, and each one's code a WebAssembly module of its own over a shared core (step 6).

## 6. Pages loaded by route

*Done: the example site's list page downloads a core of 20 KB and its own module of 7 KB, compressed, where it downloaded the whole site's 41 KB, and is ready as soon.*

A page downloads the code it runs and no more, as a Next.js page does, while the server goes on rendering every page natively:

- Each route's code is a function of its own in the client program the app compiler writes. `selfhost/wasm-split.js` cuts the program, optimized whole, at those functions: what one route alone reaches goes into that route's module, and everything else — the runtime, the C library, the standard library, the DOM's handler of `Ui`, the layouts, and whatever two routes share — stays in the core. The cut is made in the LLVM module after specialization, so each instance of a generic function is in exactly one module.
- In the core, a route's function becomes a stub of the same type, which asks the host for the route's module and calls the function there through the table of functions the two share: WebAssembly calling WebAssembly, so a fiber suspends through it as through any call. The program is the same program; only where its code is changes.
- A route's module is a WebAssembly side module, position-independent, linked by `web/flynext.js` as WebAssembly's dynamic linking lays it out: the core's memory and table, its part of each given it, and what it takes of the core found among the core's exports. Each module's file is named by the hash of what it holds, so a change to one page leaves every other's cached code valid.
- The server names the program and the page's own module in the page's head, so the browser fetches both as it reads the page; pointing at a link asks for the next page's data, and with it its module.
- The browser test checks that the first page downloads its own module and no other's, and that following a link downloads the next page's, once.

## 7. A smaller shared base

*Done: the example site's program is 140 KB, 38 KB compressed, from 165 KB and 48 KB; the C library's part of it is 7 KB, from 32.*

Every page downloads the core, so a byte saved there is saved for every page of every site.

- No `printf` anywhere in the runtime. A panic's message is put together by a formatter of the runtime's own, and in WebAssembly a line goes to the host whole by `writev`, with none of the C library's streams. Floats are written and read exactly by the runtime, with integers as large as the digits need, rather than by `printf` and `strtod`; the standard library now says what a float's text is, and the reference, C, LLVM, WebAssembly and JavaScript all write it alike (std, spec 0.109).
- One allocator, the runtime's, which in WebAssembly is the program's `malloc`, the C library's own code's too: classes of sizes from the pages memory grows by, and runs of whole pages for larger blocks, in place of `dlmalloc`.
- What is left of the C library is measured symbol by symbol: 128-bit division for showing the widest integers, the start of a WASI program and its preopened directories, `writev`, and the few streams the start of a program links.

## 8. Compile speed

*Done: the native compiler checks and compiles itself in 0.88 seconds, from 4.0; `--watch` compiles a change to a function again in about 100 milliseconds; native builds through LLVM use every core.*

- `--time` reports each phase: loading, checking, ownership, and code generation, which lowers and prints.
- What the profile showed was fixed where it was. A nominal type's class, whether it hides a borrow and whether it has a `Drop` are worked out once for the program, as the least solution over types that hold each other, not by walking its fields at every question; a method is looked up among the methods of its name; a trial unification is undone along a trail of what it bound, rather than by copying every binding; declarations, receivers and arguments are lent rather than copied; and a native program allocates from the runtime's own allocator, in classes of sizes with a cache per thread, which made binary-trees faster than C's.
- The cores go where the time is. Compiling the compiler's own C took eighteen seconds against the front end's one, so `llvm.sh` splits a program's module into a part per core, compiles the parts apart and links them with ThinLTO, which optimizes across them as one module would: the compiler builds in six seconds rather than nineteen, and runs as fast. The front end stays on one core: the time a change costs it is what `--watch` saves.
- `--watch` keeps the program between builds. A change to the bodies of a module's functions is checked, lowered and printed again for those functions alone, what they now reach for the first time with them; any other change compiles from scratch. The test changes a program's bodies and declarations, breaks it and mends it, and runs each build.

## 9. The proof joined to the compiler

*Done: a checker for λ-fly in Lean, proved sound, certifies on every build the test programs the compiler elaborates into λ-fly.*

The proof covers λ-fly; the compiler's checker was held to it by tests alone. Now the compiler's work is checked by the proof:

- `proof/FlyCore/Check.lean` is a checker for λ-fly's first-order part, `infer`, which decides an expression's type and what it leaves of its variables by λ-fly's rules, choosing where they leave a choice open: where branches disagree about a move, the variable is moved. It is proved sound, `infer_sound`: whatever it accepts is well typed, so, with the program's functions checked by it too, the program never gets stuck (`certified`).
- λ-fly's integers have the operations the language's do — arithmetic and comparisons, booleans as integers — so that ordinary code is in its part; a division by zero panics.
- `--core=f` writes the program `f` reaches as λ-fly, in Lean (`selfhost/core.fly`): integers, booleans, boxes, vectors and structs of two fields; bindings, assignments, branches, loops and arithmetic; calls that move and lend; failures of one integer. Anything else is refused with where it is.
- Each test program marked `// core: f` is certified on every build (`tests/proof.rs`): the checker runs in Lean's kernel, with no `native_decide`, on what the compiler made of it, and the certificate rests on Lean's standard axioms alone. The same programs run on every back end.
- What remains trusted is said in §9.5 of the spec: the elaboration from the source to λ-fly, and below it lowering and code generation. Closures, handlers, regions, tasks and generators are in λ-fly and its proof, but not yet in the checker, which answers for them `none`.

## 10. The standard library, filled out

*Done: files, processes, time zones, Unicode, regular expressions, an HTTP client over TLS and cryptography, each specified in [std.md](std.md) and tested on every back end its host allows, against handlers of its own and against the real system.*

- Files, directories and processes are `Io`'s own operations — `stat`, `list`, `mkdir`, `remove`, `rename`, `env`, `cwd`, `run` — so a test answers them in a handler, or the reference simulates a file system for it; `std/fs` walks trees and `std/process` runs programs, given what they read, and gives back what they wrote.
- `std/time` reads zones from the system's tz database, RFC 8536's files and POSIX's rules after their last change, and writes and reads ISO 8601. `Io.wall` is the time of day, virtual against a simulated world.
- `std/unicode` iterates code points and grapheme clusters by UAX #29, normalizes to NFC and NFD, and maps cases, from tables of Unicode 18.0.0 that `tools/unicode.py` writes; it passes Unicode's own tests of clusters and of normalization.
- `std/regex`, in Flyscript, compiles RE2's syntax to a program that a Pike VM runs, every thread at once, so a search takes time linear in its text: no pattern makes one backtrack. It finds what RE2 finds, leftmost-first, groups and all, in 9000 cases written by `tools/regex-cases` with Rust's `regex` crate, after 129,000 checked; a literal prefix and the bytes a match can start with let it skip what cannot match.
- `std/crypto` binds OpenSSL's libcrypto, loaded when first used natively and by the reference, Node's in JavaScript and under WASI, WebCrypto in a page: SHA-2, HMAC, HKDF, AES-256-GCM and Ed25519, each pure, and secure random bytes as `Io.random`, which a simulated world gives from its seed so that a run replays. Each host passes the standards' own test vectors.
- `std/http`, in Flyscript, is an HTTP/1.1 client over `std/net`, with `Socket.connectTls` through libssl, the certificate checked against the system's roots for the host; it is tested against a simulated world's peers on every back end and, natively, against a real TLS server.

## 11. Packages, a lockfile and `fly`

*Done: `fly new`, `build`, `run`, `test`, `add`, `update` and `accept` ([fly.md](fly.md)); the example site and the compiler build from their manifests, an update that adds an effect stops the build, and two builds from one lockfile are the same, byte for byte.*

- `fly` is a Flyscript program, `selfhost/fly.fly`, with a reader of TOML of its own; the launcher in the repository's root builds it and the native compiler when their source changes.
- `fly.toml` names a package, its kind — a program, a library or a site — and its dependencies, from git by a semantic version requirement, or by path. Both compilers find a package's modules where the build says it is, by `FLY_PACKAGES` (spec §8.1).
- `fly.lock` records each dependency's version, the commit its tag named, and SHA-256 of its files, which every build checks; a commit is fetched once, into `FLY_HOME`.
- It records too what each exported function performs, from the compiler's `--interface`, and whether the package vouches for unchecked code. An update after which a function performs `Io` or `Unsafe` where it did not, or a module has an `unsafe` block or an `extern` function where none did, stops the build and says where, until `fly accept` records it.
- `tests/fly.rs` makes a package and a repository to depend on, adds it, runs the package's tests, updates the dependency into `Io` and into foreign code and sees both stopped, changes its fetched files and sees that stopped, and builds twice from one lockfile, fetching afresh the second time, to the same bytes; and builds the site and the compiler from their manifests.

## 12. The runtime in Flyscript

*Done: the runtime's higher layers are Flyscript, in `selfhost/rt`, over a C core that switches stacks, makes system calls, parks and wakes threads, and tells the sanitizers about fibers; every back end interleaves tasks as before, from a seed, on every test.*

- Numbers as text (`rt/format.fly`): floats shown in the fewest digits that read back, fixed to the even, read to the nearest, over bignums of its own, and integers of up to 128 bits. Byte for byte what the C did, and what the JavaScript runtime does, on 200,000 random floats.
- The scheduler of a simulated world (`rt/sched.fly`): ready and waiting tasks, the seeded choice at each scheduling point, waits and wakes, scopes and their failures, cancellation, the virtual clock and channels, all of it values the scheduler owns. A task asks it as a handler is asked, by a request and a switch to the scheduler's stack; what needs no choice of who runs next is answered on the task's own stack, through `Ptr.with`, and a task woken from a receive is resumed with its message. It switches as often as the C scheduler did, and runs a channel ping-pong within 1.2 times its time; the simulated world is for tests and replay, and programs on the machine run on the scheduler for every core.
- Channels and `Mutex` on every core (`rt/mt.fly`): what a channel holds and decides — its messages, senders, closing, a receiver gone, whom a message wakes — and how a `Mutex` is taken and given back, over the core's monitors: a lock held for a few instructions and the tasks parked under it. As fast as the C they replace, faster on a channel ping-pong. The core keeps what only threads and the operating system need: the workers and their work-stealing deques, parking and inboxes, timers and the poller.
- Buffered I/O (`std/io`, in Flyscript): `File` reads ahead into a buffer of its own and streams a file a line at a time, and `Writer` gathers writes, over `Io`'s descriptors, which a test may answer itself; `String.fromUtf8Lossy`, `Vec.extend` and `slice.copyFrom` came with it.
- What the move found: `String.fromUtf8` did not check its bytes in compiled code; a loop over a generator leaked what an outer binding held when it assigned it; a range of a list lent `mut` changed a copy in JavaScript; a punned field was not a move in the reference; a closure missed the names in a range; and a program that starts tasks did not link when built split across cores, which `fly build` does.
