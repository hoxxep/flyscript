# Roadmap

Flyscript compiled itself, to JavaScript and to C, when this roadmap was written. Its steps take it from a self-hosted language to a systems platform: one intermediate form under every back end, kernels, LLVM, WebAssembly, every core of the machine, and a web framework that shows what all of it buys. Steps 0 to 12 are done, and each says what was built. Steps 13 to 19 close what remains between Flyscript and every language it is measured against; [what they are for](#what-steps-13-to-19-are-for) comes first.

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

## What steps 13 to 19 are for

The aim is a language with no remaining technical reason to choose another one for systems work: as fast and as small as Rust and C, with Erlang's fault tolerance, TypeScript's surface, and a mechanized proof under all of it. Measured against each neighbor, what is left is this:

| Against | What Flyscript has | What it still gives up, until these steps |
|---|---|---|
| Rust | No lifetime parameters, no `async` colouring or `Pin`, cyclic data in regions, error sets by union, `comptime` instead of procedural macros, deterministic simulation, a mechanized proof | A parked task keeps a whole stack where a Rust future keeps only what lives across its `.await`s (step 15); horizontal SIMD (step 17); failures returned through memory and aliasing LLVM is never told (step 19) |
| Erlang | Native speed, no garbage collector, types | A bug in one connection ends the whole server (step 13) |
| C and Zig | Memory and data-race safety, effects, closures | Nothing at the language level; the runtime's last costs (step 16) |
| TypeScript and Go | No garbage collector, unboxed layouts, real sum types, race freedom | Nothing |

Once these steps are done, what Rust has that Flyscript lacks is its ecosystem, which C libraries reach through `extern "C"` until native packages grow, and nothing in the language. Each step below says what it is for, what it changes, and what it must measure to be done: a step is done when its bar is met on every back end, not when its code is written.

## 13. A panic ends its task

**Goal.** Erlang's fault tolerance at Rust's speed. Today a panic ends the whole program, so a server holding 5,000 connections drops all of them when one request hits an index out of bounds or an overflow, and anyone who finds that one input can take the server down at will. Erlang never has that problem, because a crash ends only its process; but Erlang pays for it with a garbage collector and copied messages. Flyscript can have the isolation without paying for it, because its types already prove what Erlang gets by copying: a task shares nothing mutable with another except through a `Mutex`, and everything it owns is its own.

**The unification.** Today a computation stops early in one of three ways:

1. `throw`, which unwinds to a `try`/`catch` or a `fork`, running drops and `defer`s;
2. a dropped continuation (proved in 0.105), which unwinds to the continuation's root, running drops and `defer`s, with every operation a `defer` performs cancelled, so that unwinding can never wait;
3. a panic, which stops everything and drops nothing.

The third becomes a case of the first two: **a panic unwinds the task it happens in, as a failure that nothing can catch, or a continuation dropped in place, would.** This removes a mechanism rather than adding one. A panic — an index out of bounds, an overflow, division by zero, `unwrap()` of `#None`, `panic(message)` — unwinds the task to its root, and no handler, `try` or `catch` inside the task can stop it. Everything the task owns is dropped and its `defer`s run, to their end, as they do for a failure: §5.6 lets a `defer` rely on its `Io`, a connection closed with a last message, and a panic keeps that promise. (The operations of a continuation's cleanup are cancelled only when it is dropped cut off from every handler, after leaving its arm; a panicking task unwinds in place, its handlers around it.) A socket it owned closes; a channel it was the last sender of closes, and its receiver wakes; its regions are released. Then:

- **in `main`**, the message is printed and the program exits with a failure status, having leaked nothing, so even a panicking program passes the leak checker;
- **in a task started with `fork`**, the scope is cancelled and the panic carries on in the task that opened it, from `Io.scope`, because that task asked for the result;
- **in a task started with `spawn`**, it ends there: the message is reported, and the scope and every other task go on. A server that spawns its connections survives a connection that hits a bug, as it already survives one that fails;
- **inside `Mutex.lock`'s body**, the mutex is poisoned and its value stays where it is. `lock` lends the body `mut T` in place, so when the body panics the value may be half updated: two fields changed of three. Dropping it in the panicking task would run `T`'s `Drop` on that state, and a `Drop` that panics there aborts the program, the opposite of what this step is for. So waiters wake, and locking a poisoned mutex panics; the value is dropped when the mutex is, or when `reset(value)` replaces it, which clears the poison.

**The rest of what makes Erlang dependable.** A crash staying in its process is half of it. The other half is dealing with a process that is stuck, and restarting what crashed:

- **Stopping one task.** `spawn` returns a handle that cancels that task alone, so a task that has run too long can be ended without ending its scope. A cancelled task unwinds from its next `Io` operation, as cancellation already does.
- **Stopping a loop that never waits.** Erlang gets this from preemption; Flyscript's tasks are cooperative, so without help a pure infinite loop could be neither stopped nor killed. Compiled code polls the task's cancellation flag, a load and a predicted branch, at the back edge of every loop that does not perform `Io` on each iteration, and on entry to every function that is recursive (in a cycle of the call graph). Code with neither runs for a bounded time, so it needs no check. A cancellation noticed in pure code unwinds the task exactly as a panic does, since pure code has no other way out. Signal-based safepoints are not used: they do not exist in WebAssembly or freestanding programs, and an asynchronous signal can stop a function between the points where its cleanup state is defined.
- **Stack overflow as a panic of its task.** Recursive functions compare the stack pointer with the task's limit on entry, two instructions, and panic before they reach the guard page. Non-recursive call chains have a stack depth known at compile time and need no check.
- **Supervision**, in `std/supervise`. Children are given as functions that build them afresh, since a task that panicked leaves nothing to resume. They are restarted one for one, all for one, or the rest for one, with a limit on restarts in a span of time; past the limit the supervisor itself panics, to its own supervisor. This answers §12.3's second question, supervision beyond scopes, as a library.

A panic inside a `Drop`, or while a panic is already unwinding, ends the program; a freestanding program's panics go to the handler it names. Panics remain outside the effect system: `xs[i]` and `a + b` stay pure, so `par` and every pure function stay as they are, and `xs.get(i)` stays the way to index with a number that came from outside.

**What unwinding from pure code requires.** Today a panic is a terminal state, so nothing after it is ever observed. Once code runs after a panic, every point where a panic can happen must leave memory in a state that drops and `defer`s can safely see:

- **Assignment evaluates before it drops.** `place = rhs` computes `rhs` completely, then drops the old value and stores the new one, with nothing that can panic between the two. If the old value were dropped first and `rhs` then panicked, unwinding would drop it again.
- **Containers stay consistent.** Every runtime routine and library container (`Vec.pop`, `HashMap.remove`, growth) keeps its length and its initialized elements in agreement at every point where it can panic.
- **`join` and `par` wait before they unwind.** These run pure closures on other workers, borrowing the caller's stack. If one half panics while a thief still runs the other, unwinding the caller would free memory the thief is writing. So `join` sets the sibling's cancellation flag, waits for it to finish, drops its result, and only then passes the panic on.
- **A task is finished when its unwinding is.** `Io.scope` returns only when every task started in it has finished running its drops and `defer`s, whatever ended them. Otherwise a spawned task's `defer`, still running on another core, could read a `readonly` borrow from outside the scope after the scope has returned and dropped it.

**Every back end.**

- **The reference evaluator** unwinds as it does for a failure nothing catches.
- **JavaScript** throws, and its `finally` blocks run the cleanups.
- **LLVM, natively,** uses landing pads, as Rust does. A call where a block's cleanups are live is an `invoke`, and its landing pad drops exactly what may hold a value at that call, then runs the `defer`s around it and resumes. Calls nothing is live across stay plain calls, and checked arithmetic and bounds checks stay a compare and a branch, with only the cold call to `fly_panic` invoked. The personality is the runtime's own, `fly_personality`, which reads the Itanium exception tables. A panic is raised in two phases, as a C++ exception is, and caught by the runtime's catch points (a task's root, a fiber's entry, `Io.scope`, `Mutex.lock`, `join`, `main`). Each catch point calls `fly_try`, which is written in IR because C cannot catch, with a landing pad that catches the panic's type and nothing else. A landing pad runs as code of its own frame, so a cleanup may wait and let other fibers run, and unwind panics of their own. No `setjmp` or `longjmp` remains. Measured on the compiler compiling itself, the unwind tables and the loss of `nounwind` cost nothing, and the landing pads cost about a tenth, which step 16 is to bring down.
- **WebAssembly** uses landing pads too, through its own exceptions (`-fwasm-exceptions`). A pad is a funclet (`cleanuppad`), and each call inside it carries its `funclet` bundle. A panic is thrown with the C++ tag, which the runtime defines because there is no C++ library, and `fly_try` catches it with a `catchpad`. Both a pad and `fly_try` first ask whether a panic is what is passing (`fly_panicking`): the host ends a program by throwing an exception of its own (`proc_exit`), which must run no cleanup. On the compiler compiling itself this halved the time records took, 3.4 s to 2.0 s.
- **The C back end** has the C compiler run its cleanups, as the platform unwinds. The C is compiled with `-fexceptions`. A function with cleanups keeps a frame record, `fr_`, declared with `__attribute__((cleanup))`. Its cleanup is the code a panic goes to, made a function of its own, `always_inline`. It reads, through the record, which block the code was in and the addresses of the locals it drops, under the locals' own names. Inlined, the record comes apart again. A landing pad drops a copy of each local rather than the local itself, so no local's address is taken and locals stay in registers. Leaving the function normally, `at` is zero and the cleanup does nothing. C cannot catch, so a panic is a forced unwind, as a thread's cancellation is, stopped at the innermost catch point, which keeps the only `setjmp` record left. Measured on the compiler compiling itself, this took the C back end from 3.6 s with a record in every function with cleanups to 1.35 s, against 1.07 s before panics unwound. Most of what remains is that every call in such a function becomes an `invoke`, because the record covers the whole function. Records per block would make only calls with live cleanups invoke, as LLVM's are (step 16).
- **Freestanding programs** do not unwind: a panic goes to `fly_os_panic`.
- **Running out of memory ends the program**, as in Rust: unwinding would itself need memory, and nearly every function allocates, so nearly every one would be one a panic may leave. Code that must survive it makes room first, with `tryReserve`.
- **An LLVM bug, worked around.** On AArch64, in a function that took up a `setjmp` record, clang's redundant copy elimination reused the 64-bit register holding a union's tag, whose upper half is the padding of a returned value, in place of the 64-bit constant the tag had been compared with (Apple clang 21 and LLVM 23, under the sanitizers). Every build of a program's C turns that pass off on AArch64 (`selfhost/ccflags.sh`). Records now remain only at the C back end's catch points, so the trigger is nearly gone, but the workaround stays until LLVM fixes the bug.

**The proof.** A panic becomes a step from any expression, not only from an operation, because panics happen in pure code. It drops the task's continuation as a dropped continuation already does (§9.5). The calculus is in A-normal form, so there is no state halfway through a record literal or a call to account for; the conditions above are what the compiler and runtime must uphold for the proof to describe them. The theorem then says more than it does now: even when a spawned task panics, everything it owned is dropped exactly once, nothing leaks, and every other task goes on, under every schedule.

**Done when:** a server under load keeps every other connection when one panics, a test shows it on every back end, the theorem covers panics, and §5.7, §6.1, §6.2 and §12.3 say so.

## 14. The spec brought up to date

**Goal.** The spec is the product as much as the compiler is, and it should be the clearest statement of a language anyone has written: short where things are simple, exact where they are not, and with nothing that is no longer true. Every claim it makes about what is proved, what is open and what Flyscript gives up should be current.

- `generate` and `next`, primitives since 0.106, in the core calculus of §9.1.
- §12.3's third question says what is proved now: continuations kept in a value, and tasks that synchronize through `Io`, are.
- `RegionList<region R, T>` in one order throughout.
- §0.1 says what the current version is and what the last few versions changed; the full record of revisions moves to `docs/history/`.
- **Re-exports**, `export { a, b } from "./internal/a"`: a package presents one public face over the files behind it, as Rust's `pub use` lets a crate do, in one line of grammar and with ES modules otherwise unchanged.

**Done when:** every section agrees with the compiler and the proof, §0.1 fits on a screen, and re-exports work on every back end.

## 15. Parked tasks as small as a future

**Goal.** Win the last comparison Rust still wins. §12.1 says Flyscript gives up "stackful tasks instead of compiler-built state machines": a parked Rust future holds only the variables live across its `.await`s, a few hundred bytes, while a parked Flyscript task holds a whole stack. At ten million idle connections that is the difference between about 2 GB and 8 to 16 GB. Rust pays for its small futures with `async`, `await`, `Pin`, `'static` task bounds and a standard library split in two (`std` and `tokio`). Flyscript can have the small futures and pay none of that, because it already knows what Rust makes the programmer write down: after specialization, each function's effects say whether it can suspend — whether it performs `Io`, `Yield`, or an effect whose handler does not resume as its last act — and the calls in its body that can suspend are its `.await`s.

- **A function that cannot suspend** runs on the worker's own stack, wherever it is called from. It takes no room in a parked task.
- **A function that can suspend** is compiled to a state machine: a frame holding the locals that live across a suspension, overlapping where their lifetimes do not, a resume point, and a function that goes on from there. A direct call to a suspending function that is not recursive nests the callee's frame in the caller's, in a union over the caller's suspension points. A task whose calls are all of that kind, such as a connection handler that reads, queries and writes, gets one frame of a size known at compile time, allocated when the task starts and never moved. A borrow held across a suspension (`conn.read(mut buf)`) points into that frame, and there is no `Pin`, because user code never holds a frame by value and so can never move one.
- **Calls whose callee's frame size is not known at compile time** take their frame from the task's frame arena, a chunked bump allocator, popping it on return. These are calls through a suspending closure (`f: () => void uses Io`), recursion among suspending functions, and calls through `dyn`. A closure that can suspend carries its frame size, so `map` and every other higher-order function compile to at most two versions per element type: one for closures that cannot suspend and one for closures that can, the split Swift makes for `async` and Koka for its effects. Arena frames never move either, so borrows into them are as safe as borrows into the task's own frame.
- **Continuations that outlive their handler, and generators,** get a frame arena of their own. When an arm keeps or returns its continuation (§5.3), the `handle` expression returns while the continuation is still alive, so the body's frames cannot be nested in the caller's: the caller would reuse that space for its next call. The compiler already knows which handlers' continuations escape. Those handlers, and `generate`, allocate a detached arena that the continuation or the `Gen` owns. Dropping it walks the frames from the innermost outward, running each frame's cleanups for the point where it stopped.
- **Fibers are retired.** Stackful fibers remain only until state machines cover tasks, generators and handlers; the C and LLVM runtimes then have one suspension mechanism. C cannot call into Flyscript code that suspends, since an `export extern "C"` function performs nothing (§8.2), so no fiber is needed for foreign callbacks.
- **Fast paths stay in registers.** An uncontended `Mutex.lock`, a buffered read with bytes waiting, and a channel receive with a message waiting do not suspend. They are compiled inline as ordinary code, so the common case never reaches the scheduler.
- **Small machines.** A program whose tasks make no indirect or recursive suspending calls has every task's state of known size. It can be placed in static memory with no allocator, as Rust's embedded async runtimes do on microcontrollers with a few kilobytes of RAM.

No language change is needed. There was no `async` and no `await`, and there still is none. JavaScript already runs effects as generators, and WebAssembly no longer needs stack switching from its host.

**Done when:** a parked connection handler costs what the equivalent Rust future costs, within tens of bytes, measured; a million parked tasks fit in the memory a million Rust futures take; nothing that does not suspend runs slower; fibers are gone from the native runtime; and §8.2, §8.3, §11.3 and §12.1 say so.

## 16. Parity with the runtime it replaced

**Goal.** Moving the runtime into Flyscript (step 12) must cost nothing. This step comes after state machines (step 15) because the simulated scheduler's remaining cost is in the path step 15 rewrites: fibers, and the switch to the scheduler and back. A language that claims C's speed cannot run its own scheduler or read its own files slower than the C it replaced; if it does, the claim is false where it is easiest to check.

- **The simulated scheduler** runs a channel ping-pong in 1.2 times the old C scheduler's time, with as many switches. The simulated world is how every concurrent program is tested and replayed, so it is on the path of every test run. Every request that needs no choice of who runs next is to be answered without a switch, and a send or receive is to allocate nothing.
- **The line reader** takes 1.33 times the CPU of the C reader it replaced, which did not check that its text was UTF-8. It is to match that reader while still checking, finding a line's end and checking its bytes in one pass, eight bytes at a time and, after step 17, sixteen.
- **The same interleaving everywhere.** Done: the reference evaluator, JavaScript, C, LLVM and WebAssembly interleave tasks identically from any seed (§11.1's promise), which a test of the suite checks across 25 seeds.
- **Closures that are only called live in their caller's frame.** A closure literal passed to a function that takes a `once` closure (`with`, `Io.scope`, `Mutex.lock`) has its environment allocated on the heap, though the callee only calls it. Rust never pays this, because each closure is its own type and lives on the stack unless boxed. The compiler is to find which closure parameters a function only calls, and put those closures' environments in the caller's frame.

**Done when:** the ping-pong and the line reader are within the run-to-run noise of the C they replaced, or faster, and the interleaving test passes on all five implementations for every seed it tries.

## 17. Portable SIMD

**Goal.** Close §12.3's first question. `Soa<T>`, `par` and LLVM's auto-vectorizer already handle vertical arithmetic, the same operation on every element. They cannot do horizontal work, where lanes talk to each other: scanning sixteen bytes at a time for a quote or a newline as simdjson does, checking UTF-8, reductions, and shuffles. That work is where the fastest parsers in any language get their speed. It must be portable without an emulation cliff. ARM's NEON has no single instruction for x86's `movemask`, so code written around one is slower on ARM than plain scalar code, unless the API also offers what ARM does well.

`std/simd`: `Simd<T, comptime N>`, `N` lanes of a scalar, and `Mask<comptime N>`, both `Copy` and `Send`, lowered to LLVM's vector types and so to SSE and AVX, NEON, and WebAssembly's 128-bit SIMD. The surface:
- construction from a value or from a slice, bounds-checked once for all lanes;
- lane-wise arithmetic, bitwise operations, `min`, `max` and saturating arithmetic;
- comparisons that return a mask, and reductions;
- shuffles by indices known at compile time, and byte lookup by a vector of indices;
- on a mask: `select`, `any`, `all`, `firstTrue` and `bitmask`. `firstTrue` is lowered on ARM in two instructions (`shrn`, then count trailing zeros), so finding the first match costs no more there than on x86.

No grammar change is needed; `comptime N` is already in the language. JavaScript and the reference evaluator run SIMD a lane at a time.

**Done when:** the JSON scanner, UTF-8 checking and the line reader use it and are measurably faster on x86-64, AArch64 and WebAssembly, and no target is slower than scalar code.

## 18. FlyNext, order-free and faster

**Goal.** FlyNext's architecture is already faster than React's: the server streams HTML straight into a buffer with no tree, and the browser diffs two flat arrays in linear memory instead of a tree of objects the garbage collector must chase. Two things stand between it and a framework without footguns or wasted work.

- **Props anywhere in an element's body.** Today an attribute, class, key or listener given after an element's text or first child is silently wrong. The server writes it into the element's text (`<button>Save class="primary"</button>`) and the browser ignores it. This is a correctness bug that looks like a style rule. Order inside `el(...)` must not matter: the server writes an element's opening tag once its attributes are all known, and the browser reads an element's props past its children.
- **No wasted work in the diff.** Each recorded `#Open` knows where its element ends, so finding an element's span is a lookup rather than a scan, which removes the quadratic cost on deep pages. Strings go to the DOM as a pointer and a length into the module's memory rather than being copied into a new buffer each time.

**Done when:** props in any order render identically on the server and in the browser, by test, and diffing a 1,000-row table is measurably faster.

## 19. What LLVM is told

**Goal.** Give LLVM everything Flyscript's types already know, so that generated code is as good as hand-written C or Rust, or better, since Rust cannot promise what `readonly` promises.

- **Failures returned in registers.** A function that can fail returns its failure beside its value, in two registers, rather than through memory, so the path that does not fail costs what a plain return costs.
- **Aliasing.** A `mut` parameter is `noalias`. A `readonly` one is `noalias readonly` wherever nothing in it can change through a `Cell`. LLVM can then vectorize loops and keep values in registers across stores and calls where it could not before.

**Done when:** the compiler benchmark and the numeric examples are measurably faster, and the code LLVM produces for the vectorizable loops is vectorized.
