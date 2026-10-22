# Review: systems-roadmap

- spec: 4b343628ab34
- request: 7135fa4c3e22b32f
- tokens: prompt 84340, cached 0, answer 7069

## Question

# Flyscript: the next five phases — review the plan before we build

Context: spec 0.55 (attached). The compiler is self-hosted (`selfhost/*.fly`, ~19k lines of Flyscript) with two back ends, both from the typed, ownership-checked AST: typed JavaScript (`js.fly` + `runtime.js`) and GNU C (`c.fly` + `runtime.c`, no GC, fibers in a few lines of arm64/x86-64 asm, ASan/UBSan/leak-clean on the whole corpus, compiler compiles itself natively at a fixpoint). A Rust reference interpreter (`flyc`) defines semantics; all three agree on every test program, including a deterministic task scheduler (one thread, xorshift seed, virtual clock).

The owner has set this order: (1) "kernel tweaks", (2) a WebAssembly back end, (3) an LLVM back end, (4) multi-core tasks, (5) a proof of concept of a Next.js + React replacement (one component tree: native SSR, Wasm hydration, typed server functions, per-route Wasm chunks). Below is my plan for each. I want you to attack it: wrong order, wrong abstractions, things that will not work, designs that add concepts the language does not need, and what you would do instead. Be concrete.

## Phase 0 (prerequisite, slotted before 2): a post-monomorphization Core IR

Your last review's top recommendation. `ir.fly`: lower the checked AST once, after monomorphization, into a flat statement IR: concrete layouts; temporaries lifted into `Let`s in evaluation order; each block with an explicit cleanup list (drop local / defer / free arena) and every early exit naming the depth it unwinds through; closures converted to `{fn, env, drop}`; region evidence explicit; effect classification per function (pure / fails / regions / suspends). Then port the C back end onto it (it becomes a printer, and cleanup becomes lexical rather than drop-everything-at-one-exit), and build Wasm and LLVM on it. The JS back end stays on the AST for now (it relies on JS generators for suspension, which the IR need not model) — or should it move too?

Question: is it right to do the IR *before* the kernel work, given phase 1 adds back-end features (raw pointers, volatile, C ABI exports) that would otherwise be written twice?

## Phase 1: foreign code and a freestanding profile ("kernel tweaks")

§8.2 is specified but not implemented: the checker rejects `T*`. Plan:

1. **Raw pointers** `T*`: `Copy`, not `Send`. Inside `unsafe`: `p.read()`, `p.write(v)`, `p.add(n)`, `p.readVolatile()`, `p.writeVolatile(v)`, `p.cast<U>()`, `p.address(): usize`, `Ptr.at<T>(addr: usize): T*` (MMIO), `Ptr.null<T>()`, `p.isNull()`, and `Ptr.to(mut x): T*` / `Ptr.to(readonly x)` to take an address (a pointer outliving its referent is the `unsafe` block's promise). Pointers are not borrows: they are plain values the ownership pass ignores.
2. **`extern "C"`** declarations, calls only in `unsafe`; parameter and result types restricted to C-representable ones (integers, floats, bool, pointers, `@layout(c)` structs, `void`). The JS back end and the interpreter reject programs that call extern functions (or the interpreter gets a tiny fixed table for tests?).
3. **`export extern "C" function f(...)`**: a Flyscript function with C ABI and a fixed symbol, callable from C or assembly. Its effects must be empty (no `Io`, no `Fail` escaping): it is a root.
4. **Fallible allocation**: one addition, `tryReserve(n): void uses Fail<#OutOfMemory>` on `Vec`, `String`, `HashMap` (after which `n` pushes cannot allocate), and `Box.tryNew(v)`. Allocation stays infallible (panic) by default. Rejected: an `Alloc` effect on every allocation (would color the whole standard library), and a profile that changes allocation types (splits the library).
5. **Freestanding target** (`--freestanding`, C back end, later LLVM): no `main`; the entry points are `export extern "C"` functions; the runtime drops stdio, files, sockets, the scheduler and the `world`; `Io` is unavailable (a function that needs it is a compile error naming the target). The program supplies three C-ABI hooks: `fly_os_alloc(size, align)`, `fly_os_free(p)`, `fly_os_panic(msg, len)` — either in C/asm or as `export extern "C"` Flyscript functions. Fibers (handlers with suspending continuations, `generate`) still work: they need only the allocator and the context-switch asm. Regions, `defer`, `Fail`, generators all work unchanged.
6. **No inline `asm`, no `@section`**: kernels link a small `.S` file (boot, context switch, system registers) and call into it through `extern "C"`. Keeps the core small and works identically on C and LLVM.
7. **Proof**: `examples/kernel/`: an AArch64 kernel for QEMU `virt`: `boot.S` sets up a stack and calls `kmain`; Flyscript drives the PL011 UART through `writeVolatile`, runs a page-frame allocator (a free list over a `Pool`-like array) whose `alloc` is `Fail<#OutOfMemory>`, uses `Vec.tryReserve`, regions per "syscall", `defer` for lock release, and an effect `Sleep` that interrupt-context code (a `uses []` closure) statically cannot perform. CI runs it under `qemu-system-aarch64` when present.

## Phase 2: WebAssembly

Emit the Wasm binary format directly from the Core IR in Flyscript (no toolchain dependency; the compiler itself can then run as Wasm, e.g. in a browser playground). Linear memory with the same layouts as C (wasm32: `usize` 32-bit); a small allocator in Flyscript or a minimal runtime in Wasm; multi-value returns for failures.

The hard part is suspension (`handle` with suspending continuations, `generate`, tasks, and `Io` mapped to host promises). Options:
- (a) JSPI (`WebAssembly.Suspending` / `promising`, shipped in V8 13.x / Node 24): each fiber is a separate `promising` invocation; switching awaits a promise. Works today, every switch costs a microtask, needs JS host.
- (b) The stack-switching proposal (`cont.new`, `resume`, `suspend`): exact match to our one-shot continuations, but behind flags.
- (c) A selective state-machine transform (Asyncify-like), applied only to functions whose effect rows say they can suspend — the effect system tells us precisely which. Portable to any engine and WASI, more compiler work.
My inclination: (c) for functions that can suspend, because the effect system makes it selective and cheap, with (b) as a later optimization. Is that right, or is (a) good enough for a PoC and (c) a trap?

`Io` in the browser: the root handler calls JS imports; `Io.sleep`, fetch, etc. resolve promises that resume the waiting fiber via the scheduler.

## Phase 3: LLVM

Textual `.ll` from the Core IR (no C++ bindings), compiled with `clang`/`llc`, linked with the existing `runtime.c` (compiled by clang) so fibers, scheduler and arenas are shared. Gains: exact integer semantics (`nsw` only where we prove it, real overflow intrinsics), debug info (DWARF line tables mapping to `.fly`), `musttail`, and wasm32 as a second route. Gate: corpus identical, self-compile fixpoint. Question: worth keeping C once LLVM exists? (I think yes: C is the portable bootstrap.)

## Phase 4: multi-core tasks

The spec already makes task concurrency race-free (`Send`, readonly captures, frozen regions, `Mutex.lock` bodies that perform no effects). Runtime work: per-fiber unwind state (`{kind, err}` on the fiber, current fiber in a `_Thread_local`), small pooled fiber stacks with guard pages, atomic `Arc`, an M:N work-stealing scheduler over N worker threads with `kqueue`/`epoll` (`io_uring` later), and `par` / `parReduce` on a fork-join pool. The deterministic single-thread scheduler stays as the simulation mode (`FLY_WORLD` / seed) and is what tests run; the multi-thread scheduler is the production mode. Question: should determinism in simulation and real parallelism share one scheduler implementation with a pluggable "next task" policy, or be two?

## Phase 5: FlyNext proof of concept

- `effect Ui<Msg>` with operations `element(tag, attrs, children: () => void uses Ui<Msg>)`, `text(s)`; components are plain functions `uses Ui<Msg>`; `if`/`for`/`match` work inside the tree.
- Server: an `Ui` handler that streams HTML into the response buffer (per-request region), native.
- Client: a Wasm `Ui` handler that hydrates the server's DOM (walks it in the same order) and then re-renders on messages with a keyed diff against the previous render's flat op list (no VDOM objects; the op list lives in a per-frame region). An Elm-like `update(model, msg)`; a tiny JS shim applies DOM ops from a ring buffer.
- Server functions: an `effect` declared in a shared module; the server handles it directly; the client handler is generated by `comptime` from the operation signatures (binary codec, failures as `Fail` tags re-raised on the client).
- File routes `pages/*.fly`, a per-route Wasm module importing shared memory and a core module.
- Demo: a small store or issue tracker; measure SSR throughput vs Next.js and client bundle size vs React.
Question: is the effect-based `Ui` (direct-style emission) a sound basis for keyed diffing and event handlers, or will it fight us (e.g. closures as event handlers vs. `Msg` values)? I plan `Msg` values only (no closures in attributes), which makes the op list serializable and SSR/hydration trivial.

## What I want from you

1. Order: is "IR first, then kernel, Wasm, LLVM, multi-core, FlyNext" right? What would you reorder and why?
2. For each phase, the one decision most likely to be wrong, and the alternative.
3. Anything in phase 1 that adds a concept the language does not need, or misses one a kernel really needs (interrupt-safety? atomics/fences? alignment? packed structs? `MaybeUninit`?).
4. The Wasm suspension choice.
5. Anything here that conflicts with the spec as written.

## Context files

- `docs/spec.md`

## Answer

### Verdicts

- **Phase 0 (Core IR before Phase 1):** **Agree with changes.** Do `ir.fly` *before* Phase 1 so raw pointers, `extern "C"`, and layout calculations are lowered once, **and move the JS backend onto `ir.fly` too** (do not leave JS on the AST).
- **Phase 1 (Foreign code & freestanding kernel profile):** **Agree with changes.** The `extern "C"` / `--freestanding` / `.S` boundary is right, **except**: (1) `Ptr.to(readonly x): T*` is a mutability-casting footgun unless `readonly T*` vs `mut T*` or `Ptr.to(mut x)` is distinguished; (2) `--freestanding` still needs `Atomic*` (`§6.2`), which currently requires `Io` in the spec; and (3) a kernel cannot define page tables, MMIO descriptors, or DMA rings without `@align(N)` and a sound `sizeOf<T>()` / `alignOf<T>()` / `zeroed<T>()` primitive.
- **Phase 2 (WebAssembly backend & suspension):** **Disagree with (c) selective Asyncify; Agree with a shadow-stack fiber switcher in linear memory (or JSPI) instead.** Option (c) is a trap: it duplicates the suspension mechanism across backends and breaks when taking the address of a stack local across a call (`mut x` lent to a suspending callee). Instead, use **the exact same shadow-stack / stack-pointer switching model in Wasm linear memory** as your C backend uses, or compile via Phase 3's LLVM `wasm32` target!
- **Phase 3 (LLVM `.ll` backend):** **Agree, and move Phase 3 *before* Phase 2 (or use Phase 3 to *produce* Phase 2's Wasm!).** Keep the C backend permanently as the zero-dependency bootstrap seed.
- **Phase 4 (Multi-core tasks):** **Agree with changes.** Do **not** merge the deterministic simulator (`SimIo`) and the M:N work-stealing OS scheduler into one "pluggable policy" implementation; keep them as two clean implementations of the root `Io` handler interface. Also fix one spec soundness hole (`§4.4`/`§6.1`) with `Cell<R, T>` and `RegionList<R, T>` captured by `readonly` borrow across `Io.scope` before running on multiple OS threads.
- **Phase 5 (FlyNext PoC):** **Agree with changes.** Pure `Msg` values for events and streaming `Ui<Msg>` effects are a great fit, **provided** you solve controlled text inputs (`onInput(str => Msg)` or a payload tag `#EmailChanged(String)`) and add a `key(k: str, children: () => void uses Ui<Msg>)` operation so keyed diffing and stateful DOM subtrees (focus, scroll, input cursor) survive re-renders.

---

### Problems

#### 1. Phase 2 vs Phase 3 Order & Wasm Suspension: Selective Asyncify (Option c) breaks `mut` borrows of stack locals across suspending calls (`§4.1`, `§5.2`, `§8.3`)

In Phase 2, you propose:
> *(c) A selective state-machine transform (Asyncify-like), applied only to functions whose effect rows say they can suspend — the effect system tells us precisely which.*

Here is a 10-line Flyscript program that shows why an Asyncify-style state-machine transform in linear-memory Wasm fails on valid Flyscript code:

```ts
effect Ask { ask(): i32; }

function mutateAcrossSuspend(slot: mut i32): void uses Ask {
  slot += 1;
  const delta = Ask.ask(); // Suspends here while holding `slot: mut i32`!
  slot += delta;
}

export function outer(): i32 uses Ask {
  let x: i32 = 10;         // Stack local in `outer`
  mutateAcrossSuspend(mut x); // Passes pointer to `x` (`i32*` in Wasm linear memory)
  x
}
```
Trace what happens under state-machine / Asyncify transformation (Option c):
- `outer` has `let x: i32 = 10` and lends `mut x` (a linear-memory address `&x`) to `mutateAcrossSuspend`.
- If `outer` and `mutateAcrossSuspend` are transformed into state machines whose locals are saved into per-frame heap structs when `Ask.ask()` unwinds the Wasm call stack, then either:
  1. `x` lived on the Wasm shadow stack at address `sp + 4` when `mutateAcrossSuspend` was called, and unwinding the Wasm stack pops `sp`, invalidating the raw address `slot` that `mutateAcrossSuspend` saved in its state machine, **or**
  2. Every stack local that is ever lent (`readonly` or `mut` — including `let buf: u8[512]` in `serveOne` in `§10.2`!) must be spilled into a per-fiber linear-memory stack segment that stays at a fixed address while the continuation is suspended!

Wait: look at (2) again. In linear-memory Wasm, you **already have an explicit shadow stack pointer `__stack_pointer` (`$sp`) in linear memory** for every local whose address is taken (structs, arrays `u8[512]`, `mut`-lent locals)!
If every suspending function keeps its locals on its fiber's linear-memory stack frame (bump `$sp` on entry, pop `$sp` on exit):
- A `Cont` / fiber already owns a fixed slice of linear memory (say 16 KB or a growable segment) for its `$sp`!
- Then `slot: mut i32` is just a 32-bit linear-memory offset into that fiber's stack slice — **it never moves while suspended**!
- Even better: if locals of suspending functions live on the fiber's linear-memory stack frame `(fp->pc, fp->caller, locals...)`, then switching fibers in Wasm does **not** need general binary-level Asyncify at all! Each suspending function in `ir.fly` is simply a flat basic-block switch on `fp->pc` whose locals are fields at fixed offsets from `fp` in the fiber's linear-memory stack arena!

And look at the **order of Phase 2 (Wasm) and Phase 3 (LLVM)**:
- If you do **Phase 3 (LLVM `.ll` from `ir.fly`) BEFORE Phase 2 (Wasm)**:
  1. `clang --target=wasm32-unknown-unknown` compiles your `.ll` (plus `runtime.c`) to heavily optimized Wasm **for free on day one**!
  2. LLVM's `wasm32` backend *already* maintains `__stack_pointer` in linear memory, and paired with either **JSPI** (in browser/Node 22+, zero state-machine transform needed — just switch `__stack_pointer` to the fiber's linear-memory stack when switching fibers!) or the **`ir.fly` fiber-frame lowering**, you don't even have to write a custom Wasm binary encoder and register allocator unless you specifically want in-browser self-compilation without `clang`.
- **Recommendation:**
  1. Swap **Phase 2 and Phase 3**: build `ir.fly` -> **LLVM (`.ll`)** first, then **Phase 1 (Kernel on LLVM + C)**, then **Wasm**.
  2. For Wasm suspension, **do not write a separate Asyncify pass**. Either:
     - Use **JSPI + `__stack_pointer` swap** for browser/Node (50 lines of JS/Wasm glue, works in V8/Chrome/Node today, supports full C/LLVM optimizations), or
     - If you want pure Wasm 1.0 portability everywhere (Safari/Firefox/WASI without JSPI), do the **fiber-frame lowering in `ir.fly`** (where a suspending function's locals live in its fiber arena frame at `fp` and suspension returns `#Suspended` up the call chain, restoring `fp` on resume). Because the frame is in the fiber's linear-memory stack, `&x` (`mut x`) stays at a fixed address across suspension!

---

#### 2. Phase 0: Leaving `js.fly` on the AST while moving `c.fly`, `llvm.fly`, and `wasm.fly` to `ir.fly` duplicates the hardest part of the compiler

In Phase 0, you ask:
> *The JS back end stays on the AST for now (it relies on JS generators for suspension, which the IR need not model) — or should it move too?*

**Move `js.fly` onto `ir.fly` too.** Here is why:
1. Why did `ir.fly` come up in the first place? Because lowering Flyscript's surface AST (pattern matching with guards and per-arm move/borrow bindings `§4.1`, `if (const Pat = e && ...)` chains `§2.3`, two-phase borrows `§4.1`, `defer` and partial-move drop flags `§5.6`, closure capture modes `§4.3`, region evidence `§4.6`) directly in a code generator is complex and error-prone.
2. If `js.fly` stays on the AST while `c.fly` and `llvm.fly` use `ir.fly`, you have **two completely separate implementations of Flyscript's operational semantics** (evaluation order, pattern compilation, drop flags, `defer` unwinding, and Phase 1's `Ptr` operations). Every future language tweak has to be implemented twice.
3. Why do you think JS generators prevent `js.fly` from using `ir.fly`? **They don't!**
   In `ir.fly`, every function has an effect classification (`suspends: bool`), and every call/perform instruction is marked `suspends: bool`.
   - When `c.fly` / `llvm.fly` prints an `ir.fly` function, it emits a C / LLVM function.
   - When `js.fly` prints an `ir.fly` function with `suspends == true`, it emits `function*` and prefixes suspending `Call` / `Perform` instructions with `yield*` / `yield`!
   - And structured control flow in `ir.fly` (`Block`, `Loop`, `If`, `Switch`, `TryFinally` — rather than arbitrary `goto` spaghetti, which Wasm and JS both dislike!) maps 1-to-1 to C, LLVM basic blocks, Wasm `block`/`loop`/`br`, **and** JS!

---

#### 3. Phase 1 Soundness & Expressiveness: Four Kernel Blockers (`§6.2`, `§8.2`)

You asked in Question 3 whether Phase 1 adds any unneeded concepts or misses anything a kernel really needs. Here are four concrete issues, each with a program:

**Blocker 1A: `Atomic*` in `--freestanding` (`§6.2` conflict).**
In `§6.2`, `Atomic*` operations perform `Io`:
> *"`Mutex<T>`, `Atomic*` and channels — a `Sender<T>` and a `Receiver<T>` — are library types whose operations perform `Io` (through `Io.park`)."*

And in your Phase 1 plan (item 5):
> *"`Io` is unavailable (a function that needs it is a compile error naming the target)."*
> *"...and an effect `Sleep` that interrupt-context code (a `uses []` closure) statically cannot perform."*

Now try to write an interrupt handler or a spinlock or a reference count in your AArch64 kernel (`examples/kernel/`):
```ts
// Interrupt handler: must be `uses []` (cannot perform `Io` or `Sleep`)
export extern "C" function irqHandler(): void {
  // How does irqHandler increment a tick counter or release a spinlock or wake a task?
  TICKS.fetchAdd(1); // ERROR if AtomicU64.fetchAdd uses `Io`!
}
```
Why did `Atomic*` have `uses Io` in `§6.2`? Because of Law 2 ("Effects are visible: a function with no effects is pure") and `SimIo` interleaving (`Atomic.wait` / `park`).
Wait: in a kernel (and in lock-free code inside `unsafe`), raw atomic memory operations (load-acquire, store-release, CAS, fences) do **not** park on the OS scheduler!
**Fix (adds zero new concepts):**
Keep the high-level `std/sync` `Atomic*` with `uses Io` for task code and `SimIo`, and put raw hardware atomic operations on `T*` inside `unsafe` alongside `readVolatile` / `writeVolatile`:
- `p.loadAcquire(): T`, `p.storeRelease(v: T): void`, `p.compareExchange(expected: T, desired: T): [T, bool]`, `p.fetchAdd(v: T): T`, and `Ptr.fenceAcquire()` / `Ptr.fenceRelease()` / `Ptr.fenceSeqCst()` (for integer/pointer `T`).
Because they are on `T*`, they require `unsafe { ... }` (`§8.2`), so safe pure code (`uses []` without `unsafe`) still cannot observe shared mutation (Law 2 holds!), while kernel spinlocks, MMIO barriers on AArch64 (`dmb ish`), and `irqHandler` work in `--freestanding` with `uses []`!

**Blocker 1B: `Ptr.to(readonly x): T*` silently casts away immutability without a cast (`§8.2`).**
In Phase 1 item 1, you propose:
> *"`Ptr.to(mut x): T*` / `Ptr.to(readonly x)` to take an address"*

Look at what happens when both return the same mutable raw pointer type `T*`:
```ts
function readMmio(reg: readonly u32): u32 {
  unsafe {
    const p: u32* = Ptr.to(reg); // Took address of a `readonly` borrow!
    p.write(0);                  // Mutates through a `readonly` borrow without even a cast!
    p.read()
  }
}
```
Even worse: what if someone writes `Ptr.to(x)` where `x` is a `const` local or `readonly` parameter?
If Flyscript has only one raw pointer type `T*` (`§2.3`, `§8.2`), do **not** overload `Ptr.to` to accept both `readonly` and `mut` transparently!
Instead:
- `Ptr.fromMut<T>(r: mut T): T*` takes a `mut T` borrow (`Ptr.fromMut(mut x)` — mutable borrow visible at the call site, `§2.2`!), and
- `Ptr.fromRef<T>(r: readonly T): T*` (or `Ptr.fromConst`) explicitly states that you are obtaining a raw pointer from a `readonly` reference.
Also, remove `p.isNull()` and `Ptr.null<T>()` as special magic: `Ptr.at<T>(0)` is null and `p.address() == 0` tests for null! Fewer concepts (`Rule 3`).

**Blocker 1C: Missing `@align(N)` and `sizeOf<T>()` / `alignOf<T>()` for kernel page tables & allocators.**
In Phase 1 item 7, your kernel proof includes:
> *"an AArch64 kernel for QEMU `virt` ... runs a page-frame allocator ... uses `Vec.tryReserve`, regions per 'syscall'"*

And in item 5:
> *"The program supplies three C-ABI hooks: `fly_os_alloc(size, align)`, `fly_os_free(p)`, `fly_os_panic(msg, len)` — either in C/asm or as `export extern "C"` Flyscript functions."*

Now try to write `fly_os_alloc` or an AArch64 4KB page table in Flyscript:
```ts
// 1. How do you know the byte size or alignment of a struct `Page` or `Task` in Flyscript?
// 2. How do you align an AArch64 L1 page table struct to a 4096-byte boundary?
@layout(c)
struct PageTable {
  entries: u64[512]; // Needs 4096-byte alignment for TTBR0_EL1!
}
```
Right now, `§2.3` has `Layout = "@layout" "(" ( "c" | "packed" ) ")"` and `§7.2` has `Type.info(T)`, neither of which gives the byte size or alignment of `T` or lets a struct specify alignment!
**Fix:**
1. Add `Type.sizeOf<T>(): usize` and `Type.alignOf<T>(): usize` (or `sizeOf<T>()` / `alignOf<T>()` in the prelude, evaluated at compile time / monomorphization time when `T` is concrete).
2. Extend `@layout` in `§2.3` to allow alignment: `@layout(c, align = 4096)` (emit `__attribute__((aligned(4096)))` in C and `align 4096` in LLVM).

**Blocker 1D: Uninitialized buffers (`let buf: u8[4096] = repeat(0)` copies/zeros 4KB on every read, and large fixed arrays of non-Copy or C structs).**
In `§10.2`, `let buf: u8[512] = repeat(0);` works because `u8` is `Copy`. What about a C struct passed to an `extern "C"` out-parameter (e.g. `stat(path, mut st)` or an AArch64 trap frame) where you don't want to write out 30 fields by hand?
You do **not** need a new `MaybeUninit<T>` type in the language! Inside `unsafe`, a single intrinsic function `unsafe { Ptr.zeroed<T>() }: T` (valid when `T` is C-representable / `Copy`) returns a zero-initialized `T` (`{0}` in C, `zeroinitializer` in LLVM). One function, zero new types.

---

#### 4. Phase 4 Soundness Bug in the Spec (`§4.6`, `§6.1`): `Cell<R, T>.get()` and `RegionList<R, T>.len()` across `Io.scope` on multi-core

Before you put fibers onto multiple OS threads in Phase 4, check `§4.6` and `§6.1` carefully.
In `§4.6`:
```ts
impl<region R, T extends Copy> Cell<R, T> {
  export function new(v: T): Cell<R, T> uses Region<R>;
  export function get(self: Self): T uses Region<R>;
  export function set(self: Self, v: T): void uses Region<R>;
}
impl<region R, T> RegionList<R, T> {
  export function new(): RegionList<R, T> uses Region<R>;
  export function push(self: Self, v: T): void uses Region<R>;
  export function len(self: Self): usize;
}
impl<region R, T> Iterable<readonly T> for RegionList<R, T> { … }
```
Notice that:
- `Cell.get` requires `uses Region<R>`, and `RegionList.push` requires `uses Region<R>`.
- Because `Io.scope` freezes outer regions (`§6.1` Rule 5: tasks and the scope body can only perform `Io` and `Fail<X>`, not an outer `Region<R>`), no task can call `Cell.set` or `RegionList.push` on an outer region `R1`. **That part is sound!**
- **HOWEVER**, what if a task opens **its own inner region `region (R2)`** inside `Io.scope`, allocates a `RegionList<R2, i32>` or `Ref<R2, ...>`, and then opens a **nested `Io.scope`** inside `region (R2)`?
  Inside that inner `Io.scope`, `R2` is frozen too — **except** what if a helper function is generic over `<region R>` or what if `RegionList` reallocates chunks on `push`? `§4.6` says *"an append-only chunked list whose elements never move."* Make sure `runtime.c`'s `RegionList` is genuinely a linked list of chunks (or spine of chunk pointers) where `push` never `realloc`s an existing chunk array in place, **and** that `RegionList` in `A.5` (`for (const b of self.names)`) reads `len` and chunk pointers without racing!
- Even more importantly: what about **`Ref<R, str>` or `String` or `Arc<T>`** shared across OS threads in `runtime.c`?
  Check how `Clone` on `Arc<T>` and `String` is implemented in `runtime.c` right now!
  In single-threaded `runtime.c`, if `String` or `Vec` or `Box` is cloned, it allocates a fresh buffer, **or** if `Arc<T>` uses a non-atomic reference count `rc++` / `rc--`, running two tasks on different OS threads that clone/drop an `Arc<T>` (or capture a `readonly Arc<T>` and clone it inside a task!) will race on `rc`!
  As you noted in Phase 4, `Arc<T>`'s refcount in `runtime.c` must use `__atomic_add_fetch(..., __ATOMIC_RELAXED)` on clone and `__atomic_sub_fetch(..., __ATOMIC_ACQ_REL)` on drop.
- **On your Phase 4 question (One scheduler with pluggable policy vs two schedulers):**
  **Use two separate scheduler implementations behind the same root `Io` vtable (`sim_scheduler.c` and `mt_scheduler.c`), NOT one merged scheduler with a pluggable policy.**
  Why:
  1. `SimIo` (`§6.4`) is single-threaded, lock-free, has a virtual clock heap, deterministic PRNG fault injection, and simulated in-memory sockets/files (`FLY_WORLD`). It has zero mutexes, zero condition variables, zero `kqueue`/`epoll`, and zero work-stealing deques.
  2. The multi-core scheduler has OS worker threads, Chase-lev work-stealing deques, a real `kqueue`/`epoll` reactor thread/poller, real OS monotonic timers, and thread-safe `WaitKey` parking locks (`Io.park`).
  3. Trying to abstract a Chase-Lev multi-threaded work-stealing + `epoll` scheduler and a single-threaded deterministic discrete-event simulator into one "pluggable next-task policy" will pollute the fast lock-free simulator with locks and pollute the M:N scheduler with virtual-clock indirections. Keep them as two 250-line files implementing the 5 operations of `effect Io` (`read`, `write`, `now`, `sleep`, `park` + `scope`/`spawn`/`fork`).

---

#### 5. Phase 5 (FlyNext PoC): Three places where pure `Ui<Msg>` will fight you unless designed in up front

You asked in Question 5:
> *is the effect-based `Ui` (direct-style emission) a sound basis for keyed diffing and event handlers, or will it fight us (e.g. closures as event handlers vs. `Msg` values)? I plan `Msg` values only (no closures in attributes), which makes the op list serializable and SSR/hydration trivial.*

Using `Msg` values instead of closures is **much** better for Flyscript (no closure lifetime/capture issues in views, trivial binary serialization, zero allocation per render). **However**, three concrete UI patterns will immediately break a naive `Ui<Msg>` (`el`, `text`, `onClick(m: Msg)`) in an issue-tracker or store demo:

**1. Text inputs, checkboxes, and forms (`onInput`, `onChange`).**
In an issue tracker or store, the user types into a search box or "New Issue Title" `<input>`.
If `onClick(m: Msg)` only takes a static `Msg` value produced *during `view()`*, how does the `Msg` carry the string the user just typed into the `<input>`?!
At the time `view(model)` runs, the new string does not exist yet!
```ts
// How do you write an <input> without a closure `(val: String) => Msg`?
```
**Solution that keeps `Msg` values (no closures!):**
In Flyscript (`§3.2`), a tag constructor `#SearchChanged(String)` is a value constructor, or even simpler: give `Ui<Msg>` one input-binding operation that takes a tag or a pure stateless function pointer `fn(String) => Msg` — **or** pass a `Msg` template / field-targeted operation:
```ts
export effect Ui<M> {
  el(tag: str, attrs: readonly { key: str; val: str }[], children: () => void uses Ui<M>): void;
  keyed(key: str, tag: str, attrs: readonly { key: str; val: str }[], children: () => void uses Ui<M>): void;
  text(s: str): void;
  onClick(msg: M): void;
  onInput(makeMsg: (val: String) => M): void; // stateless function (no captures), or handled only on client!
}
```
Wait: why is `onInput(makeMsg: (val: String) => M)` completely free on both SSR and Wasm hydration?
- **During SSR:** `onInput` is a **no-op** (the server handler ignores `onClick` and `onInput`, or emits a `data-on-input` marker)! It never calls `makeMsg`!
- **During Wasm hydration / client render:** `view(model)` runs *inside Wasm on the client*! When the Wasm client handler intercepts `Ui.onInput(makeMsg)`, it stores `makeMsg` in an array `handlers[id]` in Wasm memory and emits `op = SetOnInput(domNodeId, handlerId)` to the JS ring buffer. When the user types in the browser, the JS shim writes the UTF-8 string into Wasm memory and calls `wasm.dispatchInput(handlerId, ptr, len)`, which calls `update(mut model, handlers[handlerId](str))`!
- Nothing in `onInput` or `onClick` ever needs to be serialized over the network! SSR only serializes HTML; hydration runs the exact same `view(model)` in Wasm on the client to attach event listeners!

**2. Keyed diffing in direct-style effect emission (`for (const item of items)`).**
In a direct-style `for` loop inside `view()`:
```ts
for (const issue of model.issues) {
  Ui.keyed(issue.id, "li", [], () => {
    Ui.text(issue.title);
    Ui.el("button", [], () => { Ui.onClick(#Delete(issue.id)); Ui.text("×"); });
  });
}
```
If you only have flat `el(tag, attrs, children)` without an explicit `key` parameter (or `Ui.keyed(key, ...)`), then deleting the first issue in `model.issues` shifts every subsequent `<li>` in the flat op list by 1 position, destroying focus, CSS transitions, and `<input>` cursor state on every item below it!
Make `key` an explicit part of `Ui.keyed` (or an optional/empty `key: str` on `el`), and record `(parentOpIdx, key, startOpIdx, endOpIdx)` in the per-frame region's flat op buffer so the reconciler diffs children of a node by `key` in O(N) time without allocating a VDOM tree.

**3. Client-side routing + Server Functions (`uses Rpc`, `uses Io`).**
In your Phase 5 plan:
> *Server functions: an `effect` declared in a shared module; the server handles it directly; the client handler is generated by `comptime` from the operation signatures (binary codec, failures as `Fail` tags re-raised on the client).*

Look at what `comptime` reflection (`§7.2`) can see right now:
`Type.info(T)` inspects types (`#Struct`, `#Record`, `#Union`, `#Int`, etc.), **not** `effect` declarations!
If you want a client handler for `effect Api { createIssue(title: String): Issue; }` to be generated without adding new `comptime` reflection over `effect` declarations, define the RPC interface as a **tag union of requests** or a normal **struct/interface** whose types `Type.info(T)` *already* reflects over (`std/json` `ToJson`/`FromJson` already works on every struct, record, and tag union out of the box!):
```ts
// Shared between server and client — uses existing `ToJson` / `FromJson` derivations!
effect Api {
  call<Req extends ToJson, Resp extends FromJson>(endpoint: str, req: readonly Req): Resp uses Fail<ApiErr>;
}
```
That requires **zero** new compiler features or `comptime` effect reflection, works with the existing `std/json` derivations (`§7.5`), and lets any function with `uses Api` run directly against the DB handler on the server (during SSR!) and over `fetch` on the Wasm client!

---

### Summary of Recommended Adjustments

1. **Order of phases:**
   - **Phase 0:** `ir.fly` (port **both** `c.fly` and `js.fly` to `ir.fly` so the AST-to-IR lowering is the single source of truth).
   - **Phase 1:** Kernel tweaks (`T*` with `Ptr.fromMut` / `Ptr.fromRef`, raw atomics on `T*`, `Type.sizeOf` / `Type.alignOf`, `@layout(c, align = N)`, `tryReserve`, `--freestanding`, QEMU AArch64 kernel demo).
   - **Phase 2 (was 3):** LLVM `.ll` backend from `ir.fly`. Gives you native speed, DWARF debug info, and `clang --target=wasm32` immediately.
   - **Phase 3 (was 2):** Wasm backend & browser runtime (using linear-memory fiber stack frames + JSPI or `ir.fly` frame suspension, **not** general Asyncify).
   - **Phase 4:** Multi-core tasks (atomic `Arc` refcounts, separate `mt_scheduler.c` alongside `sim_scheduler.c`).
   - **Phase 5:** FlyNext PoC (`Ui<Msg>` with `keyed` and `onInput`, shared `Api` effect using `ToJson`/`FromJson`).
