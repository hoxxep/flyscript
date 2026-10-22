# Review: native-backend

- spec: 7d9cebf442b0
- request: 47f4c77800ef9d97
- tokens: prompt 54747, cached 0, answer 7684

## Question

# Review request: Flyscript's native back end, now self-hosting

Flyscript is a TypeScript-syntax systems language: affine ownership with second-class borrows, one row calculus for records/tag unions/effects, four standard effects (Fail, Io, Yield, Region), one-shot first-class continuations, deep handlers, append-only regions, comptime, no GC. The compiler is written in Flyscript. It had a typed, monomorphizing JavaScript back end at a fixpoint; it now also has a C back end (GNU C, clang/gcc), and the compiler compiled natively reproduces its own C byte for byte (self-compile ~2.5 s vs ~8 s on Node). All 56 corpus programs run natively under ASan+UBSan with output identical to the reference interpreter, including a deterministic task scheduler.

Design of the C back end (runtime.h attached):

1. Values: C structs by value; tag unions are {tag; union u} with tag ids global across the program (so narrowing/widening conversions copy tag + payload); a union's identity for C ignores tag order and an unsolved open row tail. `mut T` is T*; `readonly T` is T* unless T is a scalar; borrows of views (str, slices, closures) are the view itself.
2. Ownership: "zero state". Every local is hoisted to the function top and zero-initialized; a move zeroes its source; every drop is idempotent and leaves zero; a scope's exit drops what it declared; the function has one exit for returns and failures that drops *every* owned local again (harmless). Types with a user Drop carry a live byte. Owned entries are stored as release statements, so defer and region arenas use the same list.
3. Failures: `fly_err` global holds a boxed (tag, payload bytes); a call that may fail is followed by `if (fly_err) goto <catch label or function exit>`.
4. Generators: a function performing Yield<T> takes a hidden `fly_yield {env, fn}` callback; `for` over a generator call compiles the body into a C function; break/return/failure inside it returns false and the generator unwinds through its single exit (a global `fly_stopping` flag reports it through forwarding generators). Library generators (list iter, map keys, adapters) are pull-based structs with per-item-type step functions.
5. Handlers: stackful fibers (hand-written context switch for arm64 and x86-64, mmap'd 64 MB NORESERVE stacks, ASan fiber annotations). `handle` runs its body on a fiber inside a heap frame refcounted by the active dispatch and by live continuations; performing an op finds the nearest handler on a per-fiber dynamic chain and switches to the body's last resumer, which runs the arm; `k(a)` re-enters the same dispatch (deep). Dropping a continuation resumes the body with a global `fly_unwinding` flag set; every call that may suspend checks it and leaves through the function exit. Abortive arms unwind first.
6. Regions: a function whose row has Region<R> takes R's arena as a hidden parameter (evidence passing); closures and body functions capture the arenas in reach.
7. Closures: environment on the heap (owning moved-in captures and unchanged Copy captures by value) unless the closure is only lent to a call, then on the stack with pointer captures. A `once` closure parameter is the callee's; others are lent.
8. Tasks: fibers under a scheduler that mirrors the reference's (same ready list ordering, seeded xorshift choice at each scheduling point); cancellation is delivered at the next point as unwinding, which `Io.scope` takes back.

Known compromises:
- Panics exit the process immediately (the reference unwinds the task and fails its scope).
- In-flight owned temporaries in a call's argument list leak if a later argument fails (they are statement-expression locals, not registered).
- One global `fly_unwinding` / `fly_err` (single-threaded fibers only; `par` runs sequentially).
- Argument structs for effect ops are tuples of the declared parameter types; payload copies on rethrow of a task failure are shallow.

Questions:
1. Is the zero-state ownership scheme (drop everything again at the single exit, idempotent drops) sound and does it have a performance cliff I'm not seeing? Would you switch to drop flags or structured cleanup before this goes further?
2. The `fly_unwinding` / `fly_stopping` global-flag protocol for dropped continuations, stopped generators and cancellation: is there a cleaner unified design (e.g. a single "abort reason" with a target frame) that you'd adopt now, before WebAssembly?
3. For a multi-threaded native runtime (workers stealing fibers, real `par`), what in this design has to change first?
4. What is the single most important thing to do next for this to be a high-quality language implementation, rather than a working one?

## Context files

- `selfhost/runtime.h`

## Answer

### Verdicts

- **(1) Zero-state ownership scheme:** **Disagree (unsound for `defer` and enum drop order; has an $O(N)$ exit cliff in loops and match arms).** Keep zero-initialization for heap/container pointers (`ptr == NULL` is a great zero-cost niche), **replace** function-top hoisting + "drop everything at the single exit" with lexical block cleanup labels (`goto cleanup_scope_k;`).
- **(2) `fly_unwinding` / `fly_stopping` / `fly_err` protocol:** **Agree with unifying into a single per-fiber unwind state `{ kind, target_frame, err }` now.** Having three separate globals (`fly_err`, `fly_unwinding`, `fly_stopping`) fails when a cleanup block (`defer` or `Drop`) runs a nested `try/catch` or `for…of` loop during unwinding, clobbering the active unwind state.
- **(3) Multi-threaded native runtime (`par` + work-stealing fibers):** **Four concrete changes required first:** (a) move `fly_err` / `fly_handlers` / unwind state into the current `fly_fiber` (cached in a `_Thread_local fly_fiber*`), (b) replace 64 MB `MAP_NORESERVE` stacks with small pooled stacks (64 KB–256 KB with a guard page), (c) make `fly_arc_retain` / `fly_arc_release` atomic, and (d) fix the `readonly T` scalar-by-value ABI mismatch when taking a function reference or calling through an interface.
- **(4) Single most important thing to do next:** **Unify the intermediate representation (Monomorphized Core IR) between the JS and C backends and fix lexical cleanup/unwinding on it.** Right now you are maintaining two parallel code generators over raw AST; a small explicit statement/block IR with lexical cleanup scopes fixes the temporary leaks, the `defer`/enum zero-state bugs, and `panic` unwinding in one place, and becomes the direct input to WebAssembly.

---

### Problems

#### 1. Question (1): "Zero-state" hoisted cleanup violates `§5.6` for `defer`, partial moves, and enums holding owned payloads

In your C backend design (Item 2):
> *"Every local is hoisted to the function top and zero-initialized; a move zeroes its source; every drop is idempotent and leaves zero; a scope's exit drops what it declared; the function has one exit for returns and failures that drops *every* owned local again (harmless). Types with a user Drop carry a live byte. Owned entries are stored as release statements, so defer and region arenas use the same list."*

This is **unsound** in three distinct ways that you can trigger with short Flyscript programs today:

**Bug 1A: `defer` and `region` are NOT idempotent (`§5.6`).**
If `defer` is on the same release list as owned locals—or if a block with a `defer` runs in a loop, or exits normally and then the function later returns or fails through the single function exit—what happens?
```ts
import { println } from "std/io";

function work(failAfter: bool): void uses Io, Fail<#Boom> {
  {
    defer println("cleanup inner");
    if (failAfter) {
      // Exits inner block AND function via single exit!
      throw #Boom;
    }
  }
  // Inner block exited normally (ran `defer` once).
  // Now suppose we fail or return here:
  if (true) { throw #Boom; }
}

export function main(): void uses Io {
  try { work(false); } catch (_) {}
}
```
- If `defer` is in the function-wide single-exit list without a live flag cleared on normal block exit, `work(false)` runs `defer println("cleanup inner")` **twice** (once when the inner block exits normally, and a second time when `throw #Boom` jumps to the function's single exit)!
- Conversely, if `defer` is only emitted at the normal end of the inner block and NOT in the function exit path, then `work(true)` (`throw #Boom` inside the inner block) jumps to the function exit and **skips the `defer` completely**!
- Even worse, put `defer` inside a `while` loop:
  ```ts
  let i = 0;
  while (i < 3) {
    defer println(`iter ${i}`);
    i += 1;
    if (i == 2) { return; }
  }
  ```
  Each iteration registers `defer` dynamically (`§5.6`). Hoisting to the function top cannot represent loop-scoped `defer`s unless either each `defer` has a boolean armed flag cleared on normal scope exit, or you use structured lexical cleanup labels!

**Bug 1B: Zero-initialized tag `0` on a tag union / `enum` has a non-empty payload destructor (`§3.2`, `§5.6`).**
Look at how tag unions and `enum`s are represented: `{ uint32_t tag; union u; }`.
When a local `x` of type `Result<String, i32>` or `enum Cmd { #Put(String), #Stop }` is hoisted to the function top and zero-initialized (`memset(&x, 0, sizeof(x))`), **what is `x.tag`?**
`x.tag == 0`!
And if tag `0` is `#Put(String)` or `#Ok(String)`, then its payload is a `fly_String` (which happens to have `ptr == NULL` initially, so dropping `#Put(NULL)` is a no-op)—**UNTIL**:
```ts
enum State {
  #Active(Resource), // Suppose tag 0 is #Active, where Resource has a user `Drop`!
  #Idle,             // tag 1 is #Idle
}
```
Wait: if `Resource` has a user `Drop`, you gave `Resource` a live byte. What if `State` itself does NOT implement user `Drop`, or what if `x` was set to `#Active(r)` (so `r.__live = 1`), and then overwritten with `x = #Idle`?
In C, assigning `x = (State){ .tag = 1 }` **only writes `.tag` (or leaves garbage in the union padding where `r.__live` sat if the union variant `#Idle` is smaller than `Resource`)!**
When the function exits and runs `State_drop(&x)`, if `x.tag == 1` (`#Idle`), it does nothing. Wait—what if `x` was moved from (`const y = x;`), and your move zeroed `x` (`memset(&x, 0, sizeof(x))`)? That clears `r.__live` to `0`.
**Now flip the tags:** what if a user implements `Drop` on an `enum` where variant `#Empty` has tag `0` (`memset` zero-initializes it to `#Empty`), or what if a struct with user `Drop` has a valid all-zero value and is moved inside a branch? You added a `.live` byte to user `Drop` types specifically because all-zero bits is a valid value (`struct Fd { fd: i32 }` where `fd == 0` is `stdin`!).
Think about what that `.live` byte actually is: **it IS a drop flag, embedded inside the struct layout!**
Embedding the drop flag inside the struct layout (`struct Fd { int32_t fd; uint8_t __live; }`) has a serious consequence for `§8.2` (`@layout(c)` and `@layout(packed)`):
```ts
@layout(c)
struct CHandle { raw: u64; }
impl Drop for CHandle {
  function drop(self: mut Self): void { ... }
}
```
If you add a live byte to `CHandle`, `sizeof(CHandle)` becomes 16 instead of 8, breaking C ABI layout (`§3.3`, `§8.2`)!

**Bug 1C: Drop order on early `return` / `throw` violates `§5.6`.**
`§5.6` states:
> *"`defer`s and the destructors of the block's owned locals share one stack and run in reverse order of the points at which they were registered, whether the block exits normally, by `return`, `break`, `throw`, an abortive handler, a dropped continuation, or cancellation."*

Look at what happens when a block mixes owned locals and `defer`:
```ts
import { println } from "std/io";

struct Guard { name: str; }
impl Drop for Guard {
  function drop(self: mut Self): void {
    // (pure observable side effect, e.g. writing to a mut pointer or Cell, or in a test)
  }
}
```
If a block exits normally, it drops its locals at the `}` and zeroes them; then when the function later exits at the single exit, it scans *every* hoisted local in the entire function from bottom to top and calls `drop` on each zeroed local again!
In a large function like `Checker.expr` or `Gen.stmt` in `selfhost/` (which has a 30-arm `match` where each arm declares 5–10 temporary `String`s and `Vec`s, totaling ~200 hoisted owned locals in one function), **every single call to `Checker.expr` executes 200 zero-initialization stores on entry and 200 branch-checked `drop` calls on exit, even when only 1 arm of the `match` ran!**

**The Fix: Lexical Cleanup Chain (`goto cleanup_k`), Not Function-Wide Hoisting.**
Instead of hoisting all locals to the function top and re-dropping everything at a single function exit:
- Keep each C block's locals in that block, and give each block (that owns a local with a destructor, a `defer`, or a `region` arena) a cleanup label `L_clean_k:` at the end of the block.
- If a local `x` is moved on some path before the end of its block:
  - If `x` is a `String`, `Vec`, `Box`, `HashMap`, `Arc`, `Cont`, or `Gen`, zeroing `x.ptr = NULL` on move is **already** an exact, zero-space-overhead niche!
  - Only if `x` is a user `Drop` struct/enum that is conditionally moved do you emit a stack `bool drop_x = true;` local (not inside the struct!), set `drop_x = false;` on move, keeping `@layout(c)` 100% intact.
- When `return`, `break`, `continue`, or `if (FLY_UNWINDING)` leaves from inside block $k$ to an outer target block $m$, it simply `goto L_clean_k;`, which runs block $k$'s `defer`s and live drops in exact reverse declaration order and chains to `L_clean_{k-1}` up to $m$!
- **What you remove:** You delete function-top local hoisting, delete the extra `.live` byte inside user `Drop` structs, delete the duplicate drop pass at function exit, and eliminate the $O(\text{all locals in all match arms})$ entry/exit overhead!

---

#### 2. Question (1 & 4): Temporary leaks in call arguments are also move/borrow-order bugs (`§5.6`)

You noted under Known Compromises:
> *"In-flight owned temporaries in a call's argument list leak if a later argument fails (they are statement-expression locals, not registered)."*

Look closely at what happens in C when you emit a call `foo(makeA(), mayFailB())` where `makeA()` returns an owned `String` (or `Guard` with `Drop`) and `mayFailB()` throws:
```ts
function makeA(): String { "hello".toString() }
function mayFailB(): i32 uses Fail<#Err> { throw #Err; }
function consume(s: String, n: i32): void {}

export function main(): void {
  try {
    consume(makeA(), mayFailB());
  } catch (_) {}
}
```
If `makeA()` and `mayFailB()` are emitted inside GNU C statement expressions `({ ... })` inside the C call `consume(({ ... }), ({ ... }))`:
1. **C argument evaluation order is unspecified (`-Wunsequenced`)!** Clang and GCC evaluate function arguments in **different orders** on x86-64 vs arm64! In `consume(makeA(), mayFailB())`, GCC on x86-64 may evaluate `mayFailB()` *before* `makeA()`, changing program semantics when both have effects (`Io`, `Region`, `Yield`, `Fail`)!
2. If `mayFailB()` executes `goto catch_label;` from *inside* a C statement expression inside the argument list of `consume(...)`, `makeA()`'s result sits in an unnamed C temporary on the stack and is **never dropped** (violating `§5.6` deterministic destruction, not just leaking memory, if `makeA()` returned a `Drop` type like a lock guard or `Sender` whose `Drop` closes a channel!).
3. Even when nothing fails: what if an expression creates a temporary owned value that is lent to a call, e.g. `takesStr(makeString())` (`§4.1`: *"A value that is borrowed without having a place — a call's result, a template string, a literal lent as `str` — is stored in an anonymous local of the enclosing block, dropped when the block ends"*)?

**Fix:**
Before emitting a call (or any expression when an earlier sub-expression has effects or produces an owned temporary):
- Lift every effectful argument or owned temporary into an ordinary block-registered local variable **in left-to-right order before the C call statement**:
  ```c
  fly_String tmp_1 = makeA();
  if (FLY_UNWINDING) goto clean_scope;
  int32_t tmp_2 = mayFailB();
  if (FLY_UNWINDING) goto clean_scope; // drops tmp_1!
  consume(Move(&tmp_1), tmp_2);
  ```
That takes ~20 lines in the C emitter and simultaneously fixes:
1. Unspecified C argument evaluation order across Clang/GCC and x86-64/AArch64,
2. The temporary leak / skipped `Drop` when argument $k$ fails after argument $1 \dots k-1$ succeeded, and
3. `§4.1`'s rule for anonymous locals of borrowed temporaries!

---

#### 3. Question (2): Three separate globals (`fly_err`, `fly_unwinding`, `fly_stopping`) corrupt each other during cleanup (`§5.2`, `§5.5`, `§5.6`)

Right now, your C runtime has three separate unwind flags:
- `extern void* fly_err;` (for `Fail`)
- `extern bool fly_unwinding;` (for dropped continuations / abortive handlers / task cancellation)
- `extern bool fly_stopping;` (for `break` / `return` out of a `for…of` generator)

And in every function that can fail or suspend, you check `if (FLY_FAILED)` or `if (fly_unwinding)` or `if (fly_stopping)` and jump to the function's exit to run `defer`s and `Drop`s.

**Now look at what happens when a `defer` or `Drop.drop` runs while one of those flags is set!**
```ts
effect Eff { op(): void; }

function helperWithTry(): void {
  // Valid inside a defer/Drop: a self-contained try/catch or for-loop does NOT escape!
  try {
    throw #Internal;
  } catch (_) {}

  for (const x of [1, 2, 3]) {
    if (x == 2) { break; }
  }
}

export function main(): void {
  handle {
    defer helperWithTry();
    Eff.op();
  } with Eff {
    // Abortive arm (or dropping `k` in a resumptive arm):
    // sets `fly_unwinding = true` and unwinds the body!
    op() => {}
  };
}
```
Trace what happens when `Eff.op()` unwinds the `handle` body:
1. `fly_handle_unwind` sets `fly_unwinding = true` and resumes the suspended fiber so it will exit through its cleanup path and run `defer helperWithTry();`.
2. Inside `helperWithTry()`, **while `fly_unwinding` is still `true`**, `helperWithTry()` calls functions or loops!
   - Any call inside `helperWithTry()` that checks `if (fly_unwinding) goto exit;` **immediately aborts `helperWithTry()` mid-execution** without running the rest of the `defer`!
   - Even worse: if a generator is unwinding because of `throw #OuterErr` (`fly_err != NULL`) and its `defer` runs `try { throw #Internal; } catch (_) {}`, throwing `#Internal` calls `fly_err_box(...)`, **overwriting `fly_err` (`#OuterErr`) with `#Internal`**, and then the inner `catch (_)` calls `fly_err_take(...)`, **setting `fly_err = NULL`**! When the `defer` finishes, `fly_err` is `NULL`—the outer exception `#OuterErr` has vanished into thin air!
   - And if a generator is unwinding because `fly_stopping = true` and its `defer` runs an inner `for (const y of otherGen()) { break; }`, the inner loop finishes and **clears `fly_stopping = false`**, stopping the outer generator's unwind!

**Fix (answers Question 2 directly):**
Replace `fly_err`, `fly_unwinding`, and `fly_stopping` with **one unified unwind state on the current fiber** (or thread-local when not in a fiber), and **save/clear it on entry to any cleanup block (`defer` / `Drop`)**:
```c
typedef enum {
  FLY_OK = 0,
  FLY_UNWIND_FAIL,     // throwing an error (`err_tag`, `err_buf`)
  FLY_UNWIND_STOP,     // generator stopped by consumer (`target` = the `fly_yield*` being stopped)
  FLY_UNWIND_ABORT,    // continuation dropped / abortive arm / task cancelled (`target` = `fly_handler*` or fiber root)
  FLY_UNWIND_PANIC,    // panic unwinding task to fail enclosing `Io.scope` (§5.7, §6.1)
} fly_unwind_kind;

typedef struct {
  fly_unwind_kind kind;
  void* target;        // which handler / yield frame owns this unwind
  uint32_t err_tag;
  void* err_payload;
} fly_unwind;
```
Look at what this gives you:
1. **One fast check after calls:** `if (__builtin_expect(fiber->unwind.kind != FLY_OK, 0)) goto clean_scope;`.
2. **Cleanup blocks (`defer` and `Drop`) are immune to active unwinds:**
   Because `§5.6` guarantees a `defer` or `Drop` cannot exit via `throw`, `yield`, `return`, `break`, or `continue`, on entry to a `defer` or `Drop` block while unwinding you simply **stash** `fly_unwind saved = fiber->unwind; fiber->unwind.kind = FLY_OK;`, run the cleanup body normally (so inner `try/catch` or `for/break` inside the `defer` works cleanly!), and restore `fiber->unwind = saved;` at the end of the cleanup block! (If the `defer` itself panics, `FLY_UNWIND_PANIC` supersedes).
3. **Targeted stopping (`target`):** If generator $G_1$ calls generator $G_2$, and the consumer of $G_2$ breaks (`FLY_UNWIND_STOP` with `target = &yield_G2`), $G_2$ unwinds until the `for` loop driving $G_2$ sees `unwind.target == &yield_G2` and resets `unwind.kind = FLY_OK`—never confusing $G_2$'s stop with $G_1$'s stop!
4. **Panics (`§5.7`, `§6.1`) work for free:** `fly_panic` inside a task sets `unwind.kind = FLY_UNWIND_PANIC` and unwinds the task fiber using the exact same `goto clean_scope` path (`§5.7`: *"it unwinds the current task, running cleanup, and fails the task's scope"*), instead of calling `exit(1)`!
5. **WebAssembly readiness:** In Wasm, `FLY_UNWIND_FAIL` / `STOP` / `ABORT` / `PANIC` either uses that exact same state struct across suspended Wasm stacks, or lowers 1-to-1 to a single Wasm exception tag with `(kind, target, payload)`.

---

#### 4. Question (5): Shallow payload copy on task failure (`Io.scope`) causes use-after-free / double-free (`§6.1`)

Under Known Compromises you noted:
> *"payload copies on rethrow of a task failure are shallow."*

Look at what happens when a forked task throws an error whose payload owns memory (like `#MissingField(String)` in `A.9` or `#Unknown(String)` in `A.10`):
```ts
export function main(): void uses Io {
  try {
    Io.scope((s) => {
      const f = s.fork((): void uses Io, Fail<#Bad(String)> => {
        throw #Bad("something went wrong".toString());
      });
      f.join();
    });
  } catch (e) {
    match (e) {
      #Bad(msg) => println(msg),
    }
  }
}
```
Why would rethrowing a task's failure ever copy the payload at all?!
A failure value is **affine (owned)**, just like any other value:
- Even if two tasks fail during an `Io.scope`, `§6.1` rule 3 states:
  > *"once all have finished the first failure is rethrown from `Io.scope`"*
- Therefore, the first failing task **moves** its boxed error (`fly_err` pointer + tag) into the `scope` struct (`scope->first_err = task->err; task->err = NULL;`).
- If any *subsequent* task in the same scope also fails before noticing cancellation, its error is discarded—so the scope calls the error type's generated destructor `drop_E(other_task->err)` (or each `fly_err` carries `void (*drop)(void*)`, just like `fly_fn` and `fly_gen` already do in `runtime.h`!).
- Then `Io.scope` moves `scope->first_err` into the parent fiber's `fly_err` without copying a single byte!
Adding `void (*drop)(void*)` to the boxed error in `fly_err_box(uint32_t tag, const void* value, size_t size, void (*drop)(void*))` (Moving the error into `fly_err_box` so the throw site zeroes its local, and calling `drop` only if an error is overwritten/discarded by a scope or unhandled catch arm) fixes both leaks of uncaught/superseded owned error payloads and any shallow-copy bug.

---

#### 5. Question (3): What must change first for a multi-threaded native runtime (`par` + work-stealing fibers)

Besides moving `fly_err`, `fly_handlers`, `fly_unwinding`, and `fly_stopping` off global variables and into the `fly_fiber` struct (pointed to by `_Thread_local fly_fiber* fly_current_fiber`), four specific things in your current C backend and `runtime.h` will break under multi-threading unless changed first:

1. **64 MB `MAP_NORESERVE` fiber stacks will exhaust virtual address space and crash on macOS / 48-bit Linux when spawning thousands of tasks.**
   - 10,000 tasks $\times$ 64 MB = 640 GB of virtual address space; on macOS arm64 and many container limits (`ulimit -v`), `mmap` fails after a few thousand fibers, and `munmap` of 64 MB on every `handle` or `spawn` causes global TLB shootdown IPIs across all worker threads!
   - **Fix:** Pool fiber stacks in the runtime free-list, and use **256 KB stacks with a 1-page `PROT_NONE` guard page** for tasks, and **64 KB pooled stacks** for `handle` blocks (which are frequently short-lived generators). Because `§8.2` runs `extern "C"` calls on the worker thread's native OS stack, 64 KB–256 KB is plenty for pure Flyscript frames, and pooling makes `handle` / `spawn` stack allocation $O(1)$ with zero `mmap`/`munmap` syscalls and zero TLB shootdowns.

2. **`fly_arc_retain` and `fly_arc_release` in `runtime.h` must use `<stdatomic.h>` (`§4.5`).**
   - `Arc<T>` is explicitly for sharing across tasks (`§4.5`: *"atomic count"*). In `runtime.c`, the refcount must be `_Atomic size_t`: `atomic_fetch_add_explicit(&rc, 1, memory_order_relaxed)` in `fly_arc_retain`, and `atomic_fetch_sub_explicit(&rc, 1, memory_order_release) == 1` followed by `atomic_thread_fence(memory_order_acquire)` in `fly_arc_release`.
   - Same for the refcount on the heap frame of a `handle` dispatch if a task ever interacts with it (though `Cont` is `!Send`, so `handle` frames stay single-fiber).

3. **ABI mismatch on `readonly T` (scalar by value vs struct by pointer) in generic / closure callbacks (`par`, `parReduce`, `sortBy`).**
   Look at your rule in Item 1:
   > *"`mut T` is `T*`; `readonly T` is `T*` unless `T` is a scalar; borrows of views (`str`, slices, closures) are the view itself."*
   Now look at `fly_sort` in `runtime.h`:
   ```c
   void fly_sort(fly_slice s, size_t size, int (*cmp)(void* ctx, const void* a, const void* b), void* ctx);
   ```
   And look at `parReduce` (`§6.5`):
   ```ts
   function parReduce<C extends ParSplit, A extends Send>(
     c: readonly C, zero: A, one: (v: C.ReadView, i: usize) => A, both: (a: A, b: A) => A,
   ): A;
   ```
   When `C` is `Vec<f32>`, `C.ReadView` is `readonly f32` (a scalar, so passed as `float` by value under your rule!), whereas when `C` is `Vec<Vec2>`, `C.ReadView` is `readonly Vec2` (a struct, so passed as `const Vec2*` by pointer!).
   Because `par` and `parReduce` are monomorphized in Flyscript (`std/par.fly`), that works **provided** `par` and `parReduce` are compiled through the monomorphizer and call a runtime worker-pool primitive:
   ```c
   void fly_par_for(size_t n, void (*body)(void* ctx, size_t lo, size_t hi), void* ctx);
   ```
   where the compiler generates a monomorphized range wrapper `body(ctx, lo, hi)` for each `par` / `parReduce` instantiation! Make sure `par` / `parReduce` use a monomorphized range-thunk over `fly_par_for` rather than passing a `void*` element pointer directly to the user's closure.

4. **ASan fake-stack / fiber-switch hooks across worker threads.**
   When a fiber suspends on Worker Thread $A$ and is stolen by Worker Thread $B$, `__sanitizer_start_switch_fiber` / `__sanitizer_finish_switch_fiber` must pass the fiber's saved `fake_stack` pointer inside the `fly_fiber` struct (not a thread-local or stack variable of the switching function), and a fiber must not be marked runnable in the work-stealing queue until *after* its context switch out has finished saving registers to its stack! (The standard race in work-stealing fiber schedulers is pushing the fiber to the ready queue *before* `swapcontext`, allowing another worker to pop and resume the fiber while the first worker is still running on its stack!).

---

#### 6. Question (4): The single most important thing to do next

**Introduce a small, explicit Post-Monomorphization Core IR (`ir.fly`, ~350 lines) shared by the C, JS, and future Wasm backends.**

Here is why this is the highest-leverage move right now:

1. **Right now, the hardest parts of Flyscript's semantics are duplicated in `gen_js.fly` and `gen_c.fly`:**
   - Monomorphization and specialization keys,
   - Pattern-matching decision trees and binding modes (`§4.1` bind-by-use, narrowing, box/ref deref),
   - Temporary lifting and evaluation order in calls/operators (Problem 2),
   - Lexical drop/defer/region scope unwinding (Problem 1),
   - Closure environment layout and capture modes (`readonly` vs `mut` vs `once` move),
   - Effect classification (pure vs `Fail`-only vs `Region` evidence passing vs suspending).

2. **What that Core IR looks like (~15 node kinds):**
   After `check.fly` + `own.fly` + monomorphization, lower the typed AST once into a flat-statement Core IR where:
   - Every type is a concrete monomorphized layout ID (`Scalar`, `Struct`, `Union`, `Ptr`, `View`).
   - Complex sub-expressions with effects or owned temporaries are already lifted into sequence statements (`Let(id, ty, rhs)`).
   - Every lexical block carries its explicit cleanup list (`Cleanup: [Drop(local_id) | Defer(block) | FreeRegion(arena_id)]`), and every early exit (`Return`, `Break`, `Continue`, `Throw`) names the lexical scope depth it unwinds through.
   - `Region<R>` parameters are already explicit `arena*` parameters, and closures are already converted into explicit `{ env_struct, fn_id, drop_id }` records (`§1` Goal 6: just like `examples/mini` already does!).

3. **Why doing this now pays off immediately:**
   - It fixes Problem 1 (hoisted zero-state drop bugs and performance cliff) and Problem 2 (leaked argument temporaries and C evaluation order) cleanly in one ~300-line lowering pass instead of tangling C syntax emission with ownership tracking.
   - Your C backend shrinks by ~40% into a trivial syntax printer over Core IR.
   - When you add the WebAssembly backend (`§8.3`), 90% of the backend work (monomorphization, closure conversion, region evidence passing, drop/defer scheduling, and layout computation) is **already done** in Core IR!

---

### Smaller points

- **Effect operation argument lifetimes in `fly_perform` (`runtime.h:168`, `§5.3`):**
  In `runtime.h`:
  ```c
  void fly_perform(uint32_t effect, int op, void* args, void* result);
  ```
  Assume the caller on the suspended fiber allocates the `args` tuple on its own fiber stack and passes `&args` to `fly_perform`.
  Watch out for **abortive arms (`§5.2`)**:
  > *"Abortive — `op(x) => armBody`. The body's frames are unwound first (running its `defer`s and destructors and releasing its borrows), then `armBody` runs"*
  If an abortive arm unwinds the suspended fiber **before** `armBody` runs (`fly_handle_unwind(h)`), and `args` lived on the suspended fiber's stack, then unwinding the fiber overwrites/frees the fiber stack **before `armBody` reads the operation arguments `x` out of `h->args`!**
  Make sure the handler dispatch copies the operation's `args` out of `h->args` into the handler frame's own local variables **before** calling `fly_handle_unwind(h)` for an abortive arm (and if `armBody` does not use an owned argument or is skipped, drops it).
- **`FLY_RCHUNK_DATA(c)` alignment on 32-bit / 16-byte-aligned types (`runtime.h:240`):**
  `fly_rchunk` is `{ next, len, cap, pad }` = $4 \times 8 = 32$ bytes on 64-bit, which is 16-byte aligned (good for `fly_i128`). Make sure `fly_arena_alloc` also rounds `a->head->offset` up to `alignof(max_align_t)` (16 bytes) so `alloc(1u8)` followed by `alloc(1i128)` does not fault with UBSan misaligned-pointer errors!
