# Review: panics-and-state-machines

- spec: 65616151792d
- request: d29619aee5d1b2b7
- tokens: prompt 69344, cached 0, answer 8827

## Question

# Two design decisions: panics that end their task, and suspending code as state machines

Context: the attached roadmap, steps 15 and 16, and the spec (0.113). The compiler is self-hosted with JS, C, LLVM and wasm back ends over one core IR; the C/LLVM runtime currently runs every task, pull generator and non-tail-resumptive handler on a fiber with its own stack. The Lean proof covers ownership, effects, handlers with dropped and kept continuations, tasks under any schedule, regions and Mutex.

I want your strongest objections and anything I have missed, not agreement. Please be concrete.

## Step 15: a panic unwinds its task

Proposal: a panic drops the panicking task's continuation (as 0.105's dropped continuation does): drops and defers run, each operation a defer performs is cancelled, nothing in the task can catch it. At `main`: print and exit nonzero, nothing leaked. At `fork`: cancel the scope, re-panic in the parent from `Io.scope`. At `spawn`: the task ends, the scope and siblings go on, a supervisor callback hears the message. Inside `Mutex.lock`'s body: the lent value is dropped, the mutex is poisoned. Panic in Drop or during unwinding aborts. Panics stay outside the effect system so `xs[i]` stays pure.

Additions for Erlang-grade robustness: a handle from `spawn` that cancels that one task; cancellation checks at loop back-edges and function entry so a pure infinite loop can be stopped; stack overflow as a panic of its task (entry check); `std/supervise` (one-for-one / one-for-all / rest-for-one, restart intensity).

Back ends: LLVM `invoke` + landing pads; C returns a panic as a failure only the task root catches (so every call site of anything that may panic gets a check); JS throws; wasm exception handling.

Questions:
1. Is unwinding-from-pure-code sound to add to a calculus where panics today are a terminal state? What invariant breaks first — e.g. a value moved out of a place mid-expression, a two-phase borrow half done, a region arena mid-allocation, a `Drop` observing a partially initialized record?
2. Is poisoning the right Mutex rule, given `lock` takes a body with no effects? Alternatives?
3. Is the C back end's per-call check acceptable, or should C use something else (setjmp at task roots + no destructors-on-panic for C-only builds is unacceptable to me)? How costly is it typically?
4. Cancellation checks at back-edges: is a polled flag the right mechanism, versus signal-based safepoints / page-protection polling as some JVMs do?
5. Anything about `spawn` capturing `readonly` outer state that makes isolation unsound — e.g. a `readonly` borrow of something containing a `Cell`, or a region?

## Step 16: suspending code compiled to state machines

Proposal: after specialization, each function's effect row says if it can suspend (Io, Yield, or an effect whose handler is not tail-resumptive). Non-suspending functions run on the worker's native stack. Suspending functions become state machines; callee frames nest in the caller's so a task's frame tree is one allocation of compile-time size, allocated at spawn and never moved, so borrows across suspension need no Pin. Recursion or `dyn` suspension takes a frame from a task-local frame stack. Fast paths (uncontended lock, buffered read, ready channel) inline.

Questions:
6. Handlers: a non-tail-resumptive handler arm receives a continuation `k` that it may resume later, once, or drop. With state machines, `k` is a pointer to the suspended frame chain from the perform site up to the handler. Is anything lost compared with fibers? What about a handler installed inside a suspending function, whose body suspends to an outer handler (Io) while also performing the inner effect?
7. Higher-order effect-polymorphic functions (`map` with `uses ...E`) are specialized per E, so when E contains Io they become state machines. Is code-size blow-up a real risk, and how do Koka / Swift / Rust handle it?
8. FFI: `extern "C"` called from a suspending function, and C calling back into Flyscript that suspends. Fibers allow the latter; state machines do not. Should callbacks into Flyscript from C be forbidden from suspending (type-level), or should we keep fibers as a fallback for that case?
9. Is "frame size known at compile time for non-recursive task trees" honest given `dyn` and closures passed as values? What fraction of real programs would fall back?
10. Should we keep fibers at all after this, e.g. for debugging, or for `Gen` pulled with `next()`?

Rank the risks you see across both steps.

## Context files

- `docs/roadmap.md`

## Answer

### Verdicts

- **Q1 (Unwinding from pure code):** **Agree with changes.** It is sound *only* because `ir.fly` and λ-fly are in A-normal form (no mid-record-literal states exist in the IR), **except** for two concrete soundness bugs you must prevent: (1) a `defer` running during a pure panic can read a local binding that was temporarily `mut`-borrowed by the panicking pure function after the callee moved a subfield out or broke an invariant, and (2) `par` / `join` (`§6.5`) runs pure closures on worker threads without an `Io.scope` — if one branch of `join(a, b)` panics, the other must be joined before unwinding the caller's stack frame, or the sibling worker will read/write a dangling `readonly`/`mut` slice (`ParSplit`) on the unwound stack.
- **Q2 (`Mutex` poisoning vs dropping the locked value):** **Disagree with dropping the `Mutex`'s value in `lock` while keeping the value at its place (`v: mut T`).** In `lock((v: mut T) => ...)`, `v` is lent `mut` *in place*, not moved by value into the closure (`§4.1`: no field may be moved out of a `mut T` borrow!). If `body` panics mid-mutation, dropping `v` runs `T`'s `Drop` on a potentially half-mutated `T` (which could itself panic and abort the whole server!). Poison the `Mutex` first, and only drop `T` when the `Mutex` itself is dropped (or replaced via `clearPoison(newVal)`).
- **Q3 (C backend unwinding):** **Disagree with per-call panic checks; Agree with one `setjmp` per lexical scope that has cleanup (`Drop` / `defer` / `region`).** Checking a panic flag after *every* pure call (`xs[i]`, `a + b`, helper calls) bloats C output and costs 10–25% on CPU-bound code. A stack-linked `fly_cleanup_frame` with `setjmp` is emitted **only** in scopes that actually register a `Drop`, `defer`, or `region` (a tiny fraction of pure functions), costs ~3 instructions on scope entry, zero instructions on calls, and runs every destructor and `defer` in exact reverse lexical order.
- **Q4 (Cancellation checks at loop back-edges):** **Disagree with cancelling pure loops into a normal task exit; Agree only if cancelling a runaway pure loop is a *panic* (or only at `Io` points), using a polled thread/task flag.** If a pure function can be stopped at a loop back-edge, it is semantically identical to a panic from pure code (same Q1/Q2 invariants!). Poll a `u8` flag in the task context at back-edges of loops that contain no `Io` calls (do *not* check at every function entry — back-edges + recursive back-edges suffice and avoid per-call overhead); do not use `SIGSEGV`/mprotect safepoints (breaks freestanding, Wasm, and C portability).
- **Q5 (`spawn` capturing `readonly` outer state when panics unwind):** **Agree — sound as long as a panic in a `spawn`ed task does NOT cause `Io.scope` to exit early.** Because `Cell` and `RegionList` mutations require `uses Region<R>` and outer regions are frozen during `Io.scope` (`§6.1` Rule 5), `spawn`ed tasks cannot mutate outer regions. However, if `spawnHandle.cancel()` or a `fork` panic unwinds `Io.scope`, `Io.scope` **must still wait for all unwinding `spawn` tasks to finish their `Drop`s and `defer`s before exiting `Io.scope`**, or an unwinding `spawn` task's `defer` will read a dangling `readonly` borrow from outside `Io.scope`.
- **Q6 (State machines + first-class `Cont` and nested handlers):** **Disagree with single-slab allocation when `Cont` can escape its `handle` (`§5.3`).** If `handle { body } with Eff { op() resumes k => ... }` is inside a task and `k` escapes the `handle` expression (`§5.3`: *"A continuation that leaves its arm — returned, stored in what the arm gives..."*), `body`'s frames **cannot** live in the caller's inline task slab, because the `handle` expression returns to its caller (which will reuse that slab space for subsequent calls!) while `k` is still alive! Any `handle` whose `k` can escape (and `generate`) must allocate its frame slab separately on the heap/frame-stack.
- **Q7 (Code-size blowup from effect-polymorphic HOF specialization):** **Agree with changes.** Specializing `map`/`filter`/`fold` per concrete effect row `E` is already collapsed by erasing `E` to 1 bit (`suspends: bool`), **except** in a state machine where every call site to a closure `f: (A) => B uses ...E` needs to know the *size and alignment of `f`'s suspension frame*! Without a uniform frame convention for indirect suspending calls, every closure type with a different frame size forces a different specialization of `map`.
- **Q8 (FFI callbacks and `extern "C"`):** **Agree: forbid `export extern "C"` from having any effects (already in `§8.2`!), and run `extern "C"` calls on the worker thread's native OS stack.** Do not keep fibers as a fallback for C-calling-Flyscript-that-suspends; `§8.2` already states: *"`export extern "C" function f(…): R { … }` is a function C calls, under its symbol; it performs nothing, as C can handle no effect or failure."*
- **Q9 (Static single-slab frame size vs `dyn`, closures, and recursion):** **Disagree that most real programs have a compile-time-known single slab size.** Every call to a first-class suspending closure (`f: () => T uses Io`, or `Gen.map` / `Fail.capture` / route handlers / middleware) or recursive function (`value()` in `A.1` if it performed an effect) has an unknown callee frame size at the call site unless the closure is inlined/monomorphized. You will need the task-local bump arena (chunked frame stack) for every indirect/recursive suspending call — which is still 10× smaller than an 8–64 KB fiber stack!
- **Q10 (Keeping fibers at all after Step 16):** **Disagree with keeping two suspension mechanisms (fibers + state machines) in the native backends.** Keeping both doubles the runtime surface and sanitizer/proof complexity. Replace native fibers completely with the hybrid **inline-frame + task-local chunked frame arena** (which handles tasks, `generate`, and escaping `Cont` with one mechanism).

---

### Problems (Ranked Most Serious First)

#### 1. [Step 16, Q6 & Q9] Soundness & Architecture: Escaping `Cont` (`§5.3`), `generate` (`§5.5`), and indirect suspending closures break the "one static frame slab per task" invariant

In Step 16, you propose:
> *"Suspending functions become state machines; callee frames nest in the caller's so a task's frame tree is one allocation of compile-time size, allocated at spawn and never moved, so borrows across suspension need no Pin."*

Here are **two concrete Flyscript programs** where nesting callee frames inside the caller's single static slab either corrupts memory (use-after-free / frame overwrite) or fails to have a compile-time size:

**Program 1A: A `handle` whose continuation `k` escapes its arm (`§5.3`) or `generate` (`§5.5`) inside a task.**
```ts
effect Step { pause(): void; }
enum Yielded { #Done, #Paused(Cont<void, Yielded, []>) }

function makeStepper(): Yielded {
  handle {
    let localBuf: u64[4] = [1, 2, 3, 4];
    Step.pause();
    // `localBuf` is live across `Step.pause()`!
    if (localBuf[0] == 1) { #Done } else { #Done }
  } with Step {
    pause() resumes k => #Paused(k), // `k` leaves the arm and `makeStepper` returns!
  }
}

export function main(): void uses Io {
  const s = makeStepper();
  // Now `makeStepper()` has returned! If `makeStepper`'s frame was nested inside
  // `main`'s static frame slab at offset 64, the next call in `main` overwrites offset 64!
  otherSuspendingCall();
  match (s) {
    #Paused(k) => { const _ = k(); }, // CORRUPTION: `k`'s frame in `main`'s slab was overwritten!
    #Done => {},
  }
}
```
Look at what happens when `pause() resumes k => #Paused(k)` returns `#Paused(k)` without resuming `k`:
1. The `handle` expression finishes and `makeStepper()` returns `#Paused(k)` to `main`.
2. If the `handle` body's frame (`localBuf`, state index) was nested inline inside `main`'s static task slab, `main` then advances to `otherSuspendingCall()`, whose frame shares the **same union slot** in `main`'s static slab!
3. When `k()` is finally called, its frame has been overwritten by `otherSuspendingCall()`!

**Program 1B: First-class suspending closures (`§4.3`, `§5.1`).**
```ts
function runTwice(f: () => void uses Io): void uses Io {
  f();
  f();
}
```
Here `f` is a runtime closure value `{ fn, env, drop }` of type `() => void uses Io`. Two different callers can pass two different closures to `runTwice` — one whose body suspends across `Io.sleep` with a 32-byte frame, and one whose body suspends across `serveOne` (`§10.2`) with a 600-byte frame (`let buf: u8[512]`). `runTwice` is a single function taking a runtime function pointer `f`: it **cannot know at compile time** how large `f`'s state-machine frame is!

**Fix (Unifies static slabs, indirect closures, recursion, `generate`, and escaping `Cont` into ONE simple model):**
Do not try to make an entire task a single monolithic C `struct` with `union`s of all callees, and do not keep stackful fibers around either. Instead:
1. **Intra-procedural state machine + Direct-call frame coalescing:**
   - Every suspending function `F` has a compiler-generated `struct Frame_F { ResumeFn resume; Frame* caller; u32 pc; /* live-across-suspend locals */ }`.
   - For any **direct, non-recursive call** `G()` inside `F` (which does not cross a `handle` boundary whose `Cont` can escape), `struct Frame_F` embeds `struct Frame_G` inline in a `union` of `F`'s suspension points. This gives you the **exact single-allocation static slab** for the common case (`serveOne` -> `conn.read` / `Io.scope` / `db.fetchProfile`), with zero heap allocations at call sites!
2. **Task-local Arena Stack for indirect closures (`f()`), recursion, and `dyn`:**
   - Each task has a small chunked frame arena (say, an initial 256-byte or 512-byte slab that contains the root task's static coalesced frame plus spare tail space, allocating a new chunk only if a recursive or indirect closure chain exceeds it).
   - A suspending closure value `{ fn, env, drop, frame_size }` carries its `frame_size: u32` (or allocates its frame from the task's frame arena on entry and pops it on return). Because frames in the arena are never moved until popped on return, `mut buf` lent from a caller frame into an indirect closure or recursive callee remains at a fixed address without `Pin`!
3. **Detached Frame Slab for `generate` (`§5.5`) and `handle` with escaping `Cont` (`§5.3`):**
   - The compiler already knows statically whether a `handle` has an arm where `k` escapes (`§5.3` checks this!) and knows `generate`.
   - Those (and only those!) allocate their own small detached frame arena when the `handle` / `generate` starts. That arena is owned by `k` (or `Gen`), so when `makeStepper()` returns `#Paused(k)`, `k` owns its detached frame chain and dropping `k` walks `Frame* caller` from the leaf frame up to the `handle` root, running each frame's `pc`-indexed cleanup table!

---

#### 2. [Step 15, Q1] Soundness Bug: Unwinding from a pure panic allows a `defer` or `Drop` in the caller to observe a `mut`-borrowed binding whose invariant or ownership was broken mid-call (`§4.1`, `§5.6`, `§5.7`)

In Question 1, you ask:
> *"Is unwinding-from-pure-code sound to add to a calculus where panics today are a terminal state? What invariant breaks first?"*

Here is the exact invariant that breaks first, demonstrated with a valid Flyscript program under the current spec (`§4.1`, `§5.6`):

```ts
function badMutate(v: mut Vec<String>, i: usize): void {
  // 1. Pop an owned String out of `v` temporarily
  const saved: String = v.pop().unwrap();
  // 2. Index `v[i]` — PANICS if `i >= v.len()`!
  const peek: str = v[i].asStr();
  // 3. Put `saved` back so `v`'s invariant is restored
  v.push(saved);
}

export function worker(): void uses Io {
  let v: Vec<String> = ["hello".toString()];
  // Under §5.6, `defer` borrows `v` when registered — Wait: §5.6 says:
  // "Because a defer runs at the block's exit, it holds the borrows it needs from the point
  // it is registered to the end of the block".
  // What if instead of `defer`, a custom `struct Guard { ... }` implements `Drop.drop(self: mut Self)`?
}
```
Now write it with `Drop` (`§4.4`, `§5.6`), where the struct itself implements `Drop`:
```ts
struct Pair {
  a: String;
  b: String;
  // Invariant assumed by `Drop`: `a` and `b` are always valid initialized Strings.
}
impl Drop for Pair {
  function drop(self: mut Self): void {
    // Reads both `self.a` and `self.b`!
    const _ = self.a.len() + self.b.len();
  }
}

impl Pair {
  function swapWithPanic(self: mut Self, xs: readonly i32[], idx: usize): void {
    // What if inside a method or in `ir.fly` lowering of `self.a = exprThatPanics(xs[idx])`:
    // Does `self.a = rhs` drop the old `self.a` BEFORE or AFTER evaluating `rhs`?
    self.a = `${xs[idx]}`;
  }
}
```
Look closely at `self.a = `${xs[idx]}`` (and in general `place = rhs` in `§5.6`: *"Assigning to a place drops the value it held first, unless that value was moved out"*):
1. In `ir.fly`, when lowering `place = rhs`:
   - If `ir.fly` evaluates `place` and **drops the old value of `place` BEFORE evaluating `rhs`**, and `rhs` panics (`xs[idx]` out of bounds!), then unwinding from `xs[idx]` will run `Pair.drop(mut self)` (or the block's local destructor for `self`!) while `self.a` has **already been dropped** and not yet overwritten by `rhs` — a **double-free / use-after-free**!
   - Even if `ir.fly` evaluates `rhs` into a temporary *first* before dropping the old `place`, what about `replace(mut p.a, val)` or a multi-step mutation inside a method on `Pair` before a panic?
     Because Flyscript (`§4.1`) forbids moving a field out of a `mut` borrow *and* forbids moving a field out of a type that implements `Drop`, every field of `self: mut Pair` **always holds a valid, initialized owner** at every statement boundary **provided** `ir.fly` obeys one strict rule:

**The ANF / IR Unwind-Safety Rule you must enforce in `ir.fly`:**
1. **Evaluate `rhs` completely into a temporary `t` BEFORE dropping the old value at `place` and storing `t` into `place`!**
   Never drop `place`'s old value before `rhs` has finished evaluating (because `rhs` can now panic and unwind!). The drop of old `place` and the store `*place = t` must be adjacent with zero panicking operations between them.
2. **In `Vec.pop`, `HashMap.remove`, `String.push`, and runtime builtins:** update `len` *before* (or atomically with) moving/dropping the element so no panic can ever happen while a container's length and initialized elements disagree.
3. **In `Drop.drop(self: mut Self)`:** since `Drop.drop` is ordinary Flyscript code, it can contain `xs[i]` or integer arithmetic that panics. You already specified: *"A panic inside a `Drop`, or while a panic is already unwinding, ends the program."* Good — that is essential.

---

#### 3. [Step 15, Q1] Soundness Bug: Panic inside `par` / `join` (`§6.5`) causes a sibling worker thread to race on dangling stack memory!

Look at `§6.5` (`join`, `par`, `parReduce`):
```ts
function join<A extends Send, B extends Send>(a: once () => A, b: once () => B): [A, B];
function par<C extends ParSplit>(c: mut C, f: (v: C.View, i: usize) => void): void;
```
Notice that `join` and `par` are **pure** (`uses []`), not `Io.scope`!
Now trace what happens when a task calls `par(mut localArr, (v, i) => ...)` where `localArr` is on the task's stack (or in a local `Vec`), and worker thread 2 steals the right half of `join(left, right)` while worker thread 1 runs `left`:
```ts
export function compute(): void {
  let data: i32[1024] = repeat(1);
  par(mut data, (v, i) => {
    if (i == 0) {
      panic("boom on worker 1"); // Worker 1 panics!
    }
    v += 1; // Worker 2 is concurrently mutating `data[512..1024]` on `compute`'s stack!
  });
}
```
If Worker 1 panics at `i == 0` and immediately unwinds `compute()`'s stack frame (releasing `data: i32[1024]` on Worker 1's stack or dropping a `Vec<i32>`), **Worker 2 is still running the stolen right half of `join` and writing `v += 1` into `data[512..1024]` — a use-after-free and data race in safe pure code!**

**Fix:**
`join(a, b)` in the runtime **must join both halves before unwinding a panic!**
Specifically, in `rt`'s implementation of `join(a, b)`:
- If `a` panics (or `b` panics on a thief worker), `join` catches the panic token at the `join` boundary, sets the cancellation flag so the sibling finishes early, **waits for the stolen sibling closure to complete**, drops the non-panicking sibling's result if it succeeded, and *only then* continues unwinding the panic up into `join`'s caller!
This preserves memory safety and `§9.4`'s data-race freedom when `par`/`join` panics.

---

#### 4. [Step 15, Q2] `Mutex` Poisoning vs Dropping the Locked Value (`§6.2`)

In Step 15, you propose:
> *"inside `Mutex.lock`'s body, the value the lock lent is dropped rather than given back, and the mutex is poisoned: locking it again panics, unless a fresh value is put in it. This falls out of the proof's model of a mutex, where `lock` moves the value to the task and a panic drops what the task owns."*

Wait: look at the difference between the **Lean proof's model** (`§9.5`: *"a `Mutex` of a box, whose lock moves the box out to the task that locks it"*) and the **actual surface language & runtime** (`§6.2`):
```ts
impl<T extends Send> Mutex<T> {
  export function lock<R extends Send>(self: readonly Self, body: once (v: mut T) => R): R uses Io;
}
```
In the surface language, `body` takes `v: mut T` (a mutable borrow of the `T` stored inside the `Mutex`), **not** an owned `T` by move!
Why does this matter?
1. Because `v` is a `mut T` borrow (`§4.1`), `body` **cannot move `v` or move any field out of `v`**! At the moment `body` panics (say, on `let x = 1 / 0;` or `xs[99]` while updating two fields of `v`), every field of `v` is still physically present and initialized in the `Mutex`'s slot (thanks to the ANF assignment rule in Problem 2 above).
2. If you drop `v` immediately inside `Mutex.lock`'s unwind landing pad while the `Mutex` is still alive and shared by other tasks:
   - What if `T`'s `Drop.drop` panics because `body` panicked halfway through updating two fields of `T` whose logical invariant `Drop.drop` asserts? Then *"A panic inside a `Drop`, or while a panic is already unwinding, ends the program"* triggers and **kills your entire 5,000-connection server**!
   - Even if `T` is just `HashMap<String, Item>` (`§6.2`), why run a potentially expensive destructor of a 1,000,000-entry `HashMap` inside the panicking task while holding the mutex lock (blocking or poisoning waiters), when another task (or supervisor) might call `mutex.intoInner()` / `mutex.recover((v: mut T) => ...)` or replace it?
3. Look at the proof model too: in the proof (`§9.5`), if a poisoned `Mutex` keeps ownership of its `T` cell in a `#Poisoned(T)` state (rather than moving it back to `#Unlocked(T)`), the proof invariant is *even simpler*: the `Mutex` handler still owns the cell of `T` (so nothing leaks, and it is dropped when the `Mutex` handler scope exits!), and any subsequent `lock` operation on `#Poisoned(T)` immediately panics the calling task unless `reset(newVal: T)` replaces the old `T` (dropping it then) and transitions back to `#Unlocked(newVal)`!

**Recommendation for Q2:**
- **Keep poisoning** (because `body` takes `mut T` and may have updated `v.field1` before panicking prior to updating `v.field2`, breaking a logical invariant between fields).
- **Do NOT eagerly drop `v` during panic unwinding of `lock`:** mark the `Mutex`'s state word as `POISONED` and unlock the wait queue (waking waiters so they immediately panic rather than hanging forever!). Drop the inner `T` when the `Mutex<T>` itself is dropped, or when `m.reset(newVal)` overwrites it. That avoids double-panic aborts during unwinding and still leaks nothing when the scope owning the `Mutex` exits.

---

#### 5. [Step 15, Q5] Soundness Bug with `spawnHandle.cancel()` and `Io.scope` Unwinding while `spawn` Tasks Hold `readonly` Borrows (`§6.1`)

In Question 5, you ask:
> *"Anything about `spawn` capturing `readonly` outer state that makes isolation unsound — e.g. a `readonly` borrow of something containing a `Cell`, or a region?"*

Let's check both parts of your question:
1. **`Cell` / `RegionList` / outer region:**
   In `§4.6`, `Cell.get`, `Cell.set`, and `RegionList.push` all require `uses Region<R>`.
   By `§6.1` Rule 4 & 5, neither `Io.scope`'s body nor any `spawn`/`fork` task can perform an outer `Region<R>` effect. Therefore, no task can read or write an outer `Cell<R, T>` or push to an outer `RegionList<R, T>` during `Io.scope`. (Reading an outer `Ref<R, T>` or iterating existing elements of an outer `RegionList<R, T>` is pure and immutable, so a panicking `spawn` task cannot corrupt it.)
2. **HOWEVER, look at what happens when a `spawn` task panics or is cancelled while holding a `readonly` borrow of a binding declared outside `Io.scope`:**
   ```ts
   export function serve(db: Db): void uses Io {
     Io.scope((s) => {
       s.spawn(() => {
         defer { db.logDisconnect(); }; // Uses `readonly db` during unwinding!
         panic("connection bug");
       });
       // Suppose the scope body or another `fork` task ALSO panics or finishes!
     });
     // Right here, `db` is dropped (or mutated)!
   }
   ```
   Look at the lifetime of `readonly db`:
   - If a `spawn`ed task panics, it unwinds and runs its `defer`s and `Drop`s (which may read `readonly db`!).
   - On the multi-core scheduler (`Step 4`), the panicking `spawn` task is unwinding **on Worker Thread 2**, while `Io.scope` is running **on Worker Thread 1**!
   - If `Io.scope` only waits for *running* tasks and marks a panicking `spawn` task as "done" *before* Worker Thread 2 has finished running the panicking task's `defer`s and `Drop`s (or if a `fork` task panics and cancels `Io.scope` before all `spawn` tasks have finished unwinding), then Worker Thread 1 will return from `Io.scope` and **drop `db` while Worker Thread 2 is still reading `readonly db` inside `defer { db.logDisconnect(); }`!**

**Fix:**
A task (whether `spawn` or `fork`) is not terminal until **its unwinding (`Drop`s and `defer`s) has completely finished and its stack/frame has been retired**. `Io.scope` must wait for the active task count to reach 0 *after* all unwinding completes, even when `Io.scope` itself is exiting due to a `fork` panic or parent panic.

---

#### 6. [Step 15, Q3] C Backend Unwinding: Per-Call Checks vs Lexical-Cleanup `setjmp` (`§11.2`)

In Question 3, you ask:
> *"Is the C back end's per-call check acceptable, or should C use something else (setjmp at task roots + no destructors-on-panic for C-only builds is unacceptable to me)? How costly is it typically?"*

Do **not** emit a per-call check after every pure call in the C backend, and you do **not** have to give up destructors-on-panic to use `setjmp`!
Here is why per-call checks in C are painful:
- In Flyscript, `a + b`, `xs[i]`, `s.len()`, and almost every small helper function can panic (overflow, bounds check).
- If every call in C is followed by `if (__unlikely(task->panicking)) goto cleanup_label;`, then:
  1. No pure function in C can return a value directly in an expression (`f(g(x), h(y))`), though `ir.fly` already lifts calls to `Let`s;
  2. Every call site gets a memory load of `task->panicking` + conditional branch, preventing C tail-call optimization and adding ~10–20% overhead on call-heavy code (like the compiler itself!).

**The clean alternative that runs ALL destructors and `defer`s on panic with zero per-call checks:**
In `ir.fly`, cleanup is **already lexical** (`Phase 0`: *"each block with an explicit cleanup list (drop local / defer / free arena)"*).
Notice how few functions actually own a non-trivial cleanup scope (`Drop`, `defer`, or `region`): most pure leaf/helper functions only touch primitives, slices, or `Copy` structs!
In the C backend:
1. Only when entering a block in `ir.fly` that actually has a non-empty cleanup list (`Drop`, `defer`, or `region`), push a stack-allocated `fly_unwind_frame { jmp_buf buf; struct fly_unwind_frame* prev; }` onto `task->unwind_top` and call `if (setjmp(frame.buf) != 0) { /* run this block's cleanup list, then longjmp(frame.prev->buf, 1) */ }`.
2. When leaving that block normally (or via `return`/`break`/`Fail`), pop `task->unwind_top = frame.prev;` and run the cleanup list normally.
3. When `fly_panic()` fires anywhere, it sets `task->panicking = 1` (so any `Io`/effect op inside a `defer` is immediately cancelled) and calls `longjmp(task->unwind_top->buf, 1)`!
- **Cost on functions without `Drop`/`defer`/`region`:** **Zero** (not a single extra instruction, branch, or `setjmp`).
- **Cost on blocks with `Drop`/`defer`/`region`:** one `setjmp` per scope entry, zero per-call branches inside the block, and 100% exact destructor/`defer`/arena cleanup on panic, matching LLVM `invoke`/landingpad semantics!

---

#### 7. [Step 15, Q4] Cancellation Checks at Back-Edges and Stack Overflow (`§5.7`, `§6.1`)

In Question 4, you ask:
> *"Cancellation checks at back-edges: is a polled flag the right mechanism, versus signal-based safepoints / page-protection polling as some JVMs do?"*

1. **Use a polled flag at loop back-edges, NOT page-protection / signal safepoints.**
   - Why not `mprotect` + `SIGSEGV` safepoints? Because (a) they do not exist in WebAssembly, JavaScript, or `--freestanding` kernels (unless you wire up MMU faults per target), (b) unwinding out of an asynchronous `SIGSEGV` signal frame in C or LLVM requires async-unwind tables (`-fasynchronous-unwind-tables`) and cannot safely interrupt a function mid-instruction when `ir.fly` only defines cleanup state at statement boundaries!
   - Why a polled flag is essentially free: in `ir.fly`, every function that runs inside a task already has access to the task context pointer (or thread-local `current_task`). Polling `if (__unlikely(task->cancelled)) fly_cancel_unwind();` is ONLY needed at:
     - **Loop back-edges** of loops whose body is not statically guaranteed to perform an `Io` operation on every iteration, and
     - **Recursive function entries** (functions in an SCC of the call graph, which you already identify for Step 16's static frame analysis!). Non-recursive function entries do **not** need a cancellation check at all, because a finite DAG of non-recursive calls without loops terminates in bounded steps!
2. **One crucial semantic point:**
   If a pure function (`uses []`) can be interrupted at a loop back-edge by `cancel()`, then **cancellation at a pure loop back-edge IS a panic (unwinding), NOT an effect!**
   Make sure the spec states that cancelling a task sets its `cancelled` flag: if the task hits an `Io` point, it unwinds via cancellation; if it is stuck in a pure loop, the back-edge check triggers task unwinding identically to a panic (dropping the task's continuation).
3. **Stack overflow as a task panic:**
   Once Step 16 (state machines) lands:
   - Suspending call chains live in the task's frame arena: checking for frame-arena overflow against a per-task limit (e.g. 1 MB max frame arena) when pushing a recursive frame is a 2-instruction integer comparison in the arena bump allocator, which cleanly raises a normal Flyscript panic (`panic("stack overflow")`) at a safe call boundary!
   - For pure recursion on the native worker stack, checking `__builtin_frame_address(0) < worker->stack_limit` ONLY on entry to **recursive functions** (functions in a call-graph cycle) costs 2 instructions on recursive functions, 0 instructions on all non-recursive functions, and turns native stack overflow into a clean, safe task panic before touching the OS guard page!

---

#### 8. [Step 16, Q7] Avoiding Code-Size Blowup in Higher-Order Effect-Polymorphic Functions (`§5.1`, `§11.3`)

In Question 7, you ask:
> *"Higher-order effect-polymorphic functions (`map` with `uses ...E`) are specialized per E, so when E contains Io they become state machines. Is code-size blow-up a real risk, and how do Koka / Swift / Rust handle it?"*

Look at what happens in the compiler today vs under Step 16:
- Today (with stackful fibers in C/LLVM), `map<T, U, E>` doesn't care about `E` at all in C/LLVM: whether `f` suspends or not, the machine code of `map<i32, i32>` is **one** function!
- Under Step 16 (state machines), for a fixed `(T, U)`:
  - When `E` cannot suspend (`suspends == false`), `map<T, U, false>` is a normal native-stack function.
  - When `E` *can* suspend (`suspends == true`), `map<T, U, true>` is a state machine.
- **When would code-size blow up?**
  Only if `map<T, U, true>` had to be specialized **per concrete closure type / per concrete closure frame size**!
  If instead a suspending closure value `f: (A) => B uses ...E` has a **uniform calling convention** (the closure pushes/allocates its frame on the task's frame arena when it suspends, or its frame pointer is allocated from the task's frame arena using `f.frame_size`), then:
  - There are at most **two** specializations of `map<T, U, E>` per `(T, U)` — one non-suspending (`map_sync`) and one suspending (`map_async`) — **exactly matching Koka's and Swift's (`rethrows` / `@async`) 2-way split**!
  - And in almost all programs, `map<T, U>` is only ever called with non-suspending closures (so only `map_sync` is emitted), or only with suspending closures (so only `map_async` is emitted).

---

### Summary of Ranked Risks Across Steps 15 & 16

1. **[Rank 1 — Soundness, Step 16 Q6]: Escaping `Cont` (`§5.3`) and `generate` (`§5.5`) overwriting inline caller frames.** A `handle` whose `k` can escape (or `generate`) must allocate its frame chain in a detached arena owned by `Cont`/`Gen`, never inline in the enclosing task's static slab.
2. **[Rank 2 — Soundness, Step 15 Q1]: Panic inside `par` / `join` (`§6.5`) unwinding the parent stack while a thief worker thread is still accessing `readonly`/`mut` stack slices.** `join(a, b)` must barrier-wait for both worker halves before propagating a panic.
3. **[Rank 3 — Soundness, Step 15 Q1]: `place = rhs` dropping old `place` before `rhs` panics.** `ir.fly` must evaluate `rhs` completely into an ANF temporary before dropping the old value of `place` and writing the new value, so no local or struct field is ever in a dropped/uninitialized state when a pure expression panics.
4. **[Rank 4 — Soundness, Step 15 Q5]: `Io.scope` exiting before a panicking/cancelled `spawn` task finishes running its `defer`s/`Drop`s on another core.** `Io.scope` must wait until every child task's unwinding has completed, or a child's `defer` will read dangling `readonly` borrows from the parent scope.
5. **[Rank 5 — Architecture, Step 16 Q9/Q7]: Indirect suspending closures & recursion in static slabs.** Use a hybrid model: coalesce direct non-recursive suspending calls inline into the caller's frame struct, and allocate indirect/recursive suspending frames on a task-local chunked bump arena.
6. **[Rank 6 — Reliability, Step 15 Q2]: Dropping `v: mut T` during `Mutex.lock` panic unwinding.** Mark the mutex poisoned and leave `T` in the mutex to be dropped when the `Mutex` is dropped or reset, avoiding double-panic aborts from broken mid-mutation invariants in `T.drop()`.
7. **[Rank 7 — Performance, Step 15 Q3/Q4]: C per-call panic checks and per-function-entry cancellation checks.** Use per-cleanup-scope `setjmp` in C (zero per-call overhead), and emit cancellation + stack-overflow checks only at loop back-edges and recursive function entries (call-graph SCCs).
