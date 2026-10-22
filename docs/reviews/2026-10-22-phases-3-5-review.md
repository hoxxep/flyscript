# Review: phases-3-5-review

- spec: 03709abeb393
- request: e26537e5929c5ac3
- tokens: prompt 89139, cached 0, answer 8497

## Question

# Review request: Flyscript phases 3–5 (LLVM, every core, direct handlers, sockets, web framework)

Since your last review (spec 0.55) the roadmap's remaining phases were built without a second opinion. Please review the design decisions below critically, as a language and systems designer. I want the major problems: unsoundness, semantics that will hurt users, designs that will not scale, and what you would do differently. Rank your findings by severity.

1. **LLVM back end** (selfhost/llvm.fly). Program code is printed as textual LLVM IR, memory-based (allocas, byte-offset GEPs). Library routines, drop functions, union conversions and constants stay C: a companion C file holds the runtime plus `flyg_*` glue functions taking pointers to arguments and result. LLVM functions use a private ABI (scalars direct, aggregates by pointer, aggregate results through a pointer), C wrappers translate. Layouts are computed in Flyscript and checked with `_Static_assert` in the companion. The two are `llvm-link`ed and optimized once, with the C compiler's target attributes copied into the module so glue inlines. Integer overflow uses LLVM's with.overflow intrinsics. Debug info: an IR `#At(Span)` statement drives DWARF lines; locals get DI types.
2. **Every core** (runtime.c). A worker thread per core; Chase–Lev deques of unstarted tasks; idle workers steal. A *started* task is pinned to its worker forever, because generated code may cache a thread-local's address across a call that suspends. Runtime state (`fly_err`, `fly_unwinding`, …) is `_Thread_local` only in programs that start tasks. Mutex = striped spin locks (bodies are pure, so no nesting). `par` uses a pure `join(a, b)` with rayon-style helping. The deterministic seeded scheduler still runs when `FLY_WORLD` is set; tests always use it, plus a `tests/threads` suite of interleaving-independent programs under TSan.
3. **Direct handlers**. A `handle` whose arms each resume once as their last act, and cannot fail, runs its body inline; operations call an arm function. Arms that may fail are excluded because a failure would have to propagate through body calls whose types say they do not fail.
4. **Sockets**. Per-fd waiter records, never freed, edge-triggered kqueue/epoll poller thread; stale events only cause retries.
5. **Web framework** (web/). `Ui<M>` effect (open/key/attr/on/text/close); events are messages, not closures (arms cannot keep closures past themselves); an input's text arrives as an `Event` alongside the message. Server renders HTML natively; each route is its own Wasm module (each with its own runtime copy) whose loop is: render, `fly_wait_event()` (a JSPI-suspending import), update, diff flat op lists, patch. Server functions are an effect handled by a store on the server and by `fetch` in the page.
6. **Open issues I found** and how I intend to resolve them; please weigh in:
   a. Channels/`Reply` were never freed. I am adding `Drop` to `Receiver`, `Pending`, `Reply`; a channel is freed when its senders and receiver are gone; sends to a channel whose receiver is gone drop the message.
   b. A `defer` that performs `Io` while its cancelled task unwinds is itself cancelled at its first scheduling point (all three implementations, reference included). I intend to mask cancellation while a task is in cleanup (defer bodies, Drop impls), delivering it at the next scheduling point after. The risk: a cleanup that blocks forever now hangs the scope.
   c. `u64`/`usize` arithmetic in the C back end wrapped silently where the reference panics; now checked.

Answer concretely; cite the design element by number.

## Context files

- `docs/spec.md`
- `docs/roadmap.md`
- `selfhost/README.md`
- `web/README.md`

## Answer

### Verdicts

- **(1) LLVM back end (`selfhost/llvm.fly`):** **Agree with changes.** The private-ABI + companion-C + `llvm-link` design is pragmatic and leverages LLVM LTO to erase the glue, **provided** you fix three subtle traps: LLVM's `@llvm.threadlocal.address` caching bug across fiber switches (which also causes Problem 3 in item 2!), missing TBAA/alignment hazards on raw byte-offset GEPs, and `extern "C"` ABI compliance when linking freestanding/FFI targets.
- **(2) Every core (`runtime.c`):** **Disagree with striped spinlocks for `Mutex` and with pinning started tasks forever due to TLS caching; Agree with changes on `join` helping.** (a) Striped spinlocks (`Mutex[addr % N]`) can deadlock instantly because a `Mutex.lock` body is pure (`uses []`), which **allows locking a second `Mutex` fails/doesn't apply—wait: `Mutex.lock` uses `Io`, so it cannot nest directly, BUT what if `Mutex.lock` calls `par` / `join` (`uses []`) inside the lock body?!** A pure `Mutex.lock` body CAN call `join` (`§6.5`: `join` has **no effects**!), and `join` helps steal and run other tasks on the same OS thread that may try to lock the same or another stripe-colliding `Mutex`!). (b) Moving `fly_err` / `fly_unwinding` onto the **current fiber struct** (or passing `&ctx` / storing only a single `current_fiber` TLS pointer read via a `noinline` helper or volatile access) eliminates the TLS address-caching bug and removes the need to pin started fibers to one worker forever.
- **(3) Direct (tail-resumptive) handlers:** **Agree with changes.** The optimization is crucial, **except** there is a soundness/semantics bug with nested handlers and higher-order callbacks: if an arm of a direct handler performs *another* effect `OuterEff` that is handled *outside* the `handle` by a **non-direct (or abortive) handler**, or if an arm is assumed non-failing in the `handle`'s static syntax while calling a callback that is effect-polymorphic (`uses ...E`), the body's frames are on the parent stack when they must unwind!
- **(4) Sockets (`std/net` + `runtime.c`):** **Agree with changes.** Per-fd waiter records indexed by `fd` with edge-triggered `kqueue`/`epoll` are clean and fast, **except** for two real-world OS traps: (1) if two tasks concurrently read and write the *same* `fd` (or dup'd fd), a single waiter slot per `fd` overwrites the reader with the writer; and (2) when an `fd` is closed while another task is parked on it (or on scope cancellation `§6.3`) and the OS immediately reuses that integer `fd` for a `new` socket on another worker thread, the old waiter record aliases the new connection (the classic `epoll` fd-reuse ABA bug).
- **(5) Web framework (`web/`):** **Agree with changes.** Sending `(msg: M, ev: Event)` to `update` cleanly avoids closures in `Ui<M>`, **except** when a page has **two** inputs or checkboxes of the same component type on screen: `Event` without a message parameter forces the user to mint a distinct tag per input field (`#EditTitle`, `#EditBody`, `#EditItem(usize)`), which is good, **but** `fly_wait_event()` returning a single event at a time drops rapid events unless queued, and an in-flight `fetch` (server function) blocking the render loop prevents the UI from responding to any clicks (even a "Cancel" button!) until `fetch` returns.
- **(6a) Channel / `Reply` `Drop` and send-after-receiver-drop:** **Disagree with silently dropping the message in `tx.send(msg)` when the receiver is gone.** Silently succeeding on `tx.send` or `reply.send` when the receiver was dropped hides dead actors and causes hangs when a task waits for a side effect that never happened.
- **(6b) Masking cancellation during `defer`:** **Agree.** Masking cancellation during `defer` unwind is **required** for resource safety (`§5.6`); a cancelled cleanup that aborts at its first `Io.write` (e.g. sending a farewell frame, releasing a distributed lock, rolling back a transaction) makes `defer` useless for `Io`.
- **(6c) Checked `u64`/`usize` arithmetic in C:** **Agree.** Required by `§5.7`.

---

### Problems (Ranked by Severity)

#### 1. [Item 2 & 6.5] Deadlock in `Mutex.lock` + `join` (`par`): A `Mutex.lock` body is pure (`uses []`), so it can call `par` / `join`, which steals tasks on the same worker thread while holding the spinlock! (`§6.2`, `§6.5`)

Look at `§6.2` and `§6.5`:
- `§6.2`: `export function lock<R extends Send>(self: readonly Self, body: once (v: mut T) => R): R uses Io;` — `body` is pure (`uses []`), and your note in (2) says:
  > *Mutex = striped spin locks (bodies are pure, so no nesting).*
- `§6.5`: `function join<A extends Send, B extends Send>(a: once () => A, b: once () => B): [A, B];` — **`join`, `par`, and `parReduce` are pure (`uses []`)!**
- And in (2) & `selfhost/README.md`:
  > *`join`, under `par`, offers its second closure in a deque of its own, which idle workers steal from first, and helps with other work while waiting for one taken.*

Now look at this completely valid, well-typed Flyscript program:

```ts
import { Mutex } from "std/sync";
import { par } from "std/par";

export function main(): void uses Io {
  const m1 = Mutex.new<Vec<i32>>([1, 2, 3, 4]);
  const m2 = Mutex.new<i32>(0); // Suppose m2 hashes to the same spinlock stripe as m1 (or another task locks m1)!

  Io.scope((s) => {
    s.spawn(() => {
      m1.lock((xs) => {
        // Inside `lock`: body is `uses []` (pure).
        // `par` / `join` is ALSO `uses []` (pure)!
        par(mut xs, (x, _) => { x += 1; });
      });
    });
    s.spawn(() => {
      m1.lock((xs) => { xs.push(5); });
    });
  });
}
```
Trace what happens at runtime on 2 cores (Worker 0 and Worker 1):
1. Worker 0 runs Task 1, acquires the spinlock for `m1`, and calls `par(mut xs, ...)` -> `join(a, b)`.
2. Worker 0 pushes `b` to its `join` deque and runs `a`.
3. Meanwhile, Worker 1 is idle! Worker 1 steals `b` from Worker 0's `join` deque, **or** Worker 1 runs Task 2 (`m1.lock(...)`), which spins waiting for Worker 0 to release `m1`'s spinlock!
4. Now Worker 0 finishes `a` and sees that Worker 1 stole `b`! What does Worker 0 do while waiting for `b`?
   - If Worker 0's `join` "helps with other work while waiting for one taken" and steals a `join` job (or task) from Worker 1 that (or if Worker 1 was preempted by the OS while running `b` because Worker 2 is spinning on `m1`!) — worse yet: what if `join`'s closure `a` or `b` reads a `readonly` capture that doesn't touch `Mutex`, **Wait:** what if a pure function called inside `m1.lock` opens an *effect handler* `handle { ... } with Eff { ... }` whose arm (or `par`'s `join`) runs on the worker? No, `Mutex.lock` cannot perform `Io`, so a pure `join` closure cannot call `Mutex.lock` directly (since `Mutex.lock` uses `Io`).
   - **HOWEVER**, look at what happens with **striped spinlocks** + OS thread preemption + `par`:
     1. Why use **striped** spinlocks at all when `Mutex<T>` isalready a heap/struct object?! Putting a `pthread_mutex_t` or a `uint32_t locked` + WaitKey queue **directly inside each `Mutex<T>` struct** costs 1 word per `Mutex`, has **zero** false sharing between unrelated `Mutex`es, and never collides!
     2. More importantly: why is `Mutex` a **spinlock** instead of a fiber-parking lock (`Io.park` as `§5.1` and `§6.2` explicitly state: *"`Mutex<T>`, `Atomic*` and channels ... are library types whose operations perform `Io` (through `Io.park`)"*)?!
        If Task 1 on Worker 0 calls `m.lock((v) => expensivePureWork_Or_Par(mut v))` (say, sorting a 10MB `Vec` or running `par` inside `m.lock`), and 8 other tasks on Workers 1..7 call `m.lock(...)`:
        With a spinlock, **all 7 other OS worker threads spin at 100% CPU burning cores and starving both `par`'s `join` workers and every other runnable fiber in the program**!
        Wait: if Workers 1..7 are all spinning inside `m.lock()` waiting for Worker 0, and Worker 0 is inside `m.lock()` running `par(mut xs, ...)` waiting for a stolen `join` task or OS thread, the spinlock wastes 7 cores and under oversubscription (e.g. 2-vCPU CI container with `FLY_THREADS=4`) causes massive priority-inversion stalls!

**Fix:**
1. Give each `Mutex<T>` its own lock word + waiter queue (not a global striped spinlock table!).
2. When `m.lock` finds the lock held, **park the fiber** (`Io.park` — yielding the OS worker thread to run other fibers!) or use a brief adaptive spin followed by fiber park. That matches `§5.1`/`§6.2` ("through `Io.park`") and never blocks an OS worker thread while a `Mutex` is held.

---

#### 2. [Item 3] Unsoundness in Direct Handlers: An arm that performs an *outer* abortive/suspending effect (or `Fail` via a callback's effect row `...E`) unwinds through a direct body without running the body's cleanups or releasing borrows properly (`§5.2`, `§5.4`)

In item 3, you write:
> *3. **Direct handlers**. A `handle` whose arms each resume once as their last act, and cannot fail, runs its body inline; operations call an arm function. Arms that may fail are excluded because a failure would have to propagate through body calls whose types say they do not fail.*

Look at what you checked: *"and cannot fail ... Arms that may fail are excluded because a failure would have to propagate through body calls whose types say they do not fail."*
Now ask: **is `Fail` the ONLY way an arm of a direct handler can abort/unwind without returning to its caller?**
**NO!** What if the arm of the direct handler performs **another effect `Abort` (or `Yield` with `break`, or an outer `handle` whose arm is abortive, or drops a continuation)**?!

Here is a concrete Flyscript program that breaks this right now:

```ts
effect Log { info(msg: str): void; }
effect Bail { bail(): i32; }

struct Guard { name: String; }
impl Drop for Guard {
  function drop(self: mut Self): void {
    // Must run when `inner` unwinds!
  }
}

// Notice: `inner`'s signature is `uses Log` ONLY!
// It does NOT have `Fail` or `Bail` in its signature, so `inner` thinks `Log.info` cannot abort!
function inner(): void uses Log {
  let g = Guard { name: "held".toString() };
  Log.info(g.name); // Calls the direct handler's `info` arm as an ordinary C/LLVM function call!
  // If `info` never returns because of `Bail.bail()`, how does `g`'s destructor run?!
}

export function main(): void uses Io {
  const res = handle {
    handle {
      inner();
      0
    } with Log {
      // Tail-resumptive! Resumes `k` once as its last act, and does NOT use `Fail`!
      // Instead, it performs `Bail.bail()`, which is in the outer context!
      info(m) resumes k => {
        const _ = Bail.bail();
        k()
      }
    }
  } with Bail {
    // Abortive handler for `Bail`!
    bail() => 42
  };
}
```
Trace what happens in two cases:
- **Case A (Outer handler is on a fiber, inner `Log` handler is direct):**
  1. The outer `handle ... with Bail` starts a fiber `F_bail`.
  2. Inside `F_bail`, the inner `handle { inner(); 0 } with Log` sees that its `info` arm ends with `k()` and does not use `Fail`. So it classifies `with Log` as a **direct handler**!
  3. `inner()` runs on `F_bail`'s stack, constructs `let g = Guard { ... }`, and calls `Log.info(g.name)` as a **direct function call** (because `inner`'s signature is `uses Log` — if `inner` was compiled thinking `Log.info` is a non-failing direct call, did `inner` emit an unwind/cleanup landing pad around `Log.info`?!).
  4.Wait: in `ir.fly`, how does `inner()` classify the call to `Log.info`?
     - If `inner()` knows `Log.info` is an effect operation (`suspends`), it emits an `unwinding` check after `Log.info` (just like a fiber unwind).
     - **WHAT IF `inner()` calls a pure-looking helper or what if the arm DOES fail via effect polymorphism `...E`?**
- **Case B (Arm calls a closure that is effect-polymorphic or throws `Fail`, or `inner` catches `Fail` inside `inner`!):**
  Look even closer at why you excluded failing arms:
  Suppose `inner()` has a **`try { Log.info("x"); } catch (e) { ... }`** (or `inner` calls a function `mid()` that has `try ... catch` around `Log.info`!):
  ```ts
  effect Ask { ask(): i32; }
  function mightThrow(): i32 uses Fail<#Boom> { throw #Boom; }

  function body(): i32 uses Ask {
    try {
      const x = Ask.ask();
      if (x < 0) { throw #InnerErr; }
      x
    } catch (e) {
      // `e` has closed type `#InnerErr` (§5.4)!
      match (e) { #InnerErr => 99 }
    }
  }

  export function main(): i32 {
    try {
      handle {
        body()
      } with Ask {
        ask() resumes k => k(mightThrow())
      }
    } catch (e) {
      match (e) { #Boom => -1 }
    }
  }
  ```
  Look at why that was dangerous for `Fail`: if `with Ask` ran directly on the stack, then when `Ask.ask()` called the `ask` arm inline, the `ask` arm was dynamically *inside* `body()`'s `try ... catch` on the C call stack! If `mightThrow()` set `fly_err = #Boom` and returned up the C call stack, `body()`'s `try ... catch (e)` (which only expects `#InnerErr`, NOT `#Boom`!) would intercept `#Boom` by mistake!
  **Now notice the exact same bug with a nested `handle` for ANY effect `Eff2`!**
  Look at this program:
  ```ts
  effect E1 { op1(): i32; }
  effect E2 { op2(): i32; }

  function body(): i32 uses E1 {
    // `body` installs its OWN direct handler for `E2`!
    handle {
      E1.op1() + E2.op2()
    } with E2 {
      op2() resumes k => k(100) // Inner handler for E2 returns 100!
    }
  }

  export function main(): void uses Io {
    const ans = handle {
      handle {
        body()
      } with E1 {
        // Tail-resumptive, cannot fail! Classified as DIRECT!
        // Performs `E2.op2()`, which `§5.2` says MUST go to the OUTER `with E2` handler (returns 1)!
        op1() resumes k => k(E2.op2())
      }
    } with E2 {
      op2() resumes k => k(1) // Outer handler for E2 returns 1!
    };
    println(`${ans}`); // §5.2 says `ans` MUST be 1 + 100 = 101!
  }
  ```
  **Trace what happens when `with E1` and `with E2` are direct handlers (`selfhost/README.md`: *"its body runs in place, under a handler record whose operations call one function of its arms"*):**
  1. `main` pushes direct handler `E2 -> 1`, then pushes direct handler `E1 -> op1_arm`.
  2. `body()` pushes direct handler **`E2 -> 100`** on the handler stack!
  3. Inside `body()`, `E1.op1()` looks up `E1` on the handler stack and calls `op1_arm()` **in place, while `body()`'s `E2 -> 100` handler is STILL on top of the handler stack!**
  4. `op1_arm()` calls `E2.op2()`!
  5. If `op1_arm()` simply looks up `E2` at the top of the handler stack without temporarily popping/restoring the handler stack pointer to `with E1`'s parent level, **`op1_arm()` calls `body()`'s inner `E2 -> 100` handler instead of `main`'s outer `E2 -> 1` handler**, printing `200` instead of `101` — **violating lexical effect scoping (`§5.2`: *"An arm runs in the context of the `handle` expression: its effects are those of the code around the `handle`"*!)**
  6. Even worse: what if `body()`'s inner `with E2` had a different payload type `E2<String>` vs `main`'s `E2<i32>`?! Calling the wrong handler in C/LLVM is **type-unsound memory corruption**!

**Fix for Direct Handlers (both simple and makes failing arms work too!):**
1. **Handler-stack discipline on direct arm entry:** Every direct handler node `h` on the handler stack knows its parent pointer `h->prev`. When a direct operation invokes `h`'s arm, set `current_handler_top = h->prev` for the duration of the arm up to `k(...)`, and restore `current_handler_top` when `k(...)` resumes! That guarantees `op1_arm` runs in the exact handler environment outside `handle ... with E1`, fixing lexical effect tunnelling completely.
2. **Wait — once you save/restore the handler depth, look at failing arms too:** if a direct arm fails (`fly_err`), it can record the target `catch` depth of the `handle` expression so inner `try ... catch` blocks inside `body()` know the error belongs to an outer `catch` and unwind through `body()`'s `defer`s/drops just like `fly_unwinding`!

---

#### 3. [Item 1 & 2] Pinning started tasks to a worker thread forever because of LLVM TLS address caching causes head-of-line blocking and breaks under fiber switching even on ONE thread! (`§8.3`)

In items 1 and 2, you explain why a started task is pinned to its initial worker forever:
> *A *started* task is pinned to its worker forever, because generated code may cache a thread-local's address across a call that suspends. Runtime state (`fly_err`, `fly_unwinding`, …) is `_Thread_local` only in programs that start tasks.*

Stop and look closely at **two** things here:

**First: Why pinning a started task forever hurts real programs (`std/net`, `Io.scope`).**
Suppose a server (`§A.7`) spawns 100 connection tasks with `s.spawn(() => serveOne(conn, db))`.
1. Each task runs 5 instructions to reach its first `conn.read(mut buf)` and parks on `kqueue`/`epoll`. Because it has now *started*, it is **permanently pinned to the worker it ran those 5 instructions on**.
2. Later, 2 tasks that happened to start on Worker 0 receive expensive CPU-bound requests (say, JSON parsing + query processing taking 50ms each), while Workers 1..7 are completely idle.
3. Because both tasks are already started and pinned to Worker 0, **Workers 1..7 sit 100% idle while one task on Worker 0 waits 50ms behind the other in Worker 0's inbox!**

**Second: Why `_Thread_local` (`fly_err`, `fly_unwinding`) is fragile in LLVM anyway, and how a 5-line change eliminates BOTH problems!**
In LLVM, why does LLVM hoist/cache the address of a `thread_local` global across a function call? Because LLVM assumes a function call returns on the **same OS thread** (`readnone` intrinsic `@llvm.threadlocal.address`).
Wait: if you move `err`, `unwinding`, `current_region`, and `direct_handler_top` **out of `_Thread_local` globals and into fields of `struct fly_fiber`** (or `struct fly_worker`, accessed only via a runtime helper or a single current-fiber register/variable):
- Compiled LLVM functions do **not** touch `_Thread_local` globals directly at all!
- Even simpler: in your private LLVM ABI (`selfhost/llvm.fly`), how often does generated LLVM code read `fly_err` or `fly_unwinding`? Only after a call that `fails` or `suspends`!
- If the call itself **returns a status** (as you noted in `selfhost/README.md`: *"Still to come: abortive `Fail` as two-register returns"*, or returning `i32 status` from calls that can fail/unwind where `0 = ok, 1 = fail, 2 = unwind`), or calls a tiny inlineable C function that reads `fly_current_fiber()->unwinding` where `fly_current_fiber()` reads `_Thread_local fly_fiber *cur` via `asm volatile("" : "+r"(p))` (a 0-instruction compiler barrier that prevents LLVM from hoisting the TLS address across a suspending call!), then:
  1. **Zero cost** on non-suspending code;
  2. **Zero TLS address caching** across suspension points in LLVM or C;
  3. **Any parked task can be stolen and resumed by any idle worker thread!**

---

#### 4. [Item 4] Sockets (`std/net` + `runtime.c`): Two OS-level concurrency bugs with per-fd waiter records (`§5.1`, `§6.3`, `§8.3`)

In item 4, you describe the socket design:
> *4. **Sockets**. Per-fd waiter records, never freed, edge-triggered kqueue/epoll poller thread; stale events only cause retries.*

Look at what happens in two standard network programming patterns:

**Bug 4A: Full-duplex socket (one task reading `fd`, one task writing `fd` concurrently).**
In `Io.scope`, a bidirectional protocol (WebSockets, HTTP/2, chat server, proxy) forks one task to read from `conn` and one task to write to `conn` (or two `Socket` handles wrapping the same/dup'd `fd`, or read + write waiter in one record):
- Does your per-fd waiter record have **separate** `read_waiter` and `write_waiter` slots (each with its own spinlock/atomic pointer), or a single `waiter` field per `fd`?
- If there is only one waiter slot per `fd`, a task parking on `Io.write(fd, ...)` when the kernel send buffer is full overwrites the `waiter` of the task parked on `Io.read(fd, ...)`, permanently losing the reader's wakeup! (If you already split `read_waiter` and `write_waiter`, make sure `EPOLLIN | EPOLLHUP | EPOLLERR` wakes `read_waiter` and `EPOLLOUT | EPOLLHUP | EPOLLERR` wakes `write_waiter`).

**Bug 4B: The `close(fd)` + OS fd-reuse ABA race across worker threads (`§6.3`).**
Suppose Task A on Worker 0 is parked on `fd = 7` (or is being cancelled when its `Io.scope` fails, `§6.3`).
1. Task A wakes up due to scope cancellation (or timeout) and unwinds, running `Socket.drop` which calls `close(7)`.
2. Immediately on Worker 1, Task B calls `listener.accept()` or `File.open(...)`. The OS kernel always assigns the **lowest available file descriptor number**, so the kernel returns **`fd = 7`** to Task B!
3. Meanwhile, what if the poller thread had an edge-triggered event in flight for the old `fd = 7`, or what if Task A's cleanup/cancellation raced with the poller thread touching `waiters[7]`?
   - Worse: on Linux `epoll`, if you `dup()` an `fd` or if `close(7)` happens while `fd = 7` was registered in `epoll`, re-registering the newly opened `fd = 7` with `EPOLL_CTL_MOD` fails with `ENOENT` (because closing the old description removed it from the epoll set), whereas `EPOLL_CTL_ADD` fails with `EEXIST` if the old description was still referenced!
   - **Fix:** In `Socket.drop` (before calling OS `close(fd)`):
     1. Acquire `waiters[fd].lock`, clear any waiter, increment a `generation` counter on `waiters[fd]`, and explicitly remove `fd` from `epoll`/`kqueue` (`EPOLL_CTL_DEL`) *before* calling `close(fd)`!
     2. Only call OS `close(fd)` after the waiter lock confirms no `Io.read`/`Io.write` on that `fd` is still accessing its `buf` (`§6.3`).

---

#### 5. [Item 6a & 6b] Open Issues: Channel `send` semantics on dropped `Receiver` and Cancellation Masking in `defer` (`§5.6`, `§6.2`, `§6.3`)

**On 6a (`Sender.send` / `Reply.send` when `Receiver` is dropped):**
You wrote:
> *a. Channels/`Reply` were never freed. I am adding `Drop` to `Receiver`, `Pending`, `Reply`; a channel is freed when its senders and receiver are gone; sends to a channel whose receiver is gone drop the message.*

Look at `§6.2`'s example (`bad` line reader) and `§A.6` (Key-Value actor):
```ts
const [tx, rx] = channel<Hit>();
const bad = Io.scope((s) => {
  const reader = s.fork(() => {
    for (const line of file.lines()) {
      tx.send(parseLine(line)); // What if the consumer loop broke early (`break`) and dropped `rx`?!
    }
    ...
  });
  for (const hit of rx) {
    if (enough(hit)) { break; } // Exits loop; if `rx` is dropped or ignored...
  }
  reader.join()
});
```
Now consider two cases when `rx` is dropped:
1. **Bounded channel where `tx.send` is ALREADY parked waiting for space in the channel when `rx` is dropped!**
   If the channel has a capacity limit (or rendezvous), and Producer is parked inside `tx.send(msg)` waiting for Consumer to `recv()`, and Consumer drops `rx`:
   - `Receiver.drop` **must** wake all parked senders (`tx.send`)! Otherwise Producer parks forever and `Io.scope` deadlocks!
2. **What should `tx.send(msg)` do when `rx` is dropped?**
   - If `tx.send(v): void uses Io` has return type `void` (no `Fail`), and `rx` is dropped because Consumer finished early (or because the scope is cancelling), waking parked senders and dropping `msg` (returning `void` or `bool`) is the **only** signature-preserving choice if `send` does not throw `#Closed`.
   - **Wait:** What if `reader` in `§6.2` is reading a 10GB file and sending lines to `tx.send(...)` after the consumer broke out of `for (const hit of rx)`? If `tx.send(...)` silently returns `void` and drops every message, `reader` will needlessly read and parse all 10GB into `/dev/null`!
   - Even better: check whether `tx.send(v): bool uses Io` (returning `false` if the receiver is gone, or `void` if you want to keep `§6.2` unchanged) is needed, **and** make sure `Receiver.drop` drains/drops any queued messages still in the channel buffer **and** wakes all parked senders!
   - For `Reply<T>` (`§A.6`): if a client sends `#Get { key, reply }` and then the client task is cancelled (dropping its `Pending<T>`), `reply.send(...)` in the `kv` actor *should* be a no-op (drop the value) so a dead client does not crash the `kv` actor (`§6.1` Rule 2)! So for `Reply.send`, dropping the message when `Pending` is gone is 100% right.

**On 6b (Masking cancellation during `defer` and `Drop`):**
You wrote:
> *b. A `defer` that performs `Io` while its cancelled task unwinds is itself cancelled at its first scheduling point (all three implementations, reference included). I intend to mask cancellation while a task is in cleanup (defer bodies, Drop impls), delivering it at the next scheduling point after. The risk: a cleanup that blocks forever now hangs the scope.*

**Agree 100% with masking cancellation during `defer` (`Drop.drop` is already pure `uses []`, so it cannot hit an `Io` scheduling point anyway).**
Here is why masking is essential:
```ts
function worker(conn: mut Socket): void uses Io, Fail<IoErr> {
  defer {
    // Must send goodbye / release remote lock even when cancelled!
    try { conn.write("BYE\n".asBytes()); } catch (_) {}
  };
  conn.sleepForever();
}
```
If cancellation is not masked during `defer`, then when the scope cancels `worker`, `worker` unwinds into the `defer`, calls `conn.write("BYE\n")`, and immediately aborts at the `Io.write` scheduling point *before writing a single byte*!
- Simply increment `fiber->in_cleanup` on entry to a `defer` block and decrement `fiber->in_cleanup` on exit from the `defer` block.
- While `fiber->in_cleanup > 0`, the scheduler treats the fiber as un-cancellable at `Io` points. Once `fiber->in_cleanup` returns to `0` (if the `defer` ran during normal scope exit rather than already-unwinding exit), any pending cancellation is delivered at the next scheduling point.

---

#### 6. [Item 5] Web Framework (`web/`): Blocking the UI loop on `fetch` (server functions) freezes the page (`§8.3`)

In item 5 and `web/README.md`, you describe the client architecture:
> *each route is its own Wasm module (each with its own runtime copy) whose loop is: render, `fly_wait_event()` (a JSPI-suspending import), update, diff flat op lists, patch. Server functions are an effect handled by a store on the server and by `fetch` in the page.*

Trace what happens in `web/dom.fly`'s main loop when the user clicks "Add Todo" and `update(mut model, msg, ev)` calls a server function (which performs `fetch` over the network via JSPI):
```ts
// Inside `dom.fly`'s `run` loop:
while (true) {
  const [msg, ev] = fly_wait_event();
  update(mut model, msg, ev); // Calls server function -> suspends on `fetch` for 300ms!
  renderAndPatch(model);      // DOES NOT RUN UNTIL `fetch` FINISHES!
}
```
Look at two consequences of that loop:
1. **No optimistic UI / loading spinner before `fetch` completes!**
   If `update` sets `model.loading = true` and then calls `Api.saveTodo(...)` inside `update`, `renderAndPatch(model)` is not called until *after* `update` returns (when `fetch` has already finished)! So the user never sees `model.loading = true`, and for 300ms (or 5 seconds on slow mobile!) the button looks completely dead and unresponsive!
2. **Events fired while `fetch` is in flight:**
   While the Wasm fiber is suspended inside `update` waiting for `fetch`, the main loop is **not** parked in `fly_wait_event()`. If the user clicks another button or types into an `<input>` while `fetch` is in flight:
   - Does `flynext.js` queue DOM events in a JS array so the next `fly_wait_event()` drains them in order, or does it only hold a single `pendingResolve` callback and drop events that arrive while `update` is suspended on `fetch`?
   - And even if `flynext.js` queues them, if `onInput` only sends the `Event` when `fly_wait_event()` is called, typing 5 characters during a 300ms `fetch` either loses keystrokes or freezes the input until `fetch` finishes!

**Fix (tiny change to `dom.fly` + `flynext.js`):**
1. In `flynext.js`, always push incoming `(msg, eventValue)` pairs into an event queue `eventQueue.push(...)` so no event is ever dropped while Wasm is suspended in `fetch`.
2. Allow `update` (or a `Ui` / `Cmd` helper) to flush a render *before* an RPC call, **or** let `Ui` re-render when `update` suspends on `fetch` (by triggering a microtask render before `fetch` awaits the network response)! That way setting `model.saving = true; Api.createTodo(...)` immediately patches the DOM with the loading state before the network request goes out.

---

### Smaller Points

- **Item 1 (`selfhost/llvm.fly` byte-offset GEPs and alignment):**
  When emitting `getelementptr i8, ptr %base, i64 %offset` followed by `load`/`store` in textual LLVM IR, always verify that the `load`/`store` instruction specifies the natural alignment of the field (or `align 1` for `@layout(packed)` structs, `§2.3`)! In LLVM, omitting `align` on `load`/`store` defaults to the ABI alignment of the loaded type, which will fault with `SIGBUS` / `movaps` unaligned access if the struct is `@layout(packed)`.
- **Item 5 (Per-route Wasm module size):**
  Since each route currently links its own copy of `runtime.c`, compiling with `-Wl,--gc-sections -O2` (or `-Oz` for Wasm) in `wasm.sh` strips unused runtime functions (sockets, filesystem, world simulator) from client route `.wasm` files and cuts the Wasm payload size by ~60–70% immediately without needing dynamic linking.
