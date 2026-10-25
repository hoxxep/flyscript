# Review: step15-fast-paths

- spec: 752b69902e84
- request: 18faeebd411917ea
- tokens: prompt 61947, cached 0, answer 6403

## Question

# Step 15's last item: fast paths that never reach the scheduler

Context: native runtime (`selfhost/runtime.c`, compiled into the program's C translation unit, or LTO-linked with LLVM IR), tasks are state machines; every runtime routine that may wait takes a `fly_wait` record (40 bytes: `step`, `n`, `a[2]`, `p[2]`) in the caller's frame, zeroed before the first call, and is called again with it to resume. `fly_ctx` is the per-worker context the running task uses (`fly_cx()`, a `const` function over a thread-local, computed once per call). Workers: per-worker ring (tokio-style), shared inject queue, a per-worker `next` slot for the task the running one woke (Go's runnext), searchers capped at half the workers.

## Measurements that motivate it

20M uncontended `m.lock((v) => { v += 1; })` in one task: Rust `std::sync::Mutex` 90 ms; ours 130–160 ms (LLVM / C). Profile (LLVM build): the scheduling point `mt_point_as` (out of line) plus `_tlv_get_addr` for the thread-locals it reads (`running`, `this_worker`) is ~33% of samples; the catch point `fly_try` around the body (for poisoning) ~12% — in C it is a `setjmp` per lock. The lock itself is now the runtime's 3-state futex word (one CAS, one exchange).

## Design

1. **The scheduling point is inline.** `fly_ctx` gains `uint32_t budget` (owner-only countdown) and `uint8_t attn` (set by other threads, relaxed store, after they publish what they want noticed). `fly_point(w)` becomes a `static inline` in `runtime.h`:
   `if (--cx->budget != 0 && !atomic_load_relaxed(&cx->attn) && w->step == 0) return; fly_point_slow(w);`
   The slow path clears `attn` *before* re-reading the conditions (so a set racing with it is never lost), adds what the countdown consumed to the worker's point count, and does today's work: deliver a cancellation; yield if the inbox (tasks woken from other threads) is non-empty, or if 64 points have passed and the ring or `next` holds work; re-arm the countdown. Who sets `attn` on worker W's run context: `inbox_push` to W, and `cancel(t)` (store the flag, then read `t->home`, then set its `attn`; `run_task` stores `home` then reads the flag, both seq_cst, so one of them sees the other). `run_task` arms `budget = 64` and `attn = is_cancelled(t)`. Contexts that are not a worker's task context (the program's thread under the simulated world, workers' idle contexts, single-threaded builds) keep `attn = 1` permanently, so they always take today's path and the simulated world's determinism is untouched.
   Waking into `next` lowers the countdown to at most 4, so that the slow path, reached when it runs out, moves a `next` the waker has gone on past into the ring for others.

2. **`Mutex.lock` is the point plus a CAS.** `fly_lock(w, m)` replaces `fly_point(w); fly_lock(m)`: inline, `if (point fast && CAS(word, 0, 1)) return;` else `fly_lock_slow(w, m)`, a waiting routine: the point's slow work, then spin ~100 relaxes trying, then **park the task** (§6.2: "a task that finds it held waits without its core, woken in turn"), not the thread. Waiters are kept in a global table of wait queues hashed by the lock word's address (WebKit's ParkingLot / Rust `parking_lot`), so a `Mutex`'s header stays one word plus its poison byte (16 bytes, for the state's alignment). Protocol (Drepper mutex 2 with tasks instead of futex): under the bucket lock, `xchg(word, 2)`; 0 → acquired; else enqueue (address, task) FIFO and suspend. `unlock`: inline `if (xchg(word, 0) == 2) fly_unlock_slow(m)`, which under the bucket lock wakes the first waiter for that address. A woken waiter retries with `xchg(word, 2)` (so later waiters' wakes are not lost). Waiters are woken in FIFO order; a running task may barge ahead of a woken one (no handoff), which keeps throughput under contention and does not convoy; starvation is bounded in practice by the body being effect-free and short. Unlock is inline in every build: a word never set is 0.

3. **Poisoning by a cleanup, not a catch.** Both back ends already unwind with the platform unwinder over `-fexceptions` C whose cleanups are `__attribute__((cleanup))` (LLVM: landing pads). The lock site becomes `{ guard g __attribute__((cleanup(lock_guard_end))) = { m, &f }; fly_lock(...); r = body(...); g.done = 1; }` where the cleanup poisons if `!done`, unlocks, and drops the closure. The panic is never taken up and re-raised; it just passes through, as through any frame with cleanups. Zero cost on the normal path, no `setjmp` in C.

4. **Receives, sends, buffered reads.** After (1), a channel receive with a message waiting is the inline point, a lookup of the channel's record, its monitor lock and the take: no scheduler, no suspension. A buffered read with bytes waiting is already ordinary code (`File.fill` returns at once). I plan to measure these after (1)–(3) rather than make the channel lock-free now.

## Questions

- Is the attention-flag protocol sound as described (in particular cancellation racing with migration, and the clear-before-check order)? Anything cheaper or simpler for the fast check?
- Parking-lot table vs a wait queue in each mutex's header: any reason to prefer the per-mutex queue here (header 48 → 16 bytes is the gain)?
- Barging vs FIFO handoff for "woken in turn": is barging an acceptable reading of the spec's wording, or should the spec say "woken in the order they began to wait, and a running task may take it first"?
- Cleanup-based poisoning: any semantic difference from catch-and-rethrow I am missing (uncaught-panic detection at raise time, panics in the closure's drop during unwinding)?

## Answer

### Verdicts

- **1. Inline scheduling point (`budget` + `attn`):** **Agree with changes.** You can cut the fast check from **two** loads (`budget` and `attn`) to **one** (`if (UNLIKELY(--cx->budget <= 0))`) by folding `attn` into a signed `int32_t budget`, and the cancellation-vs-migration race has one gap when a task exits and re-enters `run_task` unless `t->home` is cleared or checked with a fence.
- **2. `Mutex.lock` inline fast path + task-parking slow path:** **Disagree with the ParkingLot hash table when the mutex word itself can be the wait-queue head (at the exact same 16-byte header size), and fix two bugs in the Drepper-2-for-tasks protocol (lost wakeups on barge + unlinking on task cancellation).**
- **3. Barging vs. FIFO handoff for `§6.2` ("woken in turn"):** **Agree with barging + eventual fairness**; the current spec wording (`"woken in turn"`) already describes waking order, not strict handoff, so no spec change is needed.
- **4. Cleanup-based poisoning instead of `fly_try` (`setjmp`):** **Agree with changes.** Two semantic edge cases in `lock_guard_end` must be distinguished: **(a) `fly_lock` itself unwinding on task cancellation before acquiring the lock** (must **not** poison or unlock!), and **(b) the body returning vs. unwinding via `fly_unwinding` flag when a parent frame catches panics by flag (`fly_panic_flag`)**.
- **5. Channel & buffered I/O fast paths:** **Agree** — measure after (1)–(3); only inline the `fly_wait` zeroing on the fast path so you don't pay a 40-byte store before an uncontended lock or ready channel receive.

---

### Problems

#### 1. [Mutex Protocol Bug] Drepper's "Mutex 2" (`0/1/2` + Global Hash Table) Loses Wakeups on Barge and Orphans Cancelled Tasks (`§6.1`, `§6.2`)

Look closely at the lock/unlock protocol you proposed in (2):
> *"Protocol (Drepper mutex 2 with tasks instead of futex): under the bucket lock, `xchg(word, 2)`; 0 → acquired; else enqueue (address, task) FIFO and suspend. `unlock`: inline `if (xchg(word, 0) == 2) fly_unlock_slow(m)`, which under the bucket lock wakes the first waiter for that address. A woken waiter retries with `xchg(word, 2)` (so later waiters' wakes are not lost)."*

There are **two bugs** in applying Drepper's futex-based Mutex 2 directly to user-space tasks, plus a simpler design that needs no global hash table at all:

##### Bug 1A: Lost wakeup when a running task barges via the fast-path `CAS(0, 1)`
Trace three tasks $A$, $B$, $C$ on mutex $m$:
1. $A$ holds $m$. $B$ and $C$ both contend, take the slow path, set `m->word = 2`, and enqueue `[B, C]` in the bucket queue.
2. $A$ unlocks: `xchg(&m->word, 0)` returns `2`. $A$ calls `fly_unlock_slow(m)`, which pops $B$ from the bucket queue and wakes $B$ (putting $B$ in a worker's `next`/ring). Note that `m->word` is now **`0`**, and $C$ is still sleeping in the bucket queue!
3. **Before $B$ runs**, a running task $D$ on another core executes the inline fast path of `fly_lock`:
   ```c
   CAS(&m->word, 0, 1) // SUCCEEDS! m->word is now 1!
   ```
4. While $D$ holds the lock (`m->word == 1`), $B$ finally gets scheduled and runs its retry:
   > *"A woken waiter retries with `xchg(word, 2)`"*
   $B$ sees that `xchg(&m->word, 2)` returns `1` (held by $D$), so $B$ re-enqueues itself in the bucket queue `[C, B]`. (Or worse: if $D$ unlocks **before** $B$ runs!).
   Look at what happens if $D$ unlocks **before** $B$ runs:
   - $D$ acquired with `CAS(0, 1)`, so `m->word == 1`.
   - $D$ finishes its 5-ns body and runs `unlock`: `xchg(&m->word, 0)` returns **`1` (not `2`!)**, so $D$ does **not** call `fly_unlock_slow`!
   - Now $B$ runs, acquires the lock... Wait: how does $B$ acquire the lock on retry?
     If $B$ retries with `xchg(&m->word, 2)` when $B$ wakes, then even when **$C$ is NOT in the queue** (i.e. $B$ was the *only* waiter), $B$ sets `m->word = 2` and forces $B$'s own unlock to take `fly_unlock_slow(m)` every single time!
     Conversely, if $B$ retries with `CAS(0, 1)`, then when $C$ *is* in the queue, $B$'s unlock sees `xchg == 1` and **never wakes $C$** ($C$ deadlocks forever)!

##### Bug 1B: Task cancellation while parked on a `Mutex` (`§6.1`)
Look at `§6.1`:
> *"If a forked task fails, the scope is cancelled: the body and every other task stop at their next `Io` operation and unwind"*
And `Mutex.lock` has signature `uses Io` (`§6.2`)!
When task $B$ is parked in the mutex's wait queue and $B$'s scope is cancelled (or `task.cancel()` is called on $B$), the scheduler wakes $B$ to unwind from `fly_lock_slow`.
- If $B$ is still linked into the mutex's wait queue when $B$ unwinds, and then $A$ calls `fly_unlock_slow(m)` and pops $B$, $A$ will **wake a dead/unwound task $B$** instead of waking the next live waiter $C$!
- Worse: if the queue node was allocated in $B$'s `fly_wait` record inside $B$'s frame, and $B$ unwinds and frees its frame while the node is still in the bucket queue, `fly_unlock_slow(m)` will **use-after-free $B$'s frame**!

##### Why use a global ParkingLot hash table at all when `m->word` itself is 64 bits?
You noted:
> *"Waiters are kept in a global table of wait queues hashed by the lock word's address ... so a `Mutex`'s header stays one word plus its poison byte (16 bytes, for the state's alignment)."*

Wait: a `Mutex` header is **already 16 bytes** (`uintptr_t word` = 8 bytes + `uint8_t poisoned` + 7 bytes padding = 16 bytes)!
In 16 bytes, you don't need a global hash table of buckets at all:
- Either `m->word` (`uintptr_t`) **is** the state + pointer to the waiter queue head (`0` = unlocked, `1` = locked with no waiters, `(uintptr_t)waiter_node | 1` = locked with wait stack/queue, using the remaining 7 bytes of the 16-byte header for a 1-byte spinlock `m->qlock` and `m->poisoned`!), **OR**
- Even simpler: look at the 16-byte header of `Mutex`:
  ```c
  struct fly_mutex_hdr {
    _Atomic uint32_t state;   // 0 = unlocked, 1 = locked, 2 = locked with waiters
    _Atomic uint8_t  qlock;   // spinlock protecting head/tail
    uint8_t          poisoned;
    uint16_t         _pad;
    fly_wait*        head;    // 8 bytes: intrusive doubly-linked circular list in fly_wait!
  }; // Total: 4 + 1 + 1 + 2 + 8 = 16 bytes!
  ```
Look at `struct fly_mutex_hdr` above:
- **It is 16 bytes total!** (`4 + 1 + 1 + 2 + 8 = 16 bytes` — zero extra memory over your `(word, poisoned)` header!)
- Each waiting task already has a 40-byte `fly_wait` record (`step`, `n`, `a[2]`, `p[2]`) in its frame, where `p[0]` (`next`) and `p[1]` (`prev`) form an intrusive doubly-linked list rooted at `m->head`!
- Because the queue is per-mutex (inside the same 16-byte header) and protected by `m->qlock`:
  1. **No global hash table, no false sharing between unrelated mutexes.**
  2. **Clean cancellation:** If a waiting task is woken by `cancel()`, it resumes at `step == 1` in `fly_lock_slow`: if it was not woken by `unlock` (e.g. `w->n == 0`), it acquires `m->qlock`, unlinks `w` from `m->head` in $O(1)$, and returns unwinding!
  3. **No lost wakeups on barge:** Under `m->qlock`, when `fly_unlock_slow` pops a waiter `w`, it checks if `m->head` is still non-empty; when the woken waiter `w` resumes and acquires the lock, if `m->head != NULL`, it sets `m->state = 2` (or `unlock` sets `m->state = (m->head != NULL) ? 2 : 0` when releasing `m->qlock`!).
     Specifically:
     - Fast lock: `CAS(&m->state, 0, 1)`.
     - Slow lock: under `m->qlock`, loop trying `CAS(&m->state, 0, (m->head ? 2 : 1))` or if `m->state == 1`, set `m->state = 2`, enqueue `w`, and suspend. When woken (`w->n == 1`, meaning `unlock` handed wake rights to `w` or woke `w`), acquire `m->qlock`: if `m->state == 0`, set `m->state = (m->head != NULL) ? 2 : 1` and return! If a barger took it (`m->state != 0`), ensure `m->state = 2` and re-enqueue at the **front** of `m->head`!
     - Look how clean that is: if a running task barges between `unlock` and `w` waking up, `w` sees `m->state != 0` under `m->qlock`, forces `m->state = 2` (so the barger's unlock is **guaranteed** to call `fly_unlock_slow`!), and puts `w` back at the **head** of `m->head` so `w` doesn't lose its FIFO turn!

---

#### 2. [Attention Flag + Budget] Folding `attn` into `int32_t budget` and Closing the Cancellation Race (`§6.1`)

In (1), you wrote:
> ```c
> if (--cx->budget != 0 && !atomic_load_relaxed(&cx->attn) && w->step == 0) return;
> fly_point_slow(w);
> ```
> *"Who sets `attn` on worker W's run context: `inbox_push` to W, and `cancel(t)` (store the flag, then read `t->home`, then set its `attn`; `run_task` stores `home` then reads the flag, both seq_cst, so one of them sees the other)."*

Two points here:

##### 2A. Check the race when task `t1` suspends on worker `W` and `W` immediately starts `t2`
Trace this interleaving between Worker `W` and Canceller `C` (cancelling `t1`):
1. `t1` was running on `W`, so `t1->home == W`. `t1` parks on a channel or yields, and `W` picks up `t2` in `run_task(W, t2)`.
2. In `run_task(W, t2)`: `W` sets `cx->budget = 64` and `cx->attn = is_cancelled(t2)` (which is `0`).
3. Concurrently, `C` cancels `t1`: `C` sets `t1->cancelled = 1`, reads `t1->home` (which is still `W` if `t1` hasn't cleared `home`, or loaded just before `t1` parked), and sets `W->cx.attn = 1`.
   - That part is harmless (it just causes `t2` to take one extra slow path).
4. **Now consider the reverse race:**
   - `C` calls `cancel(t2)` while `t2` is in `W`'s local ring (not running yet).
   - What is `t2->home` while `t2` is sitting in `W`'s ring or stolen by `W2`?
   - If `t2->home` was `W1` (where `t2` last ran), `C` writes `t2->cancelled = 1`, `seq_cst`, reads `t2->home == W1`, and sets `W1->cx.attn = 1`.
   - Meanwhile, `W2` steals `t2` and starts `run_task(W2, t2)`:
     If `run_task(W2, t2)` does:
     ```c
     atomic_store_explicit(&t2->home, W2, memory_order_seq_cst);
     uint8_t c = is_cancelled(t2); // MUST load t2->cancelled AND t2->scope->cancelled with seq_cst/acquire AFTER storing t2->home!
     atomic_store_explicit(&cx->attn, c, memory_order_relaxed);
     ```
     **Check `scope_cancel` too!**
     In `§6.1`, a task can be cancelled in **two** ways:
     1. `task.cancel()` (which sets `t->cancelled = 1` on a single task).
     2. `scope_cancel(scope)` (when a sibling `fork` fails or panics, or a parent scope cancels).
     If `scope_cancel(scope)` sets `scope->cancelled = 1`, which worker's `cx->attn` does `scope_cancel` set?
     It doesn't know which workers are currently running tasks of `scope` unless it sets **`w->cx.attn = 1` on ALL workers `w`**!
     Setting `w->cx.attn = 1` on all `N` workers in `scope_cancel` (which only runs when a scope fails/panics) is a loop over ~8–32 workers doing a relaxed byte store — practically free, and guarantees that **every** running task in `scope` on **every** core notices `scope->cancelled` at its very next `fly_point` instead of waiting up to 64 points!

##### 2B. Make the fast path a single test by separating `fly_point()` from `fly_wait`
Look at your fast check:
```c
if (--cx->budget != 0 && !atomic_load_relaxed(&cx->attn) && w->step == 0) return;
```
Notice:
1. For `Mutex.lock` (`fly_lock`) on the uncontended fast path, if `fly_lock` doesn't suspend, **it never uses the 40-byte `fly_wait` record `w` at all!**
   Yet right now, the compiler zeroes the 40-byte `fly_wait` record in the frame *before* calling `fly_lock(w, m)`, and then `fly_point(w)` reads `w->step == 0`!
   Wait: why would `fly_lock(w, m)` be called again with `w->step != 0` on the fast path?
   Only when `fly_lock_slow` previously suspended (`w->step != 0`)!
   If `w->step` is only zeroed as `w->step = 0` (a single 4-byte store instead of zeroing all 40 bytes of `fly_wait` before the call!) or if `fly_lock` checks `w->step == 0` first, you save 36 bytes of dead stores on every uncontended `Mutex.lock`!
2. Even better, why check both `--cx->budget != 0` AND `!atomic_load_relaxed(&cx->attn)` when `cx->attn` can just be the sign bit of `cx->budget` (or `atomic_store_relaxed(&cx->budget, 0)`), OR keep `budget` and `attn` adjacent in a union if you don't want an atomic RMW on `budget`? Keeping `budget` non-atomic (`--cx->budget`) and `attn` as a separate `uint8_t` in the same cache line is fine (on ARM64/x86, a relaxed `ldrb` from L1 takes 1 cycle and fuses/dual-issues with the decrement), **as long as `cx->attn` is only written by other threads when an event actually happens** (so the cache line stays in Shared/Exclusive state in `W`'s L1 cache).

---

#### 3. [Cleanup-Based Poisoning] Two Edge Cases in `lock_guard_end` (`§5.7`, `§6.2`)

In (3), you proposed:
> *"The lock site becomes `{ guard g __attribute__((cleanup(lock_guard_end))) = { m, &f }; fly_lock(...); r = body(...); g.done = 1; }` where the cleanup poisons if `!done`, unlocks, and drops the closure. The panic is never taken up and re-raised; it just passes through, as through any frame with cleanups."*

Check **four** things that happen in that snippet:

##### 3A. What if `fly_lock(...)` itself unwinds because the task was cancelled while waiting for the mutex?
Look at the order in your snippet:
```c
guard g __attribute__((cleanup(lock_guard_end))) = { m, &f };
fly_lock(...);
r = body(...);
g.done = 1;
```
`fly_lock` is an `Io` scheduling point (`§6.1`, `§6.2`). If the task is **cancelled** before or while waiting in `fly_lock_slow`, `fly_lock` unwinds the task **without having acquired the mutex `m`**!
If `g` was already armed with `m` before `fly_lock` acquired the lock, `lock_guard_end` will run during cancellation unwinding and **poison and unlock a mutex that this task does NOT hold**!
- **Fix:** Either initialize `g.m = NULL` and set `g.m = m` **inside `fly_lock` after acquiring** (or immediately after `fly_lock` returns when `!fly_pending`), and in `lock_guard_end`:
  ```c
  if (g->f) drop_closure(g->f); // always drop the closure if not yet consumed
  if (g->m && !g->done) {
    fly_mutex_poison(g->m);
    fly_unlock(g->m);
  }
  ```
- **And what if `fly_lock` returns with `fly_pending == 1` (the task suspended because the mutex is contended)?**
  Wait! Read that again!
  In a state-machine function `F`, when `fly_lock_slow` **suspends** (`fly_pending = 1`), **`F` executes `return (R){ 0 };` to return to the worker loop!**
  In C, executing `return` from a block with `__attribute__((cleanup(lock_guard_end)))` **runs `lock_guard_end` when `F` returns `fly_pending`!**
  Let's trace that!
  ```ts
  export function worker(m: readonly Mutex<i64>): void uses Io {
    m.lock((v) => { v += 1; });
  }
  ```
  If `worker` is a state machine (because `m.lock` can suspend!) and uses `__attribute__((cleanup(lock_guard_end)))` around `fly_lock` + `body`:
  1. `fly_lock` finds `m` contended, sets `fly_pending = 1`, and returns to `worker`.
  2. `worker` sees `if (fly_pending) { fr->state = 1; return; }`.
  3. Because `worker` returns from C while inside the scope of `guard g __attribute__((cleanup))`, **C runs `lock_guard_end(&g)` on suspension!**
  4. And when `worker` is resumed (`goto resume1;`), it jumps **into** the scope of `g` without re-initializing `g`!

Look why that happens:
- `body(...)` in `Mutex.lock` is **pure / effect-free** (`§6.2`: *"a body that performs no effects"*), so `body(...)` itself can **never** suspend (`fly_pending` is impossible inside `body`)!
- Only `fly_lock` can suspend!
- Therefore, the `cleanup(lock_guard_end)` guard **must start AFTER the `resume1:` label of `fly_lock` (after `fly_lock` has finished waiting and acquired the mutex)**, in an inner block `{ guard g __attribute__((cleanup(...))) = { m }; r = body(...); g.done = 1; fly_unlock(m); }` that contains **zero suspension points**!
- Wait: what if `fly_lock` unwinds due to cancellation while waiting, before `body` ever starts? Then the closure `f` (which was moved into the frame before `fly_lock`) is dropped by the frame's normal block cleanup, and the mutex `m` was never acquired so it needs neither poisoning nor unlocking!
- Putting the `__attribute__((cleanup))` guard in an inner block **strictly around `body(...)` (after `fly_lock`'s `done1:` label)** means:
  1. `fly_lock` suspending (`fly_pending`) is **outside** the guard block, so `return` on `fly_pending` never triggers `lock_guard_end` and `goto resume1` never jumps into the guard's scope!
  2. By the time the guard block is entered, `m` is **already acquired**, and `body` cannot suspend (`fly_pending` is impossible inside the guard block)!

##### 3B. What if the enclosing function catches panics by flag (`setjmp` in C for a machine with a suspending `defer`)?
Check how your Phase B panic machinery interacts with `__attribute__((cleanup))` in the C back end:
- In Phase B: *"Through C the catch is a `setjmp` record the machine keeps as it starts ... the machine's own landing code does nothing when the panic is to be taken up by its record"*.
-Wait: in C, does `fly_panic` unwind using `_Unwind_RaiseException` (which runs `__attribute__((cleanup))`) or `longjmp` (which skips `__attribute__((cleanup))` unless registered in the machine's own block table)?
- If a machine with a suspending `defer` uses `setjmp`/`longjmp` in the C back end, `longjmp` jumps to the `setjmp` buffer at the top of the machine **without running C `__attribute__((cleanup))` handlers** inside that machine!
- Check your C back end: if `fly_panic` always uses `_Unwind_RaiseException` (or C++ exceptions) and only converts to `fly_panic_flag` at a catch boundary *above* the frame, then `__attribute__((cleanup))` runs. **If** `fly_panic` uses `longjmp` to the enclosing machine's `setjmp` record when `m.lock(...)` is inlined into a machine that has a suspending `defer`, then `longjmp` would **skip** `__attribute__((cleanup(lock_guard_end)))` and leave the mutex locked and unpoisoned!
- **Fix:** Either make `lock_guard_end` a normal block cleanup entry in the compiler's IR (or put the `guard` in a tiny non-machine helper function `fly_lock_run`, or ensure `setjmp` is only outside the helper). Since `body` cannot suspend, wrapping `r = body(...);` or registering the mutex unlock/poison in the block's IR cleanup list works uniformly for both `_Unwind_RaiseException` and `setjmp`/LLVM landing pads!

##### 3C. What if dropping the `once` closure `f` panics?
- By `§5.6` and `§5.7`, a closure's drop is a destructor of its captured values, and a panic out of a destructor (or during panic unwinding) aborts the program (`§5.7`: *"A panic in cleanup that is running because of a panic ... ends the program at once. So does a panic that escapes a destructor"*).
- Still, in `lock_guard_end` (and on the normal exit path), **always unlock `m` (and set `poisoned = 1` on unwind) BEFORE dropping `f`'s captures**, or drop `f` inside `body` when `f` is called (`once` closures consume their captures when called, so after `body` runs normally, `f` has already been consumed!). Only if `fly_lock` fails by cancellation *before* `body` is called does `f` need to be dropped uncalled.

---

### Summary of Recommended Changes

1. **Per-mutex wait list inside the existing 16-byte `Mutex` header (instead of a global ParkingLot table):**
   - `uint32_t state` (`0/1/2`) + `uint8_t qlock` + `uint8_t poisoned` + `uint16_t pad` + `fly_wait* head` = **16 bytes**.
   - Use `fly_wait`'s existing `p[0]/p[1]` pointers for an intrusive doubly-linked list so a cancelled waiter can unlink itself in $O(1)$ under `m->qlock`, and re-queue a woken waiter at the **head** of `m->head` with `m->state = 2` if a running task barged ahead of it.
2. **Place the poison/unlock cleanup guard strictly around `body(...)`, AFTER `fly_lock`'s resume label:**
   - Never let `fly_lock`'s `if (fly_pending) return;` exit through the poison/unlock `__attribute__((cleanup))` scope, and ensure `setjmp`-based machines in the C back end cannot `longjmp` past the unlock/poison cleanup.
3. **In `scope_cancel(scope)`, set `w->cx.attn = 1` on all workers:**
   - Ensures tasks in the cancelled scope running on other cores hit `fly_point_slow` on their very next point rather than up to 64 points later.
4. **Only zero `w->step = 0` (4 bytes) instead of `memset(w, 0, 40)` before `fly_lock` / fast-path `Io` calls:**
   - Initialize the rest of `fly_wait` inside the slow path when a call actually suspends.
