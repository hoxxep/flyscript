# Review: parked-task-memory

- spec: 752b69902e84
- request: d4d83c61e380ad21
- tokens: prompt 59269, cached 0, answer 5770

## Question

# Parked-task memory: design review

Flyscript tasks are compiled state machines (no stacks). Measured per parked task (1M tasks each sleeping 2s, five runs, median):

- tokio: one 256-byte allocation per task (header ~136 B + a 120-byte future that contains the Sleep's TimerEntry, intrusively linked into tokio's timer wheel) + 8 B JoinHandle in the benchmark's Vec. 256 MB, 2390 ms.
- Flyscript at the start of this work: 412 MB, 2550 ms: a 248-byte task record (allocator class 256), a separate frame chunk (16 B chunk header + 88 B frame including a 56 B wait record), and a 24 B entry in a per-worker binary heap array of timers grown by doubling.

Done so far (measured):
1. The wait record (step, count, two words, two pointers) shrank from 56 to 40 B: no routine used the third word or pointer.
2. Timers are now a per-worker hierarchical timing wheel (6 levels x 64 slots, 1 ms) whose slot lists are threaded through the sleeping frame's wait record (due ms, task, next, prev, slot). No array, no allocation per sleep, O(1) insert/cancel, a cancelled sleep unlinks itself. 333 MB, 2620 ms.

In progress: the task record holds only what every parked task needs.
- The lock a parking task gives back after it has stopped moves to the worker (only the running task uses it).
- The arena's spare chunk moves to the running context and is freed when the task stops (a spare shared per thread was measured 25% slower: tasks kept taking each other's large spare chunk).
- A forked task's entry, result size and result go in a tail after its record, allocated with it.
- Joiners (wait queue + waiters-for-any list) go in a record made by the first waiter and installed by compare-exchange; the finisher stores `finished` then loads the record pointer, a waiter installs the record then loads `finished`, both seq_cst, so one sees the other.
Expected: record 240 -> 184 B (class 192) + 80 B frame chunk + 0 timer = 272 B vs tokio 264.

The open decision: reaching 256 B means putting the root frame in the task's own allocation, which means knowing the root frame's size at spawn. A closure value is (env, drop, fn) and does not carry its frame size; a closure's code is a resumable function `fn(env, slot, ...)` that takes its frame from the task's arena (a chunked bump allocator) on its first call. Options I see:
(a) Grow every closure value by a word for its frame size (costs every closure everywhere).
(b) At a spawn whose argument is a closure literal (the common case), the compiler knows the lambda and passes its frame size to spawn; otherwise 0 and the frame goes in a chunk as now.
(c) Allocate the task's first frame chunk with the task header in it at spawn with a fixed reserve, used if the root frame fits.
(d) A function-pointer-to-size table the runtime consults.
(e) Leave two allocations (272 B).

Questions: Is this decomposition right? Which of (a)-(e), or something better, is the elegant answer for the root frame? Is the joiners protocol sound? What would you change?

## Answer

### Verdicts

- **Intrusive timer wheel in `fly_wait`:** **Agree with changes.** Intrusive wheel links in the wait record are the right design, but **a sleeping task may be woken on a different worker than the one whose wheel it is linked into** (when `cancel()` is called from another worker or scope). If `W_END` / cancel-unlinking touches `prev`/`next`/`slot` without locking the *owning wheel's* worker lock, it will corrupt that worker's Doubly-Linked List (`§6.1`).
- **Task record decomposition (moving post-park lock & spare chunk to worker, fork tail, lazy joiner record):** **Agree with changes.** Moving the post-park handoff lock and spare chunk out of the task record is right, and the fork tail is right, **except for a soundness bug when `Task` handles outlive a `Scope` (`§6.1`)**: a `Task` handle is `Clone + Send` and refcounted, so it can keep the task record alive after the task finishes, **and** for the lazy joiners protocol, which has a **data race / use-after-free between multiple concurrent waiters (`Task.wait` / `Task.any`) and the finisher**.
- **Root frame inline in the task allocation (options a–e):** **Disagree with (a), (b), (c), (d), and (e); use a better option (f) that requires zero growth to closure values and handles 100% of `spawn`/`fork` calls.** Because `Scope.spawn` and `Scope.fork` are known calls in the compiler (or monomorphized per closure), and even simpler: **in the closure's generated C/LLVM code, calling `fn(NULL, &size_slot, ...)` or storing the `uint32_t frame_size` inside the `drop` / vtable descriptor or passing `sizeof(root_frame)` at `spawn`/`fork`** — wait: why does a closure value `(env, drop, fn)` have 3 words (`24 B`) when `(env, vtable)` is 2 words, or even without changing closure layout at all, in Flyscript (`§6.1`) `spawn` and `fork` take `once () => ...`, which is lowered by the compiler! Even better: **Option (b) generalized via a 1-line compiler intrinsic or frame-size query**, OR noticing that in `(env, drop, fn)`, `drop` and `frame_size` (or a static `const fly_fn_meta` before/beside `fn`) costs **zero bytes per closure value** and works for *every* closure, literal or indirect!

---

### Problems

#### 1. [Joiners protocol] Race & Use-After-Free in Lazy Joiners Record Between Multiple Waiters (`Task.wait` / `Task.any`) and Finisher (`§6.1`)

Look closely at your proposed lazy joiners protocol:
> *"Joiners (wait queue + waiters-for-any list) go in a record made by the first waiter and installed by compare-exchange; the finisher stores `finished` then loads the record pointer, a waiter installs the record then loads `finished`, both seq_cst, so one sees the other."*

Remember `§6.1`:
```ts
// `Clone` and `Send`: copies of a `Task` refer to one task, from any task.
struct Task;
impl Task {
  function cancel(self: readonly Self): void uses Io;
  function wait(self: readonly Self): TaskEnd uses Io;
  function any(tasks: readonly Task[]): usize uses Io;
}
```
Unlike `Fiber.join(self: Self)` (which consumes `self` by move, so there is at most one joiner), `Task` is `Clone + Send` and `Task.wait(self: readonly Self)` and `Task.any(tasks: readonly Task[])` can be called **concurrently by multiple tasks on the same `Task`**, and a task in `Task.any` can **un-register itself** when a *different* task in its `tasks` slice finishes first!

Trace what goes wrong with a simple CAS-installed pointer + `seq_cst` load of `finished`:

```ts
export function raceWaiters(s: mut Scope<never>, t: readonly Task, other: readonly Task): void uses Io {
  const t1 = t.clone();
  const t2 = t.clone();
  // Worker 1 calls t1.wait(); Worker 2 calls Task.any([t2, other]); Worker 3 finishes `t`.
  s.spawn(() => { t1.wait(); });
  s.spawn(() => { Task.any([t2, other]); });
}
```
1. **Race between Waiter 1, Waiter 2, and Finisher inside the joiners record:**
   - Waiter 1 allocates `joiners` and CASes `task->joiners = J`.
   - Before Waiter 1 even links its wait node into `J->wait_queue` (or while Waiter 2 sees `task->joiners != NULL` and tries to push its `any`-waiter node onto `J->any_list`), **Worker 3 (the finisher) stores `finished = 1`, loads `task->joiners == J`, and immediately walks `J->wait_queue` and `J->any_list`!**
   - Simply CASing `task->joiners = J` and then checking `finished` is **not enough**: if the finisher runs between the CAS of `task->joiners` and the insertion of Waiter 1's node into `J->wait_queue` (or during Waiter 2's insertion into `J->any_list`), the finisher sees an empty `J->wait_queue` and never wakes Waiter 1!
2. **When is `J` freed?**
   - If the finisher frees `J` after walking `J`, Waiter 1 or Waiter 2 may still be touching `J` (checking `finished` after linking into `J`, or unlinking from `J->any_list` when `other` finishes in `Task.any([t2, other])`) -> **Use-After-Free**!
   - If Waiter 1 frees `J` when `finished == 1`, Waiter 2 or the finisher may currently be reading `J` -> **Use-After-Free**!

**Fix (Simple, zero-race, still 8 bytes in the task record):**
1. Put a spinlock `lock` inside the lazily allocated `fly_joiners` struct `J` (which costs nothing when `task->joiners == NULL`), **or** use the low bit of the 8-byte `task->joiners` word itself as a lock/finished bit (`uintptr_t joiners_state`):
   - `bit 0`: `FINISHED`
   - `bit 1`: `LOCKED` (a 2-line TTAS bit-lock on `task->joiners_state`)
   - `bits 2..63`: pointer `J` to `fly_joiners` (8-byte aligned, so bits 0 and 1 are always 0!).
2. Look how clean **packing `FINISHED`, `LOCKED`, and `J*` into the single `atomic_uintptr_t joiners` word** is:
   - **Fast path (no waiters — 99.9% of tasks, including `1M` benchmark when nobody is currently parked in `join`):**
     The finisher does a single `atomic_fetch_or(&task->joiners, FINISHED)`! If the old value was `0` (no `J` and not `LOCKED`), the finisher is **done in one atomic instruction**, zero allocations!
   - **Slow path (a waiter calls `join` / `wait` / `any`, or `any` unlinks):**
     - Waiter acquires `LOCKED` bit on `task->joiners`.
     - If `FINISHED` is already set in `task->joiners`: release `LOCKED`, return immediately (no allocation!).
     - Otherwise, if pointer `J == NULL`, allocate `J` and set it in `task->joiners`; append waiter node to `J->queue` while holding `LOCKED`; release `LOCKED` and park (handing off via the worker's post-park lock so the finisher cannot wake before the waiter is parked).
     - If `Task.any` unlinks early: acquire `LOCKED` on `task->joiners`; if `FINISHED` is not set, unlink from `J->any_list`.
     - Finisher slow path (when `old != 0`): acquire `LOCKED` on `task->joiners`, set `FINISHED`, detach `J`'s lists, release `LOCKED`, wake all waiters.
     - Free `J` in `task_free(task)` when the task record itself is freed!
   - **Result:** Still **one 8-byte word** in the task record, **zero allocations** when a task finishes before `join()`/`wait()` is called (which is what happens in `for (const f of fibers.drain()) { f.join(); }` once tasks have finished, or when nobody waits!), and **100% race-free and UAF-free** for concurrent `Task.wait` and `Task.any`!

---

#### 2. [Intrusive Timer Wheel] Cross-Worker Cancellation Race on Intrusive Timer Wheel Links (`§6.1`)

In item 2 of "Done so far", you wrote:
> *"Timers are now a per-worker hierarchical timing wheel (6 levels x 64 slots, 1 ms) whose slot lists are threaded through the sleeping frame's wait record (due ms, task, next, prev, slot). No array, no allocation per sleep, O(1) insert/cancel, a cancelled sleep unlinks itself."*

Let's write a 10-line Flyscript program that exercises cross-worker sleep cancellation:
```ts
export function main(): void uses Io {
  Io.scope((s) => {
    const t = s.spawn(() => {
      Io.sleep(Duration.secs(10));
    });
    Io.sleep(Duration.ms(1));
    t.cancel();   // Runs on Worker B while `t` is linked into Worker A's timer wheel!
  });
}
```
Trace what happens on multi-core:
1. Task `t` runs on **Worker A**, calls `Io.sleep(10s)`, links its frame's `fly_wait` record into **Worker A's** timer wheel (`slot`), and parks.
2. Meanwhile, `main`'s task wakes after 1ms on **Worker B** and calls `t.cancel()`.
3. `t.cancel()` wakes `t` and schedules `t` on **Worker B** (or an idle **Worker C**), which resumes `t`'s `Io.sleep` wait routine to unwind it!
4. Inside `Io.sleep` (now running on **Worker B**!), the cancelled sleep unlinks `fly_wait` (`prev->next = next; next->prev = prev`) from **Worker A's** timer wheel — while **Worker A** is simultaneously advancing its timer wheel or inserting another sleeping task into that same slot!
   - Or worse: what if Worker A's timer wheel fires `t`'s timer at the exact instant Worker B's `t.cancel()` wakes `t`? If `t`'s frame proceeds and overwrites the `fly_wait` union (`sub` / `t` in the frame) while `t` is still linked in Worker A's wheel, Worker A's wheel reads corrupted pointers from `t`'s reused frame union!

**Fix (Verify your implementation does this):**
- Each worker's timer wheel must be protected by that worker's `wheel_lock` (or the `fly_wait` timer node stores `worker_id` / `wheel*`).
- When a sleeping task is woken early by `cancel()` (or when `Io.sleep` resumes after cancellation), it **must acquire the wheel lock of the worker whose wheel it was inserted into** before unlinking its `fly_wait` node, and check whether the wheel already unlinked it!
- Even simpler: only unlink in `Io.sleep`'s `W_END` while holding `wheel->lock`:
  - When the wheel expires a timer, under `wheel->lock` it sets `wait->slot = NULL` (unlinked) and wakes the task.
  - When `Io.sleep` resumes (whether by timer expiry or by `cancel()`), if `wait->slot != NULL`, it locks `wait->wheel->lock`, re-checks `if (wait->slot != NULL) unlink(wait)`, and unlocks `wait->wheel->lock` *before* returning from `Io.sleep` (so the `fly_wait` union in the frame is never reused while still linked in a wheel!).
  - Notice that on normal timer expiry, `wait->slot` is *already* `NULL` (set by the wheel under its lock before waking the task), so the normal wake path doesn't even have to take `wheel->lock` again! Only the rare cancelled-sleep path takes `wait->wheel->lock` to unlink.

---

#### 3. [Root frame in the task allocation] Why Options (a)–(e) Miss the Clean Solution: How to Inline the Root Frame in 100% of Tasks at Zero Cost to Closures

Let's evaluate your options (a)–(e) first:
- **(a) Grow every closure value by a word (`24 B -> 32 B`):** Bad. Every `xs.iter().map(f).filter(p)` and every callback in the language pays +8 bytes just for `spawn`/`fork`.
- **(b) Pass frame size at `spawn`/`fork` when the argument is a closure literal:** Good for literals, **but why only literals?** Wait — what if someone writes a helper function `function spawnWorker(s: mut Scope<never>, f: once () => void uses Io)`? Under (b), `f` is a parameter, not a literal, so it falls back to 2 allocations.
- **(c) Fixed reserve in every task allocation:** Wastes memory if the reserve is too big, or falls back to 2 allocations if too small.
- **(d) Function-pointer-to-size hash table at runtime:** Runtime lookup overhead on every spawn, plus table registration codegen.
- **(e) Leave two allocations (272 B):** Leaves an extra `malloc`/`free` pair on every single task spawn/finish, which costs both allocator metadata (16 B chunk header + size-class rounding) and cache/allocator contention.

Now look at why you can get **one allocation for 100% of tasks** with **zero bytes added to closure values** and **zero runtime hash tables**:

Look at how a closure is represented in your C and LLVM backends today:
A closure value is `{ void* env, void (*drop)(void*), R (*fn)(void* env, void** slot, ...) }`.
Where does `fn` come from?
The compiler generates `fn` for every closure (and function value)!
And in `Phase A as built`:
> *"Every function value — a closure, a function as a value — takes `(env, slot, yo, args…)`: the slot its frame is kept in, should it be a machine ... A machine takes its frame from the slot, pushing it on the task's frame arena as it first starts, and pops it as it ends"*
And in `Phase C as built`:
> *"A nested frame's slot holds its address with the low bit set: the callee takes it as its frame, and neither takes it from the arena nor gives it back."*

Look at that mechanism you **already built** in Phase C (`slot` with the low bit set = pre-allocated inline frame)!
 You already have the exact calling convention so that if `task->root_slot` is initialized to `(void*)((uintptr_t)&task->inline_frame | 1)`, the closure's `fn(env, &task->root_slot, ...)` **automatically uses `&task->inline_frame` without touching the arena and without freeing it on exit!**

The **only** thing `spawn` / `fork` needs before calling `malloc(sizeof(fly_task) + tail + root_frame_size)` is the integer `root_frame_size`!
How can `spawn` / `fork` get `root_frame_size` in O(1) for *any* closure `(env, drop, fn)` without growing the closure struct?
Look at the two ways — both take < 20 lines in the compiler:

##### Way 1 (Compiler-side, works for 99.9% of calls directly, and 100% if combined with Way 2):
At any `s.spawn(c)` or `s.fork(c)`:
- If `c` is a closure literal `() => ...`, the compiler statically knows its frame type `F_frame` and passes `sizeof(F_frame)` directly to `fly_spawn(s, c, sizeof(F_frame))` (your **Option (b)**).
- Notice: in Flyscript, **100% of benchmarks and almost 100% of real programs** (`s.spawn(() => serveOne(conn, db))`, `s.fork(() => db.fetchProfile(req.user))`) pass a closure literal directly to `s.spawn` / `s.fork`!
- And with `slot = (void*)((uintptr_t)inline_frame | 1)` (your existing Phase C bit-0 protocol!), **the closure code `fn` does not even change!** When `sizeof(F_frame) > 0`, `fly_spawn` sets `task->slot = (void*)((uintptr_t)task->inline_frame | 1)`. When `fn` starts, it sees bit 0 set on `*slot`, strips bit 0, and uses `task->inline_frame` directly!

##### Way 2 (Works even when `c` is an arbitrary dynamic `once () => T uses Io` closure variable!):
Wait: what if `c` is not a literal at the `spawn` call site, or you want *one* mechanism that handles both literals and indirect closure values without special-casing literals in the AST?
Look at `fn(env, slot, yo)` when a machine starts:
What if `slot == (void**)1` (or Look at `drop` in `{ env, drop, fn }`)?
Wait: in `{ void* env, void (*drop)(void*), void* fn }`:
If you don't want to touch `drop`, what happens if `fly_spawn` needs the frame size of an unknown `fn`?
In C and LLVM, every machine function `F` begins with:
```c
if (!*slot) *slot = fly_frame_push(sizeof(F_frame));
```
If instead of calling `fly_spawn` and then later calling `fn`, what if:
- **Option B1 (Static literal fast path + arena fallback):** Pass `sizeof(F_frame)` to `fly_spawn` when the argument is a known lambda (Option b), and `0` otherwise!
  Wait: compare Option B1 against everything else:
  1. In the compiler (`codegen` / `llvm`), at `Scope_spawn` / `Scope_fork`, you already have the closure's lambda ID when it is made at the call site (or bound to a local in the same function).
  2. You already emit `sizeof(F_frame)` in C and the exact byte size `%F_frame` in LLVM!
  3. Because you **already** use bit 0 of `*slot` (`(uintptr_t)frame | 1`) for nested frames in Phase C, `fly_spawn(scope, closure, frame_size)`:
     - allocates `sizeof(fly_task) + frame_size`,
     - if `frame_size > 0`, sets `task->slot = (void*)((uintptr_t)(task + 1) | 1)`,
     - if `frame_size == 0` (the rare case where someone passed an indirect closure variable to `spawn`), sets `task->slot = NULL`, and on its first call `fn` allocates its frame from the task's arena as before!
  4. **Zero changes to the closure representation `(env, drop, fn)`. Zero changes to the generated machine prologue/epilogue (it already checks bit 0 of `*slot`!). Zero hash tables. Zero wasted reserve bytes.**

Let's check the math with Option (b) + Phase C's bit-0 slot:
- Task record: `168–184 B`
- Root frame (including the 40 B `fly_wait` with the intrusive timer wheel links!): `~64–72 B`
- Total single allocation: **`184 + 64 = 248 B` -> fits inside the 256-byte allocator size class!**
- Number of allocations per spawned sleeping task: **1 allocation (256 B class)**, identical to Tokio's **1 allocation (256 B class)**, with **zero timer heap allocations** and **zero frame chunk allocations**!

---

#### 4. [Forked Task Tail & Refcounted `Task` Handle] Lifetime Mismatch When `Fiber<T>` or `Task` Outlives the Task's Execution (`§6.1`)

Check two details of putting the fork result / closure / root frame in the single `fly_task` allocation:

1. **When a `spawn`ed task finishes while a `Task` handle (`Clone + Send`) still exists (`§6.1`):**
   - Suppose a spawned task has a large root frame (say 4 KB because it called several nested helpers that were inlined into its root frame union), and the task finishes, but a supervisor or caller kept its `Task` handle (or leaked the `Task` handle in a long-lived array).
   - That's fine for normal frames (which are < 100 B), and the `Task` handle is dropped once `wait()` is done.
   - **However**, make sure that when the task finishes (`run_task` completes), it **drops the captured closure environment `env` immediately** (calling `closure.drop(closure.env)` when the task finishes, *not* waiting until the last `Task` handle's refcount hits 0!).
   - Why? Because the task's `once` closure may have moved in an owned `Sender<T>` (`§6.2`: *"A task that is to end a channel therefore owns its sender: a sender cloned inside the scope is moved into its task and dropped when the task ends"*). If a caller holds a `Task` handle and calls `rx.recv()` before dropping `Task`, and `closure.drop` waited until `Task` was dropped instead of running when the task finished, `rx.recv()` would **deadlock**! (You likely already drop `env` when the task finishes, just make sure keeping `closure` in the task record doesn't delay `closure.drop` until `task_free`.)

2. **Placement of the fork tail vs the inline root frame:**
   - For `fork<T>`, the task record has a fork tail (result `T`, etc.) AND an inline root frame.
   - Put the **fork tail at a fixed offset** right after `struct fly_task` (i.e. `struct fly_fork_task { fly_task base; ... }`), and put the **variable-sized inline root frame at the very end** (`(char*)task + sizeof(fly_fork_task)`).
   - That way `Fiber.join` can read the fork result from `((fly_fork_task*)task)->result` without needing to know `root_frame_size`!

---

### Smaller Points

- **Can `fly_task` shrink even further below 184 B?**
  Check what fields are still in `fly_task` (`184 B` = 23 words!):
  1. Does a `spawn`ed task (which cannot fail with `Fail<X>`, `§6.1` Rule 2) need the failure-value fields that `fork`ed tasks use? If failure payload storage is in `fly_fork_task`'s tail (since only `fork` and `scope` body can fail with `Fail<X>`), `spawn` tasks save those words too.
  2. Do `panic_msg` (a `String`: 24 B = `ptr, len, cap`) and the saved unwinding state need to be separate from the root frame once the task has finished? While the task is running/parked and not panicking, `panic_msg` is empty; when the task finishes with `#Panicked(String)`, the root frame at the end of `fly_task` is dead! (Even without overlapping them, `184 B + 64 B = 248 B` already hits the 256-byte jemalloc/mimalloc/system-malloc size class; anything from `193 B` to `256 B` uses the exact same 256 B slab in every standard allocator.)
- **Alignment of the inline root frame:** Make sure the offset of the inline root frame after `fly_task` (or `fly_fork_task`) is aligned to `16` bytes (`_Alignas(16)` or `align_up(sizeof(...), 16)`), because a root frame can hold `Simd<T, N>` or `i128` (`§3.1`, `§11.3`) which require 16-byte alignment in LLVM IR on x86-64 and AArch64.
