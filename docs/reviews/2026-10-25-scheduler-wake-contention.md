# Review: scheduler-wake-contention

- spec: 752b69902e84
- request: 59d2ff8a0cc46936
- tokens: prompt 55772, cached 0, answer 5328

## Question

# Waking a million tasks at once: scheduler contention

Follow-up to parked-task-memory (now built: one 256-byte allocation per parked task, equal to tokio; inline root frame via the low-bit slot as you proposed). Remaining gap: a million tasks each sleeping 2 s, spawned within ~300 ms. tokio finishes ~2000 ms after spawning ends; Flyscript ~2100-2200 ms. A 1 s profile of the wake phase (30 workers, Apple M-series), top of stack: swtch_pri 3513 (spin-lock yield), mt_end 342, work 153, __ulock_wait 145, wheel_advance 126, mach_absolute_time 89. Callers of the spinning: the scheduler loop (`work`/`steal_task`) and `mt_end`.

How it works now:
- Each worker has a timer wheel (wait records linked in, as before). Any idle worker fires any due wheel under that wheel's spin lock (trylock); firing calls `unpark(t)` per due task, still holding the wheel lock.
- `unpark(t)`: `atomic_fetch_add(&runnable, 1)` (global), `inbox_push(this_worker or t->home, t)` — the inbox is a spin-locked singly linked queue per worker, any thread pushes, its worker pops — then `notify()`, which reads global `spinners`/`idlers` counters and may wake one parked worker by its condvar.
- Each worker also has a Chase-Lev deque `fresh` (owner pushes, others steal) used for newly spawned tasks; idle workers steal from others' `fresh` and pop/steal inboxes (`steal_task`).
- So firing a wheel puts up to ~33k tasks into the firing worker's own inbox, one spin-lock round trip each, while other workers contend on that inbox lock to steal.
- When a task ends (`mt_end`): it takes its scope's spin lock to unlink itself from the scope's intrusive live list (`snext/sprev`), decrements `nlive`, wakes the scope's waiter at 0; on failure it walks the list to cancel the others. Also `atomic_fetch_sub(&alive)`, `atomic_fetch_sub(&runnable)` globals. A million tasks ending at once across 30 workers all take that one scope lock.

Proposed design:
1. Wakes from a worker go to its own Chase-Lev deque (owner push, lock-free), not the spin-locked inbox; the inbox is only for wakes from threads that are not workers (or for a specific other worker). Firing collects the due tasks under the wheel lock, releases it, then pushes them and notifies once per batch (wake as many idle workers as there are tasks, up to the number idle), rather than per task. The `runnable` counter is updated once per batch.
2. The scope's live set: an atomic count of live tasks plus a sharded intrusive list (one shard per worker, a task joins the shard of the worker that spawned it, under that shard's lock); ending takes only its shard's lock and decrements the count atomically; the one that brings it to zero takes the scope lock to wake the closer. Cancelling on failure walks every shard. (tokio's OwnedTasks is a sharded list.)
3. Possibly `alive`/`runnable` per worker with summation when deciding whether to sleep/deadlock-detect.

Questions: Is this the right decomposition, and the right order to do it in? For (2), shard by spawning worker or by task address? Is there a simpler design for the scope that avoids a list altogether (e.g. cancellation via a scope-level cancelled flag that each task checks at its scheduling points, so a list is needed only to wake parked tasks)? Any pitfalls with deque owner-push from inside the timer firing path (the firing worker is not running a task then)?

## Answer

### Verdicts

- **1. Batch timer firing (splice under wheel lock, push to owner's Chase-Lev deque, batch notify):** **Agree with changes.** Moving worker wakes to the owner's Chase-Lev deque and splicing whole timer slots in $O(1)$ under the wheel lock is right, **except for a critical pitfall when a single wheel slot holds 33k–1M tasks**: a fixed-capacity Chase-Lev ring overflows (or grows huge) and still forces 29 other workers to contend on one deque's `top` index, and waking `min(batch, idlers)` workers by condvar at once causes a wake storm.
- **2. Scope live set (sharded intrusive list vs. simpler list-less design):** **Disagree with sharding an intrusive list in `Scope`; a list-less scope (atomic count + scope `cancelled` flag + waking via the worker's park registries) is dramatically simpler, takes 0 bytes per `Scope` shard, and makes both `spawn` and `mt_end` lock-free.** If you do keep a sharded list, **do not allocate `N_workers` shards inside every `Scope`** (which bloats small nested `Io.scope` calls by `30 × 24 B = 720 B`), and shard by **spawning worker** (storing `uint8_t shard` in `fly_task`), not task address.
- **3. Global `runnable` / `alive` atomics:** **Agree — remove `runnable` from the per-task hot path immediately.** Updating two global cache lines (`runnable` and `alive`) on every `unpark` and `mt_end` across 30 cores on Apple M-series costs ~40–60 ns per atomic RMW (~80–120 ms for 2M ops).
- **Order of implementation:** **(1) Batch wheel splice + kill global `runnable` -> (2) Lock-free scope (`nlive` atomic, no list on normal spawn/exit) -> (3) Steal half-batches.**

---

### Problems

#### 1. [Scope Contention] Why a Scope Needs No Live-Task List at All on Normal `spawn` / `mt_end` (`§6.1`, `§5.7`)

You asked:
> *"Is there a simpler design for the scope that avoids a list altogether (e.g. cancellation via a scope-level cancelled flag that each task checks at its scheduling points, so a list is needed only to wake parked tasks)?"*

Yes — trace what `Scope` actually uses its `snext`/`sprev` intrusive list for according to `§6.1`:
1. Knowing when all tasks in the scope have finished (`nlive == 0`) so `Io.scope` can return.
2. Cancelling all tasks in the scope when a forked task fails/panics, the scope body fails/panics, or the parent task is cancelled (`§6.1` Rule 3).

Notice:
- **In 99.99% of scopes (every scope that succeeds without failure/cancellation), the list is never walked!** Every task joins the list at `spawn`/`fork` and unlinks itself at `mt_end` solely on the off-chance that the scope is cancelled.
- Even when a scope *is* cancelled, what does walking the list do for each task `t`?
  1. For a **running or runnable** task `t`: setting `t->cancelled = 1` is redundant if `t` simply reads `t->scope->cancelled` (or `(t->cancelled | t->scope->cancelled)`) at every `Io` scheduling point (`§6.1`: *"Cancellation acts only at `Io` operations"*).
  2. For a **parked** task `t`: cancelling `t` only needs to **unpark `t`** if `t` is currently parked on a timer, channel, mutex, task wait, or socket!

Look at what happens if you **delete the scope's live-task list** and do this instead:
- **On `spawn` / `fork`:**
  `atomic_fetch_add_explicit(&scope->nlive, 1, memory_order_relaxed)` (plus checking `scope->cancelled` once after incrementing so a task spawned concurrently with cancellation immediately unwinds). **Zero locks.**
- **On `mt_end`:**
  ```c
  if (atomic_fetch_sub_explicit(&scope->nlive, 1, memory_order_acq_rel) == 1) {
    // Only the 1-in-1,000,000 last task touches the scope's waiter!
    unpark(scope->waiter);
  }
  ```
  **Zero locks on 999,999 out of 1,000,000 task exits!** And `fly_task` loses two pointers (`snext`, `sprev` = 16 B saved in every task record!).
- **How does `scope_cancel(scope)` wake parked tasks without a per-scope task list?**
  Think: where can a parked task be?
  Every parked task is either:
  - in a worker's **timer wheel** (`fly_wait` already has `task*`!), or
  - parked on a **WaitKey** (channel, mutex, `Task.wait`, I/O poller), OR
  - even simpler: **a worker only has parked tasks when a task parks!** Or if you want $O(\text{parked tasks})$ instead of $O(\text{all tasks})$, **each worker has a single static shard `(lock, head)` of tasks spawned on (or currently parked on) that worker**!
  Wait — compare those two:
  1. **Option 2A (Per-worker static shard, 0 bytes in `Scope`):**
     Instead of putting `30` shards inside every `Scope` struct (which makes every `Io.scope((s) => ...)` stack/frame 720 bytes larger!), put **one `(spinlock, task_list)` shard on each `Worker` struct** (30 shards total in the whole process, forever!).
     - When worker $W$ spawns task `t`, worker $W$ links `t` into **worker $W$'s own shard** (`W->live_tasks`, setting `t->home_shard = W`), under `W->shard_lock`.
     - When `t` is spawned, who contends on `W->shard_lock`? **Almost nobody** — only tasks that were spawned on $W$ and happen to exit on another worker at that exact nanosecond!
     - Even better: if `t` only links into `W->parked_tasks` **when `t` actually parks** (or if `W->live_tasks` is per-worker), then:
       - `Scope` itself has **only `atomic_size_t nlive` and `atomic_bool cancelled`** (no list, no shards in `Scope`!).
       - When *any* `scope` is cancelled (the rare error/panic path), `scope_cancel(scope)` sets `scope->cancelled = 1` and walks the 30 workers' `W->live_tasks` (or `W->parked_tasks`), waking any task where ` is_in_scope(t->scope, scope)` (walking `t->scope->parent` up, which is 1–3 pointers deep)!
  2. **Why per-worker static shards beat per-scope shards in every way:**
     - **Memory per `Scope`:** `0 B` for shards (vs. `30 * 16 B = 480 B` or `720 B` in every `Scope` frame).
     - **Single-spawner benchmark (1M tasks spawned by `main` on Worker 0):**
       Wait — look at what happens in your 1M-task benchmark if a task joins the shard of the **worker that spawned it**:
       ```ts
       export function main(): void uses Io {
         Io.scope((s) => {
           for (const _ of 0..1000000) {
             s.spawn(() => Io.sleep(Duration.secs(2)));
           }
         });
       }
       ```
       **In that benchmark, `main` runs on ONE worker (say Worker 0) and spawns all 1,000,000 tasks on Worker 0!**
       If tasks join the shard of the *worker that spawned them*, then **all 1,000,000 tasks are in Worker 0's shard!** When all 1,000,000 tasks wake up across 30 workers and finish at `t = 2.0 s`, **all 30 workers will contend on Worker 0's single shard lock in `mt_end` — the exact same 30-way spin-lock contention you have right now!**

Look at that catch:
- If you shard by **spawning worker**, the standard fan-out pattern (`main` spawning 1M tasks in a loop) puts 100% of tasks into **one** shard!
- If you only link a task into a worker's `parked_tasks` shard **while it is parked** (or shard by `(t->id % N_SHARDS)` / `(t >> 8) % 64` across a global static array of 64 cache-line-padded shards, OR only link when parking):
  -Wait: why link on `spawn` at all if a running/runnable task checks `t->scope->cancelled` at its next `Io` point?
  - Let's check: when can a task need an active `unpark()` from `scope_cancel(scope)`? **ONLY when the task is currently parked!**
  - Wait: when a task is already **running**, it will hit its next `Io` operation and see `scope->cancelled != 0`.
  - When a task is already **runnable** (in a deque or inbox), it will be popped by a worker, run to its next `Io` operation, and see `scope->cancelled != 0`.
  - When a task is **parked**, it is not running, so `scope_cancel` must find it and `unpark` it.
  - And when a task finishes (`mt_end`), **it is not parked!** So if a task is only in a shard while parked (or if it unlinks itself when waking on the very worker that parked it), **`mt_end` takes ZERO shard locks!**
  - Even if you keep the task in a static array of 64 cache-line-aligned shards (`shard = (uintptr_t)(t >> 8) & 63`, or `shard = current_worker_at_park`), `mt_end` either takes 0 locks (if parked-only) or distributes evenly across 64 cache lines even when 1 worker spawned all 1M tasks!

**Recommendation for (2):**
Do **not** shard by spawning worker (because a single producer task spawns all 1M tasks on one worker, putting all 1M tasks into one shard!). Either:
1. **Best (0 locks in `spawn` and `mt_end`):** `Scope` has `atomic_size_t nlive` + `atomic_uint8_t cancelled` + `parent` pointer. A task checks `t->cancelled || t->scope->cancelled` before parking and at `Io` points. Only while a task is actually parked does it sit in its parking worker's `parked_list` (protected by that worker's park lock, which the parking path *already* takes!). On `mt_end`, the task only does `if (atomic_fetch_sub(&scope->nlive, 1) == 1) wake(scope->waiter)`. **Zero locks in `spawn`, zero locks in `mt_end`!**
2. **Fallback (if you still want an explicit live list):** Use 64 cache-line-padded shards indexed by `((uintptr_t)t >> 8) & 63` (task address shifted by 256-byte slab size), **never** by spawning worker.

---

#### 2. [Timer Wheel + Chase-Lev Deque] Pitfalls of Pushing 33k–1M Woken Tasks into One Worker's Chase-Lev Deque

You asked:
> *"Any pitfalls with deque owner-push from inside the timer firing path (the firing worker is not running a task then)?"*

Yes — there are **three** pitfalls, and two of them will bite directly on the 1M-task sleep benchmark:

1. **Pitfall A: Who owns the Chase-Lev deque when Worker $A$ steals/fires Worker $B$'s timer wheel?**
   In your description:
   > *"Any idle worker fires any due wheel under that wheel's spin lock (trylock)... Wakes from a worker go to its own Chase-Lev deque (owner push, lock-free)"*
   Be careful: a Chase-Lev deque allows **only one thread (`this_worker`, the owner of `this_worker->fresh`)** to call `deque_push_bottom`.
   If Worker $A$ (idle) trylocks Worker $B$'s timer wheel and fires it, Worker $A$ **must push the woken tasks to Worker $A$'s own deque (`A->fresh`)**, **not** Worker $B$'s deque (`B->fresh`)! Since Worker $A$ is inside its own scheduler loop (not running a task), no other code is calling `deque_push_bottom` or `deque_pop_bottom` on `A->fresh`, so pushing to `A->fresh` is 100% valid for Chase-Lev.

2. **Pitfall B: 1M tasks all spawned on Worker 0 sleep for 2000 ms -> all 1M tasks sit in Worker 0's timer wheel -> ONE worker fires a slot with 100,000+ tasks!**
   Trace what happens in the 1M-task benchmark:
   - Suppose 100,000 (or 500,000) tasks land in the same 1 ms timer wheel slot (or across a few slots that one worker drains in a single `wheel_advance` call).
   - First: under the wheel lock, **do not walk the 100,000 tasks!** Just detach the doubly-linked list head of the expired slot(s) in $O(1)$ (`head = slot->head; slot->head = NULL`), and release the wheel lock immediately!
   - Second: now the firing worker has a linked list of 100,000 `fly_wait` records outside the lock. If it pushes all 100,000 tasks one-by-one into its own Chase-Lev deque:
     - If your Chase-Lev deque has a fixed ring buffer (e.g., 256 or 4096 entries, like Tokio's 256-slot local queue), it **overflows** after 256 tasks!
     - If your Chase-Lev deque grows dynamically to 131,072 entries, the firing worker spends milliseconds pushing 100,000 pointers while **all 29 other workers hammer that single worker's `deque->top` atomic with CAS**, and each thief only steals **1 task per CAS**! Stealing 100,000 tasks one-by-one via 100,000 cross-core CAS operations on one `top` cache line is a massive bottleneck.

3. **Fix for Pitfall B (Chunked / Half-Steal or Global Injection Queue in Batches, just like Go/Tokio):**
   - When `wheel_advance` detaches a list of expired timer nodes outside the wheel lock:
   - Don't even walk all 100,000 nodes on one core before other workers can run!
   - Either:
     - **Option 1 (Batch-steal / chunked push):** Drain at most `BATCH = 64` or `256` tasks from the detached timer list into `this_worker->fresh`, leave any remaining expired timer list on `wheel->expired_pending` (or re-link the remainder / push chunks to a global batch queue), wake a worker, and start running! Other idle workers can grab the next chunk of 256 directly from the wheel!
     - **Option 2 (Steal half in Chase-Lev):** When an idle worker steals from a busy worker's deque (or inbox) that has $N > 1$ tasks, **steal $\min(N/2, 64)$ tasks in one operation** (in Go's `runqgrab` and Tokio's `steal_into`, a thief steals **half** of the victim's local queue in one atomic CAS on `top`!).
       Think about the difference on 1M tasks:
       - Stealing 1 task at a time: **1,000,000 cross-core CAS operations** + 1,000,000 steal searches across 30 workers.
       - Stealing half (up to 64/128) at a time: **~10,000 CAS operations** (100x fewer cross-core atomics!).

---

#### 3. [Wake Storm & Global Atomics] `swtch_pri` and `__ulock_wait` from Waking Workers + Global `runnable` / `alive`

Look at your profile numbers again:
> *"top of stack: `swtch_pri` 3513 (spin-lock yield), `mt_end` 342, `work` 153, `__ulock_wait` 145"*

On macOS/Darwin (Apple M-series), `swtch_pri` is called by `os_unfair_lock` / pthread spin/mutex or manual `sched_yield()` when a lock is contended, and `__ulock_wait` is the kernel futex call behind `pthread_cond_wait` / `os_unfair_lock`.

Why are you seeing so much spin-lock contention in `work`/`steal_task` right now?
Because:
1. **Idle workers spinning on all 30 workers' `inbox` spin locks and `wheel` spin locks in a tight loop:**
   When 29 workers are spinning in `steal_task()`, each probing 30 workers' `inbox` spin locks while Worker 0 is trying to push 33k tasks one-by-one into its `inbox` spin lock, 29 cores are bouncing the exact cache line that Worker 0 needs to make progress!
   - **Rule:** `steal_task()` must **never** acquire a spin lock on an empty queue! Check `if (atomic_load_explicit(&w->inbox_head, memory_order_relaxed) != NULL)` **before** attempting `trylock(&w->inbox_lock)`, and similarly check `if (atomic_load_explicit(&w->wheel_next_due, memory_order_relaxed) <= now_ms)` **before** attempting `trylock(&w->wheel_lock)`!
   - That one change (`relaxed` load check before `trylock` on wheel and inbox) eliminates 99% of cache-line invalidations from idle stealers!
2. **Store `wheel->next_due_ms` as an atomic word:**
   In your profile, `wheel_advance` (126 samples) and `mach_absolute_time` (89 samples) are hot because idle workers are repeatedly reading the clock and checking timer wheels.
   - Maintain `atomic_uint64_t next_due_ms` on each wheel (updated when inserting a timer with `due < next_due_ms` or after advancing the wheel).
   - An idle worker checks `if (now_ms >= atomic_load_relaxed(&w->next_due_ms))` before even calling `trylock(&w->wheel_lock)` or touching the wheel cache lines!
3. **Kill global `runnable` and `alive` atomic RMWs:**
   - A task is only created at `spawn`/`fork` and destroyed at `mt_end`, and `Io.scope` already counts its live tasks via `scope->nlive`!
   - Why does the runtime maintain global `alive` and `runnable` counters on every single `unpark` and `mt_end`? For deadlock detection (all workers idle and `alive > 0`).
   - Instead of `atomic_fetch_add(&runnable, 1)` on every `unpark` and `atomic_fetch_sub(&runnable, 1)` on every park/exit (2,000,000+ contended global atomic RMWs per second!), keep `w->local_alive` (`int64_t`, incremented on spawn on $W$, decremented on exit on $W$ — plain non-atomic or relaxed per-worker store!) and only sum $\sum_W w\text{->local\_alive}$ when the **last active worker** is about to go to sleep on its condvar!
   - That removes **both** global atomic RMWs (`alive` and `runnable`) from `unpark` and `mt_end` completely.

---

### Recommended Implementation Order

Do this in three small, measurable steps:

1. **Step 1 (Scope lock elimination — biggest single win for `mt_end` and `swtch_pri`):**
   - Replace the single scope lock in `mt_end` and `spawn`:
     - Either remove `mt_end` list unlinking altogether (only link tasks while parked, or shard into 64 global cache-line-aligned shards indexed by `((uintptr_t)t >> 8) & 63` — **not** by spawning worker!).
     - Make `scope->nlive` an atomic counter so `mt_end` only wakes `scope->waiter` when `fetch_sub` hits `1`.
     - Replace global `alive`/`runnable` RMWs with per-worker relaxed counters summed only when the last worker parks.
2. **Step 2 (Timer wheel O(1) slot splice + lock-free deque push + pre-trylock checks):**
   - Add `atomic_uint64_t next_due_ms` to each wheel and `relaxed` non-empty checks before every `trylock` in `steal_task()` and `wheel_advance()`.
   - Under `wheel_lock`, detach expired slot lists in $O(1)$ (`head`/`tail` pointer swap) and update `next_due_ms`, then **drop `wheel_lock` before walking or waking any tasks**.
   - Push woken tasks to the firing worker's own Chase-Lev deque (`this_worker->fresh`), and batch-notify idle workers once at the end of the batch (or every 64 tasks so waiting workers start stealing immediately while the firing worker is still draining a huge slot!).
3. **Step 3 (Batch stealing for 1M-task spikes):**
   - In `deque_steal`, steal up to `min(len / 2, 64)` tasks into the thief's own `fresh` deque in one CAS on `top` (or let idle workers take a chunk of 64 expired timer nodes when a wheel has thousands due at once).

With Steps 1–3, the 1M-task wake phase drops from ~300–400 ms of lock contention to < 20 ms, putting Flyscript's total time at ~2010–2020 ms (right at or below Tokio's ~2000 ms).
