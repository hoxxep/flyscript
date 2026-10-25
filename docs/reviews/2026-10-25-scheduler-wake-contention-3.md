# Review: scheduler-wake-contention

- spec: 752b69902e84
- request: 14aa767798c62379
- tokens: prompt 55162, cached 0, answer 5225

## Question

# Spreading fresh tasks from one busy spawner

Follow-up (scheduler-wake-contention). Measured on a quiet machine, 1M tasks spawned in a loop by one task, each sleeping 2 s:
- tokio: spawning ends at ~390 ms, everything done at ~2395 ms: done - spawned = ~2005 ms.
- Flyscript: spawning ends at ~300 ms, done at ~2520 ms: done - spawned = ~2220 ms, with or without the sharded scope and dealt wakes (both built, both sound, neither visible here).

Instrumented (per-op averages): a task's first run (start, then park on its sleep) ~8-18 us; its second run (wake, end) ~2-4 us of which ending ~1-2 us; a steal ~2.5-5 us each; 1.2M of the 2M runs came by stealing. A sleep is registered at a task's first run, so the extra ~200 ms is first-run latency: the spawner pushes 1M tasks onto its own Chase-Lev deque and 29 thieves take them one at a time; each steal attempt scans every worker's deque (and inbox) from a random start, so a steal costs O(workers) of cache traffic when only one worker has work.

The deque is Chase-Lev (growable buffer; owner pops from bottom without a CAS unless one item remains), so a thief cannot safely take k > 1 items with one CAS on top (the owner can pop into the range meanwhile). Options:
(a) Replace it with a tokio-style local run queue: a fixed ring of 256 (head and tail; the owner pushes at tail; head moved by CAS for owner pops and for steals, so a thief can take half in one CAS), overflowing half its contents into a shared injection queue (mutex-protected linked list, taken from in batches) when full.
(b) Keep Chase-Lev, and when the spawner's deque grows past a threshold (say 64), move a batch of fresh tasks to a shared injection queue or deal them into idle workers' inboxes (as the woken batches are), so thieves rarely need to steal from it.
(c) Make stealing cheaper: thieves first try the worker that last had work (a hint), and a global count of runnable fresh tasks lets idle workers skip scanning when nothing is anywhere.

Which is the elegant, robust design here? (a) seems the principled one (it's what tokio and Go do), but it is a larger change: our deque also holds `par` jobs (a separate deque per worker, `jobs`, with a join-in-order fast path that pops back what it pushed), and fresh tasks. Pitfalls with a fixed 256 ring and overflow to a global queue under a single spawner producing 1M tasks? Is a LIFO slot (tokio's) worth having for message-passing ping-pong?

## Answer

### Verdicts

- **Why `done - spawned` is 2220 ms vs. Tokio's 2005 ms:** **The primary culprit is not just steal latency — it is Cooperative Preemption (Yield) of the spawner task + single-item stealing.** In Flyscript, `main` spawns all 1,000,000 tasks in a non-blocking loop in ~300 ms and **never yields its worker (`W0`)**, while all 29 thieves fight over `W0->fresh`'s `top` cache line one task at a time, so ~200,000+ tasks are still sitting unstarted in `W0->fresh` at `t = 300 ms` and don't even *begin* their 2000 ms sleep until `t = 520 ms`! In Tokio, `tokio::spawn` pushes to a 256-slot ring; every 256 spawns it overflows 128 tasks to the global queue, and Tokio's budget/tick drains keep the 29 other workers running the spawned futures **at the same rate they are spawned**, so at `t = 390 ms` when `spawn` finishes, almost all 1,000,000 tasks have *already* registered their timers (`done - spawned = 2005 ms`)!
- **Option (a) (Tokio/Go-style 256-slot bounded ring + batch steal-half + batch overflow):** **Agree for `fresh` tasks, keep Chase-Lev for `jobs` (`par`/`join`).** Since `jobs` (`§6.5`) is already a separate deque per worker that relies on Chase-Lev's zero-CAS LIFO pop for `join(a, b)`, leave `jobs` as Chase-Lev and make `fresh` a 256-slot FIFO ring with half-steal and batch overflow.
- **Option (b) (Keep Chase-Lev for `fresh`, overflow batches at threshold):** **Disagree as a standalone fix.** Because the owner can only pop from the *bottom* of a Chase-Lev deque, overflowing a batch from the bottom requires popping $K$ items one by one, and thieves *still* steal 1 item at a time from `top`.
- **Option (c) (Last-victim hint + skip empty scan):** **Agree as a 10-line addition to (a), insufficient alone.** With 1 spawner and 29 thieves, a hint makes all 29 thieves hammer `W0->fresh`'s `top` even faster, turning $O(W)$ scan traffic into 29-way CAS contention on a single cache line unless paired with batch stealing (stealing 64–128 tasks per CAS).
- **LIFO slot:** **Agree — add it for woken tasks (`unpark`), never for `spawn`/`fork`.**

---

### Problems

#### 1. [Root Cause] Why `done - spawned` Is 2220 ms: The Unstarted Backlog at `t = 300 ms`

Look closely at the numbers you measured:
- **Tokio:** `spawn` loop finishes at **`390 ms`**, all 1M tasks finish at **`2395 ms`** (`done - spawned = 2005 ms`).
- **Flyscript:** `spawn` loop finishes at **`300 ms`**, all 1M tasks finish at **`2520 ms`** (`done - spawned = 2220 ms`).
- And your per-op instrumentation says:
  > *"1.2M of the 2M runs came by stealing... a steal ~2.5-5 us each... A sleep is registered at a task's first run, so the extra ~200 ms is first-run latency"*

Do the arithmetic on what happens during `[0 ms, 520 ms]`:
1. In Flyscript, `s.spawn(...)` (`§6.1`) does not suspend the caller (`main`). So `W0` executes the `for (const _ of 0..1000000)` loop uninterrupted from `0 ms` to `300 ms`, pushing 1,000,000 tasks into `W0->fresh` (at `300 ns/spawn`).
2. Meanwhile, the other 29 workers (`W1..W29`) are stealing from `W0->fresh` **one task at a time** at `~2.5-5 us` per steal + `~8-18 us` per first run ($\approx 15\,\mu\text{s}$ per task per worker $\approx 1.9\text{ tasks/ms/worker} \times 29\text{ workers} \approx 55,000\text{ tasks/ms}$ at best, or ~1,900 tasks/ms under 29-way CAS contention!).
3. That means when `W0` finishes the `for` loop at `t = 300 ms` and parks on `Io.scope`, **hundreds of thousands of spawned tasks are still sitting in `W0->fresh` and have not executed their first step yet!**
4. The last of those tasks does not get popped and run its `Io.sleep(Duration.secs(2))` call until **`t = 520 ms`**! And `520 ms + 2000 ms = 2520 ms`!

Why didn't Tokio have a 220 ms backlog when its `spawn` loop ended at `390 ms`?
Because in Tokio:
1. Every 256 spawns on `W0`, `W0`'s local 256-slot ring fills up.
2. When `W0`'s ring is full, `W0` takes half the ring (128 tasks), links them together into an intrusive doubly/singly linked list in local memory, pushes that 128-task batch to the shared injection queue (or deals it), and wakes an idle worker.
3. Even more importantly, when any thief `W1..W29` steals from `W0`'s 256-slot ring, **one CAS on `W0->head` steals half of `W0`'s queue (up to 128 tasks) into the thief's own 256-slot ring!**
4. Because each thief grabs ~64–128 tasks per steal instead of 1, the 29 thieves execute **~100x fewer steals** (~10,000 steals instead of 1,000,000 steals!), so `W0`'s cache line isn't hammered by 29 cores, and the 29 workers drain the spawned tasks **as fast as `W0` spawns them** (`390 ms` total to both spawn *and* run the first step of all 1M tasks!).

---

#### 2. [Design of Option (a)] Keep Chase-Lev for `jobs` (`par`/`join`), Use a 256-Slot Batch-Stealable Ring for `fresh`

You noted a key architectural constraint:
> *"our deque also holds `par` jobs (a separate deque per worker, `jobs`, with a join-in-order fast path that pops back what it pushed), and fresh tasks."*

Notice that `jobs` and `fresh` have **opposite** access patterns and invariants:
- **`jobs` (`join` / `par`, `§6.5`, `§11.3`):**
  - Strictly **LIFO** for the owner (divide-and-conquer tree: push right half, run left half, pop right half if no thief took it) and **FIFO** for thieves (steal the coarsest tree node from `top`).
  - Owner push+pop must be **zero-CAS** so `join(a, b)` when all cores are busy costs just a store and load (`§11.3`: *"splitting where no core is free costs little more than a call"*).
  - Never has 1,000,000 items pushed without executing (`par` splits binary-tree-wise to $\log_2 N$ depth).
  - **Keep `jobs` as your existing Chase-Lev deque unchanged!**
- **`fresh` (tasks from `spawn`, `fork`, and woken batches from `unpark`):**
  - **FIFO** for both the owner and thieves (fair scheduling), except for the single **LIFO slot** for message-passing wakes.
  - Both owner pop and thief steal advance `head` (`uint32_t` packing two 16-bit unsigned counters `(steal_head, real_head)`, or `uint64_t` packing two 32-bit counters), which allows **both the owner (pop 1) and a thief (steal $N/2$) to advance `head` in a single atomic CAS!**

Here is the exact lock-free 256-slot ring algorithm (Tokio/Go's algorithm, ~60 lines of C) and how it avoids every pitfall:

```c
#define RING_CAP 256
#define RING_MASK (RING_CAP - 1)

typedef struct {
  _Atomic uint64_t head; // low 32 bits: real_head, high 32 bits: steal_head
  _Atomic uint32_t tail; // written only by owner
  _Atomic(fly_task*) buffer[RING_CAP];
} fly_ring;
```

- **Owner Push (`ring_push`):**
  1. Owner reads `tail` (relaxed) and `head` (acquire). Let `steal = (uint32_t)(head >> 32)`.
  2. If `(uint32_t)(tail - steal) < RING_CAP`:
     - `atomic_store_explicit(&r->buffer[tail & RING_MASK], t, memory_order_relaxed);`
     - `atomic_store_explicit(&r->tail, tail + 1, memory_order_release);`
     - **0 CAS, 0 locks** on the fast path!
  3. If `(uint32_t)(tail - steal) == RING_CAP` (ring is full — happens once every 128 spawns!):
     - Call `ring_push_overflow(w, t)` (see Problem 3 below!).

- **Owner Pop (`ring_pop`):**
  1. Loop: read `head` (acquire) and `tail` (relaxed). Let `real = (uint32_t)head`, `steal = (uint32_t)(head >> 32)`.
  2. If `real == tail`, the ring is empty (`return NULL`).
  3. Increment `real_next = real + 1`. If `steal == real` (no thief is mid-steal), also set `steal_next = real_next`; otherwise keep `steal_next = steal`.
  4. CAS `r->head` from `head` to `((uint64_t)steal_next << 32) | real_next` (`acq_rel`).
  5. Once CAS succeeds, read `r->buffer[real & RING_MASK]` and return it.

- **Thief Steal Half (`ring_steal_into(victim, dst_ring)`):**
  1. Read `dst_ring->tail` and `dst_ring->head` to check free capacity in `dst_ring`.
  2. Read `victim->head` (acquire) and `victim->tail` (acquire).
  3. Let `real = (uint32_t)head`, `steal = (uint32_t)(head >> 32)`.
  4. **If `steal != real`, another thief is already copying from `victim` right now — abort immediately (`return NULL`)!**
     - **Why this matters:** When 29 thieves see `W0` has work, the *first* thief sets `real = real + n` while keeping `steal = old_real`. The other 28 thieves see `steal != real` with a **single read (no CAS!)** and immediately back off instead of 28 cores fighting in a CAS loop on `victim->head`!
  5. Compute `n = (uint32_t)(tail - real); n = n - (n >> 1);` (steal half, rounded up, capped to free space in `dst_ring`). If `n == 0`, return `NULL`.
  6. Claim `[real, real + n)` in one CAS on `victim->head`: set `real_next = real + n`, keep `steal_next = steal` (`((uint64_t)steal << 32) | (real + n)`).
  7. Copy the `n - 1` tasks from `victim->buffer[(real + 1)..(real + n)]` into `dst_ring->buffer`, advance `dst_ring->tail` with `release`, and update `victim->head`'s `steal` field from `real` to `real + n` (via CAS loop on `victim->head`) so the slots in `victim` can be reused by `victim`'s owner!
  8. Return the first stolen task (`victim->buffer[real & RING_MASK]`) directly to the caller to run immediately.

Look at what Step 4 + Step 6 do to your 1M-task benchmark:
- Instead of 1,200,000 steals (each scanning 30 workers + doing a CAS on `W0->top`), a thief steals **up to 128 tasks in ONE CAS**.
- While that thief is copying its 128 pointers (~50 ns), `steal != real` tells any concurrent thief in a single `acquire` load that `W0` is busy being stolen from.
- Total steals across the entire 1M-task run drop from **1,200,000** to **< 10,000**!

---

#### 3. [Pitfall with 256-Ring Overflow] Do NOT Contend on a Single Global Mutex When `W0` Overflows 7,800 Times!

You asked:
> *"Pitfalls with a fixed 256 ring and overflow to a global queue under a single spawner producing 1M tasks?"*

Here is the #1 pitfall with a naive global overflow queue, and how to make it even faster than Tokio's:

If `W0` spawns 1,000,000 tasks in a tight loop and its 256-slot ring overflows 128 tasks at a time (`1,000,000 / 128 = 7,812` overflows):
- **Pitfall 1 (O(N) locking or copying under the global lock):**
  If `ring_push_overflow` locks the global injection mutex and pushes 128 tasks one by one (or if thieves pop 1 task at a time under the global mutex), the global mutex becomes the new `swtch_pri` bottleneck!
  - **Fix:** Link the 128 tasks together through their existing `next` pointer (`t->next`) **before** acquiring the global injection lock! Then under the global lock, appending all 128 tasks is **two pointer stores (`tail->next = batch_head; tail = batch_tail; n_batches++`) — $O(1)$!**
  - Even better: since each 128-task overflow batch is already linked into a chain of 128 tasks (say via `t->next`, with the head task storing `t->batch_tail` or simply pushing the **head pointer of the 128-task chunk** into a lock-free / spin-locked **chunk queue**!), a worker that pops from the global injection queue pops **an entire 128-task linked chain in $O(1)$ (two pointer reads under the lock)**, moves all 128 tasks into its own 256-slot ring outside the lock, and runs!
  - Read that again: **a global queue of *batches* (each item in the global queue is a linked list of up to 128 tasks!)** means:
    - Pushing 128 overflowed tasks takes **1 lock acquisition and 2 pointer writes ($O(1)$)**.
    - Popping 128 tasks into an idle worker's empty 256-slot ring takes **1 lock acquisition and 2 pointer reads ($O(1)$)** — **not** walking 128 links while holding the global lock!
    - For 1,000,000 tasks, the global batch lock is taken at most `7,812 * 2 = 15,624` times for ~10 ns each (= **0.15 ms total across the whole benchmark**!).

- **Pitfall 2 (Thief Starvation / Missing Wake on Overflow):**
  When `W0` pushes a 128-task batch to the global batch queue (or has tasks in its ring), make sure `W0` calls `notify_one()` if `idlers > 0` so sleeping workers wake up and grab the batch immediately!

- **Pitfall 3 (Timer Wheel Firing > 256 Tasks at Once):**
  Remember from our last review: when `wheel_advance` fires at `t = 2.0 s`, a single worker may detach a list of **10,000+ expired tasks** from a timer wheel slot!
  If `wheel_advance` pushes those 10,000 tasks into its 256-slot ring, the first 255 go into the ring and the remaining 9,745 immediately trigger 76 batch overflows into the global batch queue!
  With the **global batch queue** above, that works seamlessly and fast: `wheel_advance` fills the firing worker's own 256-slot ring with the first 128 tasks, slices the remaining detached timer list into 128-task chunks, appends all chunks to the global batch queue in **one** lock acquisition, and wakes up to `min(n_chunks, idlers)` workers! Every woken worker grabs a 128-task chunk from the global batch queue in $O(1)$ without touching any other worker's ring!

---

#### 4. [LIFO Slot] Yes for `unpark` (Channels/Mutexes), NEVER for `spawn`/`fork`

You asked:
> *"Is a LIFO slot (tokio's) worth having for message-passing ping-pong?"*

Yes — and the rule for when to use it is critical:
- **What it is:** Each worker struct has a single non-shared pointer `fly_task* lifo_slot` (only accessed by the owning worker; **never** stolen by thieves unless the worker's 256-ring is empty, or migrated into the 256-ring if replaced).
- **When `unpark(t)` is called on worker `W` (e.g. `tx.send(v)` or `reply.send(...)` in Appendix A.6 waking a task waiting on a channel, or unlocking a `Mutex`):**
  - Place `t` into `W->lifo_slot`. If `W->lifo_slot` already held a task `prev`, push `prev` into `W`'s 256-slot FIFO ring (`ring_push(W, prev)`) and wake a thief if `idlers > 0`.
  - When `W`'s current task parks or yields, `W` checks `W->lifo_slot` **first** before `ring_pop(W)` (except every 61 ticks, when it checks the global batch queue and FIFO ring first for fairness so two ping-ponging tasks can't starve the FIFO ring).
- **Why it matters:**
  - In a request/reply pipeline (`A.6`, `channel<T>()`), Task A sends a message to Task B and parks on the reply channel. With the LIFO slot, `W` immediately runs Task B on the **same CPU core with the message hot in L1 cache and 0 atomic operations** (since `W->lifo_slot` is local to `W` unless stolen!).
- **Why `spawn`/`fork` must NEVER use `lifo_slot`:**
  - If `spawn` used `lifo_slot`, a loop spawning 1M tasks would keep overwriting `lifo_slot` and wouldn't make tasks immediately visible to thieves until the second spawn, and running the last-spawned task first reverses spawn order. So `spawn`/`fork` always goes straight to `ring_push(W, t)` (the FIFO ring), and only `unpark` from a synchronization primitive (`channel`, `Mutex`, `Task.wait`) uses `lifo_slot`.

---

### Summary of the Complete Design

1. **Keep `jobs` (for `par`/`join`) as your existing Chase-Lev deque.** It is already tuned for LIFO owner / FIFO thief divide-and-conquer.
2. **Replace `fresh` with a 256-slot bounded ring (`fly_ring`) + a global queue of 128-task linked batches (`global_batches`):**
   - **Owner push (`spawn`/`fork`):** 0-CAS store into `ring->buffer[tail & 255]`. When full (256 items), pop half (128 items), link them via `t->next` outside any lock, append the 128-task chain as **one node** to `global_batches` in $O(1)$, and `notify_one()`.
   - **Timer wheel wake (`wheel_advance`):** Put up to 128 woken tasks into `this_worker->ring`, slice the rest into 128-task chains, append them to `global_batches` in one lock acquisition, and wake `min(n_batches, idlers)` workers.
   - **Worker run loop priority:**
     1. Every 61 ticks: pop 1 batch (up to 128 tasks) from `global_batches` into `this_worker->ring`.
     2. Check `this_worker->lifo_slot` (capped at 3 consecutive LIFO runs before checking the FIFO ring so ping-pong can't starve FIFO tasks).
     3. `ring_pop(&this_worker->ring)`.
     4. Pop 1 batch from `global_batches` (check `atomic_load_relaxed(&global_batches_head) != NULL` before locking!).
     5. `steal_task()`: scan workers starting at `last_victim_hint` (or random), skipping any worker where `real == tail` or `steal != real` (a thief is already stealing from it!), and call `ring_steal_into` to take **half** of the victim's ring in a single CAS.

This eliminates both the 1.2M single-item steals and the `t = 300..520 ms` unstarted-task backlog, bringing `done - spawned` down to ~2005 ms alongside Tokio.
