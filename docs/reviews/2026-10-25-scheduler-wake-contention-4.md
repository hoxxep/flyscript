# Review: scheduler-wake-contention

- spec: 752b69902e84
- request: 78b16a930ac9f91f
- tokens: prompt 61111, cached 0, answer 5179

## Question

# Follow-up: a single producer task on a worker, the ring, and thieves

Built your design: tokio-style 256-slot ring per worker (packed steal/real head, owner push without RMW, steal half in one CAS, second thief backs off on steal != real), overflow half to a shared queue of 128-task chains, woken batches into the waker's ring + chains to the shared queue, searchers capped at half the workers, notify() suppressed while anyone is searching, and the last searcher to find work notifies another. Locks now spin ~100 iterations then sleep on the word (os_sync_wait_on_address / futex). All corpora pass.

Benchmark: one task (on a worker) spawns 1M tasks in a loop, each sleeps 2 s. tokio (its spawner is #[tokio::main]'s block_on thread, not a worker, so tokio's spawns go to its inject queue): spawned in ~390 ms, done ~2395 ms. Ours: spawned in ~850-1100 ms, done = spawned + ~2001 ms (no wake lag any more).

Counters for one run: notify() 1.23M calls, of which 116k actually woke a parked worker; 228k-280k parks; 1.01M successful steals out of 2.33M attempts, moving ~2.2M tasks: ~1-2 tasks per steal. An accidental experiment: when the searcher cap was read by getenv() on every steal attempt (a slow call, i.e. an accidental backoff), the same program spawned in 230-300 ms and finished at ~2250-2290 ms, ahead of tokio.

So the producer's ring is drained one or two tasks at a time by up to 15 thieves, each steal costing a scan plus two CASes on the producer's head cache line (which the producer re-reads on every push), and workers thrash between parking and being woken.

What is the principled fix? Ideas: (1) a searcher that steals fewer than some number of tasks, or fails, backs off (exponential, bounded) before searching again, rather than looping at full speed; (2) a victim with fewer than 2-4 tasks isn't stolen from (the owner will run them soon); (3) the producer publishes to the shared queue in batches when its ring passes half full, so consumers take 128 at a time from there and rarely steal from rings; (4) the owner caches the last seen `steal` and reloads `head` only when its view says the ring is full (`tail - cached_steal >= RING`), so pushes don't touch the head line; (5) count spawns as "making work" and wake at most one worker per N spawns. Which combination, and why? What does Go do for a goroutine spawning in a loop?

## Answer

### Verdicts

- **Why you saw 1.01M steals of ~1–2 tasks and 280k parks:** Because 15 thieves drain `W0`'s ring faster than `W0` can accumulate a batch, **keeping `W0`'s ring perpetually at length 1–2**. Every push by `W0` reads `W0->head` (which a thief just invalidated with 2 CASes) and modifies `W0->tail` (which 15 thieves are polling), and every `spawn` calls `notify()`, waking a worker for 1 task that then immediately runs out of work and calls `futex_wait` (`280k parks`!).
- **Idea (4) (Cache `steal` in `w->cached_steal`, reload `r->head` only when `tail - cached_steal >= RING_CAP`):** **Agree — mandatory and unconditional.** There is zero reason for `ring_push` to read the contended `r->head` cache line on every push when `tail - cached_steal < 256` already guarantees free space! Also pad `head`, `tail`, and `buffer` onto separate 64/128-byte cache lines.
- **Idea (5) (Do NOT call `notify()` on every `spawn` — batch `spawn` publication or only `notify()` when transitioning ring `0 -> 1` or overflowing a batch):** **Agree with changes — fix the root cause of 1.23M `notify()` calls and 280k parks.** Calling `notify()` on every `spawn` when the ring already has items is pointless if a searcher is active or if the owner hasn't accumulated a batch. Even better: **batch `tail` publication** or **only `notify()` when `tail - real == 1` (ring was empty) or on batch overflow**.
- **Idea (2) & (3) (Minimum steal threshold vs. buffered local spawn):** **Agree with changes — combine them via private/buffered `tail` or a minimum steal threshold (`len >= 4` while owner is running a task).** If a worker is actively *running* a task (not parked/searching), thieves should not steal its lone 1–2 items unless `tail - real >= 8` (or `W0` buffers local spawns and publishes `r->tail` every 32–64 spawns and when the running task yields/parks!).
- **Idea (1) (Searcher spin/backoff before parking):** **Agree — add a short `cpu_relax()` / `yield` spin loop (e.g. 32–64 pause iterations across 3–4 steal rounds) before `park()`, instead of immediately calling into the kernel (`os_sync_wait_on_address`) on the first empty scan.**

---

### Problems

#### 1. [Root Cause + What Go & Tokio Do] Why 15 Thieves Keep `W0`'s Ring at Size 1–2 and Cause 280,000 Kernel Parks

Look at the feedback loop in your counters:
- `1.01M successful steals` moving `2.2M tasks` (= **2.17 tasks per steal**).
- `1.23M notify() calls`, `116k wakeups`, `228k-280k parks`.
- And when you accidentally put a slow `getenv()` (~500 ns backoff) into the steal path, spawn time dropped from **850–1100 ms to 230–300 ms**!

Why did slowing down thieves make spawning **3.5x faster**?
Trace what happens at the cache-line level when 15 thieves scan at full speed while `W0` runs `for (0..1_000_000) { s.spawn(...); }`:
1. `W0` creates 1 task (~200 ns) and writes `r->tail = 1`, then calls `notify()`.
2. Within 50 ns, one of the 15 spinning thieves sees `tail - real == 1`, executes **two** atomic CASes on `W0->head` to steal **that 1 single task** (`n - (n >> 1) = 1 - 0 = 1`), and runs it for ~300 ns (registering its sleep timer).
3. Meanwhile, `W0` creates the 2nd task, tries to read `W0->head` in `ring_push`, and **stalls for ~80–120 ns** waiting for the cache line of `W0->head` to come back from the thief's L1 cache in Exclusive/Modified state!
4. Worse: because the thief only got **1 task**, 300 ns later that thief's ring is empty again! It scans once, finds `W0`'s ring empty (because another thief just stole the 1 task `W0` produced), **and goes straight into the kernel (`os_sync_wait_on_address` / `futex_wait`)**!
5. 100 ns later, `W0` spawns the next task and calls `notify()`, which calls into the kernel (`os_sync_wake_by_address_any`) to wake the worker that just went to sleep!
6. Result: **280,000 kernel park/wake syscalls** and **2,020,000 cross-core CASes on `W0->head`**! `W0`'s ring **never reaches 256** (in fact, it rarely exceeds 2!), so the 128-task batch overflow queue you built is **never used at all** during spawning!

Now, **what do Go and Tokio actually do when a task spawns in a loop?**
1. **Go (`runtime/proc.go` — `runqput`, `runqgrab`, `findrunnable`):**
   - First, Go puts the newly spawned goroutine into `_p_.runnext` (the 1-element LIFO slot), **which is NOT visible to thieves** until the *next* `go` statement displaces the previous `runnext` into the 256-slot `runq`!
   - Second, in Go, `runqput` only calls `wakep()` when `atomic.Load(&sched.nmspinning) == 0`.
   - Third, in Go's `findrunnable()`, a spinning `M` (searcher) does **4 full steal passes** (with `procyield` / `PAUSE` instructions between passes) before giving up its spinning status and calling `stopm()` (kernel futex sleep). It does **not** call into the kernel after 1 failed scan!
   - Fourth, in Tokio, why did `#[tokio::main]` finish spawning in 390 ms? Because in your Tokio benchmark, `#[tokio::main]` ran the `for` loop on the `block_on` thread or pushed to the inject queue, OR when spawned inside `tokio::spawn(async move { for _ in 0..1_000_000 { tokio::spawn(...); } })`, Tokio's coop budget yields the spawner every 128 polls, and Tokio's `Ring` **caches `steal_head` on the producer** and **splits struct fields across cache lines**!

Look at how clean the fix is once you see why `W0`'s ring never accumulated a batch.

---

#### 2. [Fix 1 — Idea (4) + Cache-Line Padding] Stop `ring_push` from Reading `r->head` on Every Push

In your current `ring_push`:
> *"each steal costing a scan plus two CASes on the producer's head cache line (which the producer re-reads on every push)"*

Think about that:
- `r->head` is modified **only** by consumers (`ring_pop` and `ring_steal_into`), and it **only increases monotonically** (`steal_head` only moves forward).
- If `W0` knows that at some point in the past `steal_head` was `cached_steal`, and `(uint32_t)(tail - cached_steal) < RING_CAP`, then the actual current `(uint32_t)(tail - current_steal_head)` is **guaranteed to be `< RING_CAP`**!
- Therefore, `ring_push` **never needs to load `r->head` at all** until `(uint32_t)(tail - w->cached_steal) >= RING_CAP`!

```c
typedef struct {
  alignas(128) _Atomic uint64_t head;      // cache line 0: written by thieves & owner pop
  alignas(128) _Atomic uint32_t tail;      // cache line 1: written ONLY by owner push
  uint32_t cached_steal;                   // also on cache line 1: private to owner!
  alignas(128) _Atomic(fly_task*) buf[256]; // cache lines 2+: ring slots
} fly_ring;
```

Look at what happens in `ring_push` with `cached_steal` + `alignas(128)` (Apple M-series L2 cache lines are **128 bytes**, x86 are 64 bytes):
```c
static inline bool ring_push(fly_worker* w, fly_task* t) {
  fly_ring* r = &w->ring;
  uint32_t tail = atomic_load_explicit(&r->tail, memory_order_relaxed);
  if (UNLIKELY((uint32_t)(tail - r->cached_steal) >= RING_CAP)) {
    uint64_t h = atomic_load_explicit(&r->head, memory_order_acquire);
    r->cached_steal = (uint32_t)(h >> 32);
    if ((uint32_t)(tail - r->cached_steal) >= RING_CAP) {
      return ring_push_overflow(w, t, h, tail); // overflow 128 tasks to shared batch queue
    }
  }
  atomic_store_explicit(&r->buf[tail & RING_MASK], t, memory_order_relaxed);
  atomic_store_explicit(&r->tail, tail + 1, memory_order_release);
  return (tail == r->cached_steal); // true if ring might have been empty
}
```
- **Why `alignas(128)` is critical on Apple Silicon (M1–M5):**
  Apple M-series CPUs have **128-byte cache lines / coherency granules**! Without `alignas(128)`, `r->head` and `r->tail` sit in the **exact same 128-byte cache line**, so every thief CAS on `r->head` invalidates `r->tail` in `W0`'s L1 cache, and every `W0` store to `r->tail` aborts every thief's LL/SC / LSE atomic on `r->head`!
- Putting `head` on its own 128-byte cache line and `tail` + `cached_steal` on a separate 128-byte cache line means `W0` only reads `r->head` **at most once every 256 pushes** instead of every single push!

---

#### 3. [Fix 2 — Idea (2)/(3)] Let the Producer Accumulate a Batch Before Exposing `tail` to Thieves (or Require `len >= 8` When Stealing from a Busy Worker)

Even with `head` and `tail` on separate 128-byte cache lines, if `W0` publishes `r->tail = tail + 1` on every single `spawn` and 15 thieves immediately steal when `tail - real == 1`, thieves will still steal **1 task at a time** (1,000,000 steals of 1 task instead of 15,000 steals of 64 tasks).

Compare the two ways to stop 1-by-1 stealing from an active producer:

##### Mechanism A (Simplest, 3 lines in `ring_steal_into`): Thief Batch Threshold + Spin Backoff (Ideas 1 + 2)
When a thief inspects `victim`:
1. Check `n = (uint32_t)(tail - real)`.
2. **If `victim` is currently running a task (`victim->running == 1`) and `n < 16` (or `n < 8`), do NOT steal from `victim` yet!**
   - Wait: what if `victim`'s running task never spawns again (e.g., it only spawned 3 tasks and is now doing 10 ms of CPU work)?
   - Simple: in `steal_task()`, Pass 0 (fast pass) only steals from a busy worker if `n >= 16` (so a spawner loop always builds up at least 16 tasks before any thief touches its `head`, meaning every steal takes **at least 8 tasks at once**!). If Pass 0 finds nothing across all workers, **Pass 1 steals any `n >= 1`!**
   - Trace what that 2-line rule (`if (pass == 0 && victim->busy && n < 16) continue;`) does!
     - When `W0` is spawning in a loop, thieves on Pass 0 leave `W0` alone while `n < 16` (~3 microseconds), and the moment `n` hits 16–64, a thief takes **8–32 tasks in one CAS**!
     - If `W0` only spawned 1 task and is doing CPU work, the thief finishes Pass 0 in ~100 ns, enters Pass 1 (`pass == 1`), and steals that 1 task immediately!
     - Zero latency penalty for 1-task spawns, and **minimum 8–16x reduction in steals** for loop spawns!

##### Mechanism B (Even stronger — Buffered `tail` publication or Batch-Threshold Overflow):
Alternatively (or in addition):
- What if `W0` keeps `w->local_tail` (non-atomic) and only publishes `atomic_store_release(&r->tail, w->local_tail)` (and calls `notify()`) **every 32 spawns OR whenever the running task yields/parks/finishes**?
- Think about what happens if `r->tail` is published every 32 spawns (and flushed in the scheduler loop whenever `run_task` returns):
  1. While `W0` is inside the `for` loop spawning, `W0` writes 32 tasks to `r->buf` with **zero cache-line invalidations of `r->tail`** and **zero `notify()` calls** for 31 out of 32 spawns!
  2. On the 32nd spawn, `W0` publishes `r->tail += 32` and calls `notify()` **once**.
  3. The first thief to look at `W0` sees `tail - real == 32` and steals **16 tasks in one CAS**!
  4. If `W0` only spawns 1 task and then does an `Io` wait (like `join` or `sleep` or `scope` end), `run_task` returns to `W0`'s scheduler loop, which immediately flushes `r->tail = w->local_tail` and calls `notify()` — so a 1-task spawn is published within nanoseconds as soon as the parent hits any scheduling point!
  5. What if a task spawns 1 child and then computes purely for 100 ms without suspending? To cover that case without delay, if `local_tail - published_tail == 1` **and** `published_tail == cached_steal` (the published ring is completely empty), publish the **first** task immediately, and then buffer subsequent spawns until `local_tail - published_tail >= 32` or `run_task` returns!
  - Let's trace that!
    - **1st spawn when ring is empty:** Published immediately (`published_tail = local_tail`) so if the parent only spawns 1 task and does pure CPU work for 100 ms, a thief can steal that 1 task immediately.
    - **2nd..32nd spawn while ring is non-empty:** Buffered in `w->local_tail` until either `local_tail - published_tail == 32` **or** `run_task` returns!
    - That gives **instant publication for 1-off spawns** AND **32-task batch publication for spawn loops**!

---

#### 4. [Fix 3 — Idea (1) & (5)] Stopping the 280,000 Park/Wake Thrash and 1.23M `notify()` Calls

Look at your park/wake numbers:
> *"notify() 1.23M calls, of which 116k actually woke a parked worker; 228k-280k parks"*

Why are workers parking 280,000 times during a 300 ms spawn loop?
Because when a searcher scans the 30 workers once and comes up empty, it **immediately decrements `searching` and parks in the kernel (`os_sync_wait_on_address`)**!
And then 200 ns later, `W0` calls `notify()`, sees `searching == 0` (or wakes a worker), and does a kernel `os_sync_wake_by_address_any` syscall!

Fix both sides of this thrash:

1. **On the Searcher side (Idea 1 — Spin with pause/backoff before parking):**
   Before a searching worker gives up and goes to sleep in the kernel:
   - Run **4 steal rounds** (just like Go's `findrunnable`).
   - Between round `k` and `k+1` (`k = 0..3`), execute `1 << (k + 4)` iterations of `__builtin_arm_yield()` / `_mm_pause()` (16, 32, 64, 128 yields $\approx 0.1\,\mu\text{s} \to 1\,\mu\text{s}$ total spin window), checking `global_batches` before each round.
   - Only after all 4 rounds find no work does the worker decrement `searching`, re-check queues once (to prevent lost wakeups), and call `os_sync_wait_on_address` / `futex_wait`.
   - Why this works: during that ~1–2 $\mu$s pause window, the searcher is **not hammering `W0`'s cache lines** (giving `W0` clear air to push 32–64 tasks!), AND the searcher stays in `searching > 0` state in userspace so `W0`'s `notify()` is a single relaxed load (`if (atomic_load_relaxed(&searching) > 0) return;`) with **zero kernel syscalls**!

2. **On the Producer side (Idea 5 — When `spawn` should call `notify()`):**
   - Look at `notify()`: `W0` called `notify()` **1,230,000 times**!
   - Why should `spawn` call `notify()` on every single task?
   - If you use **buffered `tail` publication (every 32 spawns)** from Problem 3, `notify()` is called at most **once per 32 spawns** (`1,000,000 / 32 = 31,250` calls instead of `1,230,000`!).
   - And inside `notify()`, the fast check is:
     ```c
     if (atomic_load_explicit(&searching, memory_order_relaxed) > 0 ||
         atomic_load_explicit(&idlers, memory_order_relaxed) == 0) {
       return;
     }
     ```
     (Only perform the `seq_cst` fence + wake when transitioning the ring from **empty to non-empty** or when pushing a batch to `global_batches`!)

---

### Summary: The Exact Combination to Build

All five of your ideas fit together into ~40 lines of C with no new data structures:

1. **Pad `fly_ring` to 128-byte cache lines and cache `steal` (Idea 4):**
   - Put `head` on its own `alignas(128)` cache line, `tail` + `cached_steal` + `local_tail` on a second `alignas(128)` cache line, and `buf` on a third.
   - In `ring_push`, only load `r->head` when `(uint32_t)(local_tail - cached_steal) >= RING_CAP`.
2. **Batch `tail` publication + `notify()` every 32 spawns (Ideas 3 & 5):**
   - In `spawn`, write to `r->buf[local_tail & 255]` and increment `w->local_tail`.
   - Publish `atomic_store_release(&r->tail, w->local_tail)` and call `notify()` only when:
     - `(w->local_tail - w->published_tail) >= 32`, OR
     - `w->published_tail == w->cached_steal` (the first task pushed to an empty ring, so single spawns are visible immediately), OR
     - in the worker loop as soon as `run_task()` returns (flushing any remaining `local_tail > published_tail`).
3. **Two-pass steal + 4-round pause backoff before kernel park (Ideas 1 & 2):**
   - In `steal_task(pass)`, on `pass == 0` skip any busy victim (`victim->busy`) with `(tail - real) < 8`; on `pass > 0` steal any `(tail - real) >= 1`.
   - A searcher runs up to 4 rounds with `16, 32, 64, 128` `yield`/`pause` instructions between rounds before decrementing `searching` and parking in the kernel.

With this combination:
- `W0` only touches `r->head` once per 256 spawns and only publishes `r->tail` + calls `notify()` once per 32 spawns.
- Every thief steal grabs at least 16 tasks at a time (~30,000 steals total instead of 1,010,000).
- Kernel parks during the spawn phase drop from 280,000 to near zero, and spawn time will hold steady at the **~230–300 ms** you saw in your backoff experiment (finishing the benchmark at ~2250–2300 ms, beating Tokio's 2395 ms).
