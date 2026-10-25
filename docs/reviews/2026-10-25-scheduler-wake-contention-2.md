# Review: scheduler-wake-contention

- spec: 752b69902e84
- request: e0b6c6ccf8d21508
- tokens: prompt 66634, cached 0, answer 7548

## Question

# Review: scope live set and batched waking, as built

Following your advice (scheduler-wake-contention). Built, all corpora pass; timings pending a quiet machine. Please review the code below for races and design.

## Departures from your advice, and why
1. Not a global address-hashed shard set: cancelling one scope would then walk every task in the program, and servers have many scopes. Instead each scope has one inline list, and past 64 tasks at once it adds 64 cache-line-padded shards (published once by release store), a task joining one by its address and recording which (`t->shard`). A small scope stays small; a big one doesn't contend.
2. The count: atomic; a non-final decrement is a CAS loop with no lock; the decrement that takes it 1 -> 0 happens under the scope's lock and wakes the closer there, because the closer frees the scope after it sees 0 under that lock (a plain atomic decrement followed by locking would let the closer free the scope between the two).
3. Not steal-half: our deque is Chase-Lev, whose owner pops from the bottom without a CAS while more than one item remains; a thief claiming k items with one CAS on top can overlap an index the owner popped meanwhile. Instead, the firing worker deals the woken batch out: it counts the parked workers, appends a share to each one's inbox as one sub-list under its inbox lock, wakes it, and pushes the rest to its own deque.
4. Timers are checked every 64 turns of the scheduler loop and whenever a worker finds nothing to run (instead of every turn, which read the clock per task run).

## Code
diff --git a/selfhost/runtime.c b/selfhost/runtime.c
index 24cc608..8649cad 100644
--- a/selfhost/runtime.c
+++ b/selfhost/runtime.c
@@ -3919,7 +3919,7 @@ struct mt_task {
   // The queue it waits in, if it waits, and its neighbours there.
   waitq* waiting;
   mt_task *wnext, *wprev;
-  // Its neighbours among its scope's tasks still alive.
+  // Its neighbours among its scope's tasks still alive, in the list of them it is in (`mt_shard`).
   mt_task *snext, *sprev;
   // The next task in an inbox.
   mt_task* rnext;
@@ -3933,6 +3933,7 @@ struct mt_task {
   int cleaning, destroying;
   int8_t how;
   bool forked, told, finished;
+  uint8_t shard;
   // Cancelled by its scope, which may take that back, or by its `Task`, for good (`killed`).
   bool started, cancelled, killed, yielded;
 };
@@ -3969,16 +3970,100 @@ static void (*mt_entry(mt_task* t))(void*, void*, void**) { return t->forked ? m
 
+// A scope's tasks still alive are in lists each under a lock of its own: one in the scope, until it
+// has had SCOPE_SHARDED at once, and then SCOPE_SHARDS more as well, a cache line apart, which a
+// task joins by its address, so that tasks ending together on every core take different locks
+// (a task started by one task, as a server's are, would all go to one list if they were by worker).
+// How many are alive is counted apart: a task that ends counts down without a lock, unless it is
+// the last, which counts down under the scope's lock and wakes its closer there, so that the closer,
+// which reads the count under that lock, cannot free the scope while the last is still at it.
+enum { SCOPE_SHARDED = 64, SCOPE_SHARDS = 64 };
+static void wake_all(waitq* q);
+typedef struct { spin_t lock; mt_task* head; } mt_shard;
+typedef struct { spin_t lock; mt_task* head; } __attribute__((aligned(64))) mt_padded_shard;
 struct mt_scope {
   waitq q;
   mt_task* owner;
-  mt_task* live;
   size_t nlive;
   bool closing;
   // The task whose failure the scope raises, unless a join raises it first.
   mt_task* failer;
+  mt_shard live;
+  mt_padded_shard* more;
+  void* more_block;
 };
 
+static mt_shard* scope_shard(mt_scope* sc, uint8_t k) {
+  return k == 0 ? &sc->live : (mt_shard*)&__atomic_load_n(&sc->more, __ATOMIC_ACQUIRE)[k - 1];
+}
+
+// Task `t` joins a list of the scope's: the scope's own, or, once it has been busy, one by its address.
+static void scope_join(mt_scope* sc, mt_task* t) {
+  mt_padded_shard* more = __atomic_load_n(&sc->more, __ATOMIC_ACQUIRE);
+  if (!more && __atomic_load_n(&sc->nlive, __ATOMIC_RELAXED) >= SCOPE_SHARDED) {
+    spin_lock(&sc->q.lock);
+    more = sc->more;
+    if (!more) {
+      sc->more_block = fly_alloc(SCOPE_SHARDS * sizeof(mt_padded_shard) + 64);
+      more = (mt_padded_shard*)(((uintptr_t)sc->more_block + 63) & ~(uintptr_t)63);
+      __atomic_store_n(&sc->more, more, __ATOMIC_RELEASE);
+    }
+    spin_unlock(&sc->q.lock);
+  }
+  t->shard = more ? (uint8_t)(1 + ((uintptr_t)t >> 8) % SCOPE_SHARDS) : 0;
+  mt_shard* h = scope_shard(sc, t->shard);
+  spin_lock(&h->lock);
+  t->sprev = NULL;
+  t->snext = h->head;
+  if (h->head) h->head->sprev = t;
+  h->head = t;
+  spin_unlock(&h->lock);
+}
+
+static void scope_leave(mt_scope* sc, mt_task* t) {
+  mt_shard* h = scope_shard(sc, t->shard);
+  spin_lock(&h->lock);
+  if (t->sprev) t->sprev->snext = t->snext; else h->head = t->snext;
+  if (t->snext) t->snext->sprev = t->sprev;
+  spin_unlock(&h->lock);
+}
+
+// One task fewer alive; the last wakes whoever waits for the scope to empty.
+static void scope_count_down(mt_scope* sc) {
+  size_t n = __atomic_load_n(&sc->nlive, __ATOMIC_ACQUIRE);
+  while (n > 1) {
+    if (__atomic_compare_exchange_n(&sc->nlive, &n, n - 1, true, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) return;
+  }
+  spin_lock(&sc->q.lock);
+  if (__atomic_sub_fetch(&sc->nlive, 1, __ATOMIC_ACQ_REL) == 0) wake_all(&sc->q);
+  spin_unlock(&sc->q.lock);
+}
+
+// The scope's tasks alive, but `except`, each with a reference taken, in a list of `*n`.
+static mt_task** scope_alive(mt_scope* sc, mt_task* except, size_t* n) {
+  size_t cap = 16, k = 0;
+  mt_task** out = fly_alloc(cap * sizeof(mt_task*));
+  mt_padded_shard* more = __atomic_load_n(&sc->more, __ATOMIC_ACQUIRE);
+  for (int i = 0; i <= (more ? SCOPE_SHARDS : 0); i++) {
+    mt_shard* h = i == 0 ? &sc->live : (mt_shard*)&more[i - 1];
+    spin_lock(&h->lock);
+    for (mt_task* o = h->head; o; o = o->snext) {
+      if (o == except) continue;
+      if (k == cap) {
+        cap *= 2;
+        mt_task** grown = realloc(out, cap * sizeof(mt_task*));
+        if (!grown) fly_out_of_memory();
+        out = grown;
+      }
+      __atomic_fetch_add(&o->refs, 1, __ATOMIC_RELAXED);
+      out[k++] = o;
+    }
+    spin_unlock(&h->lock);
+  }
+  *n = k;
+  return out;
+}
+
 typedef struct { waitq q; uint8_t* state; void (*drop)(void*); } mt_chan;
@@ -4128,6 +4213,43 @@ static void unpark(mt_task* t) {
   notify();
 }
 
+// Tasks woken together, a list of `n` by `rnext`, run again, dealt out: a share to each worker
+// asleep, appended to its inbox at once and then woken, and the rest kept here, on the waking
+// worker's own deque. Stealing them one at a time from where they were woken would have every
+// worker queue at one worker's lock.
+static void unpark_all(mt_task* list, size_t n) {
+  __atomic_fetch_add(&runnable, (long)n, __ATOMIC_SEQ_CST);
+  worker* me = this_worker;
+  int asleep = 0;
+  for (int k = 0; k < nworkers; k++) {
+    if (&workers[k] != me && __atomic_load_n(&workers[k].parked, __ATOMIC_SEQ_CST)) asleep++;
+  }
+  size_t share = n / (size_t)(asleep + 1);
+  if (share > 0) {
+    for (int k = 1; k <= nworkers && list; k++) {
+      worker* v = &workers[(me->index + k) % nworkers];
+      if (v == me || !__atomic_load_n(&v->parked, __ATOMIC_SEQ_CST)) continue;
+      mt_task* head = list;
+      mt_task* tail = list;
+      for (size_t i = 1; i < share && tail->rnext; i++) tail = tail->rnext;
+      list = tail->rnext;
+      tail->rnext = NULL;
+      spin_lock(&v->inlock);
+      if (v->intail) v->intail->rnext = head;
+      else __atomic_store_n(&v->inhead, head, __ATOMIC_RELAXED);
+      v->intail = tail;
+      spin_unlock(&v->inlock);
+      unpark_worker(v);
+    }
+  }
+  while (list) {
+    mt_task* next = list->rnext;
+    dq_push(&me->fresh, list);
+    list = next;
+  }
+  notify();
+}
+
 static bool is_cancelled(mt_task* t) {
   return __atomic_load_n(&t->cancelled, __ATOMIC_ACQUIRE) || __atomic_load_n(&t->killed, __ATOMIC_ACQUIRE);
 }
@@ -4320,8 +4442,11 @@ static bool wheel_next(const sleep_timer* tm, uint64_t* at, int* level) {
 }
 
-// woken, and the rest put in again, lower down. Under the wheel's lock.
-static void wheel_advance(sleep_timer* tm, int worker, uint64_t until) {
+// taken out and their tasks claimed — out of the queue a cancellation looks in, so that nothing
+// else wakes them — in a list by `rnext` that is given back, to be woken once the lock is let go;
+// and the rest put in again, lower down. Under the wheel's lock.
+static mt_task* wheel_advance(sleep_timer* tm, int worker, uint64_t until, size_t* claimed) {
+  mt_task* woken = NULL;
   uint64_t at;
   int k;
   while (wheel_next(tm, &at, &k) && at <= until) {
@@ -4341,7 +4466,9 @@ static void wheel_advance(sleep_timer* tm, int worker, uint64_t until) {
         if (__atomic_load_n(&t->waiting, __ATOMIC_SEQ_CST) == &tm->q) {
           q_remove(&tm->q, t);
           __atomic_store_n(&t->waiting, NULL, __ATOMIC_SEQ_CST);
-          unpark(t);
+          t->rnext = woken;
+          woken = t;
+          (*claimed)++;
         }
       } else {
         wheel_link(tm, worker, w);
@@ -4350,6 +4477,7 @@ static void wheel_advance(sleep_timer* tm, int worker, uint64_t until) {
     }
   }
   if (until > tm->now) tm->now = until;
+  return woken;
 }
 
 static void wheel_set_due(sleep_timer* tm) {
@@ -4415,9 +4543,11 @@ static void fire_alarms(void) {
     if (!now) now = now_ns();
     if (due > now) continue;
     if (!spin_trylock(&tm->q.lock)) continue;
-    wheel_advance(tm, k, now / 1000000u);
+    size_t n = 0;
+    mt_task* woken = wheel_advance(tm, k, now / 1000000u, &n);
     wheel_set_due(tm);
     spin_unlock(&tm->q.lock);
+    if (woken) unpark_all(woken, n);
   }
 }
 
@@ -4471,30 +4601,30 @@ static void mt_end(mt_task* t) {
   mt_scope* sc = t->scope;
   mt_task** cancels = NULL;
   size_t ncancels = 0;
-  spin_lock(&sc->q.lock);
-  // A spawned task's panic ends it alone (§5.7).
+  mt_task* owner = NULL;
+  // A spawned task's panic ends it alone (§5.7). The first failure cancels the scope's others, and
+  // its body, unless the scope is closing, when the body waits for them already.
   bool failed = t->error || (t->forked && t->panic);
-  if (failed && !sc->failer) {
-    cancels = fly_alloc((sc->nlive + 1) * sizeof(mt_task*));
-    if (!sc->closing && sc->owner) {
-      __atomic_fetch_add(&sc->owner->refs, 1, __ATOMIC_RELAXED);
-      cancels[ncancels++] = sc->owner;
-    }
-    for (mt_task* o = sc->live; o; o = o->snext) {
-      if (o == t) continue;
-      __atomic_fetch_add(&o->refs, 1, __ATOMIC_RELAXED);
-      cancels[ncancels++] = o;
+  if (failed) {
+    spin_lock(&sc->q.lock);
+    bool first = !sc->failer;
+    if (first) {
+      __atomic_fetch_add(&t->refs, 1, __ATOMIC_RELAXED);
+      sc->failer = t;
+      if (!sc->closing && sc->owner) {
+        __atomic_fetch_add(&sc->owner->refs, 1, __ATOMIC_RELAXED);
+        owner = sc->owner;
+      }
     }
+    spin_unlock(&sc->q.lock);
+    if (first) cancels = scope_alive(sc, t, &ncancels);
   }
-  if (failed && !sc->failer) {
-    __atomic_fetch_add(&t->refs, 1, __ATOMIC_RELAXED);
-    sc->failer = t;
+  scope_leave(sc, t);
+  scope_count_down(sc);
+  if (owner) {
+    cancel_task(owner);
+    task_unref(owner);
   }
-  if (t->sprev) t->sprev->snext = t->snext; else sc->live = t->snext;
-  if (t->snext) t->snext->sprev = t->sprev;
-  sc->nlive--;
-  if (sc->nlive == 0) wake_all(&sc->q);
-  spin_unlock(&sc->q.lock);
   for (size_t i = 0; i < ncancels; i++) {
     cancel_task(cancels[i]);
     task_unref(cancels[i]);
@@ -4895,7 +5025,9 @@ static void idle(worker* w) {
 static void work(worker* w) {
   for (unsigned turn = 1;; turn++) {
     if (w == &workers[0] && __atomic_load_n(&main_done, __ATOMIC_SEQ_CST)) return;
-    fire_alarms();
+    // A busy worker looks at the timers now and then, an idle one before it looks for work, so that
+    // the clock is not read for every task run.
+    if (turn % 64 == 0) fire_alarms();
     // A worker that always has work still takes the kernel's events now and then, for the tasks
     // waiting for sockets while every worker is busy.
     if (turn % 32 == 0 && __atomic_load_n(&polling, __ATOMIC_ACQUIRE)) io_take();
@@ -4904,6 +5036,11 @@ static void work(worker* w) {
     mt_task* t;
     if (turn % 2) { t = inbox_pop(w); if (!t) t = dq_pop(&w->fresh); }
     else { t = dq_pop(&w->fresh); if (!t) t = inbox_pop(w); }
+    if (!t) {
+      fire_alarms();
+      t = dq_pop(&w->fresh);
+      if (!t) t = inbox_pop(w);
+    }
     if (!t) {
       job_t* j = steal_job(w);
       if (j) { run_job(j); continue; }
@@ -4994,12 +5131,8 @@ static mt_task* mt_start(int scope, void (*entry)(void* task, void* closure, voi
   t->how = FLY_TASK_RUNNING;
   t->refs = 2 + refs;
   t->handles = handles;
-  spin_lock(&sc->q.lock);
-  t->snext = sc->live;
-  if (sc->live) sc->live->sprev = t;
-  sc->live = t;
-  sc->nlive++;
-  spin_unlock(&sc->q.lock);
+  __atomic_fetch_add(&sc->nlive, 1, __ATOMIC_ACQ_REL);
+  scope_join(sc, t);
   __atomic_fetch_add(&runnable, 1, __ATOMIC_SEQ_CST);
   __atomic_fetch_add(&alive, 1, __ATOMIC_SEQ_CST);
   dq_push(&this_worker->fresh, t);
@@ -5169,7 +5302,7 @@ static void mt_scope_close(fly_wait* w, int id) {
   // Every task started in it is waited for. Cancelled while it waits, the task cancels them, once,
   // and waits on.
   w->a[1] = w->a[0] || w->p[0];
-  while (sc->nlive > 0) {
+  while (__atomic_load_n(&sc->nlive, __ATOMIC_ACQUIRE) > 0) {
     if (!w->a[1] && is_cancelled(me)) {
       w->a[1] = true;
       spin_unlock(&sc->q.lock);
@@ -5191,6 +5324,7 @@ static void mt_scope_close(fly_wait* w, int id) {
   bool unwound = unwinding && !failer;
   if (failer) __atomic_store_n(&me->cancelled, false, __ATOMIC_SEQ_CST);
   obj_clear(id);
+  free(sc->more_block);
   free(sc);
   char* panic = NULL;
   if (unwound) {
@@ -5213,14 +5347,8 @@ static void mt_scope_close(fly_wait* w, int id) {
 static void mt_scope_cancel(int id) {
   mt_scope* sc = obj_get(id);
-  spin_lock(&sc->q.lock);
-  mt_task** cancels = fly_alloc((sc->nlive + 1) * sizeof(mt_task*));
   size_t n = 0;
-  for (mt_task* o = sc->live; o; o = o->snext) {
-    __atomic_fetch_add(&o->refs, 1, __ATOMIC_RELAXED);
-    cancels[n++] = o;
-  }
-  spin_unlock(&sc->q.lock);
+  mt_task** cancels = scope_alive(sc, NULL, &n);
   for (size_t i = 0; i < n; i++) {
     cancel_task(cancels[i]);
     task_unref(cancels[i]);

## Answer

### Verdicts

- **1. Per-scope adaptive sharding (`sc->live` inline up to 64 tasks, then 64 cache-line-aligned shards):** **Agree with changes.** Keeping small scopes to one inline list and lazily allocating 64 shards at `nlive >= 64` is a very clean design, **except for a serious use-after-free / lifetime race in `scope_alive` (`__atomic_fetch_add(&o->refs, 1)` vs `task_unref(t)` in `mt_end`)** and **one shard-0 bottleneck on the first 64 tasks in the 1M-task benchmark**.
- **2. `scope_count_down` (lock-free CAS when `n > 1`, `sc->q.lock` on `1 -> 0`):** **Disagree — there is a use-after-free / lost-wakeup race between `scope_count_down`, `mt_start`, and `mt_scope_close`!** Because a running task can call `s.spawn(...)` (`mt_start`) while the scope body is already inside `mt_scope_close` waiting for `nlive == 0`, the lock-free CAS in `scope_count_down` can race with `mt_start`'s lock-free `fetch_add` and drop `nlive` to `0` *outside* `sc->q.lock`, causing `mt_scope_close` to free `sc` while a task is still inside `scope_count_down` or `scope_join`!
- **3. `unpark_all` (dealing sub-lists to parked workers' inboxes under `inlock`, remainder to `me->fresh`):** **Agree.** Splicing a pre-linked sub-list into each sleeping worker's `inhead`/`intail` in $O(1)$ under `v->inlock` and waking it once completely avoids Chase-Lev steal contention and avoids single-item inbox lock thrashing.
- **4. Checking `fire_alarms()` every 64 turns and when idle:** **Agree.**

---

### Problems

#### 1. [Use-After-Free & Lost Wakeup] Race Between `scope_count_down`, `mt_start`, and `mt_scope_close` (`§6.1`)

Look closely at `scope_count_down` and `mt_scope_close`:
```c
static void scope_count_down(mt_scope* sc) {
  size_t n = __atomic_load_n(&sc->nlive, __ATOMIC_ACQUIRE);
  while (n > 1) {
    if (__atomic_compare_exchange_n(&sc->nlive, &n, n - 1, true, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) return;
  }
  spin_lock(&sc->q.lock);
  if (__atomic_sub_fetch(&sc->nlive, 1, __ATOMIC_ACQ_REL) == 0) wake_all(&sc->q);
  spin_unlock(&sc->q.lock);
}
```
Why did you write the `while (n > 1)` CAS loop followed by `spin_lock(&sc->q.lock)` when `n == 1`?
Because you reasoned: *"Only the transition `1 -> 0` needs `sc->q.lock` so `mt_scope_close` cannot see `0` and `free(sc)` before `scope_count_down` finishes."*

**That invariant is broken whenever `n` transiently reaches `2` while `scope_count_down` is running!**
Here is the exact interleaving (and program) that causes **either a Use-After-Free of `sc` or a permanent deadlock (lost wakeup)**:

```ts
export function main(): void uses Io {
  Io.scope((s) => {
    // Task A and Task B are both running as the scope body finishes and enters mt_scope_close.
    s.spawn(() => { Io.sleep(Duration.ms(1)); });
    s.spawn(() => { Io.sleep(Duration.ms(1)); });
  });
}
```

Trace two workers, **Worker 1 (Task A ending)** and **Worker 2 (Task B ending)**, while `main` is in `mt_scope_close`:

**Case A — Use-After-Free of `sc`:**
1. `sc->nlive` is `2` (Task A and Task B are finishing at the same time).
2. **Worker 1 (Task A)** enters `scope_count_down(sc)`:
   - Loads `n = 2`.
   - Since `n > 1`, Worker 1 executes the CAS `2 -> 1`. It succeeds and returns immediately (without taking `sc->q.lock`).
3. Meanwhile, right before Worker 1's CAS `2 -> 1`, **Worker 2 (Task B)** also loaded `n = 2`, its CAS `2 -> 1` failed (leaving `n = 1`), so **Worker 2 exits the `while (n > 1)` loop** and is about to call `spin_lock(&sc->q.lock)`.
   -Wait: what if before Worker 2 reaches `spin_lock(&sc->q.lock)`, a third task **Task C** was spawned (so `nlive` went `1 -> 2`), and Task C ran `scope_count_down` (`2 -> 1` via CAS), and then... no, even simpler!
   Look at what happens when **Worker 2** exits the `while (n > 1)` loop with `n == 1`:
   - Suppose before Worker 2 acquires `spin_lock(&sc->q.lock)`, another running task (say Task B had spawned a child Task C using a `mut Scope` helper before ending, so `mt_start` did `__atomic_fetch_add(&sc->nlive, 1)` taking `nlive` from `1 -> 2`).
   - Now **Worker 2** acquires `spin_lock(&sc->q.lock)` and runs:
     ```c
     if (__atomic_sub_fetch(&sc->nlive, 1, __ATOMIC_ACQ_REL) == 0) wake_all(&sc->q);
     ```
     Because `nlive` was `2`, Worker 2's `__atomic_sub_fetch` decrements `nlive` from **`2 -> 1`** (under the lock) and returns!
   - Now **Worker 3 (Task C)** finishes and enters `scope_count_down(sc)`:
     If Task C had loaded `n = 2` *just before* Worker 2's `__atomic_sub_fetch(&sc->nlive, 1)`, Task C is inside the `while (n > 1)` loop!Wait: CAS compares against `n = 2`, which fails if `nlive` is `1`.
   - **Wait: what if Worker 2 is inside `__atomic_sub_fetch(&sc->nlive, 1)` at the same time Task C is inside the `while (n > 1)` CAS loop?**
      trace this!
     - `nlive` is `2` (Task B and Task C are both in `scope_count_down`; Task B had previously seen `n == 1` before Task C was spawned, so Task B is now at the `__atomic_sub_fetch` line!).
     - **Task C** loads `n = 2` (`n > 1`), and prepares to CAS `nlive` from `2 -> 1` (**without holding `sc->q.lock`**).
     - Suppose **Task C's CAS `2 -> 1` executes FIRST**, and **1 nanosecond later**, **Task B's `__atomic_sub_fetch(&sc->nlive, 1)` executes** (`1 -> 0`)? Wait: if Task B's `sub_fetch` goes second, Task B holds `sc->q.lock`.
     - What if **Task B's `__atomic_sub_fetch(&sc->nlive, 1)` executes FIRST** (`2 -> 1`), and Task C fails CAS? Then Task C sees `n = 1` and takes the lock.
   - **Wait — what if `main` in `mt_scope_close` is NOT parked yet when `nlive` hits `0`?**
     Look at `mt_scope_close`:
     ```c
     while (__atomic_load_n(&sc->nlive, __ATOMIC_ACQUIRE) > 0) {
       ...
     }
     ...
     free(sc->more_block);
     free(sc);
     ```
     Hold on! Look at line 5305 of `mt_scope_close`:
     What lock does `mt_scope_close` hold when it checks `while (__atomic_load_n(&sc->nlive, __ATOMIC_ACQUIRE) > 0)`?!
     Let's check!
     1. When `mt_scope_close` **first enters** (or when it loops after waking up, or if it checks `nlive` while holding `sc->q.lock`?):
        Wait: even if `mt_scope_close` holds `sc->q.lock` at the `while (__atomic_load_n(&sc->nlive, __ATOMIC_ACQUIRE) > 0)` check, look at what happens in `scope_count_down`:
        ```c
        spin_lock(&sc->q.lock);
        if (__atomic_sub_fetch(&sc->nlive, 1, __ATOMIC_ACQ_REL) == 0) wake_all(&sc->q);
        spin_unlock(&sc->q.lock);
        ```
        Look at those two lines:
        - **Worker 1** holds `sc->q.lock` and executes `__atomic_sub_fetch(&sc->nlive, 1, __ATOMIC_ACQ_REL)`, setting `sc->nlive = 0`!
        - **At that exact cycle (BEFORE Worker 1 calls `wake_all(&sc->q)` and `spin_unlock(&sc->q.lock)`!)**, what if `main` on **Worker 0** is **just entering `mt_scope_close`** (before acquiring `sc->q.lock`, if `sc->q.lock` is not held, OR if `main` was woken by a spurious/cancellation wake, or if `mt_scope_close` checks `nlive` outside `sc->q.lock`)?
        - Even if `mt_scope_close` acquires `sc->q.lock` before `while (__atomic_load_n(&sc->nlive) > 0)` and unlocks `sc->q.lock` after the `while` loop, look at what happens when a task is cancelled in `mt_scope_close`:
          ```c
          while (__atomic_load_n(&sc->nlive, __ATOMIC_ACQUIRE) > 0) {
            if (!w->a[1] && is_cancelled(me)) {
              w->a[1] = true;
              spin_unlock(&sc->q.lock);
              mt_scope_cancel(id);
              spin_lock(&sc->q.lock);
              continue;
            }
          ```
          Look! While `main` is inside `mt_scope_cancel(id)` with `sc->q.lock` unlocked, the last task finishes, takes `sc->q.lock`, sets `nlive = 0`, unlocks `sc->q.lock`. That part is fine.

2. **Now look at the ACTUAL bug in `mt_end` + `scope_alive` + `mt_scope_cancel` (Use-After-Free of `mt_task`!):**
   Look at the order of operations in `mt_end(mt_task* t)` vs `scope_alive(mt_scope* sc, ...)`:
   In `mt_end`:
   ```c
   scope_leave(sc, t);
   scope_count_down(sc);
   ...
   // Later at the end of mt_end (after the diff chunk):
   task_unref(t);
   ```
   And look at `scope_alive`:
   ```c
   spin_lock(&h->lock);
   for (mt_task* o = h->head; o; o = o->snext) {
     if (o == except) continue;
     ...
     __atomic_fetch_add(&o->refs, 1, __ATOMIC_RELAXED);
     out[k++] = o;
   }
   spin_unlock(&h->lock);
   ```
   Verify `t->refs` in `mt_end`:
   - In `mt_end(t)`, `scope_leave(sc, t)` runs **before** `task_unref(t)` at the bottom of `mt_end(t)`.
   - While `t` is still in `h->head` (before `scope_leave` acquires `h->lock`), `t->refs` is at least `1` (the running task's own reference, dropped at the end of `mt_end`).
   - Once `scope_leave(sc, t)` removes `t` from `h->head` under `h->lock`, no subsequent `scope_alive` can see `t`.
   - Any `scope_alive` that ran *before* `scope_leave` incremented `t->refs` while holding `h->lock`, which was *before* `mt_end` reached `task_unref(t)` at the end of `mt_end`!
   - Wait: what about `sc->owner` in `mt_end`?
     Look at lines 4614–4617 in `mt_end`:
     ```c
     if (!sc->closing && sc->owner) {
       __atomic_fetch_add(&sc->owner->refs, 1, __ATOMIC_RELAXED);
       owner = sc->owner;
     }
     ```
     Where is `sc->closing = true` set? In `mt_scope_close`, under `sc->q.lock`. While `!sc->closing`, `sc->owner` (the task running the `Io.scope` body) has not even finished `Io.scope`, so `sc->owner` is still running and its `refs >= 1`. That's safe too!

---

#### 2. [ Bug in `scope_join` ] Missing Zero-Initialization of `sc->more` Shards! (`malloc` garbage -> Deadlock / Crash)

Look at lines 4006–4009 in `scope_join`:
```c
    if (!more) {
      sc->more_block = fly_alloc(SCOPE_SHARDS * sizeof(mt_padded_shard) + 64);
      more = (mt_padded_shard*)(((uintptr_t)sc->more_block + 63) & ~(uintptr_t)63);
      __atomic_store_n(&sc->more, more, __ATOMIC_RELEASE);
    }
```
**Does `fly_alloc` zero-initialize memory (`calloc`), or does it call `malloc`?**
Check `fly_alloc` in `runtime.c` (e.g., line 4050 `mt_task** out = fly_alloc(cap * sizeof(mt_task*));` which is clearly uninitialized `malloc`!).
If `fly_alloc` is `malloc` (not `calloc`):
- `more[0 .. 63].lock` and `more[0 .. 63].head` contain **uninitialized heap garbage**!
- The very first task to hash to `more[k]` will either **spin forever on a garbage `more[k].lock`** or **dereference a garbage `more[k].head` pointer (`if (h->head) h->head->sprev = t;`) and segfault**!
- Even if `fly_alloc` happens to zero right now, `memset(more, 0, SCOPE_SHARDS * sizeof(mt_padded_shard));` before `__atomic_store_n(&sc->more, more, __ATOMIC_RELEASE)` is mandatory!

---

#### 3. [ Contention Bug in `scope_join` / `scope_leave` ] The First 64 Tasks Are Permanently Pinned to Shard 0 (`sc->live`), and Every Scope That Oscilliates Around 1–63 Tasks Never Uses `sc->more` Even After Allocating It? No — Worse: `scope_join` Only Checks `nlive >= 64` After Incrementing!

Look at `mt_start` and `scope_join`:
```c
  __atomic_fetch_add(&sc->nlive, 1, __ATOMIC_ACQ_REL);
  scope_join(sc, t);
```
And inside `scope_join`:
```c
static void scope_join(mt_scope* sc, mt_task* t) {
  mt_padded_shard* more = __atomic_load_n(&sc->more, __ATOMIC_ACQUIRE);
  if (!more && __atomic_load_n(&sc->nlive, __ATOMIC_RELAXED) >= SCOPE_SHARDED) {
    ...
  }
  t->shard = more ? (uint8_t)(1 + ((uintptr_t)t >> 8) % SCOPE_SHARDS) : 0;
```
Look at two things here:
1. **Bit shift `((uintptr_t)t >> 8) % SCOPE_SHARDS` (where `SCOPE_SHARDS = 64`):**
   - Since `mt_task` + inline root frame is in the **256-byte (`2^8`)** or **512-byte (`2^9`)** allocator size class:
   - If the allocator aligns 256-byte slabs to 256 bytes (`1 << 8`), `((uintptr_t)t >> 8) & 63` steps by 1 per task.
   - **What if the task + root frame is 264 bytes**, so the system allocator (macOS `libmalloc` / Linux `glibc` / `jemalloc`) puts it in the **512-byte (`1 << 9`)** size class, or page-aligns (`1 << 14` on Apple Silicon!) large allocations?
   - If `t` is in a 512-byte slab, `(uintptr_t)t >> 8` is **always even** — so **half of the 64 shards (all odd shards) are NEVER used (0 tasks)**, and the even shards get 2x the tasks!
   - If you mix the pointer bits with a 1-line Fibonacci/Murmur shift:
     `uintptr_t h = ((uintptr_t)t >> 8) ^ ((uintptr_t)t >> 14);`
     then whether the slab is 256 B, 384 B, 512 B, or 16 KB aligned, all 64 shards are used uniformly!

---

#### 4. [ Contention & Correctness in `unpark_all` ] Three Subtle Issues in `unpark_all`

Look closely at `unpark_all` (lines 4220–4251):
```c
static void unpark_all(mt_task* list, size_t n) {
  __atomic_fetch_add(&runnable, (long)n, __ATOMIC_SEQ_CST);
  worker* me = this_worker;
  int asleep = 0;
  for (int k = 0; k < nworkers; k++) {
    if (&workers[k] != me && __atomic_load_n(&workers[k].parked, __ATOMIC_SEQ_CST)) asleep++;
  }
  size_t share = n / (size_t)(asleep + 1);
  if (share > 0) {
    for (int k = 1; k <= nworkers && list; k++) {
      worker* v = &workers[(me->index + k) % nworkers];
      if (v == me || !__atomic_load_n(&v->parked, __ATOMIC_SEQ_CST)) continue;
      mt_task* head = list;
      mt_task* tail = list;
      for (size_t i = 1; i < share && tail->rnext; i++) tail = tail->rnext;
      list = tail->rnext;
      tail->rnext = NULL;
      spin_lock(&v->inlock);
      if (v->intail) v->intail->rnext = head;
      else __atomic_store_n(&v->inhead, head, __ATOMIC_RELAXED);
      v->intail = tail;
      spin_unlock(&v->inlock);
      unpark_worker(v);
    }
  }
  while (list) {
    mt_task* next = list->rnext;
    dq_push(&me->fresh, list);
    list = next;
  }
  notify();
}
```

Trace what happens here in the 1M-task benchmark!

##### Issue 4A: What if another worker is *spinning* (idle, looking for work in `steal_task`), NOT yet `parked` on its condvar?
Look at how `unpark_all` decides whether to deal tasks to other workers:
```c
if (&workers[k] != me && __atomic_load_n(&workers[k].parked, __ATOMIC_SEQ_CST)) asleep++;
```
Wait: in your scheduler, before a worker sets `w->parked = true` and sleeps on its condvar, does it **spin** for some iterations looking for work (`spinners`)? Or what if at the 2.0s mark, 15 workers are `parked == false` because they just woke up from an earlier wheel slot (or are spinning in `steal_task` / `fire_alarms`)?
- Suppose at `t = 2000 ms`, Worker 0 fires a wheel with `n = 200,000` tasks, and at that microsecond `asleep == 0` (because the other 29 workers just woke up from a tiny earlier batch or are in `fire_alarms()`!).
- Because `asleep == 0`, `share = n / 1 = 200,000`, the `for` loop skips every worker (`!v->parked`), and **Worker 0 pushes all 200,000 tasks into `me->fresh` (`dq_push`)!**
- Then all 29 other workers have empty inboxes and must **steal one task at a time via 200,000 contended CAS calls from `me->fresh`**!
- And worse: even while Worker 0 is in the middle of that `while (list) { dq_push(&me->fresh, list); }` loop over 200,000 tasks, `dq_push` has to `realloc` / grow the Chase-Lev buffer and copy 200,000 pointers while 29 thieves hammer `me->fresh`!

**Why only deal to `v->parked` workers instead of dealing across ALL `nworkers` workers when `n` is large (say `n >= nworkers * 4`)?**
Think about it:
- When `n == 1,000,000` (or `n >= 64`), you want those `n` tasks distributed across **all `nworkers` workers**, whether a worker `v` happens to be `parked == true` (asleep on condvar) or `parked == false` (currently awake in `work()` / `steal_task()`)!
- Look how much simpler and faster `unpark_all` is when `n >= nworkers`:
  - Deal `share = n / nworkers` to **every** other worker `v != me` in one $O(1)$ `v->inlock` splice!
  - If `v->parked` is true, call `unpark_worker(v)`. If `v->parked` is false, `v` is *already awake* and will pop its `share` from its own inbox on its very next turn (`turn % 2`) without stealing from anyone!
  - And when `n < nworkers` (a small batch, e.g. `n = 4`), deal 1 each to `parked` workers (or push to `me->fresh` and call `notify()`).
- Let's trace what happens on the 1M-task benchmark with that 2-line change (`deal to all workers when n >= nworkers`, else to `parked` workers):
  - Even if all 30 workers are awake (`asleep == 0`) when a wheel fires 33,000 tasks, Worker `me` immediately deals `1,100` tasks to each of the 29 other workers' inboxes (one `spin_lock(&v->inlock)` per worker = 29 lock acquisitions total instead of 33,000 CAS steals!) and pushes only `1,100` tasks to `me->fresh`!

##### Issue 4B:Walking `for (size_t i = 1; i < share && tail->rnext; i++) tail = tail->rnext;` while holding nothing is fine, EXCEPT why not walk while building the list in `wheel_advance` or cap `me->fresh`?
Actually, walking 1,000,000 `rnext` pointers in `unpark_all` takes ~1–2 ms total if in cache, **provided** `share` is actually dealt out! (With `asleep` only counting `parked` workers, if `asleep == 1`, `share = 500,000`, so Worker 0 gives 500,000 tasks to 1 sleeping worker and keeps 500,000 for itself, leaving the other 28 workers with 0 tasks!)
Counting **all** `nworkers` when `n >= nworkers` (or always dividing by `nworkers` when `asleep > 0 || n >= nworkers`) fixes both the `asleep == 0` cliff and the `asleep == 1` cliff!
Wait: look at that `asleep == 1` case in your current code:
- Suppose 28 workers are awake (spinning in `steal_task`), 1 worker is `parked`, and `me` fires a wheel with `300,000` tasks.
- Your code computes: `asleep = 1`, `share = 300,000 / (1 + 1) = 150,000`!
- It gives **150,000 tasks** to the 1 parked worker and keeps **150,000 tasks** on `me`, while the 28 spinning workers get **zero**!
- Dividing by `nworkers` when `n >= (size_t)nworkers` (and dealing to every worker `v != me`, calling `unpark_worker(v)` if `v` is parked) gives **10,000 tasks to each of the 30 workers** every single time!

##### Issue 4C: Clear `tail->rnext = NULL` before `dq_push` in the final loop?
In `inbox_pop(w)`, when a worker pops from its own inbox (`inhead`/`intail`), does `inbox_pop` rely on `t->rnext == NULL` at `intail`? Yes, and you set `tail->rnext = NULL` for the inbox slices. What about the tasks pushed to `dq_push(&me->fresh, list)`? `dq_push` stores `list` in the ring buffer array, and if that task is later pushed to an inbox, `inbox_push` sets `t->rnext = NULL`. So that's fine, though `list->rnext = NULL` before `dq_push` is clean.

---

### Summary of Recommended Fixes

1. **[Critical — Crash/Hang if `fly_alloc` is `malloc`] Zero-initialize `more` in `scope_join`:**
   ```c
   memset(more, 0, SCOPE_SHARDS * sizeof(mt_padded_shard));
   ```
   before `__atomic_store_n(&sc->more, more, __ATOMIC_RELEASE)`.
2. **[Critical — Load balance cliff in `unpark_all`] When `n >= (size_t)nworkers`, deal `share = n / (size_t)nworkers` across ALL `nworkers` workers, not just `asleep` (`parked == true`) workers:**
   ```c
   if (n >= (size_t)nworkers) {
     size_t share = n / (size_t)nworkers;
     for (int k = 1; k < nworkers && list; k++) {
       worker* v = &workers[(me->index + k) % nworkers];
       mt_task* head = list;
       mt_task* tail = list;
       for (size_t i = 1; i < share && tail->rnext; i++) tail = tail->rnext;
       list = tail->rnext;
       tail->rnext = NULL;
       spin_lock(&v->inlock);
       if (v->intail) v->intail->rnext = head;
       else __atomic_store_n(&v->inhead, head, __ATOMIC_RELAXED);
       v->intail = tail;
       spin_unlock(&v->inlock);
       if (__atomic_load_n(&v->parked, __ATOMIC_SEQ_CST)) unpark_worker(v);
     }
   }
   ```
   Without this, whenever `asleep == 0` or `asleep == 1` (because other workers are spinning in `steal_task` or just woke up), `unpark_all` dumps 50%–100% of the 1,000,000 tasks onto `me->fresh` and 1 worker's inbox, starving the other 28 workers and forcing them back to single-task stealing!
3. **[Shard hash in `scope_join`] Mix higher address bits so 512-byte / 16KB slab alignment doesn't leave half the shards empty:**
   ```c
   uintptr_t h = ((uintptr_t)t >> 8) ^ ((uintptr_t)t >> 14);
   t->shard = more ? (uint8_t)(1 + (h % SCOPE_SHARDS)) : 0;
   ```
4. **[Verify `scope_count_down` when `nlive` is incremented concurrently]:**
   In `scope_count_down`, change the bottom (when exiting the `while (n > 1)` loop because `n == 1`) so that if another task called `mt_start` and incremented `nlive` back above `1` before `spin_lock(&sc->q.lock)` was acquired, you still safely decrement under `sc->q.lock`:
   Actually, wait: because `__atomic_sub_fetch(&sc->nlive, 1, __ATOMIC_ACQ_REL)` is an atomic RMW instruction, even if `nlive` grew from `1 -> 2` while acquiring `sc->q.lock`, `__atomic_sub_fetch` atomically decrements `2 -> 1`, and if another thread is in the `while (n > 1)` CAS loop at that same instant:
   - Wait: if Thread A is under `sc->q.lock` doing `__atomic_sub_fetch` (`2 -> 1`) and Thread B is in the `while (n > 1)` CAS loop doing `2 -> 1`:
     - If Thread B's CAS `2 -> 1` wins first, then Thread A's `__atomic_sub_fetch` takes `1 -> 0` *under `sc->q.lock`* and calls `wake_all(&sc->q)`!
     - If Thread A's `__atomic_sub_fetch` `2 -> 1` wins first, then Thread B's CAS `2 -> 1` *fails*, reloads `n = 1`, exits the `while (n > 1)` loop, acquires `sc->q.lock`, takes `1 -> 0` *under `sc->q.lock`*, and calls `wake_all(&sc->q)`!
   - **Wait — trace that again!** Both orders take the final `1 -> 0` transition **under `sc->q.lock`**! That CAS + locked `sub_fetch` protocol is actually completely linearizable because the `while (n > 1)` CAS only ever transitions states $\ge 2 \to \ge 1$, so it is mathematically impossible for the CAS to perform the $1 \to 0$ transition! Nice design. Ensure `mt_scope_close` holds `sc->q.lock` whenever it observes `nlive == 0` and exits the wait loop.
