# Review: panic-unwinding-native

- spec: 65616151792d
- request: 311ca359d5bddf9f
- tokens: prompt 63982, cached 0, answer 8738

## Question

# How should the C and LLVM back ends unwind a panic?

Context: roadmap step 13 (attached roadmap) makes a panic unwind its task: every block left runs its `defer`s and drops what it owns, as a failure that nothing catches would, then the task's root decides (spawn: report and end the task; fork: cancel the scope and re-panic in the parent; main: exit 101). A panic while a panic unwinds ends the program at once. The reference interpreter and the JavaScript back end already do this (JS: `finally` blocks).

The C back end today (selfhost/c.fly) prints C from a structured IR:
- Every local is declared at the top of its C block, initialized `= { 0 }`.
- A move out of a place memsets the source to zero; every drop function is a no-op on an all-zero value, and the runtime's frees zero what they free (`fly_vec_free` frees then zeroes).
- A `defer` is a separate C function given an env of pointers to the locals it uses, guarded by a `vN_armed` bool set when the defer is registered.
- Failures propagate by return: after each call to a function that can fail, `if (FLY_FAILED) goto unwN;`, where `unwN` runs that block's cleanups (armed defers, drops) and jumps to the enclosing block's `unw` label or the function's `fail:` label.
- Panics are raised by `_Noreturn void fly_panic(const char*)`, from runtime helpers called mid-expression: `FLY_ADD` overflow checks, `fly_vec_at` bounds checks, division, `unwrap`, allocation failure. Today it prints and `_Exit(101)`s.
- Tasks run on fibers: each task its own stack with a hand-written assembly switch; the task's entry is called from a trampoline with no unwind info.
- The LLVM back end prints LLVM IR for the program and links it with the runtime's C (compiled by clang to IR), optimized as one module (ThinLTO when split). WebAssembly goes through the LLVM path to wasm32-wasi; freestanding (a kernel) goes through LLVM without libc.

Options I see:
A. setjmp/longjmp: each function that has cleanups pushes an unwind record with a jmp_buf on the task's chain; fly_panic longjmps to the innermost; the landing runs the function's cleanups, pops, and longjmps on. Problem: C makes non-volatile locals modified between setjmp and longjmp indeterminate after longjmp — the very owned values the landing must drop. Making them volatile costs; relying on address-taken locals living in memory is not guaranteed.
B. Table-driven unwinding: compile C with `-fexceptions`; give each block with cleanups a guard variable with `__attribute__((cleanup(f)))` whose `f` runs the block's cleanups on the unwinding path only (a flag in the guard, cleared on the normal exits, so the normal-path call folds away after inlining); fly_panic calls `_Unwind_ForcedUnwind` with a stop function that stops at the task root (whose frame is recorded), then longjmps (setjmp only at the task root, which touches nothing). Zero cost on the normal path beyond a flag store; the same mechanism as LLVM's `invoke`/landing pads. Needs unwind tables everywhere (-fexceptions, -funwind-tables) and libunwind (present on macOS and Linux). Without them (user builds the C without the flag), `_Unwind_ForcedUnwind` fails and we fall back to printing and exiting.
C. Flag after every call that may panic (`if (fly_panicking) goto unwN`), with runtime helpers setting the flag and returning a dummy: but a helper called mid-expression returns into code that keeps computing with a garbage value (a NULL from fly_vec_at dereferenced) before the next check, so every panicking operation would need its own check. Your earlier estimate for per-call checks was 10–25%.

For the LLVM back end: emit `invoke` + `landingpad cleanup` for calls in blocks with cleanups, with a personality (`__gcc_personality_v0`, which handles cleanup-only frames), and the same fly_panic/_Unwind_ForcedUnwind raise.

For WebAssembly: LLVM's wasm exception handling (`-fwasm-exceptions`) and libunwind for wasm exist in recent LLVM, and Node 24 runs the exnref proposal; but wasi-libc support is young.

Questions:
1. Which option for C, and why? If B, is the guard design right, and are there traps: unwinding through the fiber trampoline, ThinLTO, sanitizers (ASan/UBSan/TSan) with forced unwinding, `_Unwind_ForcedUnwind` across frames compiled without unwind tables (the runtime's own C is ours, so we can compile it with -fexceptions)?
2. Is there a cheaper, simpler design I am missing — for instance, making the C back end's existing failure path carry panics by having fly_panic longjmp only to the *innermost function with cleanups* whose landing restores from a per-function record of pointers to its droppable locals (taken once at entry, so they are address-taken and live in memory)?
3. For WebAssembly: use wasm EH now, or keep a panic there as print-and-exit for the moment? What is the realistic support today (wasi-sdk, wasm-ld, Node 24)?
4. For freestanding: a kernel has no unwinder; panics go to the program's named handler without unwinding. Agree?
Rank the risks.

## Context files

- `docs/roadmap.md`

## Answer

### Verdicts

- **Q1 (C unwinding mechanism):** **Disagree with Option B (`_Unwind_ForcedUnwind` + `-fexceptions`); Agree with Option A refined via Question 2 (per-function `setjmp` + out-of-line cleanup function taking an env struct of pointers to droppable locals).** Option B has five fatal or severe traps: (1) any suspension (`Io`, `Yield`, non-direct `handle`, channel/mutex wait) inside a cleanup scope switches fibers mid-unwind or across an active DWARF frame, breaking `_Unwind_ForcedUnwind`; (2) ASan and TSan do not intercept `_Unwind_ForcedUnwind` the way they intercept `longjmp` or `__cxa_throw`, leaving shadow-stack frames poisoned and TSan shadow call stacks corrupted; (3) the hand-written fiber entry trampoline lacks `.cfi_undefined rip/lr`, causing libunwind to walk off the bottom of the fiber stack and segfault; (4) LLVM's `overflow` / bounds intrinsics cannot unwind through `invoke` unless packaged as calls; and (5) Option B fails on Wasm/wasi-libc and freestanding.
- **Q2 (Cheaper, simpler unified design):** **Agree — Question 2's insight (combined with your existing `defer` env-pointer pattern and the existing `unwN` failure path) is strictly simpler, 100% standard-C legal without `volatile`, works identically in C, LLVM, Wasm, and Freestanding, and has zero normal-path cost in functions without cleanups.** Even better: if `setjmp` is placed in a tiny wrapper or if the cleanup locals' addresses are passed to an out-of-line/noinline cleanup helper (exactly as you already do for `defer`!), C11 `§7.13.2.1` guarantees their memory values are determinate without `volatile`.
- **Q3 (WebAssembly panic unwinding):** **Disagree with `-fwasm-exceptions` / `_Unwind_ForcedUnwind` on Wasm; Agree with using the exact same `setjmp`/cleanup-chain mechanism (compiled with LLVM's `-wasm-enable-sjlj` or intra-function unwind + task-root `setjmp`).** Standard `wasi-sdk` does not ship a `libunwind` built for `-fwasm-exceptions` with `_Unwind_ForcedUnwind`, and mixing JSPI (JavaScript Promise Integration) fiber switches with Wasm EH `try_table` across C frames is a known browser/V8 hazard. By contrast, LLVM's Wasm backend natively lowers `setjmp`/`longjmp` (and if panics unwind via the Q2 design, Wasm gets full task-unwinding today!).
- **Q4 (Freestanding panic handling):** **Agree.** In `--freestanding` (`§8.3`), there is no `Io`, no `Scope`/`spawn`/`fork`, and `fly_os_panic(message, len)` is defined not to return. Panics in freestanding should call `fly_os_panic` directly without unwinding.

---

### Problems (Ranked Most Serious First)

#### 1. [Rank 1 — Soundness/Runtime Crash, Q1] `_Unwind_ForcedUnwind` (Option B) and `invoke` + `landingpad` break when a `defer` suspends or switches fibers (`§5.6`, `§5.3`)

Look at what the spec and Step 13 say happens when a panic unwinds a `defer`:
- `§5.6` / `§5.3` / Step 13: *"A panic drops the continuation of the task it happens in... Everything the task owns is dropped and its `defer`s run with their operations cancelled."*
- Wait: what if a `defer` calls a function that:
  1. Opens and uses its own inner `region (R) { ... }` or `try { ... } catch (_) { ... }` or inner `handle { ... }` (which is legal inside a `defer` because those effects are handled locally inside the `defer`!), OR
  2. Performs an `Io` or outer effect operation, which the runtime cancels by unwinding *that `defer` itself* back to the `defer` boundary (`§5.3`: *"an operation other than `Io` that a `defer` performs as it is dropped is cancelled — the `defer` unwinds from it, as from a failure, and the unwinding goes on"*)?

Demonstrating program:
```ts
effect Helper { step(): void; }

function cleanUpWork(): void {
  // Handled locally inside the defer — completely legal in §5.6!
  handle {
    Helper.step();
  } with Helper {
    step() resumes k => {
      // Non-tail-resumptive handler (runs on a child fiber in C/LLVM today!)
      k();
    }
  }
}

export function main(): void uses Io {
  let v: Vec<i32> = [1, 2, 3];
  defer {
    cleanUpWork();
  };
  const x = v[99]; // PANIC!
}
```
And a second case from `§5.3` / Step 13 (cancelling an operation performed by a `defer` during panic unwinding):
```ts
function flushAndClose(s: mut Socket): void uses Io {
  let tmp: Vec<u8> = [1, 2, 3]; // Owned local inside the function called by `defer`!
  s.write(tmp);                 // Performs `Io.write` while task is panicking -> must be cancelled!
  // When `s.write` is cancelled during panic unwinding, `tmp` MUST be dropped as `flushAndClose` unwinds!
}

export function serve(mut s: Socket): void uses Io {
  defer {
    try { flushAndClose(mut s); } catch (_) {}
  };
  panic("boom");
}
```
Look at what happens in both cases under **Option B (`_Unwind_ForcedUnwind` / LLVM `landingpad` + `_Unwind_Resume`)**:
1. `_Unwind_ForcedUnwind` is a **single-stack, single-thread C ABI state machine** inside `libunwind` that walks DWARF frames on the *current* stack and calls each frame's personality function (`__gcc_personality_v0`).
2. While inside a `__attribute__((cleanup(f)))` handler or LLVM `landingpad` (before `_Unwind_Resume`), you are **in the middle of `_Unwind_ForcedUnwind`'s callback**.
3. If `f` (running a `defer`) switches fibers (e.g., `cleanUpWork()`'s non-direct `handle`), or if `flushAndClose` performs `Io.write` which is cancelled during panic unwinding by starting a *nested* unwind to abort the `defer` while keeping the outer panic unwind going:
   - Calling `_Unwind_ForcedUnwind` a second time (to cancel the `defer`), or calling `longjmp` at the task root out of `_Unwind_ForcedUnwind`'s stop function without finishing `__cxa_end_catch`, or switching stacks inside a cleanup callback, **corrupts `libunwind` / ASan / TSan state**.
4. Worse, look at your existing C backend (`selfhost/c.fly`):
   - Your existing C backend **already has** `if (FLY_FAILED) goto unwN;` for `Fail`, where `unwN:` runs `defer`s and drops in exact lexical order!
   - Why duplicate every cleanup block into *both* `unwN:` labels (for `Fail`) AND `__attribute__((cleanup(f)))` / LLVM `landingpad` (for panics), when a single cleanup path can handle both?!

---

#### 2. [Rank 2 — Sanitizer & Toolchain Failure, Q1] `_Unwind_ForcedUnwind` + `longjmp` in the stop function breaks AddressSanitizer (ASan) and ThreadSanitizer (TSan)

In Question 1, you asked specifically:
> *"are there traps: unwinding through the fiber trampoline, ThinLTO, sanitizers (ASan/UBSan/TSan) with forced unwinding, `_Unwind_ForcedUnwind` across frames compiled without unwind tables?"*

Yes — all three of these are hard traps with Option B:

1. **ThreadSanitizer (TSan) shadow call stack corruption:**
   - TSan instruments every function entry (`__tsan_func_entry`) and every normal return (`__tsan_func_exit`).
   - When a C++ exception is thrown (`_Unwind_RaiseException`), TSan intercepts personality/cleanuplanding pads and pops its shadow stack on `_Unwind_Resume`.
   - When you call `_Unwind_ForcedUnwind` and then in the `stop` function at the task root you call `longjmp` (or return from the fiber), TSan's shadow call stack for that fiber is **not properly unwound if `stop` jumps out or if any frame lacked a personality function**, causing immediate bogus race reports or segfaults in `__tsan_func_exit` on the next task that reuses the fiber or worker!
2. **AddressSanitizer (ASan) poisoned stack frames:**
   - ASan poisons local variables' redzones on the stack. When `longjmp` is called, ASan's interceptor `__interceptor_longjmp` unpoisons the stack between `sp` and the `jmp_buf`'s target `sp`.
   - If you use `_Unwind_ForcedUnwind` across functions that have no cleanup (and therefore no personality routine / landingpad), ASan does not unpoison those intermediate frames until `longjmp` runs at the end — and if a `defer` runs *during* `_Unwind_ForcedUnwind` and allocates/reuses stack frames below the panicking frame, ASan can hit stale stack redzones.
   - By contrast, ASan and TSan have **first-class, battle-tested interceptors for `setjmp`/`longjmp`** (`__interceptor_setjmp` / `__interceptor_longjmp`) when you already use `__sanitizer_start_switch_fiber` / `__sanitizer_finish_switch_fiber` (which Step 12 says your C core already calls!).
3. **Fiber trampoline DWARF unwind crash:**
   - When `_Unwind_ForcedUnwind` walks the stack in Phase 1 (before your `stop` function even stops Phase 2, or if `libunwind` checks CFI validity on the current frame and its caller), if the fiber root trampoline does not have `.cfi_startproc` + `.cfi_undefined %rip` (x86-64) / `.cfi_undefined x30` (AArch64), `libunwind` on Linux (`libgcc_s`) frequently reads past the bottom of the fiber stack looking for the caller's FDE before terminating.

---

#### 3. [Rank 3 — The Clean Solution, Q1 & Q2] Why C11 `setjmp` + the Existing `unwN:` Path (with Address-Taken Local Env or No-Inline Unwind Helper) Wins on Every Axis

Look at the objection you raised to Option A (`setjmp`/`longjmp`), and your own insight in Question 2:
> *"Problem: C makes non-volatile locals modified between setjmp and longjmp indeterminate after longjmp — the very owned values the landing must drop. Making them volatile costs; relying on address-taken locals living in memory is not guaranteed."*
> *"Q2: Is there a cheaper, simpler design I am missing — for instance, making the C back end's existing failure path carry panics by having fly_panic longjmp only to the innermost function with cleanups whose landing restores from a per-function record of pointers to its droppable locals?"*

Let's examine why **C11 §7.13.2.1** makes non-`volatile` locals indeterminate after `longjmp`, and how your Q2 idea makes it **100% strictly conforming C AND LLVM IR with zero `volatile` overhead on the normal path**:

1. **Why C11 §7.13.2.1 has the `setjmp` rule:**
   In C and LLVM, if a function `foo()` calls `setjmp(buf)` directly, a local variable `Vec v` that lives in a callee-saved register (or SSA value in LLVM across a `returns_twice` call) might be modified in a register after `setjmp`, and `longjmp` restores the *old* callee-saved registers from the `setjmp` call site.
2. **Why `v` is NEVER in a register across calls if its address escapes to the unwind record (or if `v` is fields of one stack-allocated frame struct!):**
   In `selfhost/c.fly` today, every local is already a struct/value initialized `= { 0 }`, and a move memsets it to zero, and every drop function `fly_drop_T(&v)` takes a pointer `&v`!
   Suppose in any function `foo` that has cleanups (and **only** in functions that have at least one droppable local, `defer`, or `region`), instead of declaring droppable locals as bare register-eligible automatic variables:
   ```c
   // Generated ONLY for functions that have cleanups (drops, defers, or regions):
   struct foo_locals {
     fly_Vec v0;
     fly_String v1;
     bool defer2_armed;
     int32_t state; // Which block cleanup label (unw0, unw1, ...) is currently active
   };
   ```
   Wait: if `struct foo_locals L = { 0 };` is declared in `foo`, can the C compiler STILL cache `L.v0` in a register across a call if `setjmp` is called in `foo`?
   **Not if `&L` is stored in the task's external unwind chain (`task->unw_top->locals = &L`) BEFORE `setjmp` AND the cleanup after `setjmp` is called via `foo_cleanup(&L)` (or `task->unw_top` is read)!**
   Why? Because in C (and LLVM):
   - `&L` has **escaped to global/heap memory** (`task->unw_top->locals = &L`) before `setjmp`!
   - Therefore, before **every external/panicking function call** inside `foo` (such as `fly_vec_at`, `fly_panic`, or any callee `bar()`), the C/LLVM alias analyzer **must materialize all stores to `L` into memory**, because any external function can read `task->unw_top->locals`!
   - Even better: what about inline operations that can panic without an external call, like `FLY_ADD(a, b)` overflow or inline division `a / b`?
     If `FLY_ADD(a, b)` is:
     ```c
     static inline int64_t fly_add_i64(int64_t a, int64_t b) {
       int64_t r;
       if (__builtin_add_overflow(a, b, &r)) fly_panic("integer overflow");
       return r;
     }
     ```
     Wait: if `fly_add_i64` is inlined into `foo`, then `fly_panic("integer overflow")` is a call inside `foo`! Because `fly_panic` is an external function call, the compiler **must sink all prior stores to the escaped struct `L` into memory before the call to `fly_panic`**!
   - And when `setjmp(unw_node.buf)` returns non-zero on the panic path, `foo` simply calls an out-of-line (or `noinline`) cleanup function `foo_unwind(&L)` (or reads `(volatile struct foo_locals*)&L` inside the `if (setjmp(...) != 0)` cold branch!).
   - Because `&L` escaped before `setjmp`, every modification to `L` before the `fly_panic(...)` call was already committed to memory in `L`, and reading `L` through `unw_node.locals` (or a `volatile` pointer cast in the cold `setjmp != 0` branch) reads the memory of `L`, **never** a stale register!

3. **Wait — can we make it even tighter so non-droppable locals (like loop counters `i`, `total`, `x`) stay in registers 100% of the time?**
   **YES!**
   Which locals in `foo` can possibly be read by `unwN:` when a panic unwinds `foo`?
   Only:
   1. **Owned locals that have a `Drop`** (which in C are already structs like `String`, `Vec`, `Box`, `Arc`, user `Drop` structs — whose addresses are already passed to `fly_vec_push(&L.v0, ...)`!),
   2. **Locals borrowed by a `defer`** (which in `selfhost/c.fly` **already** have their addresses put into the `defer`'s env struct!),
   3. **Region arena pointers** (`fly_region*`), and
   4. **The `defer_armed` flags** (or a single `uint32_t unw_state` index saying which block `unwN` we are in!).
   No pure `Copy` scalar (`i32`, `u64`, `f64`, `bool`, `str`, slices, pointers) that isn't borrowed by a `defer` is ever touched during unwinding!
   So all ordinary scalars, slices, borrows, and temporaries remain plain C local variables in registers! Only the droppable locals, `defer`-referenced locals, and `defer_armed` flags go into `struct foo_cleanup_env L = { 0 };`!

---

#### 4. [Rank 4 — Unifying `Fail` and `panic` in Both C and LLVM, Q1 & Q2] How `panic` and `Fail` Share 100% of the Existing `unwN` Cleanup Code in C and LLVM

Look at how `selfhost/c.fly` and `selfhost/llvm.fly` work right now:
- In `c.fly` and `llvm.fly`, you **already generate** the `unwN:` cleanup blocks for `Fail`!
- Today, why doesn't a pure function (that doesn't call any `uses Fail` function) enter `unwN:`? Because in 0.113 panics called `_Exit(101)`.
- With the Q2 design, look at how `panic` reuses your **exact existing `unwN:` blocks** in **both** C and LLVM:

1. **When does a function `F` need a `fly_unw_frame` (`setjmp`)?**
   Only when `F` contains at least one block with a cleanup (`Drop`, `defer`, or `region`) **and** that block contains an operation that can panic (or call something that can panic) without already propagating via `FLY_FAILED`.
   In fact, if `F` is a function that has cleanups:
   - At entry to `F`, `F` links `fly_unw_frame unw = { .prev = task->unw_top, .env = &L, .state = 0 }; task->unw_top = &unw;`
   - `if (__builtin_expect(setjmp(unw.buf) != 0, 0)) goto unw_dispatch;`
   - Whenever `F` enters/exits cleanup block `k`, `L.unw_state = k;` (a single immediate store to stack memory — just like the `flag` store you noted in Option B!).
   - On `unw_dispatch:`, a `switch (((volatile struct F_env*)&L)->unw_state)` jumps directly to your **existing `unwN:` label**!
   - At the bottom of the outer `unw0:` label (where `Fail` returns with `FLY_FAILED` set), if `task->panicking` is set, it pops `task->unw_top = unw.prev;` and calls `fly_panic_continue(task)` (which `longjmp`s to `task->unw_top->buf`)!
   - And what if `F` calls a `uses Fail` function `G()` which panics?
     Wait: if `G()` unwinds via `longjmp` to `F`'s `setjmp`, `G()` doesn't even need `F` to check `FLY_FAILED` after `G()`: `longjmp` jumps **straight from the deepest cleanup frame in `G` to `F`'s `setjmp` (`unw_dispatch`)**!
     Even better: if `F` calls `G()` inside cleanup block `k`, `L.unw_state` is *already* `k`, so when `G()` finishes unwinding its own cleanups and `longjmp`s to `F`, `F` lands directly in `unw_k`, runs `F`'s cleanups, and `longjmp`s to `F`'s caller!

2. **Look at what happens when a `defer` performs an effect during panic unwinding (`§5.3`):**
   - Suppose `F` is unwinding from a panic (`task->panicking == 1`), and `unw_k:` calls `defer_fn(&L)`.
   - Inside `defer_fn`, the code performs `Io.write(...)` (or another effect).
   - The runtime sees `task->panicking == 1`! How should it cancel the `defer` (`§5.3`: *"the `defer` unwinds from it, as from a failure, and the unwinding goes on"*)?
   - Before `unw_k:` calls `defer_fn(&L)`, it pushes a `fly_unw_frame` for the `defer` (or `defer_fn` itself has one if it has cleanups), with `is_defer_root = 1`!
   - If the `defer` performs an effect while `task->panicking == 1`, the runtime simply triggers unwind to `is_defer_root`, which cleanly unwinds any locals inside `defer_fn` and returns normally to `unw_k:` so the rest of `F`'s cleanups continue!
   - And if the `defer` actually *panics* (e.g., index out of bounds inside a `defer` or `Drop` while `task->panicking == 1`), `fly_panic` sees `task->panicking == 1` and immediately aborts the program (`_Exit(101)`), just as Step 13 specifies!

3. **Should the LLVM back end (`selfhost/llvm.fly`) use the exact same `setjmp` mechanism or `invoke` + `landingpad`?**
   Let's compare both honestly for `selfhost/llvm.fly`:
   - **Why `invoke` + `landingpad` in `llvm.fly` is trickier than it looks:**
     1. In `llvm.fly`, integer arithmetic uses LLVM intrinsics (`@llvm.sadd.with.overflow.i64`, etc.) followed by a conditional branch `br i1 %ovf, label %panic, label %ok`, and division/bounds checks also branch to a call to `@fly_panic`.
     2. In LLVM IR, `call void @fly_panic(...)` will **NOT** unwind to the current function's `landingpad` unless it is emitted as `invoke void @fly_panic(...) to label %unreachable unwind label %unwN`!
     3. Similarly, *every* call inside a block with cleanups (`Drop`, `defer`, `region`) in `llvm.fly` must be emitted as `invoke ... to label %next unwind label %unwN` instead of `call`.
     4. Wait: in `llvm.fly`, you **already have** the `unwN` basic blocks! If you use `invoke` in `llvm.fly`, you don't even need `_Unwind_ForcedUnwind` inside the same function for local panics (`br label %panic_unwN` can branch straight to a helper block that sets `task->panicking = 1` and branches to `%unwN`!).
     5. **Wait — look at that:** why use `_Unwind_ForcedUnwind` and `libunwind` at all in `llvm.fly` OR `c.fly` if:
        - Every function in the program is compiled by us (except `extern "C"`, which cannot have Flyscript cleanups above it without going through a Flyscript caller!), AND
        - In `llvm.fly` (and `c.fly`), we already return a status / thread-local flag for `Fail`?
        Hold on! Why did you reject Option C (checking a flag after calls)?
        Look at why you rejected Option C in your prompt:
        > *"C. Flag after every call that may panic (`if (fly_panicking) goto unwN`), with runtime helpers setting the flag and returning a dummy: but a helper called mid-expression returns into code that keeps computing with a garbage value (a NULL from fly_vec_at dereferenced) before the next check, so every panicking operation would need its own check."*
        Because in `c.fly`, `fly_vec_at` is called mid-expression!
        Where as with **per-cleanup-function `setjmp`** (your Q2):
        - `fly_vec_at` does **not** return a dummy value on panic: it calls `fly_panic()`, which **immediately `longjmp`s** out of the middle of the expression to `task->unw_top->buf`!
        - Functions **without** cleanups don't call `setjmp` and don't have any per-call checks — `longjmp` skips right over them in zero instructions!
        - Functions **with** cleanups call `setjmp` once at function entry (and only if they actually contain a `Drop`, `defer`, or `region`), store their droppable locals in `struct fn_env L`, and `longjmp` lands straight on their `unwN:` chain!
        - And this works **identically in `c.fly`, `llvm.fly`, WebAssembly (`wasm32-wasi`), and with ASan/TSan/UBSan**, with zero dependency on `libunwind`, DWARF `.eh_frame`, `__gcc_personality_v0`, or `-fexceptions`!

---

#### 5. [Rank 5 — WebAssembly Support Today, Q3] Wasm Exception Handling vs `setjmp`/`longjmp` on `wasm32-wasi`

In Question 3, you ask:
> *"For WebAssembly: use wasm EH now, or keep a panic there as print-and-exit for the moment? What is the realistic support today (wasi-sdk, wasm-ld, Node 24)?"*

Here is the concrete state of the toolchain today:
1. **Why `-fwasm-exceptions` + `_Unwind_ForcedUnwind` is not ready on `wasi-sdk`:**
   - Standard `wasi-sdk` builds `libc.a` without `-fwasm-exceptions` by default (unless using the separate EH sysroot), and Wasm's C++ exception ABI (`__cxa_throw` / `_Unwind_RaiseException`) in LLVM uses Wasm `throw` / `try_table` (or legacy `try`/`catch`), which **does not support `_Unwind_ForcedUnwind`** (because Wasm EH instructions are caught by tag at `try_table` in the machine code rather than walked by a two-phase DWARF stack walker with a custom `stop` callback!).
   - Furthermore, your Wasm target (`§8.3`, Step 2 & Step 6) uses **JSPI (`WebAssembly.promising` / `Suspending`)** and dynamic side-module splitting (`wasm-split.js`). Wasm EH `try_table` blocks across dynamically-linked side modules and JSPI suspension boundaries require matching `__cpp_exception` tag imports/exports in `wasm-split.js` and have had V8 edge cases when suspending inside a `try_table`.
2. **Why the Q2 `setjmp`/`longjmp` chain works on Wasm (or why keeping Wasm as print-and-exit until Step 15's state machines is even cleaner):**
   - Wait: look at Roadmap **Step 15 (Parked tasks as small as a future)**, which is the very next step after Step 13/14!
   - Once Step 15 compiles suspending functions into state machines (where every frame is already an explicit `struct Frame` in a linked chain `Frame* caller` with an explicit cleanup table!), unwinding a state-machine task on **every** backend (C, LLVM, Wasm) is just a `while` loop walking `Frame* caller`!
   - And for non-suspending functions on the stack between suspension points, using the Q2 `fly_unw_frame` (`setjmp` in C/LLVM, or in Wasm either `-wasm-enable-sjlj` or waiting until Step 15) avoids wiring up `_Unwind_ForcedUnwind` only to rip half of it out in Step 15 when fibers are retired!
   - Specifically: if you use the Q2 `fly_unw_frame` (`setjmp`/`longjmp` + `struct fn_env L`) for C and LLVM now:
     - Native C and Native LLVM (macOS + Linux, x86-64 + AArch64, with ASan/TSan/UBSan and ThinLTO) work **immediately** with zero `libunwind` / fiber-trampoline / sanitizer bugs.
     - For WebAssembly (`wasm32-wasi`), `wasi-libc` **already ships `<setjmp.h>`** (supported by LLVM's `-wasm-enable-sjlj` pass in `clang`/`llc`), OR if you compile `.ll` directly with `llc` without the SjLj pass, you can either pass `-wasm-enable-sjlj` to `llc`/`clang` or keep Wasm panics as print-and-exit until Step 15 removes fibers. Passing `-mllvm -wasm-enable-sjlj` + linking `-lsetjmp` from `wasi-sdk` takes one flag; test if `wasm-split.js` handles the SjLj imports cleanly, and if `wasm-split.js` needs extra glue for `__wasm_longjmp`, only enable SjLj on non-split Wasm or after updating `wasm-split.js`.

---

#### 6. [Rank 6 — Concrete C Code Pattern for Q2] Exact C / LLVM Lowering to Avoid Every Trap

To make sure there are zero ambiguities when implementing the Q2 design in `selfhost/c.fly` and `selfhost/llvm.fly`, here is the exact structure to emit for a function `foo` that has at least one cleanup (`Drop`, `defer`, or `region`):

```c
// 1. Only emitted if `foo` has at least one droppable local, defer, or region:
struct foo_unw_env {
  int32_t unw_state;       // 0 = none, 1 = unw1, 2 = unw2, ...
  fly_Vec v1;              // droppable locals live in this struct, NOT bare locals
  fly_String v2;
  fly_region* reg3;        // region arenas
  bool defer4_armed;       // defer armed flags
  int64_t* defer4_borrowed_x; // or any local referenced by a defer also lives in foo_unw_env
};

// 2. Out-of-line (or noinline) cleanup runner for `foo` on the panic path, OR inline after setjmp:
// Because `&env` is stored into `task->unw_top->env` BEFORE `setjmp`, C/LLVM alias analysis
// treats `env` as escaped global/thread-local memory: every store to `env.*` before ANY call
// (including `fly_panic`) is guaranteed to be written to memory before the call!
```

Inside `foo`:
```c
fly_ret foo(fly_arg a) {
  struct foo_unw_env env = { 0 };
  fly_unw_node unw_node;
  unw_node.prev = fly_task_unw_top();
  unw_node.env = &env; // <-- Escapes `&env` before setjmp!
  fly_set_task_unw_top(&unw_node);

  if (__builtin_expect(setjmp(unw_node.buf) != 0, 0)) {
    // Panic path! Read `env.unw_state` and jump into the EXISTING `unwN` labels!
    switch (((volatile struct foo_unw_env*)&env)->unw_state) {
      case 2: goto unw2;
      case 1: goto unw1;
      default: goto unw_done;
    }
  }

  // Normal execution:
  // Block 1 (has cleanup unw1):
  env.unw_state = 1;
  env.v1 = make_vec();
  if (FLY_FAILED) goto unw1;

  // Block 2 (nested, has cleanup unw2):
  env.unw_state = 2;
  env.v2 = make_str();
  // Suppose `fly_vec_at(&env.v1, 99)` panics here:
  // `env.unw_state` is 2, `env.v1` and `env.v2` are already in memory in `env`.
  // `fly_panic` calls `longjmp(fly_task_unw_top()->buf, 1)`, jumping to `case 2: goto unw2;`!

  // Normal exit of Block 2:
  env.unw_state = 1;
  fly_str_drop(&env.v2);

  // Normal exit of Block 1:
  env.unw_state = 0;
  fly_vec_drop(&env.v1);
  fly_set_task_unw_top(unw_node.prev);
  return result;

unw2:
  fly_str_drop(&env.v2);
  goto unw1;
unw1:
  fly_vec_drop(&env.v1);
unw_done:
  fly_set_task_unw_top(unw_node.prev);
  if (fly_is_panicking()) {
    fly_panic_rethrow(); // longjmps to `unw_node.prev->buf` (or task root)!
  }
  return fly_fail_result();
}
```

Check every property of this lowering:
1. **Functions with NO cleanups (`Drop`, `defer`, `region`):**
   Zero changes! No `env` struct, no `unw_node`, no `setjmp`, no per-call branches. `longjmp` flies right past them to the nearest caller that has a `fly_unw_node`.
2. **Non-droppable scalars (`i64`, `f64`, `bool`, slices, borrows not used in `defer`):**
   Stay ordinary C/LLVM local variables in registers! Only droppable locals, region pointers, and `defer`-captured locals live in `env`.
3. **C11 / LLVM `setjmp` safety without `volatile` on the fast path:**
   Because `unw_node.env = &env` escapes `&env` into external runtime state before `setjmp`, every store to `env.*` must be flushed to memory before *any* function call (`fly_panic`, `fly_vec_at`, etc.), and in the cold `setjmp != 0` block we read `env` after it was written in memory. (The one rule to enforce in `c.fly`/`llvm.fly`: any operation that can panic — overflow, div-by-zero, bounds check — must call a function `fly_panic(...)`, which it already does!)
4. **Zero duplication of cleanup logic:**
   `unw1:` and `unw2:` are the **exact same cleanup blocks** already emitted for `FLY_FAILED`, with one `if (fly_is_panicking()) fly_panic_rethrow();` at `unw_done:`.
5. **Works with fibers, ASan, TSan, UBSan, ThinLTO, macOS, and Linux:**
   Each task/fiber has its own `unw_top` pointer in its task context (`task->unw_top`), starting at the task root's `setjmp` buffer. No DWARF tables, no `_Unwind_ForcedUnwind`, no fiber trampoline CFI crashes, and full ASan/TSan `longjmp` interceptor support.

---

### Summary of Ranked Risks

1. **[Rank 1 — Soundness/Runtime Crash]: Option B (`_Unwind_ForcedUnwind`) breaks when a `defer` suspends, switches fibers, or has an effect cancelled during panic unwinding (`§5.3`, `§5.6`).** Use the task-chained `setjmp` + `unwN:` design (Q2) instead.
2. **[Rank 2 — Sanitizer Failure]: `_Unwind_ForcedUnwind` + `longjmp` in a stop function corrupts TSan's shadow call stack and bypasses ASan stack unpoisoning.** Standard `setjmp`/`longjmp` is natively intercepted by both ASan and TSan.
3. **[Rank 3 — Compiler Miscompilation Risk with `setjmp`]: Putting droppable locals in bare C variables across `setjmp`.** Solve this completely by placing droppable locals, region pointers, `defer`-captured locals, and `unw_state` in a single `struct fn_unw_env env = { 0 };` whose address `&env` is stored into the task's `fly_unw_node` *before* `setjmp`.
4. **[Rank 4 — Duplicated IR/Backend Complexity]: Maintaining separate cleanup codegen for `Fail` (`goto unwN`) and panics (`__attribute__((cleanup))` / `landingpad`).** Have `setjmp` dispatch on `env.unw_state` directly into the existing `unwN:` labels in both `c.fly` and `llvm.fly`.
5. **[Rank 5 — WebAssembly Toolchain]: Relying on `_Unwind_ForcedUnwind` in `wasm32-wasi`.** Wasm EH does not implement DWARF two-phase `_Unwind_ForcedUnwind` with a custom stop function and interacts poorly with JSPI and `wasm-split.js`; the `setjmp` chain (or Step 15's explicit frame-arena chain) is portable to Wasm.
