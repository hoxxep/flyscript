# Review: panic-landing-pads

- spec: 094e7bc8e860
- request: e32adec3e2a14d3d
- tokens: prompt 64539, cached 0, answer 4943

## Question

# Measured: per-function setjmp doubles the compiler's run time. Landing pads for LLVM?

Follow-up to your review panic-unwinding-native (attached roadmap; you recommended per-function setjmp + env struct dispatching to the existing unwN labels, for C, LLVM and wasm).

I built it. It is correct: the whole corpus passes on the reference, JS, C (ASan+UBSan, leaks, TSan threads), LLVM (sanitizers) and wasm (wasi-libc setjmp via -mllvm -wasm-enable-sjlj, Node 24). Two findings:

1. Cost. The native compiler (compiled through LLVM, -O2, ThinLTO) compiling itself: 1.2 s before, 2.7 s after. Profile: `_setjmp` + its stub ≈ 10%, and derived `clone_*`/`subst` functions — small functions with cleanups, now each with a record — dominate; they are no longer inlined, since LLVM does not inline a function that calls a returns_twice function. A whole-program may-panic analysis would remove records from functions that cannot panic, but compiler-like code indexes and does checked arithmetic almost everywhere, so most functions with cleanups would keep them.

2. An LLVM AArch64 miscompile (Apple clang 21 and LLVM 23, -O1 with sanitizers) in a function that calls _setjmp: after `cmp w0, #5`, the 64-bit register holding a returned union's tag (upper half = padding) was used in place of the 64-bit constant 5. `-mllvm -aarch64-enable-copyelim=false` fixes it; we now pass that on arm64.

Proposal: for native code made through LLVM, use `invoke` + `landingpad cleanup` (personality `__gcc_personality_v0`) in blocks with cleanups, the landing pad running the block's cleanups (all of them, idempotently) and `resume`. fly_panic raises with `_Unwind_ForcedUnwind`, whose stop function stops at the innermost catch point (task root, fiber entry, Io.scope, Mutex.lock, join half — runtime C functions that keep a setjmp record and their CFA) and longjmps there. The C back end and wasm keep the setjmp records.

Your earlier objection #1 was that a defer in a landing pad may suspend or switch fibers mid-unwind. My understanding: in phase 2 the unwinder installs the landing pad's context and jumps to it — no unwinder frame remains on the stack while the landing pad runs; the exception object holds the state, and `_Unwind_Resume` continues. So a defer that switches fibers inside a landing pad is ordinary code on the panicking fiber's stack, and other fibers may even unwind panics of their own meanwhile (each with its own exception object). Is that right, for libunwind (macOS) and libgcc_s (Linux), with a forced unwind?

Questions:
1. Is landing pads for LLVM + setjmp records for C/wasm the right split, or do you see something better (e.g. setjmp records only in functions a whole-program analysis says may panic, plus allowing inlining some other way)?
2. Traps with forced unwind under ASan/TSan with our fibers (we call __sanitizer_start/finish_switch_fiber and __tsan_switch_to_fiber), ThinLTO, and `nounwind` (our functions are all `nounwind` today: must drop it on functions that may unwind).
3. Calls inlined from the runtime's C (bounds checks, overflow) become invokes when inlined at an invoke site — but a C function that panics *internally* (fly_vec_at → fly_panic) compiled without -fexceptions has no unwind table: we would compile the runtime's C with -fexceptions (it is ours). Anything else?
4. Cost of `invoke` vs `call` in hot loops after LLVM's optimizations (blocking some transformations?).
Rank the risks.

## Context files

- `docs/roadmap.md`

## Answer

### Verdicts

- **Q1 (`invoke` + `landingpad` for native LLVM, `setjmp` for C; Wasm via `-fwasm-exceptions`):** **Agree with changes.** Native zero-cost DWARF unwinding via `invoke` + `landingpad` restores 100% of inlining (`clone_*`, `subst`) and eliminates the `_setjmp` call and the LLVM `returns_twice` optimization barrier. However, **do not use `_Unwind_ForcedUnwind` with a stop function that `longjmp`s** — use standard `_Unwind_RaiseException` + `landingpad catch ptr null` at catch boundaries (or catch in C via `__attribute__((cleanup))`/ helper) instead. And on Wasm, LLVM's `-fwasm-exceptions` lowers the **exact same `invoke` + `landingpad` IR** to native Wasm `try_table`/`catch` (supported natively in Node 22/24 and all modern browsers) with zero `wasm-enable-sjlj` overhead.
- **Q2 (Phase-2 fiber switching + `_Unwind_ForcedUnwind` + ASan/TSan):** **Disagree with `_Unwind_ForcedUnwind`; Agree with `_Unwind_RaiseException`.** Your understanding that Phase 2 jumps via `_Unwind_SetIP` to the landing pad with no libunwind frame on the stack is right for **`_Unwind_RaiseException`**, where `_Unwind_Resume` restarts Phase 2 from the exception object. It is **false or broken for `_Unwind_ForcedUnwind` + `longjmp` across libgcc_s / Apple libunwind + ASan/TSan** for three concrete reasons detailed in Problem 1 and Problem 2 below.
- **Q3 (Runtime C flags, `nounwind`, `uwtable`):** **Agree with changes.** In addition to compiling runtime C with `-fexceptions -funwind-tables` and dropping `nounwind` on functions that can panic, every LLVM IR function that can be on a panic call stack **must carry the `uwtable` (or `uwtable(sync)`) attribute** — without `uwtable`, LLVM omits `.cfi_def_cfa_offset` / `.eh_frame` entries on x86-64/AArch64 when `nounwind` is absent or in leaf-like frames, causing `_Unwind_RaiseException` to return `_URC_END_OF_STACK` (5) and abort!
- **Q4 (`invoke` cost in hot loops):** **Agree — near-zero cost, if and only if you only emit `invoke` inside scopes with active cleanups and keep `nounwind` on leaf/non-panicking intrinsics.** When a function has no active cleanup (`Drop`, `defer`, `region`) at a call site, emit a normal `call` (not `invoke`) — DWARF unwinds straight through `call` frames using `.eh_frame` without needing a landing pad in that function!

---

### Problems (Ranked Most Serious First)

#### 1. [Rank 1 — Critical Bug, Q2] `_Unwind_ForcedUnwind` + `_Unwind_Resume` + `longjmp` in the stop function breaks on Apple `libunwind` and Linux `libgcc_s`, and breaks nested `Fail` / fiber switches inside `defer`

Look closely at how `_Unwind_ForcedUnwind` and `_Unwind_Resume` actually work inside `libgcc_s` (`unwind.inc`) and Apple/LLVM `libunwind` (`UnwindLevel1.c`):

1. **Apple/LLVM `libunwind` bug with `_Unwind_ForcedUnwind` + `_Unwind_Resume`:**
   In LLVM's `libunwind` (which macOS uses!), `_Unwind_Resume(ex)` checks `(ex->exception_class & 0xFFFFFFFF) == 0` or calls `unwind_phase2(uc, cursor, ex)` **instead of** `unwind_phase2_forced(uc, cursor, ex, stop, stop_parameter)` unless the private fields `ex->private_1` (the `stop` function pointer) and `ex->private_2` (`stop_parameter`) are preserved and dispatched! Even worse, on several versions of Apple system `libunwind`, `_Unwind_Resume` unconditionally calls normal `unwind_phase2` (ignoring `private_1`!), so after the **first** `landingpad cleanup` runs and executes `resume`, **your stop function is never called again** and unwinding walks right past your task/fiber root and crashes!
2. **Fiber switching or nested `try`/`catch` inside a `defer` while unwinding:**
   Consider this legal Flyscript program (`§5.6`, `§5.7`):
   ```ts
   export function work(): void uses Io {
     defer {
       // Inside a defer running during panic unwinding:
       // 1. We call a function that uses `try { ... } catch (e) { ... }`
       // 2. Or we call `Io.sleep(Duration.ms(1))`, which switches fibers!
       Io.sleep(Duration.ms(1));
     };
     panic("boom");
   }
   ```
   - While `work()` is paused at `Io.sleep` inside its `landingpad cleanup`, the exception object `ex` must live in the **task/fiber struct** (`task->panic_ex`), NOT in a stack local of `fly_panic()` (because `fly_panic()`'s stack frame was below the landing pad and has already been unwound past when `_Unwind_SetIP` jumped to the landing pad!).
   - And what if the `defer` spawns a child `Io.scope` or calls `join` whose child panics and catches its own panic while the outer task is paused mid-landing-pad? If you use normal **`_Unwind_RaiseException(&task->panic_ex)`** with a custom `exception_class` (`"FLYSCRPT\0"`):
     - Phase 1 walks the fiber's stack from `fly_panic` up to the catch frame (`landingpad catch ptr null` at the task root / `Io.scope` / `Mutex.lock` / `join` / handler boundary) and caches the target frame in `task->panic_ex`.
     - Phase 2 jumps to each `landingpad cleanup` along the way. No unwinder frame is on the stack while the landing pad runs (`_Unwind_SetIP` restored `SP` to the function's frame). So `Io.sleep` inside the `defer` can freely switch fibers!
     - When the `defer` finishes, `resume` calls `_Unwind_Resume(&task->panic_ex)`, which works reliably on 100% of `libgcc_s` and Apple `libunwind` versions because `_Unwind_RaiseException` + `_Unwind_Resume` is the standard C++ exception path!
     - And at the catch boundary (task root, `Io.scope`, `Mutex.lock`, `join`), instead of a stop function that `longjmp`s out of the middle of `libunwind`, you simply use a **catch landing pad** (`landingpad { ptr, i32 } catch ptr null`) in the LLVM wrapper or `fly_call_catch_panic(fn, ctx)`!

**Fix:**
- Use **`_Unwind_RaiseException(&task->panic_ex)`**, NOT `_Unwind_ForcedUnwind`.
- Since Flyscript `try`/`catch` (`Fail`) does **not** use DWARF exceptions (it uses your normal failure return path), **panics are the ONLY thing using DWARF unwinding in the entire program!**
- That means no user `try`/`catch` ever intercepts `_Unwind_RaiseException`. Only your runtime boundaries (`task_entry`, `Io.scope`, `Mutex.lock`, `join`, and dropped-continuation unwind boundaries) have `landingpad ... catch ptr null`, and every normal Flyscript scope with cleanup has `landingpad ... cleanup`.
- You can implement a single 10-line LLVM IR helper function emitted into every module:
  ```llvm
  define i32 @__fly_catch_panic(ptr %fn, ptr %arg) personality ptr @__gcc_personality_v0 {
  entry:
    invoke void %fn(ptr %arg) to label %ok unwind label %caught
  ok:
    ret i32 0
  caught:
    %lp = landingpad { ptr, i32 } catch ptr null
    ret i32 1
  }
  ```
  Now your C runtime (`rt`) calls `__fly_catch_panic(fn, arg)` at task roots, `Io.scope`, `Mutex.lock`, and `join` — **no `setjmp`, no `longjmp`, no `_Unwind_ForcedUnwind` stop function, and 100% standard Phase 1 + Phase 2 DWARF semantics!**

---

#### 2. [Rank 2 — Critical Bug, Q2] ASan and TSan Failure Modes with DWARF Unwinding on Fibers

You asked what traps exist with ASan (`-fsanitize=address`) and TSan (`-fsanitize=thread`) when unwinding across fibers:

1. **TSan (`-fsanitize=thread`) shadow call stack corruption if you ever `longjmp` from a stop function:**
   - TSan instruments every function entry (`__tsan_func_entry`) and exit (`__tsan_func_exit`) to maintain a per-fiber shadow call stack.
   - When LLVM emits `landingpad cleanup` and `resume`, LLVM's TSan pass automatically inserts `__tsan_func_exit` along the `landingpad` / `resume` unwind edges!
   - If you had used `_Unwind_ForcedUnwind` + `longjmp` in a stop function, any frame *without* a landing pad between two landing pads would **skip `__tsan_func_exit`** if `longjmp` bypassed TSan's personality interception, corrupting the fiber's TSan shadow stack!
   - With `_Unwind_RaiseException` + `landingpad catch ptr null` in `@__fly_catch_panic`, TSan's `_Unwind_RaiseException` interceptor and LLVM's landingpad instrumentation keep the fiber's TSan shadow call stack 100% balanced!
2. **Phase 1 stack-top sentinel on custom fiber stacks (macOS `libunwind` & Linux `libgcc_s`):**
   - In `_Unwind_RaiseException`, Phase 1 walks up the stack until it finds a `catch` handler (`@__fly_catch_panic`).
   - Because `@__fly_catch_panic` is ALWAYS at the root of every fiber / task / `Io.scope` / `Mutex.lock` / `join`, Phase 1 stops **at `@__fly_catch_panic`** and NEVER tries to unwind past the bottom of the fiber's stack (`fly_fiber_trampoline`)!
   - By contrast, if Phase 1 ever walked past `fly_fiber_trampoline` (where `RBP`/`FP` is 0 or points to the parent stack), `libunwind` can segfault or ASan can report a stack-buffer-overflow when reading CFA outside the fiber stack. Putting `@__fly_catch_panic` inside the fiber entry guarantees Phase 1 always stops inside the fiber stack.
3. **ASan poisoned redzones on unwound stack frames:**
   - Under `-fsanitize=address`, LLVM poisons local stack variables on scope exit. When `fly_panic` unwinds frames that have **no** `landingpad cleanup` (pure functions with only stack arrays/structs that don't implement `Drop`), DWARF Phase 2 skips straight over those frames without running their epilogues, leaving ASan shadow bytes poisoned on that stack region!
   - In ASan's runtime, the `__interceptor__Unwind_RaiseException` and `landingpad` instrumentation calls `__asan_handle_no_return()` before jumping. Make sure `fly_panic` calls `__asan_handle_no_return()` (when `__SANITIZE_ADDRESS__` is enabled) right before `_Unwind_RaiseException`, and at `@__fly_catch_panic` before reusing the stack!

---

#### 3. [Rank 3 — Soundness & Performance, Q3 & Q4] Emit `invoke` ONLY When Active Cleanups Exist in the Enclosing Function!

In your proposal and Question 4, you ask:
> *"Cost of `invoke` vs `call` in hot loops after LLVM's optimizations (blocking some transformations?)."*

Here is the single biggest win of DWARF unwinding over `setjmp`, and a trap to avoid when modifying `selfhost/llvm.fly`:

Suppose function `A` has a `defer` or owns a `String` (`Drop`), and `A` calls `B`, which calls `C` in a hot loop (where `B` and `C` only use primitives, slices, or `Copy` structs, and have **no** `Drop`, `defer`, or `region` of their own):
- **In `B` and `C`, you do NOT emit `invoke` or `landingpad` at all!**
- Every call inside `B` and `C` stays an ordinary LLVM `call` instruction!
- The **only** requirement on `B` and `C` is that their `define` in LLVM IR has the **`uwtable`** attribute and does **not** have `nounwind`!
- Why? Because DWARF unwinding walks straight through normal `call` instructions in `B` and `C` using the compiler-generated `.eh_frame` (`uwtable`) with **zero landing pads and zero `invoke` basic-block splits in `B` and `C`**!
- Even inside function `A` (which *does* have a cleanup scope in Part 2 of `A`), any call in Part 1 of `A` *before* the first `Drop`/`defer`/`region` is live (or after all of them have been dropped) stays a plain `call`, not an `invoke`!

Why does this matter so much for Question 4 (hot loops and inlining)?
1. In LLVM, an `invoke` instruction is a **basic-block terminator** (it splits the basic block into normal and unwind edges). Splitting a basic block at every call inside a loop prevents loop vectorization, SLP vectorization, and several loop-invariant code motion (LICM) passes across that call.
2. When you only emit `invoke` at call sites that actually have an **active enclosing cleanup (`unwN`) in the current function**, any loop that doesn't hold a live `Drop`/`defer`/`region` across the call uses plain `call`!
3. Better yet: for intrinsics and leaf operations that **cannot panic** (`llvm.sadd.with.overflow` before the branch, `memcpy`, `Ptr.read`, `vec.len()`), keep `nounwind` on their declarations and emit `call` even inside cleanup scopes — only the cold panic branch (`if (overflow) call @fly_panic(...)`) needs to be an `invoke @fly_panic(...)`!
   Read that last sentence again:
   **For checked arithmetic (`a + b`) and inline bounds checks (`if (i >= len) fly_panic()`), the hot path is a compare + branch, and ONLY `@fly_panic` itself is `invoke`d on the cold branch!** That means checked arithmetic and bounds checks in hot loops don't split the hot loop block with `invoke` even inside functions with cleanups!

---

#### 4. [Rank 4 — Correctness Trap, Q3] Three LLVM IR Details You Must Get Right in `selfhost/llvm.fly`

When adding `invoke` + `landingpad` to `selfhost/llvm.fly`:

1. **`uwtable` attribute is mandatory on every function that may unwind:**
   In textual LLVM IR, if you merely remove `nounwind` from `define void @foo()`, LLVM on AArch64 (macOS) and x86-64 will still omit `.cfi_*` / `.eh_frame` unwind info if `-funwind-tables` isn't passed to `llc`/`clang` or `uwtable` isn't on the IR function!
   - Put `uwtable` on every `define` in `selfhost/llvm.fly` (or pass `-funwind-tables` when compiling `.ll` slices in `llvm.sh`). `uwtable` has zero runtime instruction overhead (it only emits `.eh_frame` metadata in the object file) and guarantees DWARF Phase 1 can unwind through every frame.
2. **Idempotence of cleanups when a local is moved or dropped on the normal path before a panic:**
   In your `ir.fly`, a block with cleanup already maintains drop flags (or cleanup states) for variables that may be moved conditionally, and drops locals at the end of the block on the normal path.
   - Make sure that if a panic happens **inside** the block's normal-exit cleanup sequence (e.g., local `y` is dropped first, and then while dropping local `x` or running a `defer`, a call panics!), the `landingpad` for that block does **not** drop `y` a second time!
   - Concretely: either clear `y`'s drop flag (`drop_y = 0`) right before calling `drop(y)` on the normal exit path, or have the normal exit path transition out of `y`'s `invoke` landingpad scope before dropping `y`.
3. **`ThinLTO` (`llvm.sh`) + `personality ptr @__gcc_personality_v0`:**
   - When ThinLTO inlines a function `@callee` (which has `invoke` + `landingpad` and `personality ptr @__gcc_personality_v0`) into a caller `@caller` that originally had **no** landing pads and therefore **no** `personality` on its `define`, LLVM's inliner automatically copies the `personality` attribute onto `@caller` — **unless** `@caller` was marked `nounwind`!
   - If `@caller` is marked `nounwind` and LLVM inlines `@callee` into `@caller`, LLVM converts every `invoke` inside `@callee` into a `call` (discarding `@callee`'s landing pads, or turning unwind into `unreachable`/abort!).
   - Therefore: **never put `nounwind` on any Flyscript function in `llvm.fly`** except `export extern "C"` entrypoints (which cannot unwind into C per `§8.2`).

---

#### 5. [Rank 5 — Wasm Backend, Q1] Use `-fwasm-exceptions` Instead of `-wasm-enable-sjlj` for Wasm

You noted that for Wasm you currently compile via LLVM with `-mllvm -wasm-enable-sjlj`.
Look at what `-mllvm -wasm-enable-sjlj` does under the hood in LLVM's Wasm backend:
- It runs the `WebAssemblyLowerEmscriptenEHSjLj` pass, which rewrites **every** function call in every function that calls `setjmp` into an indirect state-machine dispatch through `__threwValue` checks and `setThrew` calls — the exact same inlining-blocker and 2× slowdown you just measured natively!
- Meanwhile, since your Wasm backend **already goes through `selfhost/llvm.fly`** (`§0.1`: *"0.108 compiles WebAssembly through LLVM, as native code is, rather than through C"*):
  - If `selfhost/llvm.fly` emits `invoke` + `landingpad`, passing `-fwasm-exceptions` (or `-mllvm -wasm-enable-eh -mllvm -exception-model=wasm`) to `clang --target=wasm32-wasi` compiles that **exact same `invoke` + `landingpad` LLVM IR** directly to native WebAssembly `try_table` / `throw` instructions!
  - Node 24 supports native Wasm exception handling out of the box with zero flags, and it has zero overhead on the non-panicking path and full inlining!
  - That leaves `setjmp` records **exclusively for the portable C backend (`selfhost/c.fly`)**, where bootstrap speed is secondary and where a simple static "can this function or its callees panic?" reachability bit on the call graph in `ir.fly` can still elide `setjmp` from trivial helper functions.

---

### Summary of Ranked Risks & Action Plan

1. **[Rank 1 — Do Not Use `_Unwind_ForcedUnwind`]:** Use standard `_Unwind_RaiseException(&task->panic_ex)` + `@__fly_catch_panic` (`landingpad { ptr, i32 } catch ptr null`) at task/scope/mutex/join boundaries. `_Unwind_ForcedUnwind` + `_Unwind_Resume` fails to call the stop function after the first cleanup landing pad on Apple `libunwind`, and `longjmp` from a stop function corrupts TSan shadow call stacks.
2. **[Rank 2 — Emit `invoke` Only Under Active Cleanups]:** In `selfhost/llvm.fly`, emit plain `call` whenever the current function has no active cleanup (`unwN`) at that point, and keep `a + b` / `xs[i]` hot paths as plain `call` + branch to a cold `invoke @fly_panic`.
3. **[Rank 3 — `uwtable` and No `nounwind`]:** Put `uwtable` on all emitted LLVM functions, compile runtime C with `-fexceptions -funwind-tables`, and remove `nounwind` from all Flyscript functions so ThinLTO inlining never strips landing pads.
4. **[Rank 4 — Drop-Flag Clearing Before Normal Cleanup]:** Clear a local's drop flag (or advance the unwind target) *before* running its destructor on the normal exit path, so a panic inside a destructor or `defer` during normal scope exit never double-drops an earlier local in the same scope's `landingpad`.
5. **[Rank 5 — ASan Shadow Unpoisoning]:** Call `__asan_handle_no_return()` in `fly_panic` before `_Unwind_RaiseException` when compiled with ASan so unwound frames without landing pads do not leave poisoned stack redzones on the fiber stack.
