### Verdicts

- **(1) Representation (`readonly T` by value for `Copy`, recursive types only through `Box`/`Vec`):** **Agree with changes.** Three rules in the spec contradict these assumptions: (a) recursive types also go through `Ref<R, T>` (`§3.3`, `A.1`, `A.5`), so C struct emission must be topologically sorted with forward declarations before pointer types (`Box<T>`, `Ref<R, T>`, `Vec<T>`); (b) passing `readonly T` by value for all `Copy` types breaks **address stability** when returning a sub-borrow (`readonly Field from self`) and copies huge `Copy` arrays (`u8[65536]`); (c) in C11, arrays `T[N]` cannot be assigned or returned by value unless wrapped in `struct { T data[N]; }`.
- **(2) Ownership, drops, and ownership-pass facts:** **Agree with changes.** Unlike JS (where GC cleans up heap memory and only user `Drop` matters), C requires dropping every `String`/`Vec`/`Box`/`HashMap`/`Arc`/closure, which exposes **four places where the current ownership pass's facts are insufficient for C**: uncalled escaping closures (need an `env_drop` function pointer in the fat pointer), partial moves of struct fields (`§5.6`), reassignment of live places (`§5.6`: *"Assigning to a place drops the value it held first"*), and short-circuiting/branching expression temporaries.
- **(3) `Fail<E>` via status return + `goto` cleanup chain vs shadow stack + `longjmp`:** **Agree with status return + `goto` cleanup chain.** Do not use `setjmp`/`longjmp` for `Fail`. However, you must change **panics** (`§5.7`, `§6.1`): in Flyscript, a panic inside a task *unwinds the task and fails/cancels its scope* (tested in the corpus!). With `goto` cleanup chains already emitted in every function, a task panic is just another unwind status code on the exact same `goto` chain — zero `setjmp` needed.
- **(4a) Internal-iterator lowering for `for (x of gen())` and tail-resumptive handlers:** **Agree for tail-resumptive user handlers (evidence passing); Disagree for `for (x of gen())` where the loop body can `break`/`return`/`throw` out of nested generators.** Internal iteration for `Yield` forces every `Yield` function to be compiled *twice* (push for `for…of`, pull for `generate()`), cannot propagate early `break`/`return` when a generator calls another generator alongside other statements, and is completely subsumed once you have stackful coroutines in M3.
- **(4b) Minimum coroutine story for `Cont`, `Gen`, and tasks:** **Agree with changes.** A 40-line inline-assembly context switch (`swap_sp` on x86-64 and AArch64) + one unwind flag on `Cont` handles `Gen`, general `handle`, and `Io.scope` tasks uniformly.
- **(8) Order of milestones:** **Agree with one swap:** move **M4 (self-hosting the compiler natively)** ahead of M2/M3, right after M1 + `Region`! The self-hosted compiler (`selfhost/*.fly`) uses **only** M1 + `Region` + `for…of` over slices/`Vec`/`Range`/`HashMap` (zero user `Yield` functions, zero `handle`, zero tasks). You can reach native self-hosting immediately after M1!

---

### Problems

#### 1. Question (2) & (5): Four places where JS drop-flag facts are insufficient for C (`§4.1`, `§4.3`, `§5.6`)

In the JS backend, failing to drop a `String`, `Vec`, `Box`, or closure only leaks memory until V8's GC collects it; in C, it is either a memory leak, a double-free, or a use-after-free. Here are the four cases your C emitter must handle that JS did not:

**Case 1A: Escaping closures that are dropped without being called (`once`, `mut`, and shared) (`§4.3`).**
You wrote in (5): *"once closures free their env after the call."*
What if an escaping `once` closure (such as `#Fresh(start)` inside a `Gen` that is dropped before `.next()` is ever called, or a callback stored in a struct/enum) is **never called**, or what if a shared/mut escaping closure (which can be called 0, 1, or N times!) is dropped when its owner goes out of scope?
```ts
function makeGreeter(prefix: String): (str) => String {
  // Escaping shared closure owns `prefix: String` on the heap (§4.3)
  (name: str) => `${prefix}: ${name}`
}

export function main(): void {
  const f = makeGreeter("hello".toString());
  // `f` is never called (or called 3 times) and then goes out of scope here!
}
```
If a `once` closure frees its `env` inside `fn` and has no external destructor, dropping an uncalled `once` closure leaks `env` and all owned values (`String`, `Vec`, `File`) inside it; and a shared/`mut` closure *cannot* free its `env` inside `fn` because it may be called again!
**Fix:**
Every closure type `(A) => B` in C is a 3-word fat pointer (or 2 words where `env` starts with a destructor header):
```c
typedef struct {
  void* env;
  void (*drop_env)(void* env); // NULL for non-escaping (stack-env) or zero-capture closures
  R (*fn)(void* env, ...);
} fly_fn_N;
```
- For a **stack-allocated (class-2) closure**, `drop_env = NULL`.
- For an **escaping (class-1) closure**, `env` is heap-allocated and `drop_env` drops each captured owned field and calls `free(env)`:
  - If the closure is `once`, calling `fn(env, ...)` moves the captures out of `env` and calls `free(env)`, and the caller clears the closure's drop flag (since calling a `once` closure moves it, `§4.3`). If the `once` closure is *not* called before scope exit, the scope exit sees its drop flag is still set and calls `if (f.drop_env) f.drop_env(f.env);`!
  - If the closure is shared or `mut`, calling `fn` does *not* free `env`; when the closure binding is dropped at scope exit, `if (f.drop_env) f.drop_env(f.env);` runs!

**Case 1B: Partial moves out of structs (`§4.1`, `§5.6`).**
`§4.1` and `§5.6` state: *"Moving a field out of a value moves only that field, unless the value's type implements `Drop`... Dropping a value from which fields were moved — possible only when its type does not implement `Drop` — drops the fields still in it."*
```ts
struct Pair { a: String; b: String; }

export function main(): void {
  let p = Pair { a: "left".toString(), b: "right".toString() };
  const x = p.a; // moves `p.a` only!
  // At scope exit, `p.b` must be dropped, and `p.a` must NOT be dropped!
}
```
In JS, `Pair` does not implement user `Drop`, so the JS backend emitted **no** drop flag for `p`. In C, `Pair` *needs drop* because `String` owns heap memory! If you only have a single boolean drop flag `$drop_p` per local binding `p`, moving `p.a` either clears `$drop_p` (leaking `p.b`) or leaves `$drop_p` set (double-freeing `p.a`!).
**Fix (zero extra ownership analysis needed):**
In C, represent an empty moved-out `String` / `Vec` / `Box` / `HashMap` / `Arc` / `Cont` / closure with a **null pointer (`ptr = NULL` / `env = NULL`)**, and make every C drop function null-safe (`if (s.ptr) free(s.ptr);`)!
When moving a field path `p.a` (or whole variable `p`) of a type that needs drop, emit:
```c
fly_String x = p.a;
p.a = (fly_String){0}; // zero out moved place!
```
Look at what zeroing the moved place (or moved subfield) gives you:
1. Partial moves (`const x = p.a;`, `const y = p.inner.vec;`) work automatically at arbitrarily deep field paths without per-field boolean drop flags: `Pair$drop(&p)` calls `String$drop(&p.a)` (no-op because `p.a.ptr == NULL`) and `String$drop(&p.b)` (frees `p.b.ptr`)!
2. You still keep boolean drop flags `$drop_x` only for nominal types that implement **user `Drop`** (`§4.1`: *"unless the value's type implements `Drop`, from which no field may be moved"*, so user-`Drop` types never have partial moves!).

**Case 1C: Reassignment to a live place (`§5.6`).**
`§5.6` states: *"Assigning to a place drops the value it held first, unless that value was moved out: `h = Holder { tx: b }` drops the old holder."*
And this includes assigning to an indexed element `xs[i] = newVal;` or a struct field `p.a = newVal;`!
In C:
- Before assigning `lhs = rhs` where `lhs`'s type needs drop: evaluate `rhs` into a temporary `$tmp` *first* (in case `rhs` reads `lhs` or throws `Fail`), then call `T$drop(&lhs)` on the old value of `lhs` (if `lhs` is not marked fully moved, or unconditionally if moved places are zeroed as in Case 1B!), and then assign `lhs = $tmp`!

**Case 1D: Temporaries inside short-circuiting expressions (`&&`, `||`, `if`, `match` guards) (`§4.1`).**
`§4.1` states: *"A value that is borrowed without having a place — a call's result, a template string, a literal lent as `str` — is stored in an anonymous local of the enclosing block, dropped when the block ends."*
If `if (a && makeString().asStr() == "ok")` hoists the anonymous local `fly_String $tmp1;` to the enclosing block, `$tmp1` is only initialized when `a` is `true`!
Because zero-initialized `{0}` is a no-op to drop (Case 1B), initializing hoisted temporaries at declaration as `fly_String $tmp1 = {0};` makes unconditional block-exit `String$drop(&$tmp1)` completely safe even when the branch/short-circuit was not taken!

---

#### 2. Question (1): Passing `readonly T` by value for `Copy` types creates dangling pointers when returning sub-borrows (`§4.1`, `§4.2`)

You proposed in (1): *"`readonly T` = `const T*` for non-Copy, by value for Copy."*
Look at what happens in valid Flyscript when a function takes `readonly T` (where `T` is `Copy`) and returns a `readonly` borrow of a field or array element tied to that parameter (`§4.2`), or takes the address of a field:

```ts
struct Pair { a: i32; b: i32; } // Copy!
struct BigBuf { data: u8[4096]; } // Copy!

function pickA(p: readonly Pair): readonly i32 from p {
  p.a // returns a `readonly i32` borrowing `p`!
}

function firstSlice(b: readonly BigBuf): readonly u8[] from b {
  b.data[0..10] // returns a slice `{ ptr, len }` pointing into `b.data`!
}

export function main(): void {
  const b = BigBuf { data: repeat(42) };
  const s = firstSlice(b);
  // If `b: readonly BigBuf` was passed BY VALUE into `firstSlice`,
  // `b.data` inside `firstSlice` was on `firstSlice`'s stack frame,
  // so `s.ptr` is now a DANGLING POINTER to dead stack memory!
}
```
Look at `firstSlice(b)`: `BigBuf` is `Copy` (`u8[4096]` is `Copy` by `§3.1`). If `b: readonly BigBuf` is passed by value to `firstSlice`, `b` is copied onto `firstSlice`'s C stack frame, `b.data[0..10]` takes `&b.data[0]` on `firstSlice`'s stack frame, and when `firstSlice` returns, `s.ptr` points to a popped stack frame — an immediate use-after-free in C!

**Fix:**
- Either represent `readonly T` as `const T*` **for all aggregate types** (structs, records, unions/enums, tuples, fixed arrays `T[N]`) and pass by value **only for scalar primitives** (`i8`..`i128`, `u8`..`u64`, `f32`, `f64`, `bool`, `str`, `T[]`, `Ref<R, T>`) unless a `readonly Prim` is returned by reference;
- Or even simpler and more uniform: **`readonly T` is `const T*` whenever `T` is an aggregate or when `readonly T` appears in a return type; for scalar parameters not returned by borrow, pass by value (if a sub-borrow of a scalar parameter is taken, copy it to a `const T` local on entry? No, if it's returned `from p`, the parameter itself must be `const T*` so the returned `const T*` points into the caller's frame!).**
Making `readonly T` be `const T*` for all aggregates (and for any parameter named in the return's `from` sources when the return type contains `readonly`/`T[]`) guarantees:
1. `firstSlice(b)` and `pickA(p)` point into the caller's `b` / `p` (sound!).
2. Passing `readonly AstNode` or `readonly u8[4096]` in the compiler passes an 8-byte pointer instead of copying kilobytes of structs/arrays on every call!

Also in (1), two C11 type-emission rules to get right from day one:
1. **Fixed-size arrays `T[N]`:** In C11, a bare `T[N]` decays to `T*` in parameters and cannot be assigned (`a = b`) or returned by value from a function. Always emit `T[N]` as a C struct wrapper `typedef struct { T data[N]; } fly_arr_T_N;`. Then value assignment, pass-by-value, and return-by-value work uniformly in C11!
2. **Recursive types via `Ref<R, T>`, `Box<T>`, and `Vec<T>`:** You wrote *"Recursive types only through Box/Vec"*, but `§3.3`, `§4.6`, `A.1` (`enum Json<region R>`) and `A.5` (`struct Scope<region R> { parent: Option<Ref<Scope>>; ... }`) have recursive structs and enums through `Ref<R, T>` and `RegionList<R, T>`!
   Because `Option<Ref<Scope>>` is a value struct `{ uint32_t tag; union { const Scope* Some; } }` contained *by value* inside `struct Scope`, emit C types in three passes:
   - Pass 1: `typedef struct fly_S_N fly_S_N;` forward declarations for all monomorphized structs and enums.
   - Pass 2: Topological sort of value-dependency graph (where `Box<T>` = `T*`, `Ref<R, T>` = `const T*`, `Vec<T>` = `{ T* ptr; ... }`, `RegionList<R, T>` = `fly_RegionList*` are **pointer edges** that do not require `T`'s body to be complete, whereas `Option<T>` or a by-value field `f: T` is a **value edge**).

---

#### 3. Question (3): `goto` cleanup chains for `Fail<E>` AND Task Panics (`§5.4`, `§5.6`, `§5.7`, `§6.1`)

Your proposed `goto`-cleanup-chain lowering for `Fail<E>` is **much better** than `setjmp`/`longjmp`:
- `setjmp` disables register allocation across the function in C (`-Wclobbered`), costs ~20–50ns even when no error is thrown, and interacts badly with stack switching.
- With status return + `goto` cleanup chain, the happy path is a single register test `if (FLY_UNLIKELY(st != 0)) goto cleanup_3;`, which C compilers predict and sink out of hot loops.

However, look at what you wrote at the end of (3): *"Panics: print and abort (no unwinding)."*
Check `§5.7` and `§6.1` Rule 3:
> `§5.7`: *"A panic is not an effect and cannot be caught by a handler: it unwinds the current task, running cleanup, and fails the task's scope (§6.1); an unscoped panic terminates the process."*
> `§6.1`: *"If a forked task fails, or any task panics, the scope is cancelled: the body and every other task stop at their next `Io` operation and unwind, and once all have finished the first failure is rethrown from `Io.scope` (or the panic continues)."*

If a panic calls `abort()` without unwinding:
1. Any `defer` or `Drop` cleanup along the stack does not run on panic (`§5.7` explicitly requires *"it unwinds the current task, running cleanup"*).
2. Any corpus test where a spawned/forked task panics or a scope is cancelled on `Io` will crash the process instead of unwinding!

**How to get panic & cancellation unwinding for free without `setjmp`:**
 wait — in a function without `Fail<E>`, most panics are integer overflow or out-of-bounds indexing. If only `Io.scope` tasks need to catch/propagate panics or cancellation, whereas unscoped panics terminate the process (after running cleanup if needed, or in tasks):
Look at the return status of functions:
- For `Fail<E>` functions: return a status enum `typedef enum { FLY_OK = 0, FLY_FAIL = 1, FLY_UNWIND = 2 } fly_status;` (where `FLY_FAIL` means the thread/fiber-local `fly_err_val` union holds `E`, and `FLY_UNWIND` means panic/task-cancellation is unwinding the fiber!).
- Inside `try { ... } catch (e) { ... }`, the `try` handler intercepts **only `st == FLY_FAIL`**; if `st == FLY_UNWIND` (panic or scope cancellation), it jumps straight to the enclosing cleanup label to keep unwinding the fiber!
- And what if a panic or cancellation happens inside a function whose signature does *not* have `Fail<E>` while running inside a coroutine/fiber (M3)? In M3, each coroutine/fiber has a single `jmp_buf` at the fiber root (or one shadow cleanup frame pointer per active `Drop`/`defer` scope if a pure function panics), **or** every function that contains a `Drop`/`defer` can unwind via `goto`. Even simpler: in M1 (single task, unscoped), an unscoped panic terminates the process (`§5.7`), so `fprintf(stderr, "panic: ..."); exit(1);` passes 100% of M1 and M4! Only when you add tasks in M3 does task cancellation at `Io` operations happen — and `Io` operations are in functions with `uses Io`, which can return `FLY_UNWIND` along the exact same `goto` cleanup chain as `FLY_FAIL`!

**One crucial detail for `goto` cleanup chains with `return` / `break` / `continue` / `Fail`:**
Suppose Block 1 owns `a: String`, and inside it a `while` loop (Block 2) owns `b: String`, and inside that Block 3 owns `c: String`:
```ts
function f(xs: readonly i32[]): i32 uses Fail<#Bad> {
  const a = "outer".toString();
  for (const x of xs) {
    const b = "loop".toString();
    if (x < 0) { throw #Bad; }   // must drop `b` AND `a`, then return FLY_FAIL
    if (x == 0) { break; }       // must drop `b` ONLY, then exit loop (`a` stays alive!)
    if (x == 1) { return 42; }   // must drop `b` AND `a`, then return FLY_OK (42)
  }
  a.len() as i32                 // drops `a`, returns FLY_OK
}
```
Notice that `break` and `continue` must stop unwinding at the loop boundary (dropping `b`, NOT `a`), whereas `return` and `throw` must unwind all the way to the function root (dropping `b` AND `a`)!
The clean C pattern that avoids duplicating cleanup code for every exit kind is an integer `$exit_target` variable per function:
```c
// Exit target constants for this function:
// 0 = normal fallthrough at end of block
// 1 = function return (FLY_OK)
// 2 = function fail (FLY_FAIL)
// 3 = break loop_1, 4 = continue loop_1, 5 = catch_1, ...
```
Or, since each block only has 1–3 drops in practice, a helper macro/inline sequence that drops all live bindings from the current scope depth `d` down to target scope depth `target_d` directly before `goto label;`!
Wait: **emitting the drops of scopes `[target_d .. current_d]` directly at each `break` / `continue` / `return` / `throw` site (or a per-scope fail label for `throw`)** is even simpler than a state machine:
- For `break` / `continue`: you statically know the exact enclosing loop's scope depth `loop_d`. Emit `drop_scopes(current_d down to loop_d); goto loop_break;`.
- For `return val`: store `$ret = val;`, emit `drop_scopes(current_d down to 0); return FLY_OK;`.
- For `throw err` (or a failed call `if (call(...) != FLY_OK)`): `goto fail_scope_d;`, which is a pure linear chain of labels at the bottom of the function (`fail_scope_3: drop(c); fail_scope_2: drop(b); fail_scope_1: drop(a); return FLY_FAIL;` — or if inside `try`, `fail_scope_2` jumps to `catch_1:`)!
Look how clean that is:
- The `fail_scope_d:` chain at the bottom of the function handles **all** `Fail` unwinding with zero branching (`fail_3` falls straight through to `fail_2` which falls through to `fail_1`, stopping at the nearest enclosing `catch` label if inside a `try`!).
- `break`, `continue`, and `return` emit their scope drops inline and `goto` directly to their target label!

---

#### 4. Question (4a) & (4b): Why internal iteration (`for (x of gen())`) is a trap for `Yield`, and how a 40-line coroutine primitive solves M2 + M3 together (`§5.2`, `§5.3`, `§5.5`)

Let's test your proposal (4a) — compiling a `Yield<T>` function as an internal iterator that takes the loop body as a callback `(env*, fn*)` — on a 12-line Flyscript program:

```ts
function inner(xs: readonly i32[]): void uses Yield<i32> {
  defer println("cleanup inner");
  for (const x of xs) { yield x; }
}

function outer(xs: readonly i32[]): void uses Yield<i32> {
  defer println("cleanup outer");
  inner(xs);
  // Look here: `outer` does more work AFTER `inner(xs)` finishes naturally,
  // unless the caller broke out of `for (const y of outer(xs))` during `inner(xs)`!
  println("between inner and final yield");
  yield 99;
}

export function main(): void uses Io {
  for (const y of outer([1, 2, 3])) {
    if (y == 2) { break; }
  }
}
```
Trace what happens when `main` runs `if (y == 2) { break; }`:
1. `y == 2` was yielded inside `inner`, which was called by `outer`.
2. In Flyscript (`§5.5`), `break` inside `main`'s loop must unwind `inner` (running `defer println("cleanup inner")`) **AND** immediately unwind `outer` (running `defer println("cleanup outer")` and **skipping** `println("between inner and final yield")` and `yield 99`), and then resume `main` after the `for` loop!
3. What if `outer` was instead called inside `generate(() => outer([1, 2, 3]))` (`§5.5` pull iterator `Gen`)? Now `outer` and `inner` **cannot** use internal iteration at all — they *must* be compiled as stackful coroutines so `.next()` can suspend and return `#Some(item)`!
4. What if a generator function has a `try { inner(xs); } catch (e) { ... }` around `inner(xs)`, and the `for` loop body in `main` throws `#CallerError` or `break`s? If the `for` loop body in `main` throws `#CallerError` or `return`s from `main`, that error/return belongs to **`main`'s** `try`/`return` frame, **NOT** `outer`'s `try/catch`! If `inner` returns a control code through `outer`, `outer` has to distinguish *"did `inner` itself fail (which `outer`'s `try/catch` catches), or did `main`'s loop body fail/break/return (which must bypass `outer`'s `try/catch`, run `outer`'s `defer`s only, and propagate back to `main`)?"*!

By contrast, look at what happens when **every suspending effect (`Yield`, `Cont`, `Io` tasks)** uses the **same stackful coroutine primitive** (plus direct evidence-passing *only* for tail-resumptive `handle` arms like `Clock { now() resumes k => k(t) }`):
1. Every function is compiled **once**.
2. `yield v` inside `inner` switches back to the handler (`for…of` or `Gen.next()`).
3. In `for (const y of outer([1, 2, 3]))`, if the loop body executes `break`, `return`, or `throw`: the `for` loop simply calls `coro_drop(co)`, which resumes `co` with `co->status = FLY_UNWIND`! Inside `inner`, `yield v` checks `if (co->status == FLY_UNWIND) goto fail_scope_d;` (jumping directly to the function's **existing `goto` cleanup chain**, bypassing `try/catch` because `status == FLY_UNWIND` != `FLY_FAIL`, running `inner`'s `defer`s and `outer`'s `defer`s, and exiting the coroutine cleanly)!

Look at that synergy:
**Unwinding a dropped continuation `Cont` or `break`ing from a `for…of` generator requires ZERO extra code in the function body** because `yield` / `perform` simply checks `if (FLY_UNLIKELY(co->unwinding)) goto unwind_scope_d;` — the exact same cleanup chain you already emit for `Fail<E>`!

**What is the minimum C coroutine runtime for (4b)?**
You do not even need a large library:
- Vendoring `minicoro.h` (single-file public-domain C header, ~1,500 lines, supports x86-64, AArch64, RISC-V, Wasm, Linux/macOS/Windows) **or** a 50-line `fly_coro` struct with SysV x86-64 + AArch64 `swap_context(from_sp*, to_sp)` inline asm (~20 instructions per arch) is all you need.
- Each coroutine has:
  ```c
  typedef struct fly_coro {
    void* sp;                 // saved stack pointer
    void* stack_base;         // mmap / malloc stack (e.g. 64 KB or growable)
    struct fly_coro* caller;  // who resumed this coroutine
    const char* eff_name;     // current yielded effect ("Yield", "Io", user effect)
    uint32_t op_id;           // operation index
    void* args_ptr;           // pointer to operation arguments on the yielder's stack!
    void* resume_ptr;         // pointer to operation return slot on the yielder's stack!
    bool unwinding;           // true when dropped (`Cont$drop` or `for…of` break)
    bool done;
  } fly_coro;
  ```
- Notice how fast argument/result passing is in C coroutines: when a coroutine performs `Eff.op(a, b)`, its stack stays live while suspended (`§5.3`), so `args_ptr` and `resume_ptr` point directly to structs on the suspended coroutine's stack — **zero heap allocation per `yield` or effect operation!**
- And for **tail-resumptive handlers** (`with Clock { now() resumes k => k(t) }` where every arm immediately tail-calls `k(...)`): you don't even allocate a coroutine! Pass the handler's `{ env, op_fns[] }` on a thread-local handler stack and call the arm function directly in place (`§11`: *"tail-resumptive handlers to direct calls"*).

---

#### 5. Question (6): Two subtle C pitfalls with `Region` (`RegionList` and alignment) (`§4.6`)

In (6), you proposed: *"a bump arena per `region` block; `Ref<R,T>` = `const T*`; `alloc` bumps; leaving the block frees the arena; `Cell` = pointer into the arena."*

Two details to make sure `Region` is 100% sound in C:

1. **Chunked bump arena (never `realloc` existing slabs!):**
   `§4.6` states: *"Because nothing in a region moves or is freed before the region ends... no borrow into region data can be invalidated."*
   If your bump arena used `realloc` when full, every existing `Ref<R, T>` (`const T*`) and `Cell<R, T>` (`T*`) would dangle!
   Therefore, a `fly_region` must be a linked list of slabs (e.g., 64 KB chunks; `alloc(size, align)` bumps the current slab's cursor aligned to `align`, or `malloc`s a new slab and links it if `cursor + size > end`). When the `region` block exits (whether normally or via the `goto` cleanup chain!), `fly_region_free(&r)` walks the slab list and `free`s each slab.
   *(And remember: a `region (R) { ... }` block must register `fly_region_free(&r)` in the function's `goto` cleanup chain so leaving a region via `return`, `break`, or `throw` frees the arena!)*

2. **`RegionList<R, T>` (`§4.6`):**
   `§4.6` states: *"and `RegionList<R, T>`, an append-only chunked list whose elements never move. Both are handles into their region — `Copy`, like a `Ref`... Reading a `RegionList`'s existing elements does not [perform `Region<R>`]: they never change."*
   Because `RegionList<R, T>` is `Copy` (`const items = RegionList.new(); items.push(x)`), its C representation must be a **pointer to a header allocated in the region** (`fly_region_list*`), NOT a by-value `{ ptr, len, cap }` struct! If it were a by-value `{ ptr, len, cap }`, copying the `RegionList` handle (`const b = items; items.push(x);`) would leave `b.len` stale, and `realloc`ing its backing array would invalidate borrows of existing elements!
   Allocating the `fly_region_list` header (`{ fly_region* reg; fly_chunk* head; fly_chunk* tail; size_t len; }`) inside the region arena and storing elements in linked power-of-two chunks allocated from `reg` takes ~25 lines of C and guarantees elements never move and handles are `Copy`!

---

#### 6. Question (8): Revised Milestone Order — Self-Host Natively in M2!

Look at what the self-hosted compiler (`selfhost/*.fly`) actually uses:
- Structs, enums, records, tag unions, tuples, `Vec`, `String`, `str`, slices, `Box`, `HashMap`, `HashSet`.
- Closures (passed down to `.iter().map(...)`, `.some(...)`, etc.).
- `Fail<E>` (`try` / `catch` / `throw`).
- `for (const x of ...)` over `Vec`, slices, `Range` (`0..n`), and `HashMap.entries()` — all of which are **built-in collections** that compile to ordinary C `for` loops without coroutines!
- Does `selfhost/*.fly` use user `Yield` functions, `generate()`, user `handle` blocks, or `Io.scope` tasks? **No!**

Therefore, reorder the milestones as follows:

1. **M1: Pure + `Fail` + `Region` + Drops (~35/52 corpus tests).**
   - Representations (with `struct { T data[N]; }` for arrays, `const T*` for aggregate `readonly T`, forward declarations + topo-sorted structs/enums).
   - Null-zeroing on moves (for `String`/`Vec`/`Box`/`HashMap`/`Arc`/closures) + boolean drop flags for user `Drop` + `goto` cleanup chains.
   - `Fail<E>` via status return + out-pointer + `fail_scope_d` label chain.
   - `Region` bump-slab arena + `RegionList` chunked list.
   - Built-in `for (const x of ...)` over arrays/slices/`Vec`/`Range`/`HashMap`/`HashSet`/`str.lines()`/`str.bytes()` as direct C `for` loops.
2. **M2 (was M4): Compile `selfhost` to C and reach native Stage 1 == Stage 2 fixpoint!**
   - Because `selfhost` only needs M1, you get a **native self-hosted `flyc` binary** right here (compiling itself in milliseconds instead of seconds on Node) and can use the fast native compiler to develop M3 and M4!
3. **M3 (was M2+M3): Stackful Coroutines for `Yield`, `Gen`, and `handle` (~47/52 corpus tests).**
   - Add the 50-line stack-switching coroutine (`fly_coro`) + direct evidence-passing for tail-resumptive handlers.
   - Compile `Yield<T>` functions, `generate()`, `Cont<A, B, E>`, and general `handle` arms over `fly_coro`, hooking `co->unwinding` directly into M1's `goto` cleanup chain.
4. **M4: Deterministic Scheduler over `fly_coro` for `Io.scope`, `spawn`, `fork`, `Mutex`, `channel`, and `SimIo` (52/52 corpus tests).**
   - Port the JS backend's deterministic fiber queue to C over `fly_coro`.

---

### Smaller points

- **`HashMap` lent-key lookup in C (Item 7 in your proposal):**
  `§3.1` and `§4.1` allow looking up a `HashMap<String, V>` or `HashMap<Ref<R, str>, V>` using a `str` (`counts.get(word)` in `A.2`).
  In C, `String` is `{ uint8_t* ptr; size_t len, cap; }` (24 bytes) while `str` is `{ const uint8_t* ptr; size_t len; }` (16 bytes).
  Notice that if `fly_String`'s first two fields are `{ uint8_t* ptr; size_t len; size_t cap; }` (or `{ fly_str s; size_t cap; }`), then a `const fly_String*` has the **exact same prefix layout** as `const fly_str*`! Even more generally, if the C `HashMap` lookup helper takes `(map, const void* query_key, hash_query_fn, eq_key_query_fn)`, then `counts.get(word)` hashes `word` (`fly_str`) and compares `eq(entry_key.as_str, word)` with zero allocation and full type safety.
- **C evaluation order of call arguments (`§4.1` two-phase borrows):**
  In C11, the evaluation order of function arguments `f(a(), b())` is **unspecified**!
  In Flyscript, arguments evaluate left-to-right, and two-phase borrows (`v.push(v.len())`, `replace(mut self.code, self.fresh())` in `§4.1`) or side-effecting calls (`alloc({ user: copyUtf8(raw[0..8]), token: copyUtf8(raw[8..16]) })` in `§10.2`, where the first `copyUtf8` might throw or bump the region before the second!) depend on deterministic left-to-right evaluation.
  In your C emitter, always bind any non-trivial call argument (anything containing a call, block, or mutation) to a local temporary before the C function call so evaluation order is strictly left-to-right.
