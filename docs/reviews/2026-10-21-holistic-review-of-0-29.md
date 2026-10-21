# Review: holistic-review-of-0-29

- spec: fb4558df3611
- request: 5903c6a6521ff464
- tokens: prompt 34875, cached 0, answer 13856

## Question

Spec 0.29 (included) adopts your review of 0.28: `Cont<A, B, E>` again (called `k(a)`, which performs `E` — the effects around its `handle` — and not `Send`, so a `Gen` is non-`Send` structurally); a continuation that leaves its arm makes whatever holds it borrow everything the arms use (the `handle`'s value also now includes its arms' values, which it silently did not before); several `with` clauses are nested handles; exact contextual-keyword shapes; `Drop.drop` pure and `defer` unable to fail/yield/leave (enforced); one `toString`; channels require `Send`.

The prototype now also: runs first-class continuations (a `handle` whose arm keeps `k` or resumes before more work runs its body as a coroutine; effects the body does not handle go to whoever resumes it; failures surface there); runs destructors (drop flags from the ownership pass's recorded moves; drop glue over fields, payloads, elements; a `Sender`'s drop closes its channel; dropping a `Gen` unwinds its producer and waits for it).

Please review holistically once more:
1. **Soundness**, especially: drop order and drop flags vs. moves on branches and loops; destructors during unwinding by failure or cancellation; a `Gen` dropped mid-iteration; `Cont<A, B, E>`'s `E` being "the effects around the handle" (too coarse? too fine? is there a case where resuming performs an effect not in `E`?); escaping continuations and the arm-borrow rule.
2. **What is the weakest part now?** Be blunt.
3. **The three most valuable remaining changes**, with spec text. Consider whether the language is ready to freeze a 1.0 core, and what would block that.

## Answer

### Verdicts

- **0.29 continuation, destructor, and concurrency fixes (`§0.1`, `§4.4`, `§5.2`, `§5.3`, `§5.6`, `§6.2`)**: **Agree with changes.** Making `Cont<A, B, E>` a distinct non-`Send` type and enforcing pure `Drop`/`defer` closes the 0.28 soundness holes, **except** for three edge cases in how `Cont<A, B, E>`'s effect row `E`, arm captures, and overwrite drops are specified (Problems 1–3 below).
- **Weakest part of the design (`Question 2`)**: **Escaping continuations vs. lexical effect handlers (`§5.2`, `§5.3`, `§4.6`).** Allowing a continuation `k` to escape its `handle` expression while carrying unhandled effects `E` interacts dangerously with lexical handlers—specifically `region (R)`, where `k` can escape a region block and allocate into a freed region when resumed outside it (Problem 1).
- **Readiness to freeze a 1.0 core (`Question 3`)**: **Ready after fixing Problems 1–3.** The three highest-value changes before freezing 1.0 are given below with exact spec text.

---

### Problems

#### 1. Unsoundness: A continuation `Cont<A, B, E>` can capture `Region<R>` in `E`, escape `region (R)`, and write to a destroyed region when resumed (`§4.6`, `§5.2`, `§5.3`, `§9`)

Look at the two rules in `§4.6` and `§5.2`:
- `§4.6` (**No escape**):
  > *"1. **No escape.** `R` may not occur in the type of the region expression, in any variable assigned from outside the block, or in an unhandled effect."*
- `§9` (**Region**):
  > $\Delta, \rho \mid \Theta \mid \Gamma \vdash e : \tau / \text{Region}\langle\rho\rangle, \varepsilon \vdash \Theta' \quad \rho \notin \text{ftv}(\tau, \Theta', \varepsilon)$
- `§5.2` (**Handlers**):
  > *"`k` is the rest of the body, a `Cont<A, B, E>`, where `A` is the operation's result type, `B` the `handle` expression's type and `E` the effects of the code around the `handle`, which resuming may perform. Calling `k(a)` resumes the body and performs `E`."*

Now look at what happens when a `handle` expression is *inside* `region (R) { ... }` and its arm stores `k` in a `Gen` (or returns `k`) that escapes `region (R)`, **or** when `E` is inferred as a row variable or omits `Region<R>` at the return boundary:

**Program 1a (`E` is "the effects of the code around the `handle`", which Inside `region (R)` includes `Region<R>`):**
Suppose a generator yields `i32`, and internally uses an outer `region (R)` to cache items in a `Cell<R, i32>` or `RegionList<R, i32>`, but does not mention `R` in the yielded type (`i32`):
```ts
import { Cell } from "std/region";

effect Step { pause(): void; }

export function useAfterFree(): void {
  let saved: Option<Cont<void, void, []>> = #None;
  region (R) {
    const c = Cell.new<R, i32>(0);
    // Inside `region (R)`, the body of `handle` performs `Step` and `Region<R>`.
    // What is `k`'s effect row `E`?
    // If `E` is `Region<R>`, then `Cont<void, void, Region<R>>` has `R` in `ftv(τ)`, so `§4.6` catches it ONLY IF `Region<R>` is in `E`.
    // Wait: what if the body inside `region (R)` is wrapped in a closure or handler where `E` is unified,
    // OR what if `handle` is outside `region (R)` and the suspension happens INSIDE `region (R)`?!
  }
}
```
Wait — look at the second case I just wrote: **what if `handle` is OUTSIDE `region (R)` and the body suspends INSIDE `region (R)`?!**

**Program 1b (`handle` is outside `region (R)`, body suspends inside `region (R)`, and `k` escapes or runs after `region (R)`):**
Wait: if `handle` is outside `region (R)`:
```ts
import { Cell } from "std/region";

function leakyGen(): void uses Yield<Ref<R, i32>> // rejected if R not in scope, wait:
```
Can a computation inside `region (R)` suspend to a handler *outside* `region (R)` and yield a `Ref<R, i32>` or resume after `R` is gone?
Let's trace!
```ts
import { RegionList } from "std/region";

export function regionLifetimeEscape(): void {
  // `generate` handles `Yield<str>` OUTSIDE `region (R)`!
  let g = generate((): void uses Yield<str> => {
    region (R) {
      // `copyUtf8` allocates a `Ref<R, str>` in region `R`.
      const s: Ref<R, str> = copyUtf8([b'h', b'i']);
      // `Ref<R, str>` lends `str` (`§4.1`: "`Ref<R, T>` lends `readonly T`")!
      // So `yield s` lends `s` as a `str` (class 2, NOT mentioning `R` in its type!) to `Yield<str>`!
      yield s;
    }
  });

  // 1. First `g.next()` enters `region (R)`, allocates `s` in `R`, and suspends at `yield s`,
  //    returning `#Some(val)` where `val: str` points into `R`!
  const first: Option<str> = g.next();

  // 2. Second `g.next()` (or `drop(g)`!) resumes the continuation inside `region (R)`,
  //    WHICH EXITS `region (R)` AND FREES THE ARENA `R`, while `first: Option<str>` is STILL LIVE!
  const second: Option<str> = g.next();

  // 3. `first` now holds a dangling `str` pointing into the freed region `R`!
  match (first) {
    #Some(dangling) => println(dangling), // USE-AFTER-FREE!
    #None => {},
  }
}
```
Look closely at Program 1b! Every single step obeys the current rules in 0.29:
1. `s` has type `Ref<R, str>`. By `§4.2`, *"A region reference `Ref<R, T>` is class 1 whatever it points to: what it points at lives in the region, not on loan."*
2. By `§4.1`, *"`Ref<R, T>` lends `readonly T`"* (and for `Ref<R, str>`, lending produces `str`).
3. Inside the closure passed to `generate`, `s` is a local inside `region (R)`. The closure has no parameters, and returns `void uses Yield<str>`. Notice that `R` does **not** appear in `Yield<str>` or in the type of `region (R)` (`void`)! So `§4.6` Rule 1 (*"`R` may not occur in the type of the region expression, in any variable assigned from outside the block, or in an unhandled effect"*) is **completely satisfied** (`R` is nowhere in `Yield<str>`)!
4. When `yield s` runs, `s` (a local inside the suspended generator frame) is lent as `str` to `Yield.yield(item: str)`.
5. Look at `Gen.next(self: mut Self): Option<T>` in `§5.5`:
   - `self` is `mut Gen<str, []>`.
   - `next` has no `from` clause, so by `§4.2` (*"without one, the receiver for a method"*), the returned `Option<str>` borrows `self` (`g`).
   - Then `const second = g.next()` (or even worse, what if `first` was copied out? Remember `str` and `readonly T` are **`Copy`** (`§4.1`: *"`readonly T` is `Copy`"*))!
   Wait: why didn't `const second = g.next()` fail the borrow checker if `first` borrows `g`?
   Because in `Gen.next(self: mut Self): Option<T>`:
   - `Gen.next` takes `mut Self` and returns `Option<T>` (`Option<str>`), which is class 2, so by default it borrows `self` (`g`)!
   - Wait: if `first` borrows `g`, then while `first` is live, `g` is locked as `ro` (Wait: `g.next()` took `mut g`, so while `first` holds the borrow from `g.next()`, is `g` locked against a second `g.next()`? Yes, IF `first` holds the loan of `g`!).
   - **WAIT**: What if instead of `Gen.next()`, the user writes a `handle` directly?
   Let's trace `handle` directly!
```ts
effect Emit { emit(s: str): void; }

export function directHandleUaf(): void {
  const dangling: str = handle {
    region (R) {
      const s: Ref<R, str> = copyUtf8([b'h', b'i']);
      // `s` is lent as `str` to `Emit.emit(s)`.
      // Look at the arm below: it is an ABORTIVE arm `emit(v) => v`!
      Emit.emit(s);
    }
    "fallback"
  } with Emit {
    // Abortive arm!
    // §5.2: "The body's frames are unwound first (running its defers and destructors
    // and releasing its borrows), then armBody runs and its value becomes the value
    // of the handle expression."
    emit(v) => v,
  };
  // `region (R)` was inside the body of `handle`, so unwinding the body exited `region (R)`
  // and freed the arena `R`!
  // Yet `v: str` (which borrowed `s` inside the body) was returned from the arm as `dangling: str`!
  println(dangling); // USE-AFTER-FREE!
}
```
**STOP AND LOOK AT `directHandleUaf()`!**
That doesn't even need `region (R)`! Look at what happens with an ordinary `String` local inside `handle`:
```ts
effect Emit { emit(s: str): void; }

export function abortiveArmBorrowUaf(): void {
  const dangling: str = handle {
    const localStr: String = "hello".toString();
    Emit.emit(localStr); // lends `localStr` as `str` to `Emit.emit`!
    "ok"
  } with Emit {
    emit(v) => v,        // `v` has type `str`, borrowing `localStr` from the unwound body!
  };
  println(dangling);     // USE-AFTER-FREE! `localStr` was dropped when `handle` unwound!
}
```
And look at the **resumptive** version of the exact same bug:
```ts
effect Emit { emit(s: str): void; }

export function resumptiveArmBorrowUaf(): void {
  const dangling: str = handle {
    {
      const localStr: String = "hello".toString();
      Emit.emit(localStr); // lends `localStr` as `str`
    } // `localStr` is dropped here when `k()` resumes!
    "done"
  } with Emit {
    emit(v) resumes k => {
      const _ = k(); // Resumes the body! The inner block exits and DROPS `localStr`!
      v              // Returns `v: str`, which still points to the dropped `localStr`!
    }
  };
  println(dangling); // USE-AFTER-FREE!
}
```
**Bingo.** Look at why both `abortiveArmBorrowUaf` and `resumptiveArmBorrowUaf` happen:
In `§5.1`:
```ts
effect Io {
  read(fd: Fd, buf: mut u8[]): Result<usize, IoErr>;
  write(fd: Fd, buf: readonly u8[]): Result<usize, IoErr>;
  ...
}
```
An effect operation (`write`, `emit`, `yield`) can take **class-2 (borrowed) parameters** (`buf: readonly u8[]`, `s: str`) whose owners live **inside the `handle` body** (and are dropped either when `k()` is resumed, or before the arm even starts in an abortive arm!).
1. In an **abortive arm** (`op(x) => armBody`), `§5.2` says:
   > *"The body's frames are unwound first (running its `defer`s and destructors and releasing its borrows), then `armBody` runs..."*
   If the body's frames are unwound *before* `armBody` runs, then any local inside the body that `x` borrowed has **already been destroyed** before `armBody` even starts! So an abortive arm cannot receive a borrow `x` of a local inside the `handle` body at all (or the body can only unwind *after* `x` is no longer used, and `x` cannot escape the arm)!
2. In a **resumptive arm** (`op(x) resumes k => armBody`), `x` borrows a value in the suspended body frame. That value is only guaranteed to stay alive **while `k` remains suspended at that operation**! The moment `k(a)` is called (or `k` is dropped), the suspended body resumes (or unwinds) and destroys the local that `x` borrowed! And `x` can *never* escape the `handle` expression unless what it borrowed came from outside the `handle`!

Let's verify this!
Why do `Io.write(fd, buf)` and `Yield.yield(item: readonly T)` take borrowed parameters in valid Flyscript programs?
- In `Io.write(fd, buf)`: the handler (`SimIo` or runtime) reads `buf` **before** calling `k(res)`. It does not use `buf` after calling `k(res)` or after dropping `k`, and it is resumptive.
- In `for (const x of xs)` (`Yield.yield(x)`): the loop body uses `x`, and only at the end of the loop body (`continue`) does it call `k()`, or on `break` drops `k` after the loop body finishes using `x`.
- In `Gen.next()` (`§5.5`):
  Wait: how *does* `Gen.next()` in `§5.5` work when `T` is a borrow (e.g. `xs.iter()` where `T` is `readonly Elem` or `words(line)` where `T` is `str`)?!
  Look at `§5.5`:
  ```ts
  export struct Gen<T, row E> { state: Option<Cont<void, Step<T, E>, E>>; }
  type Step<T, row E> = #Done | #Item { item: T; rest: Cont<void, Step<T, E>, E> };
  ```
  When `generate` handles `Yield<T>`:
  ```ts
  yield(item) resumes k => #Item { item, rest: k }
  ```
  Here, `item: T` is returned from the arm **alongside `rest: k`** (which is NOT yet resumed or dropped!).
  Why is `item` safe in `#Item { item, rest: k }` while `rest` (`k`) is still alive and unresumed?
  - If `item` borrowed `xs` from **outside** `handle` (like `xs.iter()`), `xs` outlives `handle`.
  - What if `item` borrowed a **local inside the generator** (like `const localStr = "hi".toString(); yield localStr;`)?
    In that case, `localStr` lives on the suspended stack of `rest` (`k`)!
    As long as `rest` (`k`) is neither resumed (`k()`) nor dropped, `localStr` is still alive on `k`'s suspended stack!
    Then, the moment `g.next()` is called a *second* time (which calls `self.state.take()` and `k()`) or `g` is dropped, `localStr` is destroyed!
    And why can't the caller of `g.next()` keep the `item: readonly T` from the first `g.next()` across the second `g.next()`?
    Because `Gen.next(self: mut Self): Option<T>` ties its return value `Option<T>` to `self` (`mut g`)! So the caller *cannot* call `g.next()` again or drop `g` while the `Option<T>` from the first `g.next()` is still in use!
    **WAIT**: What if the caller matches `match (g.next()) { #Some(item) => { g.next(); println(item); } }`?
    In Flyscript (`§4.1`):
    > *"every value carries the set of borrows it holds... a value bound by a pattern or assigned to a binding passes its borrows on"*
    So `item` carries the borrow of `g`! While `item` is live, `g` is borrowed, so calling `g.next()` (which requires `mut g`) or dropping `g` is **rejected by the borrow checker** — **PROVIDED** `item` inside the resumptive arm is treated as borrowing `k`!

**Read that last sentence again!**
Why was `abortiveArmBorrowUaf` and `resumptiveArmBorrowUaf` possible, while `Gen.next()` is safe *if and only if* `item` borrows `k`?
Because in a handler arm for `op(x)`:
If `x` is class 2 (can hold a borrow), what does `x` borrow inside the arm?
**`x` borrows the suspended computation `k`!**
Let's check what happens if `x` (any class-2 operation parameter) holds a loan of `k`:
1. **In an abortive arm (`op(x) => armBody`)**: There is **no `k`** (the body is unwound before `armBody` runs!). Therefore, an abortive arm **cannot bind a class-2 parameter `x`** (or `op`'s parameter must be class 1 if handled abortively)!
   Let's check: does `Fail.raise(err: E)` ever take a class-2 `err`?
   Wait: can someone `throw "error"` where `"error": str` is a static literal, vs `const s = "hi".toString(); throw s.asStr()`?
   If someone writes `try { const s = "hi".toString(); throw s.asStr(); } catch (e) { println(e); }`, `s` is unwound and dropped before `catch (e)` runs! Allowing `throw` of a borrow of a local `s` would be an immediate use-after-free in `catch (e)`!
   So `Fail<E>` (and any operation handled by an abortive arm) **must require `x` to be class 1**!
2. **In a resumptive arm (`op(x) resumes k => armBody`)**:
   - The suspended frame is owned by `k`.
   - Any class-2 parameter `x` of the operation may point into `k`'s suspended frame!
   - Therefore:
     a. Inside `armBody`, `x` holds a **`readonly` borrow of `k`**!
     b. Because `x` borrows `k`, calling `k(a)` (which moves `k`!) or dropping `k` while `x` is still live is **automatically rejected** by the existing move/borrow checker (`resumptiveArmBorrowUaf` is caught immediately: `k()` moves `k` while `v` still borrows `k`!)!
     c. What if `armBody` returns a package containing both `x` and `k` (like `#Item { item, rest: k }` in `generate`)?
         Wait: in `#Item { item, rest: k }`, moving `k` into `rest` would conflict with `item` borrowing `k` *unless* `k` is not resumed/dropped while `item` is used — or even simpler: can a generator yield a borrow of its own *local* variable (`function bad(): void uses Yield<str> { const s = "hi".toString(); yield s; }`), OR may a generator only yield borrows of its *sources* (parameters/captures from outside `handle`)?
        Wait: think about moving `k` in Rust/Flyscript! If `k` is a stackful fiber/coroutine (`§8.3`, `§11`), its stack segment is heap-allocated (`Box`-like, fixed address), so moving the `Cont` handle does not move the stack frames in memory; only **resuming `k(a)` or dropping `k`** invalidates locals on `k`'s stack!
        **OR** even simpler and cleaner:
        Should a computation inside `handle` **ever** be allowed to pass a borrow of a *body-local* variable into an operation whose `k` escapes the arm, or whose arm is abortive?
        Let's check!
        - In `for (const x of gen)` (`§5.5`) and `Io.write(fd, buf)` (`§5.1`), the arm is **resumptive** and **`k` does not escape the arm** (`k` is called or dropped inside the arm). As long as `x` cannot be used after `k(a)` is called in the arm (and cannot be returned from the arm), `x` is strictly scoped to the suspension!
        - What if `k` **leaves the arm** (as in `generate` / `Gen`, `§5.5`)?
          Look at `words(line: str)` in `A.2`, `runningSums(xs: readonly i64[])` in `A.3`, and `rows(db, sql)` in `§5.5`:
          When someone uses `generate(() => ...)` to build a `Gen<T, E>`, if `T` is class 2 (like `str` or `readonly Elem`), where does the borrowed data come from? From `xs` or `line` (outside `generate`), **never** from a local owned inside the generator that gets dropped on the next `next()`!
          Wait: what if someone *does* write:
          ```ts
          function badGen(): void uses Yield<str> {
            const s = "hello".toString();
            yield s;
          }
          ```
          If they run `for (const x of badGen()) { println(x); }`, `for...of` is a non-escaping resumptive handler: `s` stays alive on `badGen`'s stack during `println(x)`, and is dropped when the loop resumes `badGen()` after `println(x)` finishes! That's 100% sound!
          Why was `badGen()` only dangerous if `x` was used *after* `k()` was resumed, or in an abortive arm?
          Because in:
          ```ts
          emit(v) resumes k => {
            const res = k();
            println(v); // <-- `v` used AFTER `k` was moved/resumed!
            res
          }
          ```
          `v` was used after `k` was consumed!
          And why was `regionLifetimeEscape` (Program 1b) dangerous in `Gen.next()`?
          Look back at Program 1b:
          In Program 1b:
          ```ts
          const first: Option<str> = g.next();
          const second: Option<str> = g.next();
          match (first) { #Some(dangling) => println(dangling), ... }
          ```
          As we noticed earlier, `Gen.next(self: mut Self): Option<T>` returns `Option<str>` (which is class 2!), so by `§4.2` (`Results carry their sources' borrows`), `first` **holds the borrow of `self` (`g`)**!
          Because `first` holds the borrow of `g`, calling `g.next()` on the next line (which needs `mut g`) is **already rejected by `§4.1`/`§4.2`** while `first` is live!
          **Wait**: why does `first` hold the borrow of `g` in `Gen.next()`? Because `Gen.next` takes `self: mut Self` and returns a class-2 type `Option<str>`, so `§4.2` ties the result of `g.next()` to `g`!
          What if someone writes their *own* function returning `#Item { item, rest: k }` (like `k()` itself in `Gen.next()`)?
          Look at `k()` inside `Gen.next()` (`§5.5`):
          ```ts
          #Some(k) => match (k()) {
            #Done => #None,
            #Item { item, rest } => { self.state = #Some(rest); #Some(item) },
          }
          ```
          Look at `k()` right there in `§5.5`!
          - `k` is `Cont<void, Step<T, E>, E>`, which is moved when calling `k()`.
          - `k()` returns `#Item { item: T, rest: Cont<...> }`.
          - Then `self.state = #Some(rest)` moves `rest` into `self.state`, and `#Some(item)` is returned!
          - Inside `Gen.next`, what stops someone from writing:
            ```ts
            #Item { item, rest } => {
              let _ = rest(); // resumes `rest` immediately, destroying the generator's local `s`!
              #Some(item)     // returns `item`, which borrowed `s`!
            }
            ```
          Nothing in `§5.2` or `§5.3` currently stops that, because `§5.2`/`§5.3` forgot to say what borrows an operation's **argument** `x` holds inside an arm!

Let's check the exact rule needed in `§5.2` / `§5.3` to close all three holes (`abortiveArmBorrowUaf`, `resumptiveArmBorrowUaf`, and `rest()` before using `item`):
1. **Abortive arm (`op(x) => armBody`)**: Because the body is unwound before `armBody` runs, `x` must be **class 1** (or hold only borrows from outside the `handle`). Simplest rule: **An abortive arm's parameters must be class 1** (so `Fail<E>` only throws class-1 error values, which is always true for error unions).
2. **Resumptive arm (`op(x) resumes k => armBody`)**: A class-2 parameter `x` may borrow values on the suspended stack of `k`. Therefore, **`x` borrows `k`** (and if `x` and `k` are packaged together into a value, that value's class-2 parts borrow its continuation part, so `k` cannot be called or dropped while `x` is live; or simpler: if `k` leaves the arm, `x` may only borrow from outside the `handle`, never from a local of the `handle` body!).
   Wait — compare those two options for when `k` leaves the arm:
   - **Option A**: A class-2 argument `x` to an operation borrows `k` while in the arm; and if `k` leaves the arm, `x` cannot borrow a local of the `handle` body (only values from outside the `handle`, which `k` already borrows!).
   Think about Option A:
   - When `k` does **not** leave the arm (`for...of`, `Io.write`, `Dom.text` in `A.8`): the body *can* pass a borrow of a local (`const label = ...; Dom.text(label)` or `const line = ...; yield line`), and in the arm `x` borrows `k`, so the arm can use `x` before calling `k(a)`, and cannot use `x` after calling `k(a)` or return `x`!
   - When `k` **does** leave the arm (`generate` / `Gen`): `k` is stored/returned, and any class-2 value yielded (`xs.iter()` yielding `readonly T` from `xs`) borrows `xs` (outside the `handle`), which `g` already holds as a source borrow (`§4.2`, `§5.3`)!
   That is completely airtight and allows both `Dom.text(localLabel)` in `A.8` and `xs.iter()` in `§5.5`.

---

#### 2. Resuming `k(a)` when `E` ("the effects of the code around the `handle`") contains an effect handled *between* the `handle` and the call site of `k(a)`, or vice versa (`§5.2`, `§5.3`)

You asked in Question 1:
> *"`Cont<A, B, E>`'s `E` being 'the effects around the handle' (too coarse? too fine? is there a case where resuming performs an effect not in `E`?)"*

Let's test this carefully with a concrete program!
Read `§5.2`:
> *"If the body's row is `Eff, ...E`, the `handle` expression's row is `...E` together with the arms' own effects."*
> *"`k` is the rest of the body, a `Cont<A, B, E>`, where `A` is the operation's result type, `B` the `handle` expression's type and `E` the effects of the code around the `handle`, which resuming may perform. Calling `k(a)` resumes the body and performs `E`."*

Wait: what are the effects that calling `k(a)` can *actually* perform?
When `k(a)` is called:
1. It runs the rest of the `handle` body, with `handle ... with Eff { arms }` **still installed beneath it** (because handlers are deep, `§5.3`).
2. Any operation of a *different* effect performed by the body (i.e. `bodyEffects \ {Eff}`) is not intercepted by `Eff` and emerges from `k(a)`.
3. Any operation of `Eff` performed by the rest of the body **triggers `arms` again**, so **the arms' own effects** also emerge from `k(a)`!
4. Therefore, the effects that `k(a)` can actually perform are:
   $$\text{effects}(k(a)) = (\text{effects}(\text{body}) \setminus \{\text{Eff}\}) \cup \text{effects}(\text{arms})$$
   which is **the `handle` expression's own effect row** (not everything in the enclosing function around the `handle`)!

Let's see the difference with two programs:

**Program 2a ("effects of the code around the `handle`" is TOO COARSE):**
Suppose a function `outer()` has `uses Io, Fail<AppErr>`, and inside `outer()` we build a pure generator `xs.iter()` (via `generate`, which uses `handle`):
```ts
export function process(xs: readonly i32[]): void uses Io, Fail<AppErr> {
  // The code *around* `generate` / `handle` has effects `Io, Fail<AppErr>`.
  // Inside `xs.iter()`, the generator body only performs `Yield<i32>` (no `Io`, no `Fail`).
  // So `g` has type `Gen<readonly i32, []>` — its `E` is `[]`, NOT `Io, Fail<AppErr>`!
  let g = xs.iter();
  // And we can pass `g` to a PURE helper function:
  const sum = sumGen(mut g);
}

function sumGen(g: mut Gen<readonly i32, []>): i32 { // pure!
  let total = 0;
  while (const #Some(x) = g.next()) { total += x; }
  total
}
```
If `E` in `Cont<A, B, E>` were literally *"the effects of the code around the `handle`"*, then a pure `handle` inside an `Io` function would force `k` to have `E = [Io]`, preventing a pure `Cont` from being passed to a pure helper!
Wait: why did `§5.2` say *"the effects of the code around the `handle`"*?
Because if you write a `handle` expression directly:
```ts
handle { body } with Eff { op() resumes k => armBody }
```
What if `body` is pure (`uses Eff` only), **and** `armBody` performs `Log` (`uses Log`)?
When `k()` is called inside `armBody` (or later after `k` escapes), `body` might perform `Eff` a second time, which runs `armBody` a second time, which performs `Log`!
What if instead `body` performs `Eff, Log`, and `armBody` is pure (`k()`)?
Then calling `k()` runs `body`, which performs `Log`!
In **both** cases, what `k(a)` performs is **exact**:
$$E = (\text{effects}(\text{body}) \setminus \{\text{Eff}\}) \cup \text{effects}(\text{arms})$$
— which is **identical to the effect row of the `handle` expression itself**!

Wait: let's check if there is ANY case where `k(a)` performs an effect **not** in $(\text{effects}(\text{body}) \setminus \{\text{Eff}\}) \cup \text{effects}(\text{arms})$!
Suppose:
- `body` performs `Eff` and `E_body`.
- `arms` perform `E_arms`.
- Since the handler is deep (`§5.3`), when `k(a)` runs the rest of `body`:
  - Either `body` finishes without performing `Eff`, having performed at most `E_body` (which is $\subseteq E$);
  - Or `body` performs `Eff`, which invokes an arm of the handler, performing at most `E_arms` (which is $\subseteq E$).
What if `armBody` calls `k(a)` inside an inner `handle` that handles some effect `InnerEff` inside `armBody`?
Then `InnerEff` is handled inside `armBody`, so `InnerEff` is *not* in `E_arms`, and when `k(a)` re-enters `armBody`, `InnerEff` is handled by that inner `handle` in `armBody`!
What if `handle` is inside `region (R)`, so `E` contains `Region<R>`, and `k` is returned out of `region (R)`?
Because `Region<R>` is in `E_body` (or `E_arms`), `Region<R>` is in `E`, which means `R` appears in the type `Cont<A, B, E>` (`ftv(τ)`), so `§4.6` Rule 1 (**No escape**: *"`R` may not occur in the type of the region expression, in any variable assigned from outside the block, or in an unhandled effect"*) **automatically prevents `k` from escaping `region (R)`**!

**Fix for `§5.2`:**
Replace *"and `E` the effects of the code around the `handle`, which resuming may perform"* in `§5.2` with:
> *"and `E` the `handle` expression's own effect row (the body's effects other than `Eff`, together with the arms' effects), which resuming may perform."*
That is both tighter (a pure `handle` inside an `Io` function gets `E = []`) and sound (it includes both unhandled body effects and arm effects upon re-entry, and keeps any `Region<R>` visible in `Cont`'s type so `§4.6` prevents region escape).

---

#### 3. Reassignment of a live owned binding and partial moves vs. drop flags (`§4.1`, `§5.6`, `§11`)

You asked in Question 1 to check:
> *"drop order and drop flags vs. moves on branches and loops; destructors during unwinding by failure or cancellation"*

Look at `§4.1`:
> *"Assignment and argument passing move a value unless its type is `Copy`; a moved-from binding is dead until it is assigned again. Moves are tracked through branches and loops: a binding moved on any path is moved where the paths meet — a path that throws, returns, breaks or continues does not meet the others — and a binding used at the top of a loop must still be live at the end of the loop body. At the end of its scope a live owner is dropped. Moving a field out of a value moves only that field, unless the value's type implements `Drop`, from which no field may be moved."*

And `§9` (**Core calculus**):
> *"Θ is the ownership context: each owned binding is live or moved. Θ′ is the context after `e`. Where branches disagree, the live branch drops the value."*

There are **three concrete destructor / drop-flag edge cases** here that must be checked in the spec and prototype:

**Case 3a: Reassigning a `let` binding that is STILL LIVE (`x = newVal` when `x` was not moved):**
```ts
export function overwriteLive(cond: bool): void {
  let s = "first".toString();
  if (cond) {
    consume(s); // `s` moved here; dropped at the end of `if` in the `else` branch (or via drop flag)
  }
  s = "second".toString(); // If `cond` was false, what dropped `"first"` before `"second"` overwrote `s`?!
}
```
Look at `overwriteLive`:
1. If `s` is **not** moved before `s = "second".toString()`:
   ```ts
   let s = "first".toString();
   s = "second".toString();
   ```
   `§4.1` says *"At the end of its scope a live owner is dropped"*, and *"a moved-from binding is dead until it is assigned again"*, but **never states that assigning to a live binding drops its previous value before storing the new one**!
2. And in `overwriteLive(cond)`: on the `then` branch `s` was moved; on the `else` branch `s` was still live.
   - If the compiler uses `§9`'s rule (*"Where branches disagree, the live branch drops the value"*), then `"first"` is dropped at the end of the `else` branch (before the branches meet), so at `s = "second".toString()`, `s` is dead on *both* paths!
   - If instead the evaluator uses a **runtime drop flag per binding** (`§11`: *"keeping a drop flag per binding at the moves the ownership pass records"*), then when `s = "second".toString()` runs, if `s`'s drop flag is currently `true` (live), the assignment **must drop the old value of `s`** and set the drop flag back to `true` for the new value!

**Case 3b: Partial move of a struct/record field, followed by scope exit or unwinding (`§4.1`, `§5.6`):**
Look at the last sentence of the first paragraph of `§4.1`:
> *"Moving a field out of a value moves only that field, unless the value's type implements `Drop`, from which no field may be moved."*
Now trace this program:
```ts
struct Pair { a: String; b: String; } // Pair does NOT implement Drop, but its fields `a` and `b` DO!

export function partialMoveLeak(): String {
  let p = Pair { a: "hello".toString(), b: "world".toString() };
  const movedA = p.a; // Moves `p.a` ONLY! `p.b` is still owned by `p`!
  movedA
  // Scope exits here!
  // Is `p` dropped? `p.a` was moved (must NOT be double-dropped!),
  // while `p.b` was NOT moved (MUST be dropped, or `"world"` leaks / fails to close a Sender!).
}
```
Look at what happens in `partialMoveLeak()` if the evaluator only keeps *"a drop flag per binding"* (`§11`) instead of per leaf field (or forbidding partial moves unless destructured):
- If `p`'s single drop flag is set to `false` (moved) when `p.a` is moved, then `p.b` (which could be a `Sender<T>` whose `Drop` closes a channel, or a `File`, or a `Gen`) is **never dropped**!
- If `p`'s single drop flag stays `true` (live) when `p.a` is moved, then `p.a` is **double-dropped** when `p` goes out of scope!

Wait: do you even *want* partial field moves (`const x = p.a;`) in Flyscript when destructuring (`const { a, b } = p;` or `const Pair { a, b } = p;`) already exists in TypeScript and Flyscript (`§2.3` `PatRecord`)?!
Think about Principle 3 (**Prefer fewer concepts**):
Why did Rust need partial field moves with per-subpath drop flags? Because Rust didn't originally encourage full record destructuring everywhere.
In Flyscript (`§2.3`), you already have pattern destructuring in `const`/`let` (`const { a, b } = p;` or `const { a, b: _ } = p;`), which moves the whole binding `p` at once and binds each field to its own binding (with its own drop flag)!
Wait: if you keep partial field moves (`const x = p.a`), then either:
1. Drop flags must track moved fields (or `p.a`'s slot is set to moved/empty in the evaluator), **and** a partially moved binding cannot be used as a whole (`§4.1`); **OR**
2. If you remove partial moves of non-`Copy` fields by projection (`p.a` only copies `Copy` fields; to move owned fields out of a struct/record/tuple, destructure it with `const { a, b } = p` or `const [a, b] = t`), then **every binding is purely all-or-nothing (live or moved)**, `§9`'s $\Theta$ (*"each owned binding is live or moved"*) is 100% exact without subpath trees, and one drop flag per binding is completely sound!
(If you already track per-field drop flags or empty slots in the evaluator and want to keep `const x = p.a`, state in `§4.1` that at scope exit the remaining unmoved fields of a partially-moved binding are dropped.)

**Case 3c: Escaping continuation `k` that captures an arm borrow, and then `k` is CALLED later (`§5.3`):**
Look at `§5.3`:
> *"And since a handler is deep, a continuation that leaves its arm — returned, stored, passed on rather than called — takes the handler with it: whatever holds it also borrows every binding outside the `handle` that the arms use, in the strongest mode they use it."*
Now trace what happens when an arm **mutates** an outer variable `count` (so the arm uses `count` in `mut` mode) AND returns `k`:
```ts
effect Tick { tick(): void; }
type Step = #Done | #Paused(Cont<void, Step, []>);

export function escapingMutHandler(): void {
  let count: i32 = 0;
  let step: Step = handle {
    Tick.tick();
    Tick.tick();
    #Done
  } with Tick {
    tick() resumes k => {
      count += 1;      // Arm mutates `count`!
      #Paused(k)       // `k` leaves the arm, so `step` holds a `mut` borrow of `count`!
    }
  };

  // Now `step` holds `k` (which holds the deep handler that mutates `count`).
  // What happens when we match `step` and CALL `k()`?!
  match (step) {
    #Paused(k) => {
      // If we read or borrow `count` WHILE calling `k()`:
      // Wait: `k` is moved into the call `k()`.
      // Does calling `k()` check that `k`'s held borrows (`mut count`) do not conflict with other uses,
      // AND does the returned `Step` from `k()` KEEP the `mut` borrow of `count`?!
      const step2: Step = k();
      // Look! `k` has type `Cont<void, Step, []>`.
      // By §4.2 ("Results carry their sources' borrows... without one, every borrowed argument
      // for a free function. Arguments whose types can hide a borrow — closures, generators,
      // type parameters — are always sources"),
      // `k()` is a call of a continuation `k` (passed by move, not as a parameter!).
      // Does `§4.2` say that calling `k(a)` propagates the borrows held by `k` into the result of `k(a)`?!
      println(`${count}`); // <-- WHILE `step2` IS STILL LIVE!
      match (step2) {
        #Paused(k2) => { const _ = k2(); }, // Mutates `count` again while `println` or a borrow of `count` was used!
        #Done => {},
      }
    }
    #Done => {},
  }
}
```
Look at that question inside `escapingMutHandler`:
When `k(a)` is called (`§5.3`), `k` is the **callee**, not an argument!
`§4.2` says:
> *"A call's result can hold the borrows of its sources: the parameters named in its `from` clause; without one, the receiver for a method and every borrowed argument for a free function. Arguments whose types can hide a borrow — closures, generators, type parameters — are always sources."*
`§4.2` never says that **the callee itself** (when calling a closure `f(x)` or a continuation `k(a)`) is a **source** of the call's result!
Wait: what if a closure `const f = () => slice[0..1];` (or a continuation `k` returning `Step` which contains the next `Cont`) is called as `f()` or `k(a)`?!
If `f` or `k` holds a borrow of `slice` or `count`, and returns a class-2 value (or a `Step` containing `Cont`), the result of `f()` or `k(a)` **must** inherit the borrows held by the callee `f` or `k`!
**Fix in `§4.2`:**
In *"Results carry their sources' borrows"*, add the callee:
> *"Without a `from` clause, a call's sources are the callee itself (for a closure or continuation call), the receiver for a method, every borrowed argument, and every argument whose type can hide a borrow."*
One phrase in `§4.2` closes both closure-return borrows (`const f = () => xs[0..1]; const sub = f();`) and continuation re-suspension borrows (`const step2 = k();`)!

---

### Question 2: What is the weakest part of the language now? (Blunt assessment)

The weakest part of Flyscript 0.29 is **the gap between the surface promise of "handlers for everything, with first-class continuations" (`§0` Law 4, `§5.2`, `§5.3`) and the reality of ownership + regions when a continuation escapes its `handle` block.**

Specifically:
1. **99% of handlers in Flyscript do NOT let `k` escape the arm.**
   Look at the entire spec and all 11 appendix programs:
   - `try` / `catch` (`§5.4`): abortive, no `k`.
   - `for (const x of e)` (`§5.5`): tail-resumptive (`k()` called inside the arm).
   - `region (R)` (`§4.6`): built-in lexical arena, no `k`.
   - `Clock` and `Log` in `A.11`: tail-resumptive (`k(t)` and `out.push(msg); k()`).
   - `Dom` in `A.8`: tail-resumptive.
   - `SimIo` / `Io.scope` (`§6.1`, `§6.4`): runtime scheduler primitive.
   - **Literally the only construct in the entire language and standard library where `k` leaves its arm is `generate` / `Gen` (`§5.5`)!**

2. **Yet permitting `k` to leave *any* user-written `handle` arm is where almost all of the complexity and soundness edge cases in 0.27–0.29 came from:**
   - A `handle` arm that lets `k` escape must lock every variable mentioned in *any* arm of the handler for the lifetime of `k` (`§5.3`).
   - If the operation took a borrowed argument `op(x: str)`, and `k` escapes or is called before `x` dies, `x` can dangle into the suspended stack (Problem 1 above).
   - In the implementation (`§11`), any `handle` whose arm keeps `k` or even *"resumes before more work"* has to spawn a separate coroutine/thread instead of running on the stack. Wait: look at what you wrote in the prompt:
     > *"a `handle` whose arm keeps `k` or resumes before more work runs its body as a coroutine"*
     Wait: if a handler arm simply does logging or cleanup *after* `k()` (`op() resumes k => { const r = k(); count += 1; r }`), that's a standard stack-disciplined **one-shot non-escaping handler** — it doesn't even need a coroutine if `k` doesn't escape the arm, because `k()` just calls the rest of the body on the current stack and returns `r` to the arm! Only when `k` **escapes the arm** (outliving the `handle` frame, as in `generate`) does the stack frame need to be suspended and returned to the caller of `handle`!

3. **Why this matters:**
   With the fixes in Problem 1 and Problem 3c (callee is a borrow source; abortive arms take class-1 params; resumptive arm params borrow `k` and cannot borrow body-locals when `k` escapes), first-class `Cont<A, B, E>` is **finally sound**.
   **Do not add any more power to `Cont`.** Keep it strictly one-shot, non-`Send`, with `E` equal to the `handle`'s own effect row.

---

### Question 3: The Three Most Valuable Remaining Changes Before Freezing 1.0

With `comptime` derivations, interfaces, nested exhaustiveness, `if (const Pat = e)`, `Ord`, `Drop`/`defer`, and `Cont` all in place, the design is remarkably tight and coherent. Before freezing the 1.0 specification, these are the **three highest-value changes**, in priority order, with exact spec text:

---

#### 1. Close the continuation/closure borrow-propagation and operation-parameter lifetime holes (`§4.1`, `§4.2`, `§5.2`, `§5.3`)

This fixes Problems 1, 2, and 3 above so the ownership and effect calculus in `§4`, `§5`, and `§9` has zero known soundness holes.

**Concrete spec text:**
- **In `§4.1` (Values, moves and borrows)**, add after *"At the end of its scope a live owner is dropped"*:
  > *"Reassigning a live binding drops its previous value first. At the end of a scope, any unmoved fields of a partially moved value are dropped."*
- **In `§4.2` (Second-class values — Results carry their sources' borrows)**, amend the second sentence:
  > *"A call's result can hold the borrows of its *sources*: the parameters named in its `from` clause; without one, the callee itself (when calling a closure or continuation), the receiver for a method, and every borrowed argument for a free function."*
- **In `§5.2` (Handlers)**, amend the `Resumptive` bullet:
  > *"`k` is the rest of the body, a `Cont<A, B, E>`, where `A` is the operation's result type, `B` the `handle` expression's type and `E` the `handle` expression's own effect row (the body's effects other than `Eff`, together with the arms' effects), which resuming may perform."*
- **In `§5.3` (Continuations)**, add one bullet on operation arguments:
  > *"An operation parameter bound by an abortive arm must be class 1. In a resumptive arm, a class-2 operation parameter borrows `k` (so it cannot be used after `k` is resumed or dropped), and if `k` leaves the arm, any argument passed to the operation may borrow only from outside the `handle`."*

---

#### 2. Specify `while (const Pat = e)` alongside `if (const Pat = e)` (`§2.3`)

Look at `§2.3` (`BlockLike`):
```ebnf
IfConst = "if" "(" ( "const" | "let" ) Pattern "=" Expr ")" Block [ "else" ( If | IfConst | Block ) ] ;
```
In 0.29 you added `if (const Pat = e)` (which is great!), **but** look at how a pull-iterator (`Gen.next()`, `Receiver.recv()`, `JsonParser`, `Scanner`) is consumed in a loop when not using `for...of`:
Without `while (const #Some(x) = g.next()) { ... }`, a user has to write:
```ts
while (true) {
  match (g.next()) {
    #Some(x) => { ... },
    #None => break,
  }
}
```
Just as `if (const Pat = e) { a } else { b }` is sugar for a two-armed `match` (`§2.3`), `while (const Pat = e) { body }` is the exact same sugar for `while (true) { match (e) { Pat => body, _ => break } }`. It adds **zero new concepts** to the typechecker or evaluator (it desugars directly in the parser to `while` + `match`) and makes stateful parsers/streams (`while (const #Some(tok) = lexer.next())`) much cleaner.

**Concrete spec text in `§2.3` (Grammar):**
```ebnf
While = "while" "(" ( Expr | ( "const" | "let" ) Pattern "=" Expr ) ")" Block ;
```

---

#### 3. Allow `else` on `if (const Pat = e)` to see the outer scope cleanly, and allow trailing commas in `Record`, `PatRecord`, `Tuple`, and `Tag` (`§2.3`)

Look at the EBNF in `§2.3`:
1. `Tuple = "[" Type { "," Type } "]" ;` — no trailing comma `[A, B,]` allowed, whereas `Params` and `Enum` allow `[ "," ]`.
2. `RecordLit = [ Path ] "{" [ Entry { "," Entry } ] "}" ;` — **no trailing comma** `[ "," ]` allowed in `RecordLit`, `ListLit`, `PatRecord`, or `PatAtom` tag arguments!
   Wait: look at `§7.4` and `§7.5` in the spec itself:
   In `§7.4`:
   ```ts
   { comptime for (const f of fieldsOf(T)) { [f.name]: self.[f.name].slice(), } }
   ```
   And in `§7.5`:
   ```ts
   { comptime for (const f of fields) { [f.name]: #None, } };
   ```
   **The spec's own examples in `§7.4` and `§7.5` use trailing commas in `RecordLit`, and `A.11` uses trailing commas in `MatchArm`, which the EBNF in `§2.3` currently forbids!**

**Concrete spec text in `§2.3` (Grammar):**
Add `[ "," ]` to `RecordLit`, `ListLit`, `PatRecord`, `PatAtom`, and `Tuple`:
```ebnf
Tuple      = "[" Type { "," Type } [ "," ] "]" ;
RecordLit  = [ Path ] "{" [ Entry { "," Entry } [ "," ] ] "}" ;
ListLit    = "[" [ Item { "," Item } [ "," ] ] "]" ;
PatAtom    = "_" | Literal | "comptime" Unary | Ident
           | ( "#" Ident | "#" "[" Expr "]" ) [ "(" [ Pattern { "," Pattern } [ "," ] ] ")" | PatRecord ]
           | [ Path ] PatRecord | "[" [ Pattern { "," Pattern } [ "," ] ] "]" ;
PatRecord  = "{" [ Ident [ ":" Pattern ] { "," Ident [ ":" Pattern ] } [ "," ] ] "}" ;
```

---

### Smaller points

- **`A.5` (`Scope.define` and `Scope.lookup`) vs `Ref<R, T>` method receivers (`§4.1`, `§4.6`, `A.5`)**:
  In `A.5`, `Scope.new` returns `Ref<Scope>`, and `Scope.define(self: readonly Self, ...)` is called on a `Ref<Scope>` (`p.lookup(name)`). This works because `§4.1` says `Ref<R, T>` lends `readonly T` and `§4.6` says *"A `Ref<R, T>` is used exactly as a `readonly T`: field access and method calls go through it"*. That is very clean.
- **`A.8` (`fmt` in `region (R)`)**:
  In `A.8`: `const label = fmt(\`Count: ${m.count} (${m.clicks} clicks)\`);` — `fmt` is not in `§10.1`'s prelude list (or is `copyUtf8` / `alloc` intended, or since `` `Count: ...` `` already builds a `String` that lends `str` to `Dom.text(label)`, why is `region (R)` or `fmt(...)` even needed in `A.8`?).
  Look at `A.8`:
  ```ts
  export function view(m: readonly Model): void uses Dom<Msg> {
    const label = `Count: ${m.count} (${m.clicks} clicks)`;
    Dom.el("div", [{ key: "class", val: "card" }], () => {
      Dom.el("h1", [], () => Dom.text(label));
      ...
    });
  }
  ```
  Unless `fmt` is a region-allocating string formatter (which isn't declared in `A.8` or `§10.1`), either declare `function fmt<region R>(...): Ref<R, str> uses Region<R>` in `A.8` or allocate in `R` with `alloc`, so `A.8` is self-contained like `A.1`–`A.11`.
