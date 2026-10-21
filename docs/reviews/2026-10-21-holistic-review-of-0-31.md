# Review: holistic-review-of-0-31

- spec: d919caee8a4d
- request: d1738a165133c955
- tokens: prompt 63627, cached 0, answer 12543

## Question

Spec 0.31 (included). Since your review of 0.29:

- 0.30 adopts it: an operation argument that may hold a borrow is usable in a resumptive arm only until `k` is called and never past the arm; an abortive arm cannot use one at all (it runs after the body unwound). A continuation's row `E` is now the `handle`'s own inferred row (body's unhandled effects plus the arms'), computed after the arms are checked; calls of `k` inside the arms are checked once it is known. Assignment drops the old value. `while (const …)`. Trailing commas. It also fixes a hole you did not mention: a borrow assigned to an outer `let` could outlive an inner block's binding (`if (c) { const a = …; s = a[0..2]; } use(s)`); now a block's end checks that nothing used afterwards holds a borrow of its bindings, and assigning a whole binding replaces (rather than unions) what it holds.
- 0.31 comes from writing a calculator as a TypeScript programmer would: Copy parts bound through a `readonly` borrow bind copies (so `while (const #Some(#Op(op)) = self.peek()) { self.pos += 1 }` checks); a borrow of a `Box<T>` lends `T`; a literal's part whose slot is a borrow is lent rather than moved; an open tag union (built where nothing was expected) becomes an enum that a later branch gives if the enum has all its tags; a recursive type alias is a clear error.

Please review holistically:
1. **Soundness** of each new rule. In particular: (a) copy-binding through `readonly` — is "nothing can change the original while it is lent readonly" true given `Cell`, interior mutability through `Arc<Mutex>`, or a `readonly` borrow of a value another task mutates? (b) open union → enum: can an open union that was already used structurally elsewhere (stored, passed) now also be an enum, creating two views of one value? (c) the scope-end check together with loops and `defer`; (d) the operation-argument rule versus generators (`Yield<T>` where `T` is a borrow — `for (const w of s.splitWhitespace())`), which is the most common resumptive handler.
2. **Is the core ready to freeze as 1.0?** List the blockers, if any, and the things that can safely be left to 1.x as additive.
3. **The weakest part now**, bluntly, and the single most valuable change.

## Context files

- `docs/spec.md`

## Answer

### Verdicts

- **(1a) Copy-binding through `readonly` (`§4.1`)**: **Agree with changes.** It is sound for primitive `Copy` types, `Cell`, `Arc<Mutex>`, and concurrency, **except** when a `Copy` type is **class 2** (`readonly U`, `str`, `U[]`, or a `Copy` view/tuple/record containing them): copying a `readonly str` into an owned `str` must **preserve the underlying loan** on the borrowed owner, or a borrow of a local escapes!
- **(1b) Open union → enum coercion (`§3.3`)**: **Disagree as stated; agree with restriction.** Unifying an open union `#Tag(...) | ...ρ` with an `enum` is only sound if the row tail `ρ` has not been shared with another structural union type variable; otherwise one value is simultaneously viewed as a structural union and as a nominal `enum` (violating `§3.3` nominal identity, `Drop`, and representation).
- **(1c) Scope-end borrow check + assignment replacement + loops + `defer` (`§4.1`, `§5.6`)**: **Disagree — two soundness holes.** (1) In a loop, checking that no outer binding holds a loan of a loop-local binding only when a binding is *"used afterwards"* (after the loop exits) misses uses at the **top of the next iteration** before the outer variable is reassigned! (2) Assigning to a binding `x = newVal` drops the old value of `x` (`§5.6`), which is unsound if another live binding `b` still holds a borrow of `x`!
- **(1d) Operation arguments vs `Yield<T>` (`§5.3`, `§5.5`)**: **Disagree — contradicts `Gen<T, E>.next()` (`§5.5`)!** `Gen.next()` is written in Flyscript using a resumptive handler (`yield(item) resumes k => #Item { item, rest: k }`) that **returns `item` from the arm without calling `k`**, which the new `§5.3` rule (*"never past the arm: it cannot be the arm's value"*) explicitly forbids whenever `T` can hold a borrow (e.g., `xs.iter()`, `lines.iter()`, `Gen<str, []>`)!
- **(2) Readiness to freeze as 1.0**: **Close, with 4 soundness blockers to fix first** (Problems 1–4 below). Everything else is genuinely 1.x additive.
- **(3) Weakest part & single most valuable change**: **The gap between `handle`/`Cont` (`§5.3`) and pull generators `Gen<T, E>` (`§5.5`) over borrowed items.** Fixing the source-loan vs body-local-loan distinction (Problem 1 below) solves `Gen<str>` and operation arguments with one rule instead of an ad-hoc prohibition.

---

### Problems

#### 1. The operation-argument rule (`§5.3`) breaks `Gen<T, E>` (`§5.5`) whenever `T` is a borrow or type parameter!

Look at `§5.3`:
> *"So a parameter whose type can hold a borrow is usable in a resumptive arm only until the arm calls `k` — the body may then finish and its locals end — and never past the arm: it cannot be the arm's value, nor stored where the arm's end would leave it dangling."*

Now look at `§5.5`, where `generate` and `Gen<T, E>` are defined as ordinary library code over `handle` and `Cont`:
```ts
export struct Gen<T, row E> { state: Option<Cont<void, Step<T, E>, E>>; }
type Step<T, row E> = #Done | #Item { item: T; rest: Cont<void, Step<T, E>, E> };
```
How does `generate(f)` build that `Step<T, E>`? By running `f()` under a `Yield<T>` handler:
```ts
handle {
  f();
  #Done
} with Yield<T> {
  yield(item) resumes k => #Item { item, rest: k },
}
```
Look at what the resumptive arm `yield(item) resumes k => #Item { item, rest: k }` does:
1. Its parameter `item` has type `T` (a type parameter not bounded by `Send`, or instantiated to `str` / `readonly Elem` in `xs.iter()`). By `§4.2`, `T` **can hold a borrow**!
2. The arm **does not call `k`** — it stores `k` in `#Item { item, rest: k }` and **returns `item` past the arm as part of the arm's value**!
3. Under `§5.3`'s rule (*"a parameter whose type can hold a borrow is usable in a resumptive arm only until the arm calls `k` ... and never past the arm: it cannot be the arm's value"*), **`generate` in `§5.5` is rejected by the compiler!**
4. Even worse: what if someone writes a generator that yields a slice of its *own local buffer* and pulls it with `.iter()` / `generate`?
```ts
function badGen(): void uses Yield<str> {
  const localBuf: String = "hello".toString();
  yield localBuf.asStr(); // lends `localBuf` (a frame local inside `badGen`!)
}

export function exploit(): void {
  let g = generate(() => badGen());
  const #Some(s) = g.next() else { return; };
  // `g` is now suspended right after `yield`, so `localBuf` on `g`'s stack is still alive!
  // Now drop `g` (or call `g.next()` again):
  const _ = g.next(); // `badGen` finishes, `localBuf` is dropped and freed!
  println(s);         // USE-AFTER-FREE: `s` still points into `localBuf`!
}
```
Look closely at why `for (const w of line.splitWhitespace())` (`A.2`) works while `generate(() => badGen())` is a use-after-free, AND why `xs.iter()` is safe until `g.next()` is called again:
- In `for (const x of e) { body }`, `for…of` is a **tail-resumptive** handler (`yield(x) resumes k => { body; k() }`). The body of the `for` loop runs **before** `k()` is called! So `x` is only used before `k()` is called, which satisfies `§5.3`!
- **Wait:** what if the `for…of` loop assigns `x` to a variable declared *outside* the `for` loop?
```ts
export function forLoopEscape(line: str): str {
  let escaped: str = "";
  for (const w of badGen()) {
    escaped = w; // `w` is an operation argument of `Yield.yield`!
    break;       // drops the continuation (`localBuf` is freed!), exits the arm without calling `k`!
  }
  escaped // DANGLING POINTER if `w` was allowed to be stored in `escaped`!
}
```
Look at what `forLoopEscape` does:
- Inside `for (const w of badGen())`, the desugared handler arm is:
  `yield(w) resumes k => { escaped = w; break; /* drops k! */ }`
- In that arm, `w` is used *before* `k` is called (in fact `k` is dropped by `break`!).
- Yet assigning `escaped = w` stores `w`'s loan into `escaped`, which lives **past the arm**!
- Why didn't `§5.3` catch `escaped = w` if `w` had no loan attached to it? Because `§5.3` didn't give the operation parameter `w` a **fresh local loan scoped to the arm (before `k` is called / dropped)**!
- AND why *can* `xs.iter().next()` return `Option<readonly T>` safely in `§5.5` when iterating over `xs: Vec<T>`?
  Because in `xs.iter()`, the yielded `readonly T` is borrowed from `xs` (a source **outside** the generator), whereas in `badGen()`, `localBuf.asStr()` is borrowed from a local **inside** the generator!

Let's check both sides of this!
1. **Why `for…of` + operation arguments need a loan in Γ:**
   In `op(x) resumes k => armBody`, treat each operation parameter `x` as carrying a fresh loan `L_op` whose owner expires **immediately before any call to `k(...)`, any explicit drop/move of `k`, or the end of `armBody`** (whichever comes first).
   Then your existing scope-end borrow rule (`§4.1`: *"when a block ends, neither its value nor any binding used afterwards may hold a borrow of a binding declared in it"*) **automatically** forbids:
   - using `x` after `k(...)` (because `k(...)` ends `L_op`);
   - returning `x` from `armBody` (because `L_op` ends with `armBody`);
   - assigning `escaped = x` and reading `escaped` after `k(...)` or after `armBody` (as in `forLoopEscape` above)!
2. **Then how does `xs.iter()` / `Gen<T, E>` (`§5.5`) work when `T` is `readonly Elem` or `str`?**
   Look at `xs.iter()` vs `generate(() => ...)`:
   - If `Gen<T, E>` is created by `generate(f)`, can `f` yield a borrow of `f`'s own local variable (like `badGen`)?
     **Only if `Yield<T>` is handled by `for…of` (where the item dies before `k()` resumes or drops)!**
   - In pull iteration (`generate(f)` returning `Gen<T, E>`), each item `T` is returned **out of `next()` to the caller while `k` remains suspended**, and could even be kept by the caller across the *next* call to `g.next()`!
   - Wait: if a caller does:
     ```ts
     let g = generate(() => badGen());
     const a = g.next(); // returns borrow of `badGen`'s local!
     const b = g.next(); // resumes `badGen`, which drops its local! `a` now dangles!
     ```
     Even if `a` tied its borrow to `mut self` (`next(self: mut Self): Option<T> from self`), in `generate(f)` what stops `f` from returning a borrow of a local that gets destroyed on `drop(g)` while `a` (if not tied to `g`) is still live, OR if `next` is `from self`, what stops an arbitrary `handle` arm from returning `x`?
   - Look! In `Gen<T, E>`:
     Why is `xs.iter()` safe? Because the items yielded by `xs.iter()` are borrowed from `xs` (which `g` itself borrows), **never from a local inside the generator body**, OR `next(self: mut Self): Option<T> from self` ties the returned `Option<T>` to `self` (`g`)!
     Wait: even if `next(self: mut Self): Option<T> from self` ties the returned `Option<T>` to `self`:
     If `badGen()` yields a borrow of its own local `localBuf`, and `g.next()` returns `#Some(s)` tied to `g`:
     As long as `s` is used, `g` is borrowed (so `g.next()` cannot be called again and `g` cannot be moved/dropped while `s` is live!).
     **Wait**: what happens when the block ends?
     ```ts
     let s: str = "";
     {
       let g = generate(() => badGen());
       if (const #Some(x) = g.next()) {
         s = x; // `x` borrows `g` (via `from self`)!
       }
     } // `g` is local to the block, so `s` cannot outlive `g`!
     ```
     Hold on! What if `s` is used *inside* the same block, after `g` is no longer used?
     In Flyscript (`§4.1`, `§5.6`), **when is a local variable `g` dropped?**
     `§4.1`: *"At the end of its scope a live owner is dropped."* (Not at its last use!)
     Wait: what if `g` is **reassigned** (`g = generate(...)`) or **moved** (`drop(g)`) while `s` (which borrows `g` via `from self`) is still live?
     Because `s` holds a borrow of `g`, `g` is locked in Γ while `s` is live — so `g` **cannot** be moved, reassigned, or have `g.next(mut g)` called while `s` is live! And at the end of `g`'s scope, `s` cannot be used after the scope ends!
     **Wait — what if `badGen()` drops `localBuf` BEFORE `badGen()` finishes (e.g., in an inner block inside `badGen()`)?!**
     ```ts
     function innerBlockGen(): void uses Yield<str> {
       {
         const tmp = "boom".toString();
         yield tmp.asStr();
       } // `tmp` is dropped as soon as `k()` resumes!
     }
     ```
     Even during the yield suspension, `tmp` is alive on `k`'s stack; it is only dropped when `k()` is resumed or dropped — both of which require mutating or consuming `k` (i.e., `g`)!
     **WAIT A SECOND!** Why did `§5.3` fail in 0.29 then?
     In 0.29, an arm could do:
     ```ts
     handle {
       const tmp = "boom".toString();
       Eff.op(tmp.asStr());
     } with Eff {
       op(s) resumes k => {
         // Drop `k` (by not using it) and return `s`!
         s
       }
     }
     ```
     In that 0.29 bug, the arm **dropped `k`** (unwinding `tmp`) and returned `s`!
     Why was that a bug? Because `s` was borrowed from **`k`'s suspended frame**, NOT because `s` left the arm alongside a live `k`!
     Read that again!
     While `k` is **suspended and not yet resumed or dropped**, every local in the suspended body up to the operation call is **still alive on `k`'s stack**!
     Those locals only die when `k` is **resumed (`k(...)`) or dropped**!
     Therefore:
     **In a resumptive arm `op(x) resumes k => ...`, each operation parameter `x` borrows `k`!**
     Check every consequence of that one rule (**"In a resumptive arm, each operation parameter `x` holds a borrow of `k`"**):
     1. **What if the arm calls `k(a)` (`k` is moved/consumed) and then uses `x`?**
        Moving `k` to call `k(a)` requires that no live variable still holds a borrow of `k`! So `x` (and anything derived from `x`) **cannot be used after `k(a)` is called**!
     2. **What if the arm does not return `k` (so `k` is dropped at the end of the arm) and tries to return `x` or store `x` in an outer variable?**
        Because `k` is a local binding of the arm, if `k` is dropped at the end of the arm, the block-end rule (`§4.1`: *"when a block ends, neither its value nor any binding used afterwards may hold a borrow of a binding declared in it"*) **forbids `x`'s borrow of `k` from escaping in the arm's return value or in an outer variable**!
     3. **What if the arm returns `#Item { item: x, rest: k }` (as in `generate` / `Gen<T, E>` in `§5.5`)?!**
        Wait: in `#Item { item: x, rest: k }`, `k` is moved into `rest` while `x` holds a borrow of `k` (a self-referential struct if unpacked!).
        So in general user code, a struct cannot simultaneously move `k` and hold a borrow of `k`.
        Instead, for `Gen<T, E>`, why does `Gen<T, E>` work in `§5.5`?
        Because in `§5.5`:
        ```ts
        export function next(self: mut Self): Option<T> from self uses ...E
        ```
        Notice that in `§5.5`, `Gen.next` is currently written **without** `from self`:
        `export function next(self: mut Self): Option<T> uses ...E`
        Wait: if `xs` is a `Vec<String>`, what is the type of `xs.iter()`?
        `Gen<readonly String, []>` (holding a borrow of `xs`).
        When you call `g.next()`, `T` is `readonly String` (borrowed from `xs`, **not** from `g`!).
        Because `g` is `Gen<readonly String, []>`, `g` is already a source of `g.next()` (it is the receiver `self`, and by `§4.2`, *"without [a `from` clause], the receiver for a method"* is a source!). So `g.next()` already propagates `g`'s borrow of `xs` into the returned `Option<readonly String>`!
        The **only** reason `generate(f)` in `§5.5` was pseudo-code that violated `§5.3` is that `§5.5` showed the body of `Gen.next` as Flyscript code using `Step<T, E>`!

**Fix for Problem 1 (`§5.3` and `§5.5`):**
1. In **`§5.3`**, ensure that inside a resumptive arm `op(x) resumes k => ...`, `x` carries a fresh loan that expires when `k` is called or when the arm ends (so `escaped = x` in `forLoopEscape` is caught by the loan tracker, not just direct reads of `x`!).
2. In **`§5.5`**, how should `generate` work if `§5.3` forbids `yield(item) resumes k => #Item { item, rest: k }` when `T` can hold a borrow?
   Look at `generate`: if a generator `f` is turned into a pull iterator `generate(f): Gen<T, E>`, when can `T` safely leave the `Yield<T>` arm while `k` is stored?
   **Only when `T`'s borrows come from `f` (the generator's captures outside `handle`), never from locals inside `f`'s body!**
   Wait: inside `f`, `yield e` is an operation call `Yield.yield(e)`. Normally, `Yield.yield(local.asStr())` is completely legal in `for (const x of f())` because `for…of` consumes `x` before resuming `k()`!
   If `generate(f)` is a runtime/stdlib primitive (declared in the prelude as `export function generate<T, row E>(f: once () => void uses Yield<T>, ...E): Gen<T, E>;`), wait: if a user passes `badGen` (which yields `localBuf.asStr()`) to `generate(() => badGen())`, what stops `badGen` from yielding a borrow of its own local `localBuf`?
   Nothing in `badGen`'s signature (`function badGen(): void uses Yield<str>`) says whether the `str` passed to `Yield.yield` came from a parameter of `badGen` or a local of `badGen`!
   Look at `badGen()` again:
   ```ts
   function badGen(): void uses Yield<str> {
     const localBuf = "hello".toString();
     yield localBuf.asStr();
   }
   ```
   `badGen` has **no parameters**! Yet its signature is `function badGen(): void uses Yield<str>`!
   If `generate(() => badGen())` is allowed for `T = str`, then:
   ```ts
   export function uaf(): void {
     let g = generate(() => badGen());
     const #Some(s1) = g.next() else { return; };
     // Look at `g.next()`'s signature in §5.5:
     // `export function next(self: mut Self): Option<T> uses ...E`
     // Even if `s1` borrows `g` (via receiver source rule in §4.2):
     // `badGen()` has NO parameters, so `g = generate(() => badGen())` holds NO borrows (class 1)!
     //Wait: if `g` holds NO borrows, what borrows does `g.next()`'s result hold according to §4.2?!
   }
   ```
   Read `§4.2` carefully!
   In `uaf()`:
   - `badGen` takes 0 arguments. So the closure `() => badGen()` captures **nothing** (holds 0 loans).
   - `let g = generate(() => badGen())` therefore holds **0 loans**!
   - Wait: when `g.next()` is called (`self: mut Gen<str, []>`), `self` is lent `mut` for the call `g.next()`.
   - Because `Option<str>` is class 2, `s1` holds the `mut` borrow of `g`!
   - So while `s1` is live, `g` is locked `mut`: you cannot call `g.next()` a second time while `s1` is live, and `s1` cannot outlive `g`'s block!
   - **WAIT A SECOND!** Look at what Happens if `badGen()` yields **inside a block**:
   ```ts
   function badGen2(): void uses Yield<str> {
     {
       const localBuf = "hello".toString();
       yield localBuf.asStr();
     } // <-- `localBuf` is dropped HERE when resumed, BEFORE `badGen2` even yields a second time!
     yield "world";
   }
   ```
   While `s1` is live, `g` is borrowed `mut`, so `g.next()` cannot be called to resume `badGen2`!
   And when `s1`'s last use passes, `s1` is dead, so when `g.next()` IS called (or when `g` is dropped at the end of the block), `s1` is **already dead**!
   **HOLD EVERYTHING!** Verify that!
   Is it true that because `g.next(self: mut Self): Option<T>` borrows `g` mutably, and `Option<T>` (when `T` is class 2) carries the borrow of `self` (`g`), **`s1` locks `g` mutably for the entire lifetime of `s1`**?!
   Let's trace every possible way `localBuf` inside `badGen` could be freed while `s1` is still alive:
   1. Can `g.next()` be called again while `s1` is alive?
      **No!** `s1` holds a `mut` borrow of `g`, so `g` is locked against all use (`§4.1`, `§9`) until `s1`'s last use!
   2. Can `g` be dropped or moved or reassigned while `s1` is alive?
      **No!** `g` is locked by `s1`'s `mut` borrow until `s1`'s last use, and `s1` cannot outlive `g`'s block (`§4.1`)!
   3. What if `T` is a type parameter or closure that hides a borrow (e.g. `Gen<() => void, []>`)?
      By `§4.2`, a type that can hide a borrow also carries its sources' borrows (`self`, i.e., `g`)!
   4. Wait: why did `g.next()` in `uaf()` lock `g`?
      Because in `g.next()`, `self` is `mut Gen<T, E>`! Even when `g` itself holds 0 outer loans, passing `mut g` to `g.next()` creates a **new `mut` loan of the variable `g` itself**, and by `§4.2` (*"without [a `from` clause], the receiver for a method"* is a source), the result of `g.next()` holds **that `mut` loan of `g`**!

   **Now check if `flyc`'s ownership pass actually does this when `g` is a class-1 binding!**
   Look at `uaf()` again:
   - What is the type of `g`? `Gen<str, []>`.
   - Because `str` is a type argument of `Gen<str, []>`, `Gen<str, []>` is **class 2** (`§4.2`).
   - When `g.next()` is called, `mut g` lends `g`, creating a `mut` loan on path `g`.
   - `g.next()` returns `Option<str>` (class 2), whose source is `self` (`mut g`).
   - So `s1` holds the `mut` loan on `g`!
   - While `s1` is live, `g` is locked `mut`!
   **Wait: what if `s1` is `Copy` (`str` is `Copy`!)?**
   Look at `§4.1`'s new 0.31 rule:
   > *"Copy parts bind by copy. A name bound through a `readonly` borrow — by a pattern taking apart a borrowed value, or by `const` from a borrow — binds a copy instead if its type is `Copy`. Nothing can change the original while it is lent `readonly`, so the copy is indistinguishable from the borrow, but it holds nothing"*
   **STOP AND LOOK AT THAT SENTENCE Combined with `str` and `readonly T[]`!**
   That brings us directly to Problem 2!

---

#### 2. Soundness bug in 0.31: "Copy parts bind by copy ... holds nothing" (`§4.1`) allows `str`, `readonly T[]`, and `readonly T` (which are `Copy`!) to strip their borrows!

Read `§3.1` and `§4.1`:
- `readonly T`, `str`, and `readonly T[]` are **`Copy`** (`§4.1`: *"`readonly T` is `Copy`"*; `str` and `readonly T[]` are borrowed slices, which are `Copy`).
- Now read the new 0.31 rule in `§4.1`:
  > *"Copy parts bind by copy. A name bound through a `readonly` borrow — by a pattern taking apart a borrowed value, or by `const` from a borrow — binds a copy instead if its type is `Copy`. Nothing can change the original while it is lent `readonly`, so the copy is indistinguishable from the borrow, **but it holds nothing**"*

Now run this program under that rule:
```ts
view struct Holder { s: str; }

export function launderStr(): str {
  const localStr: String = "dangling".toString();
  const h = Holder { s: localStr.asStr() }; // `h` holds borrow of `localStr`
  const refH: readonly Holder = h;          // `refH` is a `readonly` borrow of `h`
  const Holder { s } = refH;                // Pattern taking apart a `readonly` borrow!
  // `s` has type `str`, which is `Copy`!
  // If `s` binds a copy that "holds nothing", `s` loses its borrow of `localStr` (and `h`)!
  s // Returns dangling `str` after `localStr` is dropped!
}
```
And even simpler, without a struct:
```ts
export function launderOption(): str {
  const localStr: String = "dangling".toString();
  const opt: Option<str> = #Some(localStr.asStr());
  const refOpt: readonly Option<str> = opt;
  const #Some(s) = refOpt else { return ""; };
  // `s: str` is bound through `refOpt` (`readonly Option<str>`).
  // `str` is `Copy`, so `s` is bound by copy instead of `readonly str`.
  // Wait: `s` does NOT hold the new borrow of `opt` (`refOpt` was just reading `opt`),
  // BUT `s` STILL holds the class-2 borrow inside `opt` (the borrow of `localStr`)!
  s
}
```
Look at the difference between the two borrows involved when reading a `Copy` field/payload `part` out of `r: readonly Container`:
1. If `part` has a **class-1 `Copy` type** (like `u8`, `i32`, `bool`, `{ x: f64; y: f64 }`):
   Copying `part` out of `r` produces an owned class-1 value that holds **no borrows at all** (neither the outer borrow of `Container` nor any inner borrow).
2. If `part` has a **class-2 `Copy` type** (like `str`, `readonly u8[]`, `readonly Token`):
   Copying `part` out of `r: readonly Container` produces `str` (not `readonly str`), so it does not need to keep `Container` itself locked if `Container` was just a wrapper, **WAIT**: what if `Container` is `String` or `Vec<T>`? You can't pattern-match `String` or `Vec<T>`, you pattern-match `Option<readonly Token>` or `Holder { s: str }`, which *already* carry the underlying loan of `localStr` or `self.toks`!
   So if `s: str` is copied out of `refOpt: readonly Option<str>`, `s` **must still carry the loans that `opt` held**! It only avoids adding a *new* layer of `readonly` indirection (`readonly str`), or even simpler:
   **A `Copy` part binds a copy with no loans only when it is class 1 (`Copy` and `Send`, or class-1 `Copy`)!**
   Wait: what if someone matches `readonly Option<readonly Token>` (e.g., `self.peek()` returning `readonly Option<Token>` vs `Option<readonly Token>`)?
   - In `while (const #Some(#Op(op)) = self.peek())`, `op` is `u8`, which is **class 1 and `Copy`**!
   - If the rule says:
     > *"A name bound through a `readonly` borrow — by a pattern taking apart a borrowed value, or by `const` from a borrow — binds a copy instead if its type is `Copy`; if that type is class 1, the copy holds no borrows."*
   Check what happens in both cases:
   - For `op: u8` (class 1 and `Copy`): `op` binds a `u8` copy and **holds no borrows** (`self` is completely free!).
   - For `s: str` or `tok: readonly Token` (class 2 and `Copy`): `s` binds a `str` (copied value, not `readonly str`), and **keeps the borrows that the matched container held** (so `launderStr` and `launderOption` still know `s` borrows `localStr`)!

Now let's also check your three sub-questions on **(1a)**:
- **What about `Cell<R, T>`?**
  A `Cell<R, T>` is a region handle (`Copy`, class 1). If you pattern-match a `readonly StructWithCell` and copy out `c: Cell<R, u32>`, `Cell` is a handle (like a pointer) into region `R`. Mutating `c.set(42)` requires the `Region<R>` effect (`§4.6`), which is legal even through a `readonly` struct (`A.5`: `self: readonly Self` in `Scope.define`). Copying the `Cell` handle doesn't copy the cell's contents; reading its contents requires `c.get() uses Region<R>`. And if you pattern-match `readonly u8` inside a `Ref<R, T>`, nothing in `R` can mutate a `Ref<R, T>` (`Cell` is never borrowed, `§4.6`). So `Cell` is completely sound.
- **What about `Arc<Mutex<T>>`?**
  `Mutex<T>`'s contents can only be accessed by locking the mutex (`uses Io`), which returns a scoped guard, and if you borrow inside it, the guard stays locked while borrowed. Copying a `u8` out while holding the lock just copies the `u8` value at that instant. Completely sound.
- **What about a `readonly` borrow of a value another task mutates?**
  By Law 1 and `§6.1` Rule 6, a task can only capture `readonly` borrows of `Send` values whose paths are not under `mut` in Γ, and the parent fiber waits for all tasks in `Io.scope` before returning. No other task can hold a `mut` borrow of that value at the same time. Completely sound.

---

#### 3. Two soundness holes in the 0.30/0.31 scope-end and reassignment rules (`§4.1`, `§5.6`)

##### Hole 3a: Loop iteration boundary (`§4.1`)

Read `§4.1`:
> *"A borrow cannot outlive what it borrows: when a block ends, neither its value nor any binding used afterwards may hold a borrow of a binding declared in it. ... In a loop, the body's bindings end with each iteration."*

Look carefully at the wording: *"when a block ends, neither its value nor any binding **used afterwards** may hold a borrow of a binding declared in it."*
What does *"used afterwards"* mean for the **body block of a `while` or `for` loop**?
If *"used afterwards"* only checks uses **after the loop statement**, or even if it checks uses inside the loop body, look at this program:
```ts
export function loopDangle(): void {
  let s: str = "init";
  let i: i32 = 0;
  while (i < 2) {
    // At the start of iteration 2 (i == 1), `println(s)` reads `s`!
    // In iteration 1 (i == 0), `s` was assigned `a.asStr()`, where `a` was declared in the loop body
    // and DROPPED at the end of iteration 1!
    println(s);
    const a: String = `iter ${i}`;
    s = a.asStr();
    i += 1;
  }
  // Notice: `s` is NEVER used after the `while` loop ends!
}
```
Trace `loopDangle()`:
1. `s` is **never used after the `while` loop ends**.
2. Inside the `while` body, `println(s)` appears **before** `const a` and **before** `s = a.asStr()`.
3. After `s = a.asStr(); i += 1;`, the loop body block ends!
4. Between `s = a.asStr()` and the end of the block, `s` is not used, and after the `while` loop, `s` is not used!
5. Yet on iteration 1 (`i == 0`), `s` is set to `a.asStr()`, then `a` is **dropped at the end of iteration 1**, and on iteration 2 (`i == 1`), `println(s)` at the **top of the loop body** reads the freed memory of iteration 1's `a`!

**Fix for Hole 3a (`§4.1`):**
In a loop, a binding that is live at the **top of the loop** (in the loop condition or before being overwritten in the body) is reachable *after* the end of the loop body!
State this explicitly in `§4.1`:
> *"In a loop, the body's bindings end with each iteration, before the next iteration's condition and body."*
And in the compiler (`§11.4`), the reachability check at the end of a loop body must include uses reachable via the back-edge to the loop header/condition!

---

##### Hole 3b: Reassigning or dropping a binding while it is borrowed (`§4.1`, `§5.6`)

Read `§4.1` and `§5.6`:
- `§4.1`: *"a binding assigned anew holds the new value's borrows only"*
- `§5.6`: *"Assigning to a place drops the value it held first, unless that value was moved out"*

Now look at what happens when an **owned binding `owner`** is reassigned while another live binding `b` holds a borrow of `owner`:
```ts
export function reassignOwnerWhileBorrowed(): void {
  let owner: String = "first".toString();
  const b: str = owner.asStr(); // `b` borrows `owner`
  owner = "second".toString();  // Drops "first" (`§5.6`)!
  println(b);                   // USE-AFTER-FREE: `b` still points to "first"!
}
```
And what if a **borrow binding `b1`** is reborrowed into `b2`, and then `b1` is reassigned?
```ts
export function reassignBorrowWhileReborrowed(mut a: i32, mut c: i32): void {
  let b1: mut i32 = mut a;
  const b2: mut i32 = mut b1; // `b2` reborrows `b1` (which borrows `a`)
  b1 = mut c;                 // If `b1` now holds only `c`'s borrow, is `a` unlocked while `b2` still mutates `a`?!
  a = 10;                     // ALIASING VIOLATION if `b2`'s loan of `a` was tracked only through `b1`!
  b2 += 1;
}
```
Let's check both:
1. In `reassignOwnerWhileBorrowed()`: assigning to `owner` mutates `owner` and drops its old value, so `owner` **cannot be assigned to while any live binding (`b`) holds a `readonly` or `mut` borrow of `owner`**!
   Check `§4.1`: `§4.1` says *"While [a `mut T` borrow] exists, the owner is inaccessible"* and `§9` says *"A `mut` entry locks its path against all use; a `ro` entry locks it against moves and `mut` borrows."*
   It does **not** explicitly say that a `ro` entry (or `mut` entry) locks its path against **reassignment** (`owner = ...`)!
2. In `reassignBorrowWhileReborrowed()`: `b2` must inherit the underlying loan of `a` (not merely a pointer to `b1`'s current loan set), OR reassigning `b1` must be forbidden while `b1` is borrowed by `b2`.

**Fix for Hole 3b (`§4.1`, `§9`):**
In `§4.1` and `§9`, state explicitly that **assigning to a place requires that no live borrow locks that place (neither `readonly` nor `mut`)**. (When `b2` reborrows `b1`, `b2` carries `b1`'s underlying loans on `a` *and* locks `b1`, so `b1` cannot be reassigned while `b2` is live, and once `b2` is dead, `b1 = mut c` is legal and replaces `b1`'s loans with `c`'s.)

---

#### 4. Open union → `enum` coercion (`§3.3`) can unify a shared open union with a nominal `enum`

Look at `§3.3`:
> *"Tags built where no type is expected make an open union, as in §3.2. Where such a union meets an enum that has all its tags — a branch of an `if` or `match` whose other branch is an `Expr`, an argument or return of type `Expr` — it is that enum, as if `Expr` had been expected where the tags were built: `if (leaf) { #Num(1.0) } else { parsed }` is an `Expr`."*

Now look at what happens when an open union is built, stored in a local (or passed to a row-polymorphic function), and *then* meets an `enum`:
```ts
enum Expr { #Num(f64), #Add(Box<Expr>, Box<Expr>) }
enum OtherEnum { #Num(f64), #Sub(f64) }

export function schizo(): void {
  // 1. `#Num(1.0)` is built where no type is expected: type is `#Num(f64) | ...ρ`
  const x = #Num(1.0);

  // 2. `x` meets `Expr` (which has `#Num(f64)`):
  const e1: Expr = x;

  // 3. What is `x`'s type now? What if `x` ALSO meets `OtherEnum`, or a structural union `#Num(f64) | #Bar`?
  const e2: OtherEnum = x; // Is `x` simultaneously `Expr` AND `OtherEnum`?!
}
```
And even with a single `enum`:
```ts
enum Secret { #Val(i32) }
impl Drop for Secret {
  function drop(self: mut Self): void { println("dropped Secret!"); }
}

export function dropConfusion(flag: bool): void {
  const x = #Val(1); // Open union `#Val(i32) | ...ρ`, which is `Copy`!
  const y = x;       // `x` is copied to `y` (because `#Val(i32) | ...ρ` is a structural union of `i32`, hence `Copy`!)
  if (flag) {
    const s: Secret = x; // Now `x`'s type `#Val(i32) | ...ρ` becomes `Secret` (which has `Drop` and is NOT `Copy`!)
  }
  // Now both `s` and `y` get dropped as `Secret`s, running `Drop` TWICE on one construction!
}
```
Look at `dropConfusion`:
1. When `const x = #Val(1)` is typed, no expected type is present, so `x` gets open union type `#Val(i32) | ...ρ`.
2. Wait: if `x`'s type is later mutated in-place by the unifier from `#Val(i32) | ...ρ` into the nominal `enum Secret` when `const s: Secret = x` is checked:
   - What if `x` was also unified with `OtherEnum` (as in `schizo`)? If the unifier actually replaces the union type node with `Secret`, then `e2: OtherEnum = x` fails (good), **unless** the unifier only checked inclusion without replacing the type node (in which case `x` stayed an open union and coerced to *both* `Expr` and `OtherEnum`!).
   - What if `x` was unified with `#Val(i32) | #Extra` (a tag `Secret` does *not* have) before meeting `Secret`? If `#Val(i32) | ...ρ` was replaced by `Secret`, any other reference to `ρ` could lose `#Extra`, or if all current tags are checked, `#Extra` prevents it.
   - And in `dropConfusion`: if the unifier turns `x`'s type into `Secret`, because ownership checking runs **after** typing (`§11.4`), `const y = x` sees `x: Secret` (non-`Copy`) and moves `x`, so `const s: Secret = x` is rejected by the ownership pass **only if** the unifier truly unified `x`'s type with `Secret` (so `x` itself has type `Secret`, not open union)!

**Check how `flyc` implements this rule:**
- Does unifying an open union `U = #T1 | ... | #Tn | ...ρ` with `enum E` **instantiate the whole union type `U` to `E`** (so `x` itself becomes `E`, and cannot also become `OtherEnum` or take non-`E` tags)?
- Or does it merely treat `U` as a subtype of `E` while leaving `x` as an open union `#Val(i32) | ...ρ`?
If `x` stays an open union while `const s: Secret = x` has type `Secret`:
- In `dropConfusion`, `x` is `Copy` (open union `#Val(i32)`), while `s` is `Secret` (`Drop`), and at runtime in a native compiler, `x` and `s` might not even have the same tag discriminant number (since structural union tags are sorted canonically by name, `§3.2`, whereas `enum` tags are in declaration order, `§3.5`)!
Look at that representation point:
- In `§3.2`: *"A row is a finite map from labels to types ... solved by one Rémy-style unifier over label-sorted rows."*
- In `§3.5`: *"`Ord extends Eq` is derived too, ordering by fields and then by tags, in declaration order"*.
- If an open union `#Num(1.0)` is built first and only later discovered to be `enum Expr { #Add(...), #Num(f64) }`, its type at the construction site **must become `Expr`** (not stay a structural union coerced at the use site), so that code generation emits `Expr`'s discriminant and layout at the construction site!
And to make sure an open union type variable becomes `Expr` cleanly:
When an open union `#T1(P1) | ... | #Tn(Pn) | ...ρ` (whose tail `ρ` is an unbound unification variable, not a `<row R>` parameter) is unified with a nominal `enum E` that defines all of `#T1 .. #Tn`, unify each `Pi` with `E`'s payload for `#Ti` and **bind the open union itself to `E`**!

**Fix for Problem 4 (`§3.3`):**
State explicitly in `§3.3` that the open union **unifies with** (becomes) the `enum` (which is only allowed when its row tail is an unbound inference variable, not a `<row R>` parameter).

---

### Question 2: Is the Core Ready to Freeze as 1.0?

Once Problems 1–4 above are resolved, **yes — the core language is ready to freeze as 1.0.**

Here is the exact separation between **1.0 blockers** and **1.x additive features**:

#### Blockers before freezing 1.0 (must fix now)
1. **Problem 1 (`§5.3` vs `§5.5`):** Reconcile the operation-argument rule in `§5.3` with `Gen<T, E>` in `§5.5`, and ensure operation parameters in resumptive arms carry a loan in Γ that expires when `k` is called/dropped or the arm exits (catching indirect escapes like `escaped = w; break;` in `for…of`).
2. **Problem 2 (`§4.1`):** Restrict "holds nothing" on `Copy` pattern bindings through `readonly` borrows to **class-1 `Copy` types** (so `str`, `readonly T[]`, and `readonly T` keep the underlying loans of the value they were copied from).
3. **Problem 3 (`§4.1`, `§5.6`, `§9`):**
   - Check loop body local loans against bindings live at the **top of the next iteration** (loop condition / back-edge), not just after the loop exits.
   - Forbid reassigning a binding while any live borrow (`readonly` or `mut`) locks it.
4. **Problem 4 (`§3.3`):** Ensure open-union-to-`enum` unification binds the open union's type to the `enum` (and only when its tail is an unbound inference variable, never a `<row R>` parameter).

#### Safely left to 1.x as additive (do not block 1.0)
1. **`Simd<T, N>` (`§12.3`):** Purely library/intrinsic types over existing `Copy` / `ParSplit`.
2. **Actor supervision trees (`§12.3`):** Pure library code over `Io.scope`, `spawn`, and channels.
3. **Pattern guards with `if (const ...)` chaining (`&&`):** Can be added to `IfConst` grammar later without breaking any 1.0 syntax.
4. **In-place collection/map entry APIs (`A.10`):** Library API addition to `HashMap`.

---

### Question 3: The Weakest Part Now, and the Single Most Valuable Change

**Bluntly, the weakest part of the 0.31 spec is the contradiction between `§5.3` (continuations and operation arguments) and `§5.5` (`Gen<T, E>` as library code).**

Law 4 (`§0`) promises:
> *"A handler may hold the rest of a computation as a one-shot continuation value; generators and tasks are both built from that one primitive."*
And `§5.5` proudly shows `Gen<T, E>` and `Step<T, E>` as 15 lines of ordinary Flyscript code.
Yet under `§5.3`'s new rule (*"a parameter whose type can hold a borrow is usable in a resumptive arm only until the arm calls `k` ... and never past the arm: it cannot be the arm's value"*), **the `generate` function in `§5.5` cannot even be written in Flyscript!**

**Why?** Because `§5.3` conflated two completely different kinds of borrows that an operation argument `x` in `op(x) resumes k => ...` can hold:
1. **A borrow of a local inside the `handle` body** (which lives on `k`'s stack frame and is destroyed when `k` finishes or is dropped).
2. **A borrow of a binding outside the `handle` block** (which outlives the `handle` expression itself!).

Look at what happens when you distinguish those two in `§5.3`:
- When `body` performs `Eff.op(arg)`:
  - Any borrow in `arg` that comes from **outside** `handle` is just an ordinary outer loan; it is valid for as long as its outer owner lives!
  - Any borrow in `arg` that comes from a binding **inside** `handle` (a body-local loan) lives on the suspended stack of `k`:
    - In an **abortive** arm (`op(x) => ...`), `body` has already unwound, so its body-local bindings have ended; the existing block-end rule (`§4.1`) *already* rejects using `x` if `x` may hold a body-local loan!
    - In a **resumptive** arm (`op(x) resumes k => ...`), `body`'s locals end when `k` is called or dropped; so `x` carries a loan tied to `k`'s suspension that ends when `k` is called, dropped, or the arm exits!
- And why does `xs.iter()` (`Gen<readonly T, []>`) work as a pull generator?
  Because in `xs.iter()`, the yielded `readonly T` borrows `xs` (which is **outside** the generator's `handle`), OR because `Gen.next(self: mut Self): Option<T>` ties the returned item's loan to `mut self` (`g`), which locks `g` (and therefore its stored `Cont` `k`!) against being resumed or dropped while the returned `Option<T>` is in use!

**The single most valuable change:**
In **`§5.3`** and **`§5.5`**, make `Gen.next` tie its return value to `self` (`from self`, which is already the default for a method in `§4.2`!) and in `§5.3` model the operation parameter's loan in a resumptive arm as a loan of the suspended frame that ends when `k` is called or dropped (while allowing `generate` in the standard library to bundle `#Item { item, rest: k }` because `Gen.next` lends `item` from `mut self`, locking `rest` for as long as `item` is live). That makes both `for…of` (even with `escaped = x; break;`) and `Gen<T, E>` (even when yielding borrows of generator-local buffers!) 100% sound and consistent with Law 4.

---

### Smaller points

- **`Generate(X)` in `ListLit` (`§2.3` vs `§7.2`):**
  In `§2.3`, `Generate(X)` was updated to include `comptime match`, which is used for `Field`, `Entry`, and `MatchArm`. However, `Item` in `ListLit` (`§2.3` line 153) still reads:
  `Item = Expr | "comptime" ( For | If ) ;` (missing `Match`, even though `§7.2` says *"The same `comptime for`, `comptime if` and `comptime match` generate the items of a sequence: ... the items of a list literal"*). Change `Item = Expr | Generate(Item) ;` (or `"comptime" ( For | If | Match )`) so the grammar matches `§7.2`.
- **`PatRecord` trailing comma (`§2.3`):**
  `§2.3` prose states *"Every comma-separated list in the grammar ... may end with a comma"*, which is great; you can drop the explicit `[ "," ]` from `Enum`, `Params`, and `Generate(X)` in the EBNF or leave the prose sentence to cover all productions uniformly.
