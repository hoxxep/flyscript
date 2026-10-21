# Review: holistic-review-of-0-34

- spec: 8e85fe125881
- request: dc3af8f1119695da
- tokens: prompt 67849, cached 0, answer 5949

## Question

Spec 0.34 (included). Since your review of 0.31:

- 0.32 adopts it, with two differences. (1) Instead of tying `Gen` items to `mut self`, a yielded value is now a *result* of its function: it may borrow what the function was given (parameters, a closure's captures), never its locals. That closes your `for…of` + `break` escape at the producer, keeps `best = w` across iterations legal, and makes `generate` sound with one `unsafe` arm (the `handle` body is a call of a closure, so it has no locals) — §5.5 now shows the library code, which a run test checks verbatim. (2) Open unions never become enums; the error says to annotate. Copy-binding of class-2 types keeps the loans (the implementation already did; the wording was wrong). Your loop and reassignment holes were already caught (`tests/reject/own_loop_borrow_outlives.fly`, and assignment is a write access).
- 0.33: TypeScript's array/generator methods (`sort`, stable `sortBy`, `join`, `find`, `some`, `every`, `reduce`, …); a string interpolated in generic code is written raw; a borrow of a borrow collapses.
- 0.34, from a concurrent fetch: tasks move in what is declared inside their scope and borrow only what is outside (a task could borrow a loop-local sender that died first); closures own what they move in from where they are made and a `once` closure drops it when its call ends; `Mutex<T>.lock(body)` with an effect-free body returning `Send`; `Sender` is `Clone` with the channel ending at the last sender; `drain()`; `Fail.capture` passes other effects on.

Please review holistically, then answer:
1. **Soundness** of 0.32–0.34's rules: the yield-as-result rule (including `yield` inside a closure, inside a `handle` body, and a generator method yielding borrows of `self`); the task capture rule (a task created inside a nested closure inside the scope body; `spawn` from a helper function that receives `mut Scope`); `Mutex.lock`'s effect-free body (is "no lock held across a scheduling point" enough to rule out deadlock between two mutexes? lock ordering inside one body?); `Arc` lending `readonly`.
2. **1.0 freeze**: with your four 0.31 blockers addressed, is anything else blocking? Be specific.
3. **Weakest part now**, bluntly, and the single most valuable change.

## Context files

- `docs/spec.md`

## Answer

### Verdicts

- **Yield-as-result and `generate`'s `unsafe` (`§5.5`)**: **Disagree.** The rule has two soundness holes: (1) a generator can yield a borrow of an **owned parameter** (`v: Vec<i32>`), which is dropped when the generator finishes or is broken out of, leaving the caller's kept item dangling; and (2) `generate(() => { ... }).map((x) => ...)` allows the `map` closure to yield a borrow of its **argument `x`**, which dies at the end of that `map` step when `next()` returns an owned temporary (or `xs.iter().cloned().map((s) => s.asStr())`).
- **Task capture rule (`§6.1` rule 6)**: **Disagree.** Defining task captures by *lexical position relative to `Io.scope`* fails when `mut Scope<X>` is passed to a helper function or captured by a nested closure: the helper has no `Io.scope` around it, or a parameter/local declared in the helper is borrowed by `s.fork(...)` and dropped when the helper returns, while the task is still running in the caller's scope.
- **`Mutex.lock` with a pure body returning `Send` (`§6.2`)**: **Agree.** Because `lock` itself performs `Io`, a pure body (`uses []`) cannot call `m2.lock(...)` or any other `Io` operation inside `m1.lock(...)`, so nested lock acquisition is impossible by construction. One lock per fiber at a time means a wait-for graph has out-degree $\le 1$ and no fiber waits while holding a lock — deadlock between mutexes is completely impossible, not just across I/O.
- **`Arc<T>` lending `readonly T` (`§0.1`, `§4.1`, `§4.5`)**: **Agree with changes.** Sound, because `Arc<T>` never grants `mut T` and `T extends Send` has no pure interior mutability. However, `Arc<T>` is listed as lending `readonly T` in `§0.1`'s changelog table, but is omitted from the normative **Lending** paragraph in `§4.1`.
- **1.0 freeze**: **Blocked** only by the two soundness holes above (Problem 1 and Problem 2), each of which is fixed by a one-sentence refinement to `§5.5` and `§6.1`/`§4.2`.

---

### Problems

#### 1. Yield-as-result (`§5.5`) allows yielding a borrow of an owned parameter or a transient adaptor parameter, causing a use-after-free

`§5.5` states:
> *"A yielded value is a result of the function that yields it, handed out before the function returns: like a returned value (§4.2), it may borrow what the function was given — its parameters, or a closure's captures and parameters — and never its locals, which may end before the item does."*
> *"The arm is the standard library's one use of `unsafe` outside foreign code: an item past its arm is beyond what §5.3 can check, but here the `handle` body is a call of the closure `f`, with no locals of its own, and every item borrows only what `f`'s functions were given, so no item can outlive what it borrows."*

Unlike a normal `return` (which happens after the function finishes and cannot borrow an owned parameter because owned parameters are not in the default sources of `§4.2`), `§5.5`'s wording says a yielded value *"may borrow what the function was given — its parameters, or a closure's captures and parameters"*. Even if you restrict generator functions to borrowed parameters (`§4.2` sources), look at what happens in two concrete programs:

**Program 1a (Closure parameter in `Gen.map` / nested generator call):**
Suppose we have a generator of owned `String`s (e.g., `lines()` or `xs.iter().cloned()`), and we chain `.map((s) => s.asStr())` (or write a closure `(s: String) => yield s.asStr()`):
```ts
function badMap(): void {
  const words: Vec<String> = Vec.from(["hello".toString(), "world".toString()]);
  // `cloned()` yields owned `String`s.
  // Inside `map`'s closure `(s: readonly String) => s.asStr()`:
  // `s` is a PARAMETER of the closure!
  // By §5.5, yielding `s.asStr()` (or returning it from `map`'s closure to `map`, which yields it)
  // borrows the closure's parameter `s`!
  // But `s` is owned by `map`'s loop variable `for (const x of self) { yield f(x); }`!
  let g = words.iter().cloned().map((s) => s.asStr());
  const first: Option<str> = g.next(); // `x` inside `map` is dropped when the next `next()` runs or `g` drops!
  const second: Option<str> = g.next();
  // `first` now points to freed memory!
}
```
Why did that happen? Look at how `Gen.map` is implemented in Flyscript:
```ts
function map<U, row E2>(self: Self, f: mut (x: readonly T) => U uses ...E2): Gen<U, ...> {
  generate(() => {
    for (const x of self) {
      yield f(x); // `x` is a local of `map`'s `for` loop!
    }
  })
}
```
Wait: if `self` yields an **owned** `T` (like `String`), then in `for (const x of self)`, `x` is a local binding of the `for` loop (or lent `readonly T` from the temporary returned by `self`). When `f(x)` returns a `str` borrowed from `x`, `f(x)`'s source is `x` — which is a **local of the `for` loop inside `map`'s closure**!
Wait: what if `for (const x of self)` in `§5.5` says:
> *"In return, a generator call's sources lend its items what they borrow, as a call's sources lend its result: in `for (const w of words(line))`, `w` borrows `line`, so `best = w` may outlive the iteration."*
Look closely at what that sentence does when `words(line)` yields an **owned `String`** vs a **borrowed `str`**!
```ts
function makeOwned(prefix: str): void uses Yield<String> {
  yield `${prefix}_1`;
  yield `${prefix}_2`;
}

export function danglingFromFor(): str {
  let kept: str = "";
  const p = "item".toString();
  // `makeOwned(p)` has source `p` (a borrowed `str` parameter).
  // It yields an OWNED `String`!
  // `for (const s of makeOwned(p))` binds `s: readonly String` (`§5.5`: "`for...of` reads: it lends the collection `readonly` and yields `readonly` elements").
  // What loan does `s: readonly String` carry?!
  // If `s` only carries the sources of `makeOwned(p)` (namely `p`), then `s` thinks it borrows `p`, NOT the anonymous per-iteration `String` yielded by `makeOwned`!
  for (const s of makeOwned(p)) {
    kept = s.asStr(); // `kept` gets loan of `p`, which outlives the loop!
    break;            // The yielded `String` is dropped at the end of the iteration!
  }
  kept // Use-after-free of the dropped `String`!
}
```
Look at `danglingFromFor()` above:
1. `makeOwned(p)` yields an owned `String` (`class 1`).
2. `§5.5` says: *"`for…of` reads: it lends the collection `readonly` and yields `readonly` elements (copies, for `Copy` types)."*
3. When a generator yields an owned `T` (`Yield<String>`), where does the `String` live during the iteration of `for (const s of makeOwned(p))`, and what loan does `s` carry?
   - If `s` is `String` (owned by the loop iteration), then `kept = s.asStr()` borrows the loop local `s`, which `§4.1` rejects at the end of the iteration (`s` dies at the end of the loop body).
   - **Wait:** why does `§5.5` say *"`for…of` reads: it lends the collection `readonly` and yields `readonly` elements"*? Because `Vec<T>.each()` has type `uses Yield<readonly T>`, whereas `makeOwned` has type `uses Yield<String>`!
   - If `for (const x of gen)` binds `x: T` (the exact type `T` in `Yield<T>`, which for `Vec<String>.each()` is already `readonly String`, and for `makeOwned` is `String`), then:
     - When `T` is `readonly String` (class 2), `x` is a class-2 borrow whose loan comes from the generator's sources (`line` or `vec`), so `kept = x` outlives the loop!
     - When `T` is `String` (class 1), `x` is an owned local of the loop body, so `kept = x.asStr()` borrows the loop local `x` and is **rejected** when the iteration ends!
   - Now check what happens if a function yields a borrow of an **owned parameter** or **by-move closure capture**:
```ts
function badGen(ownedVec: Vec<String>): void uses Yield<str> {
  // `ownedVec` is a parameter of `badGen`, passed by MOVE!
  // By §5.5 ("may borrow what the function was given — its parameters, or a closure's captures and parameters"),
  // if `ownedVec` is allowed to be borrowed by `yield`:
  yield ownedVec[0].asStr();
  // When `badGen` finishes (or `break` drops the continuation), `ownedVec` is DROPPED!
}

export function uafOwnedParam(): str {
  let kept: str = "";
  for (const s of badGen(Vec.from(["boom".toString()]))) {
    kept = s;
    break; // `badGen` unwinds and drops `ownedVec`!
  }
  kept // Dangling `str`!
}
```
And the exact same thing happens with a `once` closure in `generate`:
```ts
export function uafMovedCapture(): Gen<str, []> {
  const v = Vec.from(["boom".toString()]);
  // Escaping closure moves `v` in (§4.3) and is `once` because it drops/consumes `v`:
  return generate(() => {
    yield v[0].asStr();
  });
}
```
In both `uafOwnedParam` and `uafMovedCapture`, `ownedVec` / `v` is **owned by the generator/closure itself**, not borrowed from the caller! When the generator finishes (or `next()` returns `#Some(item)` on the last step and drops the `once` closure), `v` is dropped while the yielded `str` is still alive!

**Fix:**
In `§5.5`, a yielded value is just like a returned value in `§4.2`: it may borrow only from the function's **sources** (`§4.2`: borrowed parameters, the receiver of a borrowed `self`, or parameters that hide a borrow) and from a closure's **borrowed captures** — **never from an owned parameter, a by-move capture, or a local**.
Replace the sentence in `§5.5`:
> *"like a returned value (§4.2), it may borrow what the function was given — its parameters, or a closure's captures and parameters — and never its locals, which may end before the item does."*

with:
> *"like a returned value (§4.2), it may borrow only from its function's sources (§4.2) and its closure's borrowed captures — never from an owned parameter, a by-move capture, or a local, all of which end when the call or closure does."*

That single sentence makes `yield` and `return` obey the exact same source rules (`§4.2`), closes both `uafOwnedParam` and `uafMovedCapture`, and keeps `words(line)` and `xs.iter().filter(...).map(...)` 100% intact.

---

#### 2. `Scope` (`§6.1` rule 6) can be passed to a helper function or captured in a nested closure, bypassing the "declared inside its scope" rule

`§6.1` rule 6 states:
> *"What is declared outside the scope it may borrow `readonly`, since the scope outlives every task; what is declared inside the scope — a loop's `const tx2 = tx.clone()`, a buffer made for one task — it moves in, since the task may outlive it."*

And `§6.1` gives the signature:
```ts
function scope<T, X>(body: once (s: mut Scope<X>) => T uses Io, Fail<X>): T uses Io, Fail<X>;
```
Because `s: mut Scope<X>` is an ordinary `mut` parameter of `body`, nothing stops `body` from passing `mut s` to a helper function, or calling a closure inside `body` that declares a local and calls `s.fork`:

```ts
function spawnWithTemp(s: mut Scope<never>, msg: readonly String): void uses Io {
  // Inside `spawnWithTemp`, there is NO enclosing `Io.scope` AST node!
  // And `msg` is a parameter of `spawnWithTemp` whose referent may be a local of `Io.scope`!
  const localCopy = msg.clone();
  s.spawn(() => {
    // Is `localCopy` moved or borrowed? What about `msg` (which is a `readonly String` parameter)?
    // If `msg` is borrowed `readonly` by the task, the task outlives `spawnWithTemp`'s caller's local!
    println(msg);
  });
}

export function raceScope(): void uses Io {
  Io.scope((s) => {
    for (const i of [1, 2, 3]) {
      const temp = `task ${i}`;
      // `temp` is lent `readonly` to `spawnWithTemp` for the duration of the call `spawnWithTemp(mut s, temp)`.
      // `spawnWithTemp` returns immediately, releasing the borrow of `temp`, and `temp` is dropped at the end of the loop iteration!
      // Meanwhile the spawned task is still running with `msg` pointing to freed `temp`!
      spawnWithTemp(mut s, temp);
    }
  });
}
```
Look at what went wrong in `raceScope()`:
1. `spawnWithTemp(mut s, temp)` takes `s: mut Scope<never>` and `msg: readonly String`.
2. Because `spawnWithTemp` returns `void`, by `§4.2` (*"A result whose type cannot hold a borrow at all (class 1...) holds nothing"*), the borrow of `temp` passed as `msg` is **released as soon as `spawnWithTemp` returns**!
3. Inside `spawnWithTemp`, the task closure `() => println(msg)` captured `msg: readonly String`. Because `Scope.spawn` takes `task: once () => void uses Io` (whose parameter type is a function type, which in `§4.4` is considered class 1 unless checked for loans!), `spawn` did not tie the task's borrow of `msg` to `s`!

And why would anyone ever pass `mut Scope` to a helper function with borrowed data? Even if a helper function wants to spawn tasks, a task spawned on `s` lives as long as `s`, **not** as long as the helper call!
Look at the two ways to fix this cleanly without adding concepts:

**Fix:**
In `§6.1`:
1. In the closure passed to `Io.scope((s) => body)`, `s` is the scope handle. State in `§6.1` rule 6:
   > *"A task closure passed to `s.spawn` or `s.fork` may borrow only bindings declared outside the `Io.scope` that created `s`, and moves in anything else it captures (so a helper function taking `mut Scope` cannot lend its own parameters or locals to a task)."*
2. Even simpler and more direct in `§4.2` / `§6.1`: in a helper function (not inside `Io.scope`), nothing is "declared outside the `Io.scope` that created `s`" (except module constants), so any task created in a helper function must **move in all its captures** (and therefore cannot capture any `readonly` borrow parameter like `msg`)!
 Let's verify that!
- Inside `Io.scope((s) => { ... })`: bindings outside `Io.scope` may be borrowed `readonly`; bindings inside `Io.scope` are moved in.
- Inside a helper function `fn helper(s: mut Scope<X>, ...)`: there is no enclosing `Io.scope` lexical block for `s`, so *zero* local bindings or parameters are outside `s`'s scope; thus any task spawned in `helper` moves in all its captures and cannot capture a `readonly` borrow!
- In `raceScope()` above, `spawnWithTemp` tries to capture `msg: readonly String` in `s.spawn(...)`. Since `msg` is not declared outside `s`'s `Io.scope` (and is class 2, not an owned `Send` value), it is immediately rejected! If `spawnWithTemp` instead takes `msg: String` (owned `Send`), `s.spawn` moves `msg` into the task, which is completely sound!

---

### Question 2: Is anything else blocking 1.0 freeze?

Once Problem 1 and Problem 2 above are fixed, **nothing is blocking a 1.0 freeze.**

Here is why the rest of the 0.32–0.34 design holds together under adversarial checking:

1. **`Mutex.lock` (`§6.2`) cannot deadlock, period:**
   - Could a fiber lock `m1` and inside the closure lock `m2` (classic AB-BA deadlock)? **No**, because `Mutex.lock` has `uses Io`, and `lock`'s closure `body: once (v: mut T) => R` is **pure** (`uses []`)! Therefore, a fiber holding `m1` cannot call `m2.lock(...)`, cannot send/receive on a channel, cannot `join` a fiber, and cannot call `Io.park`.
   - Could a fiber lock `m1` recursively (`m1.lock(() => m1.lock(...))`)? **No**, for the same reason (`uses []`).
   - Could `body` stash `v: mut T` somewhere? **No**, because `R extends Send` (class 1) and `body` is pure and cannot mutate any external state (any outer capture would require a `mut` capture, which is fine for a `once` closure, and by `§4.2` *"No borrow is stored through a borrow"* and a class-1 local cannot store `v: mut T`).Wait — what if an outer local is `let stolen: Option<mut T> = #None;` (a class-2 local outside `m.lock`) and `body` assigns `stolen = #Some(v);`?!
   **WAIT A SECOND! Check that!**
   Let's write a program right now to test if `m.lock`'s `once` closure can assign `v: mut T` to an outer class-2 local variable!

```ts
import { Mutex } from "std/sync";

export function stealMutexGuard(m: readonly Mutex<Vec<i32>>): void uses Io {
  let dummy = Vec.new<i32>();
  let stolen: mut Vec<i32> = mut dummy; // a local class-2 binding in the enclosing function!
  m.lock((v) => {
    // `body` is `once (v: mut T) => R` (no effects, so pure!).
    // What if `body` captures `stolen` by `mut` and reassigns `stolen = v`?!
    // Look at §4.2: "No borrow is stored through a borrow. A `mut` borrow of a view may change its class-1 parts (`sc.pos += 1`) but cannot have a class-2 value written into it: a function that wrote its argument's borrow into a caller's `mut Option<mut T>` would keep that borrow alive after the call had released it."
    stolen = v;
  });
  // If `stolen = v` were allowed inside the closure, `stolen` would point into `m` after `m.lock` unlocked!
}
```
Let's check what `§4.2` and `§4.3` do to `stealMutexGuard`:
- Inside `m.lock((v) => { stolen = v; })`, `stolen` is captured by `mut` borrow by the closure (`§4.3`: *"A closure captures each binding as its body needs it, by reference: a read takes a `readonly` borrow, a change a `mut` borrow"*).
- Because the closure captures `stolen` by `mut` borrow, writing `v` (which is class 2, `mut Vec<i32>`) into the captured `stolen` is **storing a class-2 value through a `mut` borrow**, which `§4.2` explicitly forbids (*"No borrow is stored through a borrow. A `mut` borrow of a view may change its class-1 parts (`sc.pos += 1`) but cannot have a class-2 value written into it"*), **AND** `v` is a parameter of the closure, not a source of a return value!
- Make sure `flyc`'s ownership pass applies the *"no class-2 store through a `mut` borrow"* rule to `mut`-captured outer variables (`stolen = v` inside a closure) just as it does to `mut` parameters! (If `flyc` treats `stolen = v` inside a closure as a direct local reassignment rather than a write through a `mut` capture, `stealMutexGuard` would slip through — add `stealMutexGuard` as a reject test in `tests/reject/`.)

---

### Question 3: Weakest part now, and the single most valuable change

**Weakest part now:**
**Collection ergonomics for slice/array/Vec literals and `HashMap` initialization.**
Right now:
- `[1, 2, 3]` builds an inline array `i32[3]`, a tuple, or a borrowed slice `readonly i32[]` (`§2.2`), **never a `Vec<T>`**, and Appendix A doesn't even have a single clean way to write a `Vec` or `HashMap` literal.
- In `§4.1`, indexing `xs[i]` works on arrays, slices, and `Vec`, and slicing `xs[a..b]` works on arrays, slices, `Vec`, and `str`. That's hardcoded in `§3.1` for those four types; user collections (`Ring`, `Pool`, `Soa`, `Matrix`) cannot support `c[i]`. (That is acceptable for 1.0 given Goal 5, a small core.)
- More immediately noticeable to a TypeScript programmer: in `§0.1`, you added `sort`, `sortBy`, `reverse`, `join`, `includes`, `indexOf`, `last`, `pop`, `find`, `some`, `every`, `reduce`, `cloned`, and `drain` — **but none of these methods appear in the body of the specification (`§3.1` or `§5.5`), only in the `§0.1` changelog table and `§2.1` summary table!** Once `§0.1` is removed or rolled forward, those methods vanish from the spec text.

**The single most valuable change:**
1. **Fix the two soundness rules in `§5.5` (yield sources) and `§6.1` (scope helper captures) and verify `stealMutexGuard` is rejected.**
2. **Fold the `0.33`–`0.34` standard library additions (`drain`, `find`, `some`, `every`, `reduce`, `cloned`, `sort`, `sortBy`, `join`, and `Arc<T>` lending `readonly T`) from `§0.1` into `§3.1`, `§4.1`, and `§5.5`** so the normative spec sections are self-contained without relying on the changelog table.

---

### Smaller points

1. **`Arc<T>` lending `readonly T` missing from `§4.1`:**
   `§0.1` says *"`Arc<T>` lends `readonly T` (§6.2)"*, but `§4.1` (**Lending**) says:
   > *"`String` lends `str`, `Vec<T>` lends `T[]`, `Box<T>` lends `T`, and `Ref<R, T>` lends `readonly T`"*
   Add `Arc<T>` alongside `Ref<R, T>` in `§4.1`: *"`Ref<R, T>` and `Arc<T>` lend `readonly T`"*.
2. **Trailing separator in `§0.1` table:**
   `§0.1` has four `--- | :--- |` markdown table breaks separating the 0.34, 0.33, 0.32, 0.31, 0.30, and 0.29 rows, which renders as literal `---` cells in Markdown parsers. Clean up the table dividers when freezing 1.0.
