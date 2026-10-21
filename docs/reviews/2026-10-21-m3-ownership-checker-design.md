# Review: m3 ownership checker design

- spec: 70400abd40ea
- request: c020d97d10e52d83
- tokens: prompt 26283, cached 0, answer 6823

## Question

Milestone 2 (the type and effect checker) is done: all nine spec programs check, and 19 incorrect programs are rejected with the intended errors. Milestone 3 is the **ownership checker**: §4.1–§4.4 and the ownership parts of §5–§6. Below is the plan. I want you to find where it is unsound or rejects reasonable programs, with a concrete Flyscript program for each problem.

**Architecture.** A separate pass after type inference, over each function body, using the final (zonked) type of every expression and binding recorded by the type checker. The type checker currently treats borrows as transparent and accepts copying out of a borrow; the ownership pass is what rejects the unsound cases.

**1. Moves.** A binding whose type is not `Copy` is moved when it is passed by value, assigned, returned, stored in a record or tag, or captured by a `once` closure. Using a moved binding is an error. A move in one branch of `if`/`match` makes the binding moved after the join ("maybe moved" is moved). A move inside a loop body of a binding declared outside the loop is an error. Moving out of a field (`x.f`) moves just that path; the parent is then partially moved and cannot be used whole, as in Rust. Moving out of a borrow (`readonly T` or `mut T` with `T` not `Copy`, or through a `Ref`) is an error.

**2. Borrows: "NLL-lite", borrows tied to bindings.** A borrow is created by passing a place where `readonly T`/`mut T` is expected (implicitly for `readonly`, with `mut e` for `mut`), by a method receiver, by a transparent field access through a borrow, or by indexing a slice by a range. A borrow created for a call argument ends when the call returns, **unless** the call returns a class-2 value tied to that argument (§4.2 tied returns): then the borrow is transferred to the class-2 result, and if the result is bound to a local, it lives until that local's last use (computed by a backwards pass over the block; a use inside a loop extends the borrow to the end of the loop). A class-2 value stored in a record or tag carries all the borrows of its components (second-classness propagates, so borrow sets propagate too).

**3. Exclusivity.** Places are paths (`local.field.field`; any index makes the path the whole array/slice). While a `mut` borrow of path P is live: no read, write, move or borrow of P, of any prefix of P, or of any extension of P. While a `readonly` borrow of P is live: no write, move or `mut` borrow of P, its prefixes or extensions. Two-phase receiver borrows are allowed (`v.push(v.len())`): the receiver's `mut` borrow is activated only after the other arguments are evaluated.

**4. Mutability.** `const` bindings cannot be assigned, mutated through fields, or lent `mut`; `let` bindings and parameters (§2.2) can.

**5. Class (§4.2).** Class is computed from types. A class-2 value may not be: stored into a class-1 place; returned without a tie (`from param`, or the unique class-2 parameter); captured by a closure that escapes (a closure capturing class-2 values is class 2); sent to another task. At a function definition, the returned class-2 value's borrows must all derive from the tied parameter (checked with the same borrow sets as in point 2: the result's borrow set must be a subset of the borrows held by the tied parameter).

**6. Closures.** A closure's mode (`shared`, `mut`, `once`) is inferred from captures: capturing a `mut` borrow or mutating a captured `let` binding makes it `mut`; moving a captured owned value makes it `once`. The closure holds borrows of its captures for as long as the closure binding is live (same last-use rule). A closure passed where `(A) => B` is expected must be `shared`; where `mut (A) => B` is expected, `shared` or `mut`.

**7. Generators and loops.** In `for (const x of e) { body }`, all borrows taken to evaluate `e` (including those captured by the generator, e.g. `self.names` in A.5, or `v.each()`) stay live until the loop ends, so the body cannot mutate what is being iterated: `for (const x of v) { v.push(x) }` is rejected.

**8. Handlers.** In a `try`/`catch` or abortive arm, borrows taken inside the body are released before the arm runs (§5.2), so the arm may use `conn` that the body lent `mut`. In a resumptive arm, the body's borrows remain live while `k` is live.

**9. Tasks (§6.1).** A `spawn`/`fork` task's captures must be `Send` owned values (moved in) or `readonly` borrows of `Send` values; a captured `Ref<R, T>` is `Send` only if `T` contains no `Cell`/`RegionList`.

**10. Copy and Send.** Derived structurally (§4.4). Moving a value out of a `Copy` place copies.

Questions:
(a) Is "borrows tied to bindings with last-use liveness" sound for class-2 values that flow through tags and records (e.g. `const r = #Some(v.getMut(k))` and then `match (r) { #Some(n) => n += 1 }` while `v` is used elsewhere)? Where does it fail compared with Rust's NLL?
(b) What breaks with transparent borrows: is there any place where reading a `readonly T` binding of a non-`Copy` `T` *should* be a copy, or where a binding of type `mut T` passed as a `mut T` argument must be a reborrow rather than a move of the borrow?
(c) Generators that hold borrows across `yield` (§5.3 says a `Cont` is class 2 when its frame holds class-2 values): is point 7 sufficient, or can a `Gen` stored in a local outlive the loop and keep a borrow alive past its last use?
(d) Anything in §4–§6 that this plan leaves unchecked and that is needed for memory safety or data-race freedom.

## Answer

### Verdicts

- **Decision 1 (Moves)**: **Agree with changes.** Needs a loop fixpoint for moves (a move on iteration 1 can be read on iteration 2 of a `while` loop even for bindings declared or reassigned inside the loop), and must forbid moving out of a type that implements `Drop` (`§4.4`).
- **Decision 2 & Question (a) (Borrows tied to bindings with last-use liveness)**: **Disagree as stated; agree with changes.** Binding-level last-use liveness is sound *only* if (1) pattern matching and field projection propagate the scrutinee's borrow set to the bound pattern variables, (2) reassigning a `let` binding unions or kills-and-replaces borrow sets along all control-flow paths, and (3) returning a borrow or breaking/throwing does not end the borrow before destructors/`defer`s in the enclosing scope run.
- **Decision 3 & Question (b) (Exclusivity and reborrowing)**: **Agree with changes.** `mut T` is not `Copy`; passing `x: mut T` to a call expecting `mut T` (such as `value(mut sc)` in `A.1`) *must* be a reborrow that suspends `x` for the duration of the call (or transfers to the tied result), not a move that kills `x` and not a `Copy` that aliases `x`.
- **Decision 4 & 5 (Mutability and Class)**: **Agree with changes.** The class of `Cont<A, B, E>` and `Gen<T, E>` cannot be computed purely from their surface type arguments `(A, B, E)` because captured borrows in a suspended frame or closure do not appear in the type arguments (`§5.3`, `§5.5`, `A.3`).
- **Decision 6, 7, 8 & Question (c) (Closures, Generators, Handlers)**: **Disagree on Question (c).** Point 7 only covers `for…of`; pull iteration via `generate(f)` (`§5.5`, `A.3`) and user `handle` expressions (`§5.2`) create `Cont`/`Gen` values whose types hide the borrows they hold.
- **Decision 9, 10 & Question (d) (Tasks, Regions, `Send`/`Copy`)**: **Agree with changes.** Missing three critical soundness checks from `§4.6` and `§9`: (1) the region data restriction (no owned resources like `String`/`Vec` inside `alloc`), (2) the region non-escape check, and (3) `defer` / `Drop` interactions with live borrows.

---

### Problems

#### 1. Question (b): Passing `mut T` must *reborrow*, neither move nor copy (`§4.1`, `A.1`)

In `A.1`:
```ts
function value<region R>(sc: mut Scanner): Ref<Json> uses Region<R>, Fail<JsonErr> {
  ...
  while (!sc.eat(b']')) {
    items.push(value(mut sc)); // sc is passed as `mut Scanner`, then used again!
    sc.eat(b',');
  }
  ...
}
```
Here `sc` is a parameter of type `mut Scanner`. Inside the `while` loop, `value(mut sc)` passes `sc` by mutable borrow, and on the very next line `sc.eat(b',')` uses `sc` again.
- If `mut Scanner` were `Copy`, then `const a = sc; const b = sc;` would create two live `mut Scanner` bindings aliasing the same memory — unsound (`§4.1`). So `mut T` is **not** `Copy` (whereas `readonly T`, `str`, and `readonly T[]` *are* `Copy`).
- If `mut Scanner` were moved by `value(mut sc)`, then `sc.eat(b',')` and the next iteration of the `while` loop would fail with a use-after-move error, rejecting `A.1`!

And if you allow reborrowing `x: mut T` when passed to a function, consider when that function returns a tied borrow:
```ts
function id(x: mut i32): mut i32 { x }

function bug(p: mut i32): void {
  const q = id(mut p); // q reborrows from p
  p += 1;              // ERROR: must be rejected while q is live!
  q += 1;
}
```
**Fix:**
1. `readonly T`, `str`, and `readonly T[]` are `Copy` (and class 2). `mut T` and `mut T[]` are **not** `Copy` (they are affine and class 2).
2. Passing a binding `p: mut T` as a `mut U` argument (or receiver) **reborrows** `p`: it creates a new borrow of path `p` (not just the original caller's path), locking `p` until that temporary borrow (or any class-2 value tied to it, like `q` above) dies. When `q` dies, `p` becomes usable again.
3. Moving `p: mut T` into a new binding (`const q = p;`) moves `p` (killing `p` and transferring `p`'s borrow set to `q`).

---

#### 2. Question (a): Pattern bindings and `let` reassignment break naive "last-use of binding" liveness (`§4.1`, `A.2`)

Look at `A.2` (`§4.1`):
```ts
match (counts.getMut(word)) {
  #Some(n) => { n += 1; },               // n: mut u64
  #None    => { counts.insert(word.toString(), 1); },
}
```
And consider the variation in your question (a):
```ts
function leakBorrow(counts: mut HashMap<String, u64>, w: str): void {
  const opt = counts.getMut(w);          // opt: Option<mut u64>, borrows `counts`
  match (opt) {
    #Some(n) => {
      // `opt`'s last syntactic mention was the match head above!
      // If `counts`'s borrow ended at `opt`'s last use, `counts` would be unlocked here!
      counts.clear();                    // UNSOUND: frees bucket while `n: mut u64` points into it!
      n += 1;                            // use-after-free!
    },
    #None => {},
  }
}
```
Or with `let` reassignment:
```ts
function reassignBorrow(mut a: Vec<i32>, mut b: Vec<i32>, c: bool): void {
  let s: readonly i32[] = a[0..1];       // s borrows `a`
  if (c) {
    s = b[0..1];                         // s now borrows `b` (or `a` if !c)
  }
  a.push(1);                             // UNSOUND if !c: `s` still borrows `a`!
  println(`${s[0]}`);                    // last use of `s`
}
```
**Why it goes wrong:**
In `leakBorrow`, the lexical last use of `opt` is the `match (opt)` header. Once `opt` is destructured into `#Some(n)`, `opt` is never mentioned again — `n` is!
In `reassignBorrow`, `s` is reassigned on one branch, so at `println`, `s` may hold a borrow of `a` or `b`.

**Fix (how to make NLL-lite sound without full Polonius):**
Associate every binding `x` with a static **BorrowSet** `B(x)` (a set of borrowed place paths and modes `(Path, Mode)`):
1. When `x` is initialized or assigned from `e`, `B(x) = B(x) ∪ borrows(e)` (accumulating monotonically across assignments and branches is 100% sound and trivial to implement, and only loses precision if a single `let` variable is reused for unrelated borrows sequentially).
2. In `match (scrut) { Pat => body }` and `const Pat = e;` and `for (const Pat of e)`, every variable `v` bound in `Pat` whose type is class 2 inherits `B(v) = borrows(scrut)`! Thus in `leakBorrow`, `B(n) = B(opt) = {(counts, mut)}`, so `n`'s liveness at `n += 1` keeps `(counts, mut)` live across `counts.clear()`.
3. A borrow `(P, mode)` is live at program point `L` iff either (i) it is created by a temporary expression enclosing `L`, or (ii) there exists some binding `x` such that `(P, mode) ∈ B(x)` and `x` is live at `L` (computed by standard backward dataflow liveness over the CFG, where a loop creates a back-edge).

---

#### 3. Question (c): `Gen<T, E>` and `Cont<A, B, E>` hide class-2 borrows in their state (`§5.3`, `§5.5`, `A.3`)

Look at `§5.5` and `A.3`:
```ts
export struct Gen<T, row E> { state: Option<Cont<void, Step<T, E>, E>>; }

export function dot(xs: readonly f64[], ys: readonly f64[]): f64 {
  let total = 0.0;
  for (const [x, y] of zip(() => xs.each(), () => ys.each())) { total += x * y; }
  total
}
```
Inside `zip`:
```ts
let ga = generate(a); // `a` is `() => xs.each()`, which captures `xs: readonly f64[]` (class 2!)
```
What is the type of `ga`? `Gen<f64, []>`!
Look at the type arguments of `Gen<f64, []>`: `T = f64` (class 1), `E = []` (class 1).
By Decision 5 (*"Class is computed from types"*), `Gen<f64, []>` and `Cont<void, Step<f64, []>, []>` look like **class 1** types because `f64` and `void` are class 1!
Even though `§5.3` says:
> *"A `Cont` is class 2 when the suspended computation holds a class-2 value, so a continuation can never outlive a borrow it holds."*

Here is the concrete program that breaks both class checking and borrow liveness under your plan:
```ts
import { generate, Gen } from "std/iter";

function danglingGen(): Gen<i32, []> {
  let v = Vec.new<i32>();
  v.push(42);
  // () => v.each() borrows `v` (class 2).
  // But `generate` returns `Gen<i32, []>`, whose type arguments `i32` and `[]` are class 1!
  return generate(() => v.each()); // UNSOUND: returns a generator holding a borrow of `v`!
}

function mutateWhileIterating(): void {
  let v = Vec.new<i32>();
  v.push(1);
  let g = generate(() => v.each()); // `g: Gen<i32, []>` holds a borrow of `v`
  v.push(2);                        // UNSOUND: reallocates `v` while `g` is suspended inside `v.each()`!
  const x = g.next();               // use-after-free!
}
```
And the exact same bug happens with `handle` (`§5.2`):
```ts
effect Ask { ask(): void; }

function mutateSuspended(): void {
  let v = Vec.new<i32>();
  v.push(1);
  const kOpt = handle {
    const slice: readonly i32[] = v[0..1]; // borrows `v`
    Ask.ask();                             // suspends with `slice` on stack!
    println(`${slice[0]}`);
    #None
  } with Ask {
    ask() resumes k => #Some(k)            // k: Cont<void, Option<...>, []> — type args don't show `slice`!
  };
  v.push(2);                               // UNSOUND: reallocates `v` while `k` holds `slice`!
  match (kOpt) { #Some(k) => { k.resume(); }, #None => {} }
}
```
**Why it goes wrong:**
1. A `Cont<A, B, E>` (and therefore `Gen<T, E>`) does not reflect in its type parameters `A, B, E` whether the suspended computation captured a class-2 borrow, or *which* local variable (`v`) it borrowed!
2. In `generate(f)`, `f` is a closure `() => v.each()`. When `f` is passed into `generate(f)`, if `generate`'s return type `Gen<i32, []>` appears class-1 to Decision 2 & 5, the checker thinks `generate` does **not** return a class-2 value, so:
   - In `mutateWhileIterating`, the borrow of `v` inside `() => v.each()` ends as soon as `generate(...)` returns! `B(g)` is empty!
   - In `danglingGen`, `Gen<i32, []>` is treated as class 1 and allowed to be returned untied!

**Fix:**
You do **not** need to change the surface language syntax:
1. In the ownership pass, a value's effective class is `2` if its structural type is class 2 **or** its `BorrowSet` is non-empty **or** it is a `Cont`/`Gen` created from a closure/handle-body that captures or holds any class-2 value.
2. In `handle { body } with Eff { op(...) resumes k => arm }`:
   - `B(k)` (the borrow set of `k`) includes all borrows held by `body` (every outer local borrowed anywhere inside `body`), and if `body` uses any class-2 value from outside `handle`, mark `k` as class 2.
3. For calls like `generate(f)`: when a function takes a closure parameter `f` (which may capture class-2 borrows) and returns a `Gen` or `Cont` (or any type containing `Cont`), treat the return value as **tied to `f`**: `B(result) = B(f)`, and if `f` is class 2 (captures borrows), `result` is class 2!
   Check what that does to `A.3` (`zip(a, b)`): inside `zip`, `a` and `b` are closure parameters. `let ga = generate(a)` ties `ga` to `a`. `zip` consumes `ga` and returns `void` (not `ga`). In `dot`, `zip(() => xs.each(), () => ys.each())` borrows `xs` and `ys` for the duration of the `for` loop. And in `mutateWhileIterating` and `danglingGen`, `g` has `B(g) = {(v, ro)}` and class 2, so `v.push(2)` while `g` is live and `return generate(...)` are both caught and rejected!

---

#### 4. Question (d): Unchecked `defer` and `Drop` can violate borrow exclusivity or read moved bindings (`§4.1`, `§5.6`)

`§5.6` says:
> "`defer e;` schedules `e` to run when the enclosing block exits. `defer`s and the destructors of the block's owned locals share one stack and run in reverse order of the points at which they were registered..."

Your plan mentions neither `defer` nor `Drop`. Three concrete unsound programs result:

**Program 4a (`defer` mutates or moves a binding that is later borrowed or moved in the block):**
```ts
function badDefer(): void {
  let v = Vec.new<i32>();
  v.push(1);
  defer v.clear();              // registered to mutate `v` at block exit
  const s: readonly i32[] = v;  // borrows `v`
  drop(v);                      // or move `v`! When block exits, `defer v.clear()` runs on moved `v`!
}
```
**Program 4b (Moving out of a struct that implements `Drop`, `§4.4`):**
```ts
struct Guard { data: String; }
impl Drop for Guard {
  function drop(self: mut Self): void { println(self.data); }
}
function partialMoveDrop(g: Guard): void {
  const s = g.data; // moves `g.data` out of `g`!
  // At end of scope, `Guard.drop` runs on `g` and reads moved `g.data` — use-after-free!
}
```
**Program 4c (Returning a tied borrow while a `defer` in the function mutates the borrowed parameter):**
```ts
function returnDuringDefer(v: mut Vec<i32>): readonly i32[] {
  defer v.clear();  // runs when function exits — AFTER return expression is evaluated!
  return v[0..1];   // UNSOUND: caller receives dangling slice into cleared vector!
}
```
**Fix:**
1. **`defer e;` acts as a closure captured at registration and executed at every exit of the enclosing block:**
   - Any binding moved inside `defer e;` cannot be used anywhere after the `defer` statement, and `defer` cannot appear inside a loop if it moves an outer binding.
   - Any binding borrowed (`ro` or `mut`) by `defer e;` has that borrow kept **live until the end of the enclosing block** (including across `return`!). In `Program 4a`, `defer v.clear()` holds a `mut` borrow of `v` until the block exits, so neither `const s = v` nor `drop(v)` is allowed. In `Program 4c`, the `mut` borrow of `v` from `defer` is still live at `return v[0..1]`, rejecting the `ro` borrow!
2. **No partial moves out of `Drop` types:** If a `struct` implements `Drop`, moving a non-`Copy` field `x.f` out of `x` is forbidden.

---

#### 5. Question (d): Missing Region soundness checks (`§4.6`, `§9`)

Milestone 1's review noted that **region non-escape** and the **region data restriction** belong to Milestone 3 (or the boundary of M2/M3). They are not in your 10 points, and omitting them breaks memory safety without `unsafe`:

**Program 5a (Region escape via outer `let` assignment or closure, `§4.6` Rule 1):**
```ts
function escapeRegion(): void {
  let leaked: i32 = 0;
  region (R1) {
    let outerRef = alloc<R1, i32>(1);
    region (R2) {
      outerRef = alloc<R2, i32>(2); // UNSOUND if R1 and R2 unify or if outerRef escapes R2!
    }
    leaked = outerRef; // use-after-free after R2 exited!
  }
}
```
**Program 5b (Owned heap resource inside a region leaks or double-drops, `§4.6` Rule 2):**
```ts
struct Bad { s: String; }

function allocOwnedInRegion(): void {
  region (R) {
    const r = alloc(Bad { s: "hello".toString() });
    // `r` is `Ref<R, Bad>`, which lends `readonly Bad`.
    // Region release is constant-time bump reset and runs NO destructors (§4.6 Rule 2).
    // Even worse, if `Ref<R, T>` is Copy and `Bad` were ever copied or lent, `String` is unowned.
  }
}
```
**Program 5c (Capturing outer `Region<R>` effect inside `s.spawn` / `s.fork`, `§6.1` Rule 4 & `§9`):**
`§4.6` says: *"A region is a fiber-local bump arena... Because handlers are fiber-local, no other task can perform `Region<R>`."*
And `§9` (Scope) says: *"a forked task's row is `Io` and the scope's row, less every `Region` label."*
```ts
function raceRegionArena(): void uses Io {
  region (R) {
    const list = RegionList.new<R, i32>();
    Io.scope((s) => {
      // In §6.1, `s.fork` shares the scope's effect row `...E`.
      // If `...E` is allowed to contain `Region<R>`, two fibers bump-allocate and push concurrently!
      const f1 = s.fork(() => list.push(1));
      const f2 = s.fork(() => list.push(2));
      f1.join();
      f2.join();
    });
  }
}
```
Look closely at `Program 5c`!
1. `list` has type `Ref<R, RegionList<R, i32>>`. By Point 9 (`§4.4`), `list` is **not `Send`** because it contains a `RegionList`. So capturing `list` in `s.fork` will be caught by Point 9.
2. **Wait**: what if the forked task doesn't capture `list`, and just calls `alloc<R, i32>(42)` directly inside `s.fork`?!
```ts
function raceRegionAlloc(): void uses Io {
  region (R) {
    Io.scope((s) => {
      // Captures NOTHING! Only performs the effect `Region<R>`!
      const f1 = s.fork(() => { const x = alloc<R, i32>(1); });
      const f2 = s.fork(() => { const y = alloc<R, i32>(2); });
      f1.join();
      f2.join();
    });
  }
}
```
In `raceRegionAlloc`, the closures capture **zero variables** (so Point 9's `Send` check on captures passes trivially!), and `Region<R>` flows through `Io.scope`'s `...E` into both `s.fork` tasks, causing two concurrent threads to bump-allocate in the unsynchronized fiber-local arena `R` at the same time!

**Fix:**
Include all three region checks in Milestone 3 (each is ~15 lines):
1. **No escape (`§4.6` Rule 1, `§9`):** For `region (R) { body }`, verify that the region variable `R` does not occur anywhere in:
   - the type of the `region` expression itself,
   - the remaining unhandled effect row of `body`,
   - the type of any local variable declared *outside* the `region (R)` block (which prevents `outerRef = alloc<R2>(...)` in `Program 5a` from unifying `R2` with an outer variable's type!).
2. **Region data well-formedness (`§4.6` Rule 2):** At every `alloc<R, T>(v)` (and `RegionList<R, T>`), check that `T` is a valid region type: recursively composed only of `Copy` types, `Ref<R, ...>`, `Cell<R, ...>`, and `RegionList<R, ...>` of the *same* region `R`.
3. **No outer `Region<R>` in tasks (`§6.1` Rule 4, `§9`):** In `s.fork(task)` (and `Io.scope`), reject if the task's effect row `...E` contains `Region<R>` for any outer region `R`.

---

#### 6. Decision 1: Loop moves of bindings reassigned inside a loop (`§4.1`)

Decision 1 says:
> *"A move inside a loop body of a binding declared outside the loop is an error."*

That rule is both **too weak** (unsound when a binding is moved and then read before being reassigned, or reassigned conditionally) and **too strong** (rejects moving an outer binding and then reassigning it before the end of the loop body):
```ts
// Case A: UNSOUND even if `x` is declared inside the loop? No, if `x` is declared outside,
// what if a field is moved or `x` is conditionally reassigned?
function loopCondMove( cond: bool): void {
  let s = "hello".toString();
  while (cond) {
    if (cond) {
      drop(s); // moves `s`
    }
    // On iteration 2, if the first iteration took the `if` branch, `s` is moved!
  }
}

// Case B: Legal program rejected by "any move of an outer binding in a loop is an error":
function loopReinit( mut n: i32): void {
  let s = "init".toString();
  while (n > 0) {
    consume(s);              // moves `s`
    s = "next".toString();   // reinitializes `s`! Live again at loop back-edge!
    n -= 1;
  }
  consume(s);
}
```
Wait: can a `let` binding be reinitialized after being moved?
In `§9`: *"Θ is the ownership context: each owned binding is live or moved. Θ′ is the context after e."*
If `let x` can be reassigned after a move (which brings `x` back to `live` in Θ), then `loopReinit` is valid because `Θ` at the end of the loop body has `s: live`. Conversely, if `s` is `moved` at the end of the loop body (`Θ_end(s) = moved`), then at the loop back-edge it flows to the top of the loop body where `s` is read!
**Fix:** Instead of a syntactic check "was `x` declared outside the loop", just run your move analysis `Θ` over the loop body:
1. Require that for every binding `x` that is `live` on entry to the loop (`Θ_in`) and **used** (read, moved, or borrowed) inside the loop body before being definitely assigned, `x` must still be `live` in `Θ_body_end` (and on every `continue` path)!
2. On `break` paths, `Θ` joins with the loop-exit state.

---

### Smaller points

- **Two-phase borrows (`Decision 3`) must reject mutating arguments:**
  Allowing `v.push(v.len())` by delaying activation of the receiver's `mut` borrow until arguments are evaluated is fine *provided* while the receiver `v` has a pending two-phase `mut` borrow, `v` may only be borrowed **`readonly`** during argument evaluation — never `mut` borrowed or mutated (`v.push({ v.clear(); 1 })` must still be rejected!). To do this simply: record a `ro` borrow of the receiver `v` before evaluating arguments, and upgrade it to `mut` (checking that no `ro` borrow of `v` was captured into a class-2 argument) right before the call executes.
- **Lending a `const` binding (`Decision 4`, `A.1`):**
  In `A.1`: `const items = RegionList.new(); items.push(value(mut sc));`. `items` is a `const` binding of type `Ref<R, RegionList<R, Ref<R, Json<R>>>>`, and `RegionList.push` takes `self: Ref<R, Self>` (or `readonly Self`). Make sure Decision 4 only forbids `mut` borrows on `const` bindings, not `Ref<R, Self>` or `readonly Self` receivers.
- **Closure mode inference when calling a `mut` or `once` closure inside a closure (`Decision 6`):**
  If an outer closure `f` captures a `mut` closure `g: mut () => void` or a `once` closure `h: once () => void` and calls it, `f` itself must be inferred as `mut` (respectively `once`), even though `g` is not a "`mut` borrow" type (`mut T`). Ensure your mode check treats capturing and calling a `mut (...) => ...` binding as requiring `mut` access to that binding (hence making the outer closure `mut`), and calling a `once (...) => ...` binding as moving it (hence making the outer closure `once`).
- **Tied return checking with zero or multiple class-2 parameters (`Decision 5`, `§4.2`):**
  When checking a function body against its signature:
  - If the return type is class 2 and there is 1 class-2 parameter `p` (or an explicit `from p`), every borrow in the returned expression's `BorrowSet` must originate from `p` (not from a local owned variable declared inside the function!).
  - Also check the converse: if a function's return type is class 1 (or `from a`), the returned value's `BorrowSet` must not contain any borrow of a local variable or of parameter `b` (which could happen if a `Cont` or `Gen` holding a borrow of a local or of `b` is returned!).
