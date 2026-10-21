# Review: holistic review of 0.18

- spec: a4b64b929b32
- request: 0fa3ae38991d1727
- tokens: prompt 34479, cached 0, answer 12273

## Question

Step back from individual decisions. The specification is now 0.18, and a prototype compiler implements most of it: a parser for the whole grammar; a type and effect checker (one row unifier for records and tag unions, effect rows checked by set subsumption, bidirectional inference, region inference that places an undetermined allocation in the innermost region it does not escape from); and an ownership checker (loans carried by values through calls, patterns, assignments and closure captures; liveness by reachability over the program's structure; reborrowing; two-phase receivers; external loans for borrow-typed parameters). All nine spec programs and ten more check; 34 incorrect programs are rejected with the intended errors. An evaluator with handlers and one-shot continuations is next.

The goal is a **high-quality language**: a small, beautiful core; TypeScript programmers productive on day one; memory and data-race safety without lifetime annotations; effects that replace async/await, exceptions and generators.

Please give a holistic review:

1. **Is this a high-quality language design?** Judge it against Rust, Swift, Koka, OCaml 5, Hylo and TypeScript. What is genuinely better, what is worse, and is the trade worth it?
2. **The five weakest points**, ranked: places where the design is unsound, incoherent, needlessly complex, or will frustrate the programmers it targets. For each, a concrete program and a concrete fix that removes complexity rather than adding it.
3. **Learnability.** Walk through what a TypeScript programmer must unlearn or learn, in order. Which concept will cause the most confusion (second-class values? regions? effect rows? `mut` at call sites?), and how should the spec or the language reduce it?
4. **What is missing** that a real program of 10,000 lines would need within its first week (e.g. traits with generic methods, closures stored in structs, iteration adaptors, string formatting, error context, modules with private fields), and whether the core as it stands can express it as a library.
5. **Anything in §0–§9 you would cut.**

## Answer

### Verdicts

- **Question 1 (Overall Design Quality)**: **Agree.** The core thesis works: Law 2 (mutation through shared references is an effect) eliminates the need for Rust's `Sync`, and Law 1 (second-class borrows + regions) eliminates lifetime annotations while keeping unboxed, GC-free performance.
- **Question 2 (Five Weakest Points)**: **Agree with changes.** Five concrete flaws remain in v0.18: two are **soundness holes** (re-entrant effect handlers aliasing `mut` borrows, and `Cell<R, Ref<R, T>>` violating `Send`), and three are **ergonomic/expressiveness traps** (over-approximate call-result loan propagation, `Fail` open-union composition losing error provenance, and `Iterable` hiding `Yield`'s resume type).
- **Question 3 (Learnability)**: **Agree with changes.** The hardest wall for a TypeScript programmer is not `mut` at call sites or effect rows; it is **the cliff between second-class borrows (`str`, `T[]`) and first-class data (`String`, `Ref<R, str>`)** when building structs, combined with `Ref<T>` leaking into region code.
- **Question 4 (Missing for a 10,000-line program)**: **Agree with changes.** Several day-one needs cannot currently be written as libraries because of small gaps in the core (lack of error mapping/context without catching all errors, lack of iterator combinators over `Iterable`, lack of closure-in-struct ergonomics, and module-level constants).
- **Question 5 (What to cut)**: **Agree.** Three features in `§2–§8` can be cut or unified into existing mechanisms to shrink the language.

---

### 1. Holistic Judgment: Flyscript vs. the Field

| Peer | Where Flyscript is genuinely better | Where Flyscript is worse | Is the trade worth it? |
| :--- | :--- | :--- | :--- |
| **Rust** | No `'a` lifetime viral annotations; no `async`/`Pin`/`Future` coloring; error sets compose by tag union without `From`/`thiserror` boilerplate; cyclic graphs in regions (`A.5`) without `Rc<RefCell>` or unsafe; deterministic `SimIo` testing for free. | Cannot store a borrow in a heap container (`Vec<Scanner>`) or return borrows from two different parameters dynamically (`preferA ? a : b` without picking one in the signature); stackful fibers have higher per-task memory baseline than state-machine futures. | **Yes.** 90% of Rust's ceremony comes from `'a` and `Pin`/`Future`. Trading away first-class stored borrows and state-machine futures for regions and stackful effects is a huge net win. |
| **Koka / OCaml 5** | Unboxed structs/arrays, no GC pauses or RC barriers; compile-time data-race freedom (`Send` + pure `readonly`); `mut` borrows without heap refcells. | One-shot continuations only; second-class borrow restrictions on closures and continuations. | **Yes.** Koka and OCaml 5 pay for pervasive heap allocation on every closure/ADT. |
| **Swift / Hylo** | Much richer control flow (effects, generators, stackful tasks, regions) and structural rows (`{...R}`, `#Tag | ...R`), which Hylo lacks. | Hylo's `inout` projection (`subscript`) avoids returning `mut T` values altogether, whereas Flyscript tracks loan sets on class-2 values. | **Yes**, provided you fix Weak Point #2 below. |
| **TypeScript** | Ahead-of-time native/Wasm speed, real integer types, exhaustive checked errors, zero data races, deterministic simulation. | Values move; strings split into `str` / `String` / `Ref<str>`; `mut` must be written at call sites; no subtyping. | **Yes**, for systems/backend/tooling domains where TS's GC and `any` fail. |

---

### 2. The Five Weakest Points (Ranked, with Programs and Fixes)

#### Problem 1 (Soundness): Deep effect handlers allow re-entrant `mut` aliasing without `unsafe` (`§5.2`, `§4.1`, `§4.3`)

`§5.2` and `§5.3` state:
> "Handlers are **deep**: the handler stays installed beneath the suspended computation."
> "An arm runs in the context of the `handle` expression."

Look at what happens when a resumptive arm in `handle` captures a `mut` borrow (or mutates a local `let` binding from the enclosing function), and the resumed continuation performs the effect **a second time** before the first arm invocation finishes:

```ts
effect Tick { tick(): void; }

function aliasMut(): void {
  let v = Vec.new<i32>();
  v.push(10);

  handle {
    Tick.tick();
  } with Tick {
    tick() resumes k => {
      // 1st tick(): borrows `v` mutably into `elemRef`
      const elemRef: mut i32 = v[0];
      // While `elemRef` is STILL LIVE on this activation of the arm's stack frame,
      // resume `k`! If the body (or another effect) calls `Tick.tick()` again,
      // the deep handler runs this arm RE-ENTRANTLY while `elemRef` is still live!
      k.resume();
      elemRef += 1; // Use-after-free if the nested `tick()` reallocated `v`!
    }
  }
}

// Concrete trigger where the body calls `Tick.tick()` twice:
function trigger(): void {
  let v = Vec.new<i32>();
  v.push(10);
  handle {
    Tick.tick();
    Tick.tick();
  } with Tick {
    tick() resumes k => {
      const r: mut i32 = v[0]; // 1st call locks `v`
      k.resume();              // resumes body -> hits 2nd `Tick.tick()` -> re-enters arm -> borrows `v[0]` AGAIN while 1st `r` is still live!
      r += 1;
    }
  }
}
```
**What goes wrong:**
Inside the arm `tick() resumes k => { ... }`, the ownership checker checks the arm body **once** sequentially: `r` borrows `v`, `k.resume()` does not mention `v`, and then `r += 1` ends the borrow of `v`. The checker has no idea that `k.resume()` can re-enter the **same handler arm** while `r: mut i32` from the outer activation of the arm is still live on the stack! During the second activation of the arm, `v.push(...)` or `const r2: mut i32 = v[0]` executes while the first activation's `r: mut i32` is still live across `k.resume()`, creating two simultaneous `mut` references to `v[0]` (or reallocating `v` while `r` dangles).

**Fix (removes complexity, adds zero concepts):**
Treat the handler arms of a deep `handle` as a `mut` closure called by `k.resume()`:
- **Rule:** In a resumptive arm (`op(...) resumes k => armBody`), `k.resume(...)` is treated as using every outer binding that **any arm of the same `handle` block** reads, mutates, or borrows!
- Concretely, if an arm borrows outer variable `v` (`ro` or `mut`), then `k.resume()` inside that arm also accesses `v` with that mode. Therefore, no borrow of an outer variable `v` taken inside the arm may remain live *across* `k.resume()`!
In `trigger()` above, `r` holds a `mut` borrow of `v` across `k.resume()`, which conflicts with the arm's own access to `v` during `k.resume()`. Rejected immediately, in 5 lines of code.

---

#### Problem 2 (Ergonomics / False Positives): "A call's result carries the borrows of all its arguments" (`§4.2`) rejects normal polymorphic and multi-parameter code

In v0.18, `§4.2` was updated to say:
> "**Results carry their arguments' borrows.** The result of a call holds every borrow its arguments hold — including borrows captured by closure arguments — unless the result's type cannot hold a borrow at all (it is class 1 and contains no closure, continuation or type parameter)."
> "**Tied returns.** A function that returns a class-2 value and takes exactly one class-2 parameter returns a view of that parameter. With several, the return names its source, and the result then carries only that argument's borrows."

Look carefully at the interaction of those two sentences when a function takes a class-2 argument (`str`, `readonly T`, or a closure) and returns a **generic container** like `Option<String>`, `Result<usize, IoErr>`, or a tuple, or takes two borrows where only one can be returned:

```ts
// Case A: Looking up a `str` key in a `HashMap<String, i32>` or cloning an Option
function lookupOwned(map: readonly HashMap<String, String>, key: str): Option<String> {
  // Suppose `getCloned<K, V>(self: readonly HashMap<K, V>, k: str): Option<V>`
  // Return type of `getCloned` in generic signature is `Option<V>` — which contains a type parameter `V`!
  // Or even simpler: `map.get(key).cloned()`
  let kBuf = key.toString();
  const res: Option<String> = map.get(kBuf).cloned();
  drop(kBuf); // If `cloned()`'s generic return type `Option<T>` had a type parameter `T`,
  return res; // does the checker check `Option<String>` (zonked) or `Option<T>` (uninstantiated)?
}

// Case B: Much worse — a function returning a class-2 view that ALSO takes a `str` or callback!
impl HashMap<String, u64> {
  // Takes TWO class-2 parameters: `self: mut Self` and `key: str`!
  // Returns `Option<mut u64>`, which obviously borrows from `self`, NOT `key`!
  export function getMut(self: mut Self, key: str): Option<mut u64>; // <-- Notice: no `from self` required in A.2?
}

function wordCountBug(counts: mut HashMap<String, u64>): void {
  let tempKey = "hello".toString();
  // `counts` is class 2 (`mut`), AND `tempKey` lent as `str` is ALSO class 2!
  const opt = counts.getMut(tempKey);
  drop(tempKey); // ERROR unless `getMut` is declared `from self`!
  match (opt) {
    #Some(n) => { n += 1; },
    #None => {},
  }
}
```
And what if a function genuinely can return a slice from **either** `a` or `b`?
```ts
// Look at §4.2's own example:
function longer(a: str, b: str, preferA: bool): str from a {
  // WAIT: how can you even implement `longer(a, b)` if the return type is `str from a`?!
  // If `a.len() < b.len()`, returning `b` is a TYPE ERROR because `§4.2` says:
  // "everything the returned value borrows must come from the named parameter"!
  if (a.len() >= b.len()) { a } else { b } // REJECTED by §4.2!
}
```
Look at `§4.2`'s own example `function longer(a: str, b: str, preferA: bool): str from a`! A function named `longer(a, b)` cannot return `b` if its return type says `from a`!

**What goes wrong:**
1. `§4.2`'s `longer(a: str, b: str, preferA: bool): str from a` is a self-contradictory example: a function named `longer` wants to return whichever of `a` or `b` is longer (`from a, b`), which `§2.3`'s grammar (`[ "from" Ident ]`) forbids!
2. If a method like `counts.getMut(w)` takes `self: mut Self` and `w: str`, both parameters are class 2 (`mut Self` and `str`), EXCEPT `mut u64` inside `Option<mut u64>` is `mut`, while `w: str` is `readonly` — or in `counts.get(w): Option<readonly u64>`, both are `readonly`! Without `from self` on every single container lookup method in `std`, `counts.get(tempKey)` locks `tempKey` for as long as the returned reference into `counts` lives.

**Fix:**
1. Allow `from a, b` (a list of parameter names: `"from" Ident { "," Ident }`), and default an omitted `from` clause on a method with a `self` receiver (`readonly Self`, `mut Self`, `Ref<R, Self>`) to `from self` (since 99% of methods returning a borrow project from `self`, not from the lookup key). When a function actually returns from either `a` or `b` (like `longer`), omitted `from` on a free function (or `from a, b`) simply means **the result carries the union of `a`'s and `b`'s borrows**!
   Wait — notice that! If `longer(a: str, b: str): str` (with *no* `from` clause!) simply means "the result carries the borrows of all class-2 parameters (`a` and `b`)", then `longer(a, b)` works *without any `from` annotation at all*, and you only ever write `from a` when you want to *exclude* `b`'s borrows (e.g., `get(self: readonly Self, key: str): Option<readonly V> from self`)!
2. Clarify in `§4.2` that "cannot hold a borrow at all" is evaluated on the **instantiated (post-monomorphization / zonked) return type** at the call site, so `Option<String>` cannot hold a borrow even though `Option<T>` had a type parameter `T`.

---

#### Problem 3 (Soundness): `Cell<R, T>` and `RegionList<R, T>` break `Send` and the Region Data Rule through indirection (`§4.4`, `§4.6`)

`§4.4` says:
> "`T` is `Send` when it is class 1, owns no raw pointer, and contains no region data with a mutable slot (§4.6)."

And `§4.6` says:
> "Because handlers are fiber-local, no other task can perform `Region<R>`; a `Ref<R, T>` whose referent contains no `Cell` or `RegionList` is deeply immutable and may be shared with child tasks."

Now look at `A.5` (`Decl` and `Scope` in a symbol table with cycles):
```ts
export struct Decl<region R> { name: Ref<str>; ty: Cell<u32>; visiting: Cell<bool>; }

struct Wrapper<region R> {
  // Does `Wrapper<R>` contain a `Cell`?
  // Not directly — it contains a `Ref<R, Decl<R>>`, and `Decl<R>` contains `Cell<u32>`!
  decl: Ref<R, Decl<R>>;
}
```
Or even simpler, with recursive types or `Cell<R, Ref<R, ...>>`:
```ts
function raceViaCellRef(): void uses Io {
  region (R) {
    const c = alloc(Cell.new<R, i32>(0)); // c: Ref<R, Cell<R, i32>>
    // Suppose a struct holds a function/interface or recursive Ref, or suppose we check `Send` on `Ref<R, T>`:
    // Wait: why would two child tasks race on `c` if neither child task can perform `Region<R>`?
  }
}
```
Hold on! Ask yourself: if child tasks in `Io.scope` cannot perform `Region<R>` (`§6.1` Rule 4), **how** can a child task race on `Ref<R, T>` when `T` contains a `Cell` or `RegionList`?
**Because the parent fiber (running the body of `Io.scope`) CAN still perform `Region<R>` while the child task is running!**
`§6.1` Rule 4 explicitly says:
> "the body of the scope, which runs on the parent's fiber, still can [perform `Region<R>`]."

And look what happens in the parent fiber while a child task reads a `RegionList` or `Cell`:
```ts
function parentChildRegionRace(): void uses Io {
  region (R) {
    const list: Ref<R, RegionList<R, i32>> = RegionList.new();
    list.push(1);

    Io.scope((s) => {
      // Suppose `Wrapper` or `RegionList.len()` is read in a child task, OR:
      // Wait: `RegionList` implements `Iterable<readonly T>` with NO `Region<R>` effect!
      // And `Cell<R, u64>`: what if `Cell` is inside a transitive `Ref`?
      // Even without `Cell`: what if `c: Cell<R, Option<Ref<R, Node<R>>>>`?
      // `Cell.get` and `Cell.set` take `Region<R>`, which only the parent has.
      // So a child task CANNOT call `Cell.get()` at all!
      // WAIT: why can't a child task read a `Cell`? Because `Cell.get` has `uses Region<R>`!
      // What CAN a child task read without `uses Region<R>`?
      // `RegionList`! Because `§4.6` says:
      // "Reading a `RegionList`'s existing elements does not [perform Region<R>]: they never change."
      const f = s.fork(() => {
        // If `list` (or any struct transitively pointing to `list`) were allowed into `fork`:
        // child calls `list.len()` or iterates `for (const x of list)` (which is PURE!)
        // while the parent fiber concurrently calls `list.push(2)` (mutating `list`'s length/chunk pointers)!
        0
      });
      list.push(2); // Parent fiber mutates `list` concurrently with child fiber!
      f.join();
    });
  }
}
```
Look at what this reveals:
1. A child task **cannot** read or write a `Cell<R, T>` anyway, because `Cell.get` and `Cell.set` both require `uses Region<R>`, and child tasks cannot use `Region<R>`! So a `Cell<R, T>` inside `Ref<R, Decl<R>>` (like `A.5`!) is **completely inaccessible** to pure child tasks!
   Wait: why did `§4.4` and `§4.6` say a `Ref<R, T>` containing a `Cell` is not `Send`?!
   In `A.5`, `Decl<R>` has `name: Ref<str>; ty: Cell<u32>;`. If a compiler pass finishes resolving types sequentially and then wants to run codegen in parallel over `Ref<R, Decl<R>>` using `Io.scope` (or `parReduce`), `Decl<R>` is **not `Send`** under `§4.4` just because it has a `ty: Cell<u32>` field — *even if the parallel tasks only read `decl.name` or even though `ty.get()` is already forbidden by the effect system because it requires `uses Region<R>`*!
   Wait: can a child task read `Cell<R, T>` without `uses Region<R>`? **NO!** `Cell` is an opaque struct (`export struct Cell<region R, T extends Copy>;` in `§4.6`); its fields are private and its only methods `get` and `set` both require `uses Region<R>`!
   And while `Io.scope` is running, can the parent fiber mutate a `Cell` while a child task reads the `Cell`? **NO, because the child task cannot call `Cell.get` (it lacks `uses Region<R>`)!**
   What about `RegionList<R, T>`? `RegionList.len()` and `RegionList.each()` do **not** require `uses Region<R>` (`§4.6`). So if the parent fiber calls `list.push(x)` inside `Io.scope` while a child task calls `list.len()` or `for (const x of list)`, they race on the list's length/tail pointer!

**Wait — think about that!**
Why does `RegionList.each()` not require `uses Region<R>`, whereas `Cell.get()` does?
Because `A.5` wanted `Scope.lookup` to be pure (`for (const b of self.names)`).
And if `RegionList` is mutated by the parent fiber inside `Io.scope` while a child fiber iterates it, that's a data race unless either:
- `Ref<R, T>` is transitively not `Send` when reachable from `T` there is a `RegionList` (requiring a transitive graph reachability check over all fields of `T`), **OR**
- **Much better:** `s.spawn` and `s.fork` borrow the enclosing `region (R)` `readonly` for the duration of `Io.scope` (so the parent fiber *also* cannot perform `Region<R>` inside `Io.scope` while child tasks are live!).

Look at what happens if `Io.scope` (and `par`) suspends `Region<R>` mutation while tasks are running:
- While concurrent tasks exist in `Io.scope`, **nobody** (not even the parent fiber) can call `alloc`, `Cell.set`, or `RegionList.push` in an outer region `R`!
- Once `Io.scope` finishes, the parent fiber can mutate `R` again!
- Then **every `Ref<R, T>` (including `Decl<R>` with `Cell` and `Scope<R>` with `RegionList` in `A.5`!) is unconditionally `Send`!**
Let's double check that! If no fiber (neither parent nor child) can perform `Region<R>` during `Io.scope` (because `Io.scope`'s body cannot use `Region<R>` of an outer region, or `spawn`/`fork` locks outer regions), then during `Io.scope` all outer regions `R` are **100% frozen (immutable)**!
- Child tasks can freely share and read `Ref<R, Scope<R>>` and `Ref<R, Decl<R>>` from `A.5` in parallel!
- You **delete** the entire special case in `§4.4` and `§4.6` ("contains no region data with a mutable slot / contains no `Cell` or `RegionList`")!
- And in `§10.2` (the HTTP handler), `Io.scope` only calls `db.fetchProfile(req.user)` and `db.checkQuota(req.token)` — it does *not* perform `Region<R>` inside `Io.scope`!

**Fix (removes a whole concept and fixes transitive `Ref` soundness):**
1. Forbid `Io.scope` (not just `fork`/`spawn`, or forbid `Region<R>` in `Io.scope` when `R` is an outer region) from performing `Region<R>` on any region `R` declared outside `Io.scope`. (A task or scope body can still open its *own* inner `region (R2) { ... }` locally on its own fiber!)
2. Because outer regions `R` are completely read-only for the entire duration of `Io.scope` (and `par`), **every `Ref<R, T>` is unconditionally `Send`**, regardless of whether `T` contains `Cell` or `RegionList`! You remove the transitive mutable-slot check on `Ref<R, T>` completely, and `A.5`'s `Scope<R>` and `Decl<R>` become `Send` for parallel compiler passes!

---

#### Problem 4 (Scalability / Ergonomics): Open `Fail` unions lose error provenance and collide across layers (`§3.2`, `§5.4`)

`§3.2` says:
> "Determined arguments are what make error sets compose. A block that calls `conn.read` (`Fail<IoErr | ...ρ1>`) and `parse` (`Fail<#Malformed | ...ρ2>`) has one `Fail` whose payload is the merged union `IoErr | #Malformed | ...ρ3`; no conversion code is involved."

In a 50-line example (`§10.2`), this looks magical. In a 10,000-line codebase, two things immediately go wrong:

**Case A: Two calls throw the same tag with *different* payloads (unification error at a distance) or the same payload (lost provenance).**
```ts
// Module A: HTTP client
type HttpErr = #TimedOut(u32) | #BadStatus(u16); // #TimedOut carries timeout in ms (u32)
function fetchUser(): User uses Io, Fail<HttpErr>;

// Module B: Database client
type DbErr = #TimedOut | #Deadlock;              // #TimedOut has no payload (or carries query `String`)
function queryDb(): Row uses Io, Fail<DbErr>;

// Application code calling both in one function:
function handleRequest(): void uses Io {
  try {
    const u = fetchUser();
    const r = queryDb(); // TYPE ERROR! Cannot unify `#TimedOut(u32)` with `#TimedOut`!
  } catch (e) { ... }
}
```
Because both `HttpErr` and `DbErr` happened to use the tag name `#TimedOut` (or `#NotFound`, or `#Unexpected`) with different payloads (`#TimedOut(u32)` vs `#TimedOut`), **you cannot call `fetchUser()` and `queryDb()` in the same `try` block!** The row unifier merges identical tag labels by unifying their payloads (`§3.2`), which fails with a type mismatch between `u32` and `void`!
And even when their payloads match (both `#NotFound`), the `catch` block cannot tell whether the `#NotFound` came from `fetchUser()` (HTTP 502) or `queryDb()` (HTTP 404)!

**Case B: How do you wrap/namespace one call's error without catching every error?**
In `handleRequest` above, how would the programmer wrap `fetchUser()`'s error into `#Http(HttpErr)`?
If they write:
```ts
const u = try { fetchUser() } catch (e) { throw #Http(e) };
```
Look at what `try { fetchUser() } catch (e) { throw #Http(e) }` works out to: `try` closes `fetchUser()`'s failure row to `HttpErr` (`§5.4`), binds `e: HttpErr`, and throws `#Http(HttpErr)`.
Wait: that works, *if* `HttpErr` is a valid payload type, which it is (`type HttpErr = #TimedOut(u32) | #BadStatus(u16)`).
**Hold on!** Why is there no combinator or method for this? Look at `§5.4`:
> "To keep a failure as data, `Fail.capture(() => body)` returns `Result<T, E>`; `r.unwrap()` turns it back into a failure. There is no separate error-conversion machinery: failure rows compose by union (§3.2)."

If someone writes `fetchUser()` inside a helper or wants to add context (e.g. which file failed to open in `A.2`, or wrapping `HttpErr` into `#Http(HttpErr)`), writing `try { fetchUser() } catch (e) { throw #Http(e) }` on every call is noisy.

**Fix:**
Add a tiny library function in `std` (no compiler changes needed, just `Fail.map` or `Result.mapErr` in `std`):
```ts
// In `impl Fail` or prelude:
export function mapFail<T, E1, E2, row E>(
  f: once () => T uses Fail<E1>, ...E,
  wrap: once (e: E1) => E2,
): T uses Fail<E2>, ...E {
  try { f() } catch (e) { throw wrap(e) }
}
```
Wait: test whether `mapFail` actually type-checks under `§3.2`!
In `mapFail`, `Fail<E1>` in `f`'s signature is opened to `Fail<E1 | ...ρ1>` by `§3.2` ("The argument of `Fail` in a signature is open, after expanding aliases").
Wait: if `E1` is a **type parameter** (`Fail<E1>`), `E1` is not a tag union literal, so `Fail<E1>` unifies `E1` directly with the closed tag union when `try` handles `Fail`!
Ensure your checker supports `Fail<E>` where `E` is a type parameter (used in `Fail.capture` and `Scope.fork<T, X>`), and put `Fail.map(() => fetchUser(), (e) => #Http(e))` in the standard library and spec (`§5.4`).

---

#### Problem 5 (Expressiveness): `Yield<T>` is hardcoded to return `void`, and `Iterable<T>` cannot express iterator adaptors (`§5.5`, `A.3`)

Look at `A.3` (`zip`):
```ts
export function dot(xs: readonly f64[], ys: readonly f64[]): f64 {
  let total = 0.0;
  for (const [x, y] of zip(() => xs.each(), () => ys.each())) { total += x * y; }
  total
}
```
The appendix note on `A.3` admits:
> "*Awkward:* passing streams as thunks (`() => xs.each()`) rather than as values. That is the price of streams being computations; `Gen` is the value form when one is wanted."

Wait: why did `dot` have to write `zip(() => xs.each(), () => ys.each())` instead of `zip(xs, ys)`?!
Look at `§5.5`:
```ts
interface Iterable<T, row E = []> {
  function each(self: readonly Self): void uses Yield<T>, ...E;
}
```
`xs` and `ys` **already implement `Iterable<readonly f64>`**!
Why couldn't `zip` be written over `Iterable`:
```ts
export function zip<A, B, IA extends Iterable<A, E>, IB extends Iterable<B, E>, row E>(
  a: readonly IA,
  b: readonly IB,
): void uses Yield<[A, B]>, ...E {
  let ga = generate(() => a.each());
  let gb = generate(() => b.each());
  while (true) {
    match ([ga.next(), gb.next()]) {
      [#Some(x), #Some(y)] => yield [x, y],
      _ => break,
    }
  }
}
```
If `zip` takes `a: readonly IA, b: readonly IB` (or if `Gen<T, E>` also implements `Iterable`), then `dot` is simply:
```ts
for (const [x, y] of zip(xs, ys)) { total += x * y; }
```
Wait: why didn't `A.3` do that? What happens when you chain two adaptors: `filter(zip(xs, ys), ([x, y]) => x > 0.0)`?
`zip(xs, ys)` is a *generator call* (`void uses Yield<[A, B]>`), **not** an `Iterable` value! So you can pass `zip(xs, ys)` directly to `for (const p of zip(xs, ys))`, because `§5.5` has a special rule for `for…of`:
> "If `e` is a generator call, it is the generator. Otherwise `e`'s type must implement `Iterable`... and the generator is `e.each()`."

Because that coercion only exists in `for…of`, you **cannot** pass `xs` to `zip` if `zip` expects a generator closure, and you **cannot** pass `zip(xs, ys)` to `filter` if `filter` expects an `Iterable`!
Every single composition of `map`, `filter`, `take`, `enumerate`, `zip` requires wrapping in `() => ...` thunks:
`for (const x of take(() => filter(() => map(() => xs.each(), f), pred), 5))`!
A TypeScript programmer used to `xs.map(f).filter(pred).take(5)` will revolt at `take(() => filter(() => map(() => xs.each(), f), pred), 5)`.

**Fix (pure library / zero core changes):**
Have `Gen<T, E>` implement `Iterable<T, E>` (by consuming `self` or taking `mut Self`), OR provide a tiny value wrapper `Stream<T, E>` (which is just `Gen<T, E>` or a closure struct) with inherent methods `.map(...)`, `.filter(...)`, `.take(...)`, `.zip(...)`, `.collect()`!
Let's check if `Gen<T, E>` can have `.map`, `.filter`, `.zip` methods in `std/iter`:
Wait: a `Gen<T, E>` holds a `Cont` (class 2 when borrowing `xs`).
Can you call `xs.iter().map((x) => x + 1).filter((x) => x > 0)` in Flyscript?
If `.map(self: Gen<T, E>, f: ...)` takes `self` by value and returns a new `Gen<U, E>` (which calls `generate(() => { while (...) { yield f(x); } })`), then by `§4.2`, the returned `Gen<U, E>` carries `self`'s borrows (the borrow of `xs`)!
Let's trace that!
1. `xs.iter()` calls `generate(() => xs.each())`, returning `Gen<readonly f64, []>` carrying the borrow of `xs` (class 2).
2. `.zip(ys.iter())` returns `Gen<[readonly f64, readonly f64], []>` carrying the borrows of `xs` and `ys` (class 2).
3. `for (const [x, y] of xs.iter().zip(ys.iter()))` drains the `Gen`!
Look how clean that is: **because v0.18 already propagates borrow sets through `Gen<T, E>`**, `xs.iter().map(...).filter(...).zip(...)` works in the existing type and ownership system with **zero** lifetime parameters and **zero** `() =>` thunks!

---

### 3. Learnability for a TypeScript Programmer

#### What a TypeScript programmer must learn/unlearn, in order:

1. **Numbers and `match` (10 minutes):** `i32`/`usize`/`f64` instead of `number`; `#Tag` unions and `match` instead of discriminant strings and `switch`. (Easy; TS programmers already write discriminated unions.)
2. **Moves vs. `readonly` / `mut` borrows at call sites (Day 1):**
   Passing `v` moves it; passing `v` to a `readonly` parameter borrows it; passing `mut v` borrows it mutably. (Surprisingly easy to learn because `mut v` at the call site is explicit and compiler errors can suggest "did you mean `mut v` or `.clone()`?").
3. **Effect rows: `uses Io, Fail<...>` (Day 2):**
   Every exported function lists its side effects; internal functions infer them. Replaces `async`/`await`, `Promise<T>`, and untyped `throws`. (Easy and gratifying.)
4. **THE WALL: Second-class values (`str`, `T[]`, `readonly T`) cannot go into normal structs or be returned freely (Day 3–5):**
   In TypeScript, every object and string is a GC reference. A TS programmer's first instinct is to write:
   ```ts
   struct User {
     name: str; // <-- Makes `User` CLASS 2!
   }
   ```
   Wait: look at what happens when a beginner writes `struct User { name: str; }`!
   The struct declaration itself **succeeds without error**! Because `Scanner` in `A.1` (`struct Scanner { src: readonly u8[]; pos: usize; }`) is a legal class-2 struct!
   Then, 200 lines later, the programmer tries to put `User` into a `Vec<User>`, or return `User` from a function `createUser(): User`, or send `User` to a task!
   And the compiler says: *"`User` is class 2 (because `User.name` has type `str`) and cannot be stored in `Vec<User>` or returned from `createUser`."*
   Then the programmer asks: *"Wait, what should `User.name` be?"*
   And there are **three** string types in Flyscript:
   - `str` (class-2 borrow: for parameters, locals, and temporary views like `Scanner`),
   - `String` (class-1 heap owner: for long-lived structs like `Profile` in `§10.1`),
   - `Ref<R, str>` (class-1 region reference: for arena-allocated trees like `Request<R>` in `§10.2` and `Json<R>` in `A.1`).

5. **Second hardest concept: Region `Ref<T>` placement (`§4.6`, `A.1`, `A.5`):**
   Look at `Json<R>` in `A.1`:
   ```ts
   export enum Json<region R> {
     #Null, #Bool(bool), #Num(f64), #Str(Ref<str>),
     #Arr(Ref<RegionList<Ref<Json>>>),
     #Obj(Ref<RegionList<{ key: Ref<str>; val: Ref<Json> }>>),
   }
   ```
   Why is `#Arr` `Ref<RegionList<Ref<Json>>>` (two nested `Ref`s), while `#Obj`'s element `{ key: Ref<str>; val: Ref<Json> }` is NOT wrapped in `Ref`?
   Because `RegionList.new()` already returns `Ref<R, RegionList<R, T>>` (`§4.6`), and inline `Copy` structs inside a `RegionList` don't need `Ref`, whereas recursive `Json` does.

#### How to flatten the learning curve (Spec & Compiler):
1. **Require an annotation or give an immediate hint on class-2 `struct`/`enum` declarations:**
   Actually, think about this: how often does a programmer *intend* to declare a class-2 nominal `struct` (like `Scanner` in `A.1`) vs. accidentally putting `str` or `T[]` in a domain struct (`User`) when they meant `String` or `Vec<T>`?
   95% of nominal `struct`s are class-1 data (`Profile`, `Request`, `Particle`, `Decl`, `Scope`); only cursor/view structs (`Scanner`) are class 2!
   If the compiler emits a lint/note (or requires a modifier/attribute, or in diagnostics on class-2 errors points directly at the `str`/`T[]` field in `struct User` and suggests *"use `String` (owned) or `Ref<str>` (in a region) if `User` is stored or returned; `str` is a temporary borrow"*), that Day-3 wall disappears.
2. **Fix `RegionList<R, T>` so users don't write `Ref<RegionList<...>>`:**
   Look at `§4.6`:
   ```ts
   impl<region R, T> RegionList<R, T> {
     export function new(): Ref<R, RegionList<R, T>> uses Region<R>;
   }
   ```
   Wait: if `RegionList.new()` *always* returns `Ref<R, RegionList<R, T>>`, why is the type called `RegionList<R, T>` instead of `RegionList<R, T>` *being* the region handle (a `Copy` 1-word pointer to the region header, just like `Ref` is)?
   Look at `A.1` and `A.5` if `RegionList<R, T>` is itself a `Copy` handle into region `R`:
   - `#Arr(RegionList<Ref<Json>>)` instead of `#Arr(Ref<RegionList<Ref<Json>>>)`!
   - `names: RegionList<{ name: Ref<str>; decl: Ref<Decl> }>` instead of `names: Ref<RegionList<...>>`!
   - `RegionList.new(): RegionList<R, T> uses Region<R>`!
   - `push(self: Self, v: T): void uses Region<R>` (no special `self: Ref<R, Self>` receiver needed for `RegionList`!).
   Making `RegionList<R, T>` and `Cell<R, T>` value handles (where `Cell` is inline or handle and `RegionList` is a 1-word `Copy` pointer into the region) eliminates the double-indirection `Ref<RegionList<Ref<...>>>` across the entire language!

---

### 4. What a 10,000-Line Program Will Need in Week 1

Here are the six things a real 10,000-line program (say, the Flyscript compiler itself, or an HTTP service + DB driver) will hit in week 1, and whether the v0.18 core can express them:

1. **Module-level `const` declarations (`const MAX_BUF: usize = 512;`):**
   Look at the grammar in `§2.3`:
   ```ebnf
   Decl = Struct | Enum | Interface | Impl | TypeAlias | Effect | Function | Extern ;
   ```
   **You cannot declare a top-level constant `const PORT: u16 = 8080;` in a module!** `const` is only in `Stmt` (inside a `Block`).
   *Fix:* Add `[ "comptime" ] "const" Ident [ ":" Type ] "=" Expr ";"` to `Decl` in `§2.3`.

2. **Closures stored in structs / type aliases (callbacks, event handlers, parser combinators):**
   Can a class-1 struct hold a closure `(A) => B`?
   By `§4.2`: *"Some types can hold a borrow without showing it: closures, continuations... A value of such a type is class 2 when it actually holds a borrow... It may not be stored in a class-1 value."*
   Wait: how does the compiler check `struct Router { handler: (Request) => Response uses Io; }`?
   At the `struct Router` declaration, `(Request) => Response uses Io` is a **type**, not a value! Is `Router` class 1 or class 2?
   If `Router` is class 1, then storing a closure `Router { handler: f }` must require that `f` is **class 1** (i.e., `f` captures only class-1 values by move or `Copy`, and holds **no borrows**)!
   And wait: by `§4.3`, *"An escaping closure captures only by move"* — and a closure that captures an owned non-`Copy` value by move has type `once (A) => B`, **not** `(A) => B`!
   Think about that!
   If an escaping closure captures a `String` or `Arc<Db>` by move:
   - `Arc<T>` is not `Copy` (it has an atomic reference count and a destructor `Drop`); it is `Clone`!
   - Wait: if `Arc<T>` is not `Copy`, then a closure `(req) => serve(req, dbArc)` that captures `dbArc: Arc<Db>` by move is inferred by `§4.3` as **`once (Request) => Response`**, NOT `(Request) => Response`!
   - It can only be called **once**! You can't even pass a closure that captures an `Arc<T>` or `String` to a multi-shot `(A) => B` callback unless the closure only *borrows* `readonly dbArc` (which makes the closure **class 2**, so it cannot be stored in `Router`!).
   Let me show this as a concrete program:
   ```ts
   struct Router {
     onGet: (str) => String;
   }
   function makeRouter(prefix: String): Router {
     // If the closure borrows `prefix` (`readonly String`), the closure is CLASS 2 -> cannot be stored in `Router` or returned!
     // If the closure moves `prefix` (`String`), §4.3 says:
     // "once (A) => B | at least one moved value | at most once"!
     // So moving `prefix` into the closure gives it type `once (str) => String`, which doesn't match `(str) => String`!
     Router { onGet: (path) => `${prefix}/${path}` } // IMPOSSIBLE TO WRITE!
   }
   ```
   **What a great catch.** Look at `§4.3`:
   - If a closure borrows `prefix: readonly String`, it is `(str) => String`, which is **class 2** (holds a borrow of local `prefix`) and **cannot be returned from `makeRouter` or stored in `Router`**!
   - If a closure moves `prefix: String` into its environment so it can escape `makeRouter`, `§4.3` says a closure with *"at least one moved value"* is **`once (A) => B`**!
   So there is **no way in Flyscript** to create a multi-callable escaping closure `(A) => B` or `mut (A) => B` that owns a `String`, `Vec`, or `Arc<T>`!
   **Fix:**
   In `§4.3`, what makes a closure `once` is **not** moving a value *into* the closure when the closure is constructed; it is moving a captured value *out* of the closure's environment when the closure body is **called**!
   - If `(path) => `${prefix}/${path}`` moves `prefix: String` into the closure environment at construction time, and the body only *reads* `prefix` on each call, the closure is callable any number of times (`(str) => String`) and is class 1 (owns `prefix`, holds no borrows)!
   - If the body *mutates* a captured owned value on each call, the closure is `mut (A) => B` and class 1!
   - Only if the body *moves out of* (consumes) a captured value when called is the closure `once (A) => B`!

3. **Interface inheritance / supertraits (`interface Ord extends Eq`):**
   Look at `§2.3`:
   ```ebnf
   Interface = "interface" Ident [ TypeParams ] "{" { ( Sig | "type" Ident [ "extends" Bounds ] ) ";" } "}" ;
   ```
   An interface cannot declare super-interfaces (`interface Ord extends Eq { ... }`). Every generic function needing `Ord` would have to write `<T extends Ord & Eq>`. Adding `[ "extends" Bounds ]` to `Interface` is a 1-line grammar change.

4. **Operator overloading or standard traits (`Index`, `Add`, `Deref`/Lending for user types):**
   In `A.4`, `Vec2` has `p.pos.x += p.vel.x * dt` component-wise because `Vec2` cannot implement `+` or `*`. More importantly, `§4.1` hardcodes lending (`String` lends `str`, `Vec<T>` lends `T[]`, `Box<T>` lends `T`, `Ref<R, T>` lends `readonly T`). User containers (like `SmallVec<T, N>` or `ArenaStr`) cannot lend `T[]` or `str` unless lending is an interface or `std` privilege. (Acceptable for 1.0 if intentional, but worth noting.)

5. **Pattern matching ergonomics (`if let` / `let ... else`):**
   Unwrapping a single tag (`#Some(x)`) without indenting a 4-line `match` expression. Since Flyscript wants a minimal core, you don't need `if let` if `Option.unwrapOr` / `?` or `match` is concise, **or** `let #Some(x) = opt else { return; };` can wait until post-1.0.

6. **Visibility inside modules vs packages:**
   Currently (`§8.1`), each `.fly` file is a module and struct fields are private to their file unless wait — look at `§2.3`:
   ```ebnf
   Struct = [ Layout ] "struct" Ident [ TypeParams ] "{" { Ident ":" Type ";" } "}" ;
   ```
   There is no `export` keyword on struct fields in `§2.3`, yet `§3.3` says *"may keep its fields private to its module"*. How does a struct make its fields *public* outside its module (like `Profile.displayName` in `§10.1`, which is why `§10.1` had to declare `Profile` as a structural `type Profile = { displayName: String }` instead of a `struct`!)?
   *Fix:* Either allow `export` on struct fields (`export x: f64;`), or state that an `export struct` has public fields unless declared `export struct Foo;` in a `.d.fly` file or with private fields.

---

### 5. What to Cut from `§0–§9`

To keep the core as small and orthogonal as possible, I would cut or merge three things:

1. **Cut `.d.fly` as a separate file format (`§2.1`, `§8.1`); allow bodyless declarations in `std` or `extern` blocks:**
   Having both `.fly` and `.d.fly` is a TypeScript artifact from JavaScript not having types. In Flyscript, every `.fly` file *already* has types! The only reason `.d.fly` exists in `§8.1` is for runtime-backed standard library functions. Allowing bodyless function/struct signatures in `std` (or `extern "fly"`) avoids a second file extension and concept.

2. **Make `RegionList<R, T>` and `Cell<R, T>` region-handle types directly, cutting `self: Ref<R, Self>` (`§3.4`, `§4.6`):**
   Look at `§3.4`:
   > "A method's receiver is `self: Self` (by move), `self: readonly Self`, `self: mut Self`, or, for types stored in regions, `self: Ref<R, Self>`."
   Why did `§3.4` need a fourth receiver kind `self: Ref<R, Self>`?
   Only for `RegionList.push(self: Ref<R, Self>, v: T)` (`§4.6`) and `Scope.define(self: Ref<Self>, ...)` (`A.5`)!
   Wait: because `Ref<R, T>` lends `readonly T` (`§4.1`), any method taking `self: readonly Self` can *already* be called on a `Ref<R, T>` (as `Scope.lookup` and `RegionList.len` already do)! The only place `self: Ref<R, Self>` is needed in `A.5` is when the method itself wants to copy the `Ref<R, Self>` pointer (e.g., to store `self` as a parent pointer). And for `RegionList<R, T>`, if `RegionList<R, T>` is itself a `Copy` handle into region `R` (so `RegionList.new()` returns `RegionList<R, T>`, not `Ref<R, RegionList<R, T>>`), then `RegionList.push` simply takes `self: Self` (or `self: readonly Self`), and `#Arr(Ref<RegionList<Ref<Json>>>)` in `A.1` simplifies to `#Arr(RegionList<Ref<Json>>)`.

3. **Cut the mutable-slot exception from `Send` (`§4.4`, `§4.6`) by freezing outer regions across `Io.scope` (Problem 3 above):**
   In `§4.4`, `Send` is defined as: *"class 1, owns no raw pointer, and contains no region data with a mutable slot (§4.6)."*
   By simply forbidding `Io.scope` from performing `Region<R>` on regions outside the scope while tasks are running, outer regions are guaranteed immutable during parallel execution. Then `Ref<R, T>` is **always `Send`**, and the "contains no region data with a mutable slot" rule disappears from both the spec and the compiler.
