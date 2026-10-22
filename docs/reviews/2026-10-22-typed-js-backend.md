# Review: typed-js-backend

- spec: ff173eecc106
- request: fe7b7d776f476e4e
- tokens: prompt 65522, cached 0, answer 6092

## Question

# Typed JavaScript backend for the self-hosted Flyscript compiler: design review

Context: Flyscript (TypeScript syntax; affine ownership with second-class borrows `readonly T` / `mut T`; one row calculus for records, `#tag` unions and effects; effects Fail, Io, Yield, Region plus user effects with `handle` and one-shot first-class continuations; Drop; comptime templates/derivation). The self-hosted compiler (selfhost/, ~11k lines of Flyscript) has a full type/effect checker identical to the Rust prototype's, and an *untyped* JS backend that guesses at runtime (method dispatch by value shape, `$t` tags on structs, WRITEBACK hacks for `String.push`). It reaches a byte-identical self-compile fixpoint. 15/52 of the run corpus pass on JS. The Rust prototype's tree-walking interpreter is the semantic reference (every local a cell; a borrow is a pointer to a place).

Proposed typed backend:

1. Pipeline: load + check the whole program (std included), then **monomorphize from `main`**: instance = (function id, concrete generic args incl. effect-row args). Each instance becomes one JS function. Interface calls through bounds resolve statically per instance (resolveImpl + methodFor; specialize template impls on demand and check them). std functions with bodies are compiled like user code; body-less std declarations (~120: Vec.push, HashMap.get, str.split, channels…) are runtime builtins keyed `Type.method`.

2. Representation: integers BigInt (checked arithmetic per width, panics like the interpreter), floats numbers, strings JS strings of bytes, structs/records plain objects (no type tag), tuples/arrays/Vec JS arrays, tags `{ $tag, $ }`. **A value of type `mut T` is always a Ref** (an object with get/set `v`): a local that is ever lent `mut` is stored in a cell `{v}` so the cell *is* the ref; a field/element place lent mut becomes `new FieldRef(obj, key)`. `readonly T` is the value itself (sharing is safe under the borrow rules). A `Copy` value read out of a place into a new owner is copied iff its type is Copy and is a JS object. Box/Arc are transparent. show/eq/cmp/hash are type-directed: derived impls are compiled from the checker's comptime-expanded bodies; structural fallbacks are generated per concrete type.

3. Effects: Fail = JS exceptions. An instance whose concrete effect row contains any suspending effect (Yield or a user effect) is a JS generator; calls to it are `yield*`. Closures likewise by their function type's effect row. `perform` = `yield {op}`. `handle` = a driver that steps the body generator, runs matching arms with a resume function (deep handler: resume re-enters the driver), forwards foreign ops outward with `yield`. A one-shot continuation kept first-class is the suspended generator. `for (x of g())` over a Yield function iterates the generator. Tasks/channels: a cooperative scheduler over generators (Io ops as scheduling points), later.

4. Drops: needs the ownership pass (own.rs) ported first for move facts; then drop flags only for bindings whose type needs drop, with try/finally at scope exit.

Questions:
A. Is "mut T is always a Ref" the right uniform rule, versus passing objects directly for `mut self` on struct types? Trade-offs for performance of the self-compiled compiler and for simplicity.
B. Monomorphization vs passing runtime type dictionaries for this JS backend, given a later C backend. Any traps (polymorphic recursion, effect-row args in instance keys, code size)?
C. Generators for every instance with a suspending effect row: pitfalls? Higher-order builtins in the runtime (e.g. Fail.capture, Vec.retain, sortBy) receiving generator closures.
D. Order of work: what should come first to maximize corpus pass rate while staying on the path to a principled backend?
Keep the answer concrete and ranked.

## Context files

- `selfhost/gen.fly`
- `selfhost/runtime.js`

## Answer

### Verdicts

- **(A) "`mut T` is always a `Ref`" vs direct object passing:** **Agree with "`mut T` is always a `Ref`" as the uniform rule.** Do not special-case `mut self` on structs; passing structs directly breaks wholesaling reassignment (`self = other`), `swap(mut self, ...)`, and lending `mut` of a struct parameter. Make it zero-cost in hot paths via two tiny refinements: `{ v }` cells for mut-lent locals and direct field mutation `r.v.f = x` instead of `new FieldRef(r.v, "f")` when assigning to a field through a `Ref`.
- **(B) Monomorphization from `main` vs runtime type dictionaries:** **Agree with changes.** Monomorphization is the right choice and directly reusable as the mid-level IR for a C backend, **provided** you canonicalize and erase non-codegen-relevant components (region parameters, `Fail` payloads, and `Region<R>` effects) from the specialization key. Otherwise effect-row polymorphism and recursive region functions will cause combinatorial explosion or non-termination.
- **(C) JS generators for instances with suspending effect rows:** **Agree with changes.** Two concrete traps will bite you unless handled up front: (1) body-less runtime HOFs (`Fail.capture`, `Fail.map`, `Option.map`) that are effect-polymorphic in `std` must either be written in Flyscript or step generator callbacks, and (2) `generate()` / `for…of` over a generator that *also* performs an outer effect (`Io` or `Clock`) requires `Yield` to go through the same `{ $eff, $op, $args }` protocol rather than bare `yield item`.
- **(D) Order of work:** **Agree with a 4-step sequence** (Ranked below) that takes the corpus from 15/52 to ~48/52 before porting `own.fly`, and 52/52 once `own.fly` + `Drop` land.

---

### Problems

#### 1. Question (A): Passing `mut self` directly on structs miscompiles whole-place mutation (`replace`, `swap`, `self = …`), whereas uniform `Ref` is both sound and fast (`§3.1`, `§4.1`)

Suppose you special-cased `self: mut Self` on structs to pass the plain JS object instead of a `Ref`, while other `mut T` parameters are `Ref`s. Look at what happens in valid Flyscript:

```ts
struct Node { val: i32; }

impl Node {
  function reset(self: mut Self): Node {
    // §3.1: replace(mut place, v) gives back what a place held and leaves v there.
    replace(mut self, Node { val: 0 })
  }
  function step(self: mut Self): void {
    self = Node { val: self.val + 1 };
  }
}

export function main(): void uses Io {
  let n = Node { val: 42 };
  const old = n.reset();
  n.step();
  println(`${old.val} ${n.val}`); // Expected: "42 1"
}
```
If `self` inside `reset` and `step` is the plain JS object `{ val: 42 }` instead of the caller's `Ref` to `n`:
- `self = Node { val: ... }` only rebinds the local parameter `self`; the caller's `n` is still `{ val: 42 }`!
- `replace(mut self, ...)` creates a `Ref` to the parameter variable `self`, leaving the caller's `n` untouched!
- Even worse: what if a generic function `function clear<T extends Reset>(x: mut T)` calls `x.reset()`? Inside `clear`, `x` is a `Ref`. And what if a struct is represented as a primitive or array after a type alias (`Vec<T>`, `String`), or in `Option<T>.take(self: mut Self)` where `self` is a tag object `{ $tag: "Some", $: ... }`?

With **"a value of type `mut T` is always a `Ref`"**:
- There are **zero** special cases: `self: mut Self` on `String`, `Vec`, `Option`, `Node`, or `i32` is a `Ref`. `WRITEBACK` in `gen.fly` disappears completely.
- What about the performance of the self-hosted compiler (`selfhost/`, which uses `self: mut Self` on `Lexer`, `Parser`, `Checker`, `Gen`)?
  1. **Locals that are lent `mut`:** As you proposed, a local `let p = Parser.new(...)` that is ever lent `mut` is allocated once as `const p = { v: Parser$new(...) };`. Passing `mut p` to `p.parseExpr()` passes `p` itself — **zero allocation at the call site**!
  2. **Field access through `self: mut Self` (`self.pos += 1`, `self.scopes.push(...)`):** Inside a method where `self` is a `Ref` (`{ v: obj }`), reading or mutating `self.pos` is just `self.v.pos += 1n`. You do **not** allocate a `new FieldRef(self.v, "pos")` unless `self.pos` is itself passed as `mut self.pos` to *another* function!
  3. **When `mut self.field` IS lent to a call** (e.g., `replace(mut self.out, String.new())` in `gen.fly:335`): `new FieldRef(self.v, "out")` allocates a 2-field JS object `{ o: self.v, k: "out", get v() { return this.o[this.k]; }, set v(x) { this.o[this.k] = x; } }`, which V8 escape-analyses and scalar-replaces when inlined.
  4. **One subtle aliasing case to get right with `FieldRef` / `IndexRef`:**
     Consider lending a field or index of a `mut` place where the base could be reassigned while the sub-borrow is not yet used, or lending through a chain `mut a.b.c`:
     ```ts
     struct Inner { x: i32; }
     struct Outer { inner: Inner; }
     function inc(r: mut i32): void { r += 1; }
     export function main(): void {
       let o = Outer { inner: Inner { x: 1 } };
       inc(mut o.inner.x);
     }
     ```
     Because `o` is a cell `{ v: { inner: { x: 1 } } }`, `o.v.inner` evaluates to the `Inner` JS object, so `new FieldRef(o.v.inner, "x")` (eagerly evaluating the target object `o.v.inner` once, and storing `(obj, "x")`) evaluates side effects in the receiver/index **exactly once** (fixing Problem 3 from the previous review!) and is valid for the duration of the borrow because Flyscript's borrow rules (`§4.1`) forbid mutating `o` or `o.inner` while `o.inner.x` is borrowed!
     *(Exception: if `o.inner` is a `String` or primitive, you cannot lend a subfield of it anyway; if `xs[i]` is a `Vec` element `mut xs[i]`, `new IndexRef(xs.v, Number(i))` holds the JS array `xs.v` and index `Number(i)`, which cannot be reallocated while `xs[i]` is borrowed).*

---

#### 2. Question (B): Three monomorphization traps with effect rows, regions, and `Type.info` (`§3.2`, `§4.6`, `§7.2`)

Monomorphizing from `main` is the right architecture for both the typed JS backend and a future C backend. However, if your instance key is literally `(fnId, concreteTypeArgs)` using the checker's raw `Type`s, you will hit three traps:

**Trap B1: Effect-row and `Region<R>` explosion in the instance key.**
Look at `A.1` (`value<region R>`) or any generic helper `map<T, U, row E>`:
```ts
function helper<T, row E>(x: T, f: (a: T) => T uses ...E): T uses ...E {
  f(x)
}

export function main(): void uses Io {
  region (R1) {
    const a = helper(1, (x) => { const _ = alloc(x); x }); // E = [Region<R1>]
  }
  region (R2) {
    const b = helper(1, (x) => { const _ = alloc(x); x }); // E = [Region<R2>]
  }
}
```
And what if `helper` is called in two places that throw different errors (`E = [Fail<#ErrA>]` vs `E = [Fail<#ErrB | #ErrC>]`)?
At runtime in JS (and in C!), neither `Region<R>` nor the payload of `Fail<...>` changes the generated code of `helper`!
For JS codegen, an effect row `E` in an instance key only has **one bit of information**: *does `E` contain any suspending effect (`Yield` or a user effect, or `Io` once the task scheduler is enabled)?*
Even better:
- **Erase all `region R` arguments** in instance keys to a single canonical region `R0` (just as `§11` step 2 already specifies for `comptime`: *"once per set of `comptime` arguments with their regions erased"*).
- **Erase `Fail<...>` payloads and `Region<R>`** from effect-row arguments in instance keys, reducing every concrete effect row in an instance key to a single `bool` (`suspends: bool`)!
That collapses all pure, `Fail`-only, and `Region`-only instantiations of `map<i32, i32, E>` into **one** JS function, and all suspending instantiations into **one** generator function `map*`!

**Trap B2: Structural record/union canonicalization in instance keys.**
In Flyscript's row unifier (`§3.2`), `{ x: i32; y: i32 }` and `{ y: i32; x: i32 }` are the **same type**, and `#A | #B` and `#B | #A` are the **same type** (and a closed union with an empty/solved row tail is the same as one without a tail).
When building the string/structural key for a monomorphized instance `(fnId, typeArgs)`:
- Always normalize types through `zonk` (following solved unification variables and stripping solved/empty row tails) and sort record fields and union tags by label!
- And in `record` literal codegen (`§3.2`: *"Physical layout is canonical (by alignment, then name)"*), emit structural record fields in **label-sorted order** so `Object.keys(r)` in `Show` / `Eq` is deterministic regardless of the order written at the construction site!

**Trap B3: Polymorphic recursion.**
Can a generic function call itself at a strictly larger type `f<T>(x)` -> `f<Box<T>>(Box.new(x))` without a nominal cycle?
In standard Flyscript (`§3.3`), recursive data types are nominal (`enum`/`struct`), so ordinary recursion over recursive types keeps `T` fixed. However, a user could write a pathological polymorphic-recursive function `function loop<T>(x: T): void { loop([x, x]); }`.
Put a depth/instance limit (e.g. `maxInstancesPerFn = 256` or nesting depth `64`) in the monomorphizer worklist so polymorphic recursion fails cleanly with a compile-time diagnostic instead of hanging the compiler.

---

#### 3. Question (C): Two generator pitfalls with runtime HOFs and nested `Yield` + user effects (`§5.2`, `§5.5`)

**Pitfall C1: Body-less runtime HOFs receiving generator closures.**
Look at `runtime.js` in the current backend:
- `Fail.capture(body)` and `Fail.map(body, wrap)` (`runtime.js:354`)
- `Option.map(o, f)` (`runtime.js:299`)
- `Vec.retain(a, keep)` and `slice.sortBy(a, cmp)` (`runtime.js:264`)
- `Gen.map`, `Gen.filter`, `Gen.find`, `Gen.some`, `Gen.every`, `Gen.reduce` (`runtime.js:279`)

Now trace what happens when the callback passed to `Fail.capture` or `Gen.some` has a suspending effect (e.g. `Clock`, `Log`, `Yield`, or `Io`):
```ts
effect Log { info(s: str): void; }

export function main(): void {
  const res = handle {
    // The closure has effect row `uses Fail<#Oops>, Log` -> compiled as a JS `function*`!
    Fail.capture(() => {
      Log.info("trying");
      if (true) { throw #Oops; }
      42
    })
  } with Log {
    info(_) resumes k => k(),
  };
}
```
If `Fail.capture` is a body-less JS runtime function:
```js
capture: (body) => { try { return { $tag: "Ok", $: body() }; } catch (e) { ... } }
```
When `body` is compiled as a `function*` because its effect row contains `Log`, calling `body()` inside `STATICS.Fail.capture` **does not run `body` at all** — it returns an unstepped JS `Generator` object as `{ $tag: "Ok", $: Generator }`!
And the exact same bug happens in `Option.map(o, f)`, `Gen.some(g, f)` (`§5.5` explicitly highlights: `params.iter().some((p) => occurs(v, p))` where `occurs` performs an effect!), `Gen.map`, `Gen.find`, `Gen.reduce`, etc.!

**Fix (clean, aligns with Law 5 / Goal 5 "A small core: features are library code"):**
Write **every effect-polymorphic HOF in Flyscript (`std/prelude.fly`) instead of `runtime.js`!**
Look at the list of HOFs in `std`:
1. `Fail.capture` and `Fail.map`: already 1-line Flyscript functions (`§5.4`: *"It is library code: `try { f() } catch (e) { throw wrap(e) }`"*).
2. `Option.map`: 1-line Flyscript (`match (self) { #Some(x) => #Some(f(x)), #None => #None }`).
3. `Gen` and all its methods (`next`, `map`, `filter`, `take`, `zip`, `enumerate`, `collect`, `find`, `findIndex`, `some`, `every`, `reduce`, `cloned`, `join`): `§5.5` **gives the exact Flyscript source for `Gen` and `generate`!**
4. `Vec.retain` and `slice.sortBy`: their signatures in `std` take *pure* callbacks (or if effect-polymorphic, writing `retain` and merge-sort `sortBy` in 15 lines of Flyscript in `std/prelude.fly` means the monomorphizer automatically generates the plain `function` version for pure callbacks and the `function*` (`yield*`) version for suspending callbacks!).

Once HOFs with `uses ...E` are ordinary Flyscript functions in `std/prelude.fly`, the monomorphizer specializes them for `suspends = false` and `suspends = true` automatically. **Zero runtime HOFs in `runtime.js` ever call a user closure!**

**Pitfall C2: Mixing bare `yield item` (for `Yield<T>`) with `yield { $eff, $op, $args }` (for `handle`).**
Suppose `yield e` in a generator emits bare `(yield v)` while user effects emit `(yield { $eff: "Clock", $op: "now", $args: [] })`, and `for (const x of gen())` uses JS `for (const x of gen())`.
What happens when a generator function uses **both** `Yield<T>` and another effect `Clock` (or `Io`, like `function rows(db: readonly Db, sql: str): void uses Io, Fail<DbErr>, Yield<Row>` in `§5.5`)?
```ts
effect Clock { now(): i64; }

function ticks(): void uses Yield<i64>, Clock {
  yield Clock.now();
  yield Clock.now() + 1;
}

export function main(): void {
  let sum: i64 = 0;
  handle {
    for (const x of ticks()) { sum += x; }
  } with Clock {
    now() resumes k => k(10),
  };
}
```
If `for (const x of ticks())` is compiled to JS `for (const x of ticks())`, then when `ticks()` performs `Clock.now()` via `yield { $eff: "Clock", ... }`, the JS `for…of` loop **intercepts the `Clock.now()` effect object as the yielded loop element `x`**, binds `x = { $eff: "Clock", ... }`, and adds it to `sum` instead of forwarding `Clock.now()` to the enclosing `handle ... with Clock`!

**Fix:**
**`Yield<T>` is an ordinary effect (`§0` Law 4, `§5.5`), so use the exact same `{ $eff, $op, $args }` yield protocol for `Yield<T>` as for every other effect!**
- `yield e` is simply performing `Yield.yield(e)`: it emits `yield { $eff: "Yield", $op: "yield", $args: [v] }` (or a dedicated fast tag `{ $yield: v }`).
- Only **intrinsic pure iterators** (`Array`, `Range`, `Bytes`, `HashMap.keys/values/entries`) are iterated with raw JS `for (const x of ...)`.
- A `for (const x of genCall())` over a `Yield<T>` function is literally a tail-resumptive handler for `Yield<T>` (`§5.5`), or steps `genCall()` via `$rt.forEachGen`: when `step.value` is `{ $eff: "Yield", $op: "yield", $args: [item] }`, it runs the loop body with `item` and resumes; when `step.value` is any other effect (`Clock`, `Io`), it `yield`s that effect outward (`const ans = yield step.value;`) and passes `ans` back into the generator!
- Better yet: once `Gen<T, E>` and `generate` are compiled from their 20-line Flyscript definition in `§5.5` using `handle { f(); #Done } with Yield<T> { yield(item) resumes k => ... }`, `Yield<T>` doesn't even need a second runtime mechanism — it is handled by `runHandle` just like `Clock`! (And for simple `for (const x of gen())` where `break`/`return` can exit early, wrap the loop in `try { ... } finally { it.return(); }` so `defer`s inside the generator run on `break` as required by `§5.5`!).

**Pitfall C3: One-shot continuation `Cont` representation (`§5.3`).**
You wrote in (3): *"A one-shot continuation kept first-class is the suspended generator."*
Be careful with **deep handlers** (`§5.3`: *"Handlers are deep: the handler stays installed beneath the suspended computation"*):
A first-class continuation `k` is **not** just the raw inner generator `it`; it is the **closure `(resumeVal) => runHandle(it, effName, arms, resumeVal, false)`** (wrapped with a single-use guard `used` and a `$drop()` method that calls `it.return()` if dropped unresumed). If `k` were just `it`, calling `k(v)` outside the `handle` block (as `Gen.next()` does!) would run `it` *without* the `Yield<T>` handler installed around it!

---

#### 4. Question (D): Ranked Order of Work to Maximize Corpus Pass Rate

Here is the concrete sequence that gets the maximum number of the 52 corpus tests passing at each milestone with zero throwaway code:

1. **Milestone 1: Monomorphizer + Typed Codegen for Values, Calls, Arithmetic, and `comptime` Derivations (~25 -> ~38/52 tests).**
   - Build the reachability monomorphizer from `main` (normalizing types, erasing regions, and reducing effect rows in keys to `suspends: bool`).
   - Emit direct calls `inst$42(...)` for all user/std functions and methods; replace `WRITEBACK` with uniform `Ref` (`{ v }` for mut-lent locals, `FieldRef`/`IndexRef` for mut-lent places).
   - Emit width-checked integer ops (`$rt.add(a, b, 32, true)`) and primitive float `===` vs derived `Eq.eq` (`NaN` == `NaN`).
   - Compile the checker's already-expanded `comptime` templates and derived impls (`Eq`, `Ord`, `Hash`, `Show`, `Clone`, `ToJson`, `FromJson`, `Soa`) as ordinary monomorphized instances, plus a tiny type-directed generator for structural record/union/tuple `Show`/`Eq`/`Ord`/`Hash`/`Clone` when no user impl applies.
   - *Result:* Every test in Groups 2 and 3 (types, integer overflow, generics, associated types, `comptime`, `std/json`, `Soa`, `par`) passes immediately.

2. **Milestone 2: Suspending Generators + `runHandle` for `handle`, `Yield`, and `Cont` (~38 -> ~44/52 tests).**
   - Mark any monomorphized instance (and closure) whose concrete effect row contains `Yield`, `Io`, or a user effect as `function*`, and emit `yield*` at call sites to suspending instances/closures.
   - Move `Fail.capture`, `Fail.map`, `Option.map`, `generate`, and `Gen` methods into Flyscript (`std/prelude.fly`) so they monomorphize over `...E`.
   - Implement the 30-line `runHandle(it, effId, arms, ...)` driver in `runtime.js` (supporting both abortive and resumptive arms, forwarding outer effects via `yield`, and unwinding via `it.return()`).
   - *Result:* All user effect handlers, dependency injection (`A.11`), coroutines, stored continuations (`Cont`), and complex `Yield` generators pass.

3. **Milestone 3: Cooperative `Io` / `SimIo` Fiber Scheduler over Generators (~44 -> ~49/52 tests).**
   - Because `Io` is already treated as a suspending effect from Milestone 2, `Io.scope`, `s.spawn`, `s.fork`, `f.join`, `channel`, `Mutex`, and `Io.sleep`/`Io.now` are just operations handled by a ~120-line root `Io` / `SimIo` fiber scheduler in `runtime.js` (a seeded priority queue of suspended generator fibers + virtual clock).
   - *Result:* All concurrency, channel, mutex, cancellation, and `SimIo` deterministic simulation tests pass.

4. **Milestone 4: Port `own.fly` + Drop Flags (`~49 -> 52/52 tests` + full spec compliance).**
   - Port `own.rs` to `own.fly` (needed both for compile-fail borrow/move diagnostics and for move/drop facts).
   - Emit drop flags (`let $drop_x = true;`) and `try ... finally { if ($drop_x) Drop$drop(x); }` **only** for bindings whose concrete monomorphized type transitively implements `Drop` (including `Cont` / `Gen`, whose drop calls `k.$drop()` -> `it.return()`).
   - *Result:* All `Drop` and generator/continuation cleanup tests pass, and `selfhost` reaches 100% parity with the Rust reference compiler.

---

### Smaller points

- **`Copy` read out of a place (Item 2 in your proposal):**
  You wrote: *"A `Copy` value read out of a place into a new owner is copied iff its type is `Copy` and is a JS object."*
  Make sure "into a new owner" includes **passing a `Copy` place by value as a function argument** (or copy value parameters of `Copy` JS-object type at function entry if the parameter is ever mutated or lent `mut`), and includes **fixed-size arrays `T[N]`** (`§3.1`: `T[N]` is `Copy` if `T` is, and is represented as a JS Array, so `$rt.copy` must clone fixed arrays too, not just plain objects!).
- **`HashMap` / `HashSet` keys with custom `Eq` and `Hash` (`runtime.js:126`):**
  In the current `runtime.js`, `HashMap` keys use `keyOf(k)` which calls `show(k)`! In the typed backend, a type `K` may implement custom `Eq` and `Hash` without implementing `Show` (or where two equal keys have different internal fields, like a case-insensitive string or a float `-0.0` vs `0.0`).
  In the typed backend, `HashMap.insert/get/has/remove` have `K`'s concrete monomorphized `Hash.hash` and `Eq.eq` functions: bucket the JS `Map` by the `u64` hash (`BigInt` key in `this.m`, mapping to a small bucket array `[[k, v], ...]`) and compare keys in the bucket with `K`'s `Eq.eq` (or for lent lookups `Q` where `K` lends `Q`, e.g. `String` / `Ref<R, str>` looked up by `str`, `str`'s `Hash` and `Eq` are identical by `§3.5`). That is 15 lines in `runtime.js` and makes `HashMap` 100% faithful to `§3.5`.
