I wrote eight real programs against v1.3 (a JSON parser, a CLI word count, a generator pipeline, a particle game loop, a compiler symbol table in a region, a key-value actor, a web server accept loop, and a browser UI in the Elm style). The core held up: the UI and the actor were beautiful, and `par` over `Soa` reads perfectly. But they exposed three serious problems and a lot of duplication. Here are the findings and the decisions for **v1.4**. Push back on any decision you think is wrong, with a concrete program.

## Serious problems

**A. Regions are unsound and break the Shared-Mutation Law.** `In<R, T>` is `Copy` *and* mutable through any copy, which is shared mutable aliasing:
```ts
const a = s; const b = s;
const first = a.names[0];      // borrow into a's Vec storage
b.names.push(x);               // reallocates through the other alias
use(first);                    // stale or dangling
```
Same with enum fields: borrow `a.kind`'s `Num(f64)` payload, overwrite `b.kind = Str(...)` through the alias, read garbage. And a `uses []` function holding `readonly In<R, T>` can mutate the region through a copy, which violates Law 2.

**B. Pull iteration is impossible.** `zip`, `merge`, `iter.next()` and parser combinators over token streams can't be written, because a suspended generator can't be held as a value (`k` may not outlive its handler arm).

**C. The most common concurrent program doesn't typecheck.** In `for (const conn of listener.accept()) { s.spawn(() => handle(mut conn, db)); }`, `conn` must be *moved* into the task, but `spawn` only accepts shared closures.

## Decisions for v1.4

1. **Regions are an append-only immutable heap; `Cell` is the only mutable slot; writing is an effect.** (This is how production arenas such as rustc's work.)
   - Rename `In<R, T>` to **`Ref<R, T>`**: `Copy`, points to **immutable** data. Reading a field is pure. Immutable region data (fields, `str`, slices) may be borrowed `readonly` freely.
   - Mutation inside a region happens only through **`Cell<T>`** (with `T extends Copy`: get copies out, set writes in, never borrowed) and **`RegionList<T, R>`** (append-only: existing elements never move). Both `set` and `push` perform the **`Region<R>`** effect.
   - **`Region<R>` replaces `Alloc<R>`:** it covers allocation and writes. `region (R) { ... }` is its handler.
   - **Heap allocation is not an effect at all** (it's unobservable), so the `Alloc<Heap>` ambient-effect asymmetry disappears.
   - `Ref<R, T>` is shareable with child fibers iff `T` contains no `Cell`/`RegionList` (it's then deeply immutable). Handlers are **fiber-local**, so a spawned task can never perform `Region<R>`. This deletes the special "region frozen during `Async.scope`" rule.
   - Check that this restores Law 2 everywhere, and that it fixes both aliasing examples above.

2. **Continuations are first-class affine values.** A resumptive arm's `k` is an ordinary affine value that may be stored, moved and returned. By the propagation rule it is second-class iff its suspended frame holds borrows. This gives:
   - **`Gen<T>`**: `generate(() => body)` handles `Yield<T>` into a value with `g.next(): Option<T>`, so `zip`, `merge`, `peekable` and parser combinators become library code.
   - **`Fiber<T>`**: a spawned task is the same kind of object (a suspended computation), scheduled by `Io`. One concept: **suspended computation**, consumed by `next()` (generator) or `join()` (fiber).
   - State the one-shot and drop rules for stored continuations (dropping one unwinds its frame).

3. **`spawn` takes `once` closures** whose captures are owned `T extends Send` values (moved in) or `readonly T` with `T extends Send`. Show the accept loop.

4. **Four standard effects: `Fail<E>`, `Io`, `Yield<T>`, `Region<R>`.** Merge `Shared` into `Io`: every synchronization (locks, atomics, channels) is a scheduling point the deterministic simulator must control anyway, and `Shared`'s placeholder op (`synchronize()`) shows it was never a real effect. Keep a single `scope` (delete the `Async.scope`/`Io.runScope` duplication).

5. **One sum type and one product type, with structural rows underneath.**
   - `#Tag` syntax everywhere. `enum Json<R> { #Null, #Bool(bool), #Arr(Vec<Json<R>, R>), ... }` declares a **nominal name for a closed variant row**, and `struct Point { x: f64; y: f64 }` declares a **nominal name for a record row**. Construction, matching and row machinery are identical for named and anonymous types; nominal declarations only add identity, privacy, `Drop` and layout.
   - **Recursive types only through nominal names** (iso-recursive), so the row unifier never needs equi-recursive types.

6. **Data and behavior separate.** `struct`/`enum` bodies contain only data. Methods go in `impl T { }`, interface implementations in `impl I for T { }`. Delete inline `implements`. (Structural records can't have methods anyway, so this makes nominal and structural types uniform.) Add **associated types** to interfaces formally (`ParSplit.ItemView` already relies on them, but they're in neither the grammar nor the interface section).

7. **One handler-arm form plus `defer`.** Arms are `op(args) => body` (abortive) or `op(args) resumes k => body` (resumptive). Delete the `return(v)` arm and the `finally` arm: across eight programs I never needed `return`, and `finally` duplicates `Drop`. Add a `defer expr;` statement (runs at scope exit in LIFO order with destructors).

8. **Pointers organized by one principle**, presented as a small table:
   - unique: `Box<T, R>`
   - shared within a region (immutable plus `Cell`): `Ref<R, T>`
   - shared across threads (immutable): `Arc<T>`
   - `Pool`/`Handle` are library code, not primitives.

9. **Smaller fixes found by the programs:**
   - **Region inference:** region variables are unification variables solved over the function body (still purely type-directed); unconstrained means `Heap`. This removes the annotation in `let items: Vec<Json<R>, R> = Vec.new()` when `items` is returned as `Json<R>`.
   - **Derived structural interfaces:** `Eq`, `Hash`, `Show` and `Clone` are derived automatically for records and variant rows via `comptime` reflection, so `match` errors print and tags hash.
   - **Borrowed lookup:** `HashMap<String, V>.get(key: str)` via a `Borrow`-style interface. Specify it.
   - **`parMap`/`parReduce`** with an associative combiner, since `par` bodies are pure and can't accumulate.
   - **`Soa<T>` flattens nested records** recursively (`pos.x` becomes its own plane).
   - **`const`:** explain that with affine ownership there's no aliasing, so "deep" and "shallow" immutability coincide for owned values. It's a consequence, not a difference from TS.

## Output

**v1.4**, complete and self-contained (every v1.3 section, updated). Then an **appendix with all eight programs rewritten in v1.4**, each 20–50 lines, written as idiomatic code. For each, note anything that still felt awkward. Update the concept-count table (v1.0 vs v1.4) and the five laws. The bar: fewer concepts than v1.3, and every one of the eight programs reads like something you'd want to write.

Here are the v1.3 sketches of the three that broke, for reference:
```ts
// B: zip, impossible in v1.3
function zip<A, B>(a: () => void uses Yield<A>, b: () => void uses Yield<B>): void uses Yield<[A, B]> { ??? }

// C: accept loop, rejected in v1.3
export function serve(listener: mut Listener, db: readonly DbClient): void uses Io {
  Async.scope((s) => { for (const conn of listener.accept()) { s.spawn(() => handleConnection(mut conn, db)); } });
}

// A: symbol table in a region, unsound in v1.3
struct Scope<region R> { parent: Option<In<R, Scope<R>>>; names: Vec<{ name: In<R, str>; decl: In<R, Decl<R>> }, R>; }
```
