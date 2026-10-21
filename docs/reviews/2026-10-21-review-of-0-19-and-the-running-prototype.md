# Review: review of 0.19 and the running prototype

- spec: 9d21ceea5286
- request: ef3d490e063cf092
- tokens: prompt 35650, cached 0, answer 9605

## Question

This is a follow-up to your holistic review of 0.18 (included as an earlier exchange). The specification is now 0.19, which adopted every point from that review except cutting `.d.fly` (the alternatives each needed a new keyword or a standard-library privilege, and `.d.ts` is familiar to the audience): outer regions frozen during `Io.scope` (every `Ref` is `Send`), `k.resume()` using every binding the body and arms use, `from` lists with method/function defaults, `view struct`, escaping closures capturing by move, region handles, iteration chains on `Gen`, `Fail.map`, module constants, `interface … extends`, and `private` fields.

The prototype now implements all of it except code generation and `comptime` evaluation, and **runs** programs: a direct-style evaluator with effect handlers (abortive arms unwind; tail-resumptive arms run at the perform site; a `Gen` pulled with `next()` runs on its own thread), against a deterministic world with a seeded fault schedule. Nine programs run with checked output, including the HTTP server under injected faults (same seed, same run). 13 extra programs check and 40 incorrect ones are rejected with the intended errors.

Please review 0.19 as a whole:

1. **Did 0.19 fix the problems you raised correctly?** For each of the five weak points and the learnability and week-one items, say whether the fix is sound and complete, or what remains, with a program.
2. **New soundness holes**, especially from the interaction of the new rules: `from` defaults with hidden-borrow parameters; escaping closures capturing by move combined with `once`/`mut` modes; frozen outer regions with nested scopes and generators (a `Gen` created outside a scope, pulled inside a task?); `view` types inside generics (`Vec<Scanner>`); private fields and structural records.
3. **Is it now a high-quality language?** Be direct: what would stop you recommending it (as a design) to a team writing a networked service in TypeScript today, and what is the single most valuable next change?

## Answer

### Verdicts

- **Frozen outer regions during `Io.scope` (`§4.4`, `§6.1`)**: **Agree with changes.** Sound for direct calls inside `Io.scope`, and `Gen<T, E>` carries `Region<R>` in `E`, so a generator over a region cannot be pulled in a task. **One hole remains:** `RegionList` and `Cell` are now `Copy` and `Send` (`§4.4`, `§4.6`), so a `RegionList<R, T>` can be captured by a task and iterated via `Iterable.each` (which is pure — no `Region<R>` effect!) while another task — or a nested region/handler — races, or worse: a `Gen` or `Cont` whose `E` hides `Region<R>` via a handler, or `Io.start` (the raw effect operation in `§5.1`) which bypasses `Io.scope`'s `row E extends Send` check completely!
- **`k.resume()` re-entry rule (`§5.3`)**: **Agree.** Sound and complete for single-handler re-entry.
- **`from` defaults and hidden-borrow sources (`§4.2`)**: **Agree with changes.** Making closures, generators, and type parameters automatic sources when `from` is omitted is smart, **but** when an explicit `from` clause is written (`function f<T>(x: str, y: T): T from x`), allowing a function to omit a type-parameter or closure argument from an explicit `from` list lets a hidden borrow in `T` escape untied.
- **`view struct` / `view enum` (`§3.3`, `§4.2`)**: **Agree with changes.** Clean at the declaration site, but `§3.3` does not forbid instantiating a class-1 generic container with a class-2 type (`Vec<Scanner>`, `Box<str>`, `Arc<readonly i32>`), and `§4.2` says *"Every other type takes the maximum class of its components: fields, payloads and type arguments"*, which silently turns `Vec<Scanner>` into a legal class-2 value instead of rejecting the store into the heap container!
- **Escaping closures capturing by move (`§4.3`)**: **Disagree as stated; agree with changes.** Two serious problems: (1) an escaping `(A) => B` closure that captures an owned non-`Copy` value (`String`) and can be called **concurrently** (`§4.3` table: *"any number of times, concurrently"*) without `T extends Send` creates a data race on non-`Send` owned state; and (2) an escaping closure that captures a `let` binding by move silently diverges from TypeScript's shared-variable semantics if the outer function also uses the binding after creating the closure, or is ambiguous about *when* the move happens.
- **Region handles (`Cell`, `RegionList`), iteration chains, `Fail.map`, `const`, `interface extends`, `private` fields (`§3.3`, `§3.4`, `§4.6`, `§5.4`, `§5.5`)**: **Agree with changes.** One soundness hole in `private` fields (`§2.2` record literals and pattern matching bypass `private` unless checked), and one ownership hole in `Gen` iteration chains (`xs.iter().map(f)` where `f` captures a borrow).
- **Overall readiness (`Question 3`)**: **Yes, the core design is now coherent, small, and genuinely compelling.** Once the five interaction bugs below are closed, the single highest-leverage next step is **completing `comptime` and derived interfaces (`§3.5`, `§7.1`)** so JSON/wire serialization (`Serde`) works out of the box.

---

### Problems

#### 1. `Io.start` and custom `Io` handlers bypass `Io.scope`'s frozen-region rule (`§4.4`, `§4.6`, `§5.1`, `§6.1`)

`§5.1` exposes `start` as an ordinary operation of `effect Io`:
```ts
effect Io {
  ...
  start(task: once () => void uses Io): TaskId; // the primitive under Io.scope (§6.1)
}
```
And `§4.4` / `§4.6` now state that **every** `Ref<R, T>`, `Cell<R, T>`, and `RegionList<R, T>` is class 1 and `Send`!
Why did 0.19 make `RegionList<R, T>` and `Cell<R, T>` unconditionally `Send`? Because `§6.1` Rule 5 says:
> *"The body of a scope runs on the parent's fiber, but its effects must be `Send` — a row is `Send` when it contains no `Region` — so it cannot write to a region outside the scope while tasks may be reading it."*

Look at what happens when code calls `Io.start` directly (or uses `SimIo` / a custom handler, or spawns a task that outlives a region, or calls `Io.start` while holding `Region<R>`):

```ts
import { RegionList } from "std/region";

function raceAndUaf(): void uses Io {
  region (R) {
    const list = RegionList.new<R, i32>();
    list.push(1);

    // `list` is `RegionList<R, i32>`: class 1, Copy, and Send (§4.4, §4.6)!
    // `list.each()` is pure (`uses Yield<readonly i32>`), NOT `uses Region<R>`!
    // And `Io.start` is an operation of `effect Io` (§5.1): it does NOT freeze `Region<R>`!
    Io.start(() => {
      for (const x of list) {          // reads `list` on another thread/fiber...
        Io.sleep(Duration.ms(10));
        println(`${x}`);
      }
    });

    // 1. DATA RACE: Parent fiber still has `Region<R>` in scope and mutates `list` concurrently!
    list.push(2);
  }
  // 2. USE-AFTER-FREE: `region (R)` exits and frees the arena while the `Io.start` task is still running!
}
```
Even if you make `Io.start` private to `std/io`, look at **Problem 1b** using only `Io.scope` and `Cont` (`§5.3`):
```ts
import { RegionList } from "std/region";

effect Step { pause(): void; }

function scopeBypassViaCont(): void uses Io {
  region (R) {
    const list = RegionList.new<R, i32>();
    list.push(1);

    // Create a continuation `k` outside `Io.scope` that mutates `list` (uses Region<R>),
    // or hide `Region<R>` inside a resumptive handler around `Io.scope`!
    handle {
      Io.scope((s) => {
        // Inside `Io.scope`, the body's effect is `Io, Step` — which contains NO `Region`!
        // So `E = [Step]` satisfies `row E extends Send`!
        const f = s.fork(() => {
          let sum = 0;
          for (const x of list) { sum += x; } // reads `list` on worker thread!
          sum
        });
        Step.pause(); // suspends to the outer handler while `f` is running concurrently!
        f.join();
      });
    } with Step {
      pause() resumes k => {
        // We are now outside `Io.scope`'s body check, in `region (R)`, WHILE task `f` is running!
        list.push(2); // DATA RACE with `for (const x of list)` in task `f`!
        k.resume();
      }
    }
  }
}
```
Look at what `scopeBypassViaCont` does:
1. Inside `Io.scope`, the body performs `Step.pause()`. `Step` is not a `Region` effect, so `row E = [Step]` satisfies `row E extends Send` (`§6.1`).
2. `Step.pause()` suspends the scope body to the outer `with Step` handler **while the forked task `f` is actively running on another worker thread**.
3. The `pause() resumes k =>` arm is outside `Io.scope` and inside `region (R)`, so it legally calls `list.push(2)` (`uses Region<R>`) **while `f` is concurrently reading `list`!**

**Fix:**
1. **`Io.start` must not be a public safe operation in `effect Io`.** Either remove `start` from the public `Io` effect interface (making `Io.scope` the effect operation or marking `Io.start` internal to `std`), because raw `Io.start` allows unscoped tasks that outlive `region (R)` and borrowed captures (`§6.1` Rule 6).
2. **`Io.scope`'s body cannot suspend across `Io.scope` to an outer handler (`E` in `Io.scope` cannot contain unhandled user effects, or `Io.scope` only allows `Fail<X>`):**
   Look at `§6.1` Rule 4: *"A task runs on a new fiber, where the only handlers are the runtime's `Io` and the scope's capture of failures."*
   Why does `Io.scope`'s body even have `, row E extends Send` in `function scope<T, X, row E extends Send>(body: once (s: mut Scope<X>) => T uses Io, ...E): T uses Io, Fail<X>, ...E`?
   If `Io.scope` is a concurrency barrier that blocks the parent fiber until all child tasks complete, allowing the parent fiber inside `Io.scope` to yield/suspend to an **outer** resumptive handler (`Step.pause()` or `Yield.yield()`) while child tasks are running in the background means:
   - the parent fiber can run outer handler arms that mutate `Region<R>` while child tasks read `R` (the data race above); and
   - if the outer handler **drops `k`** (e.g., `for (const x of genThatUsesScope) { break; }` or an abortive handler around `Io.scope`), it unwinds `k` while child fibers are running!
   **Fix:** Remove `row E` from `Io.scope`! The body of `Io.scope` should have effects `uses Io, Fail<X>` (just like `fork` tasks). Anything the scope body wants to do with `Yield` or `Region` can either be handled *inside* the scope body or after `Io.scope` returns. Removing `row E` from `Io.scope` simplifies `Io.scope`'s signature to:
   ```ts
   function scope<T, X>(body: once (s: mut Scope<X>) => T uses Io, Fail<X>): T uses Io, Fail<X>;
   ```
   and **completely closes** the handler-suspension race on outer regions!

---

#### 2. Class-1 containers instantiated with Class-2 (`view` or borrow) type arguments (`§3.3`, `§4.2`)

`§3.3` says:
> *"A struct or enum that holds a borrow (§4.2) must say so: `view struct Scanner { src: readonly u8[]; pos: usize; }`. A view is a temporary lens on someone else's data; it can be a local or a parameter but never stored or returned untied."*

And `§4.2` says:
> *"- `readonly T`, `mut T`, `str` and `T[]` are class 2.*
> *- Every other type takes the maximum class of its components: fields, payloads and type arguments, structural or nominal alike. `Option<mut u64>` is class 2; so is `view struct Scanner { src: readonly u8[]; pos: usize; }`."*
> *"A class-2 value may be a parameter, a local, or a return value tied to a parameter. It may not be stored in a class-1 value..."*

Look at what happens when you instantiate `Vec<T>`, `Box<T>`, or `HashMap<K, V>` with `T = str`, `T = mut i32`, or `T = Scanner`:
```ts
function badVecOfBorrows(): void {
  let x = 1;
  let y = 2;
  // What is the class of `Vec<mut i32>`?
  // By §4.2, a nominal type takes the maximum class of its type arguments!
  // So `Vec<mut i32>` has class = max(class(mut i32)) = 2!
  // Because `v` itself is now considered a "class-2 local", storing `mut x` into `v`
  // is storing a class-2 value into a CLASS-2 value (`v`), NOT a class-1 value!
  let v = Vec.new<mut i32>();
  v.push(mut x); // `v.push` takes `self: mut Vec<mut i32>, val: mut i32` -> returns `void`!
  v.push(mut y);
  // Look at `v.push(mut x)`: `v.push` returns `void` (which cannot hold a borrow, §4.2)!
  // So by §4.2 ("A borrow taken for an argument is held by the call's result if the result can hold it"),
  // the borrow `mut x` ENDS immediately when `v.push(mut x)` returns!
  x = 99;        // UNSOUND: `x` is no longer locked, even though `v[0]` holds `mut x`!
  const p = v.pop(); // `p` is `#Some(mut x)` — two mutable aliases to `x`!
}
```
Read that trace carefully!
1. `Vec<T>` is an owning heap container whose `push(self: mut Self, item: T): void` mutates `self` in place and returns **`void`**.
2. Because `push` returns `void`, the borrow tracker rule in `§4.2` (*"A call's result can hold the borrows of its sources... A result whose type cannot hold a borrow at all holds nothing"*) transfers the borrow of `mut x` to the **return value** (`void`), NOT into the `self` receiver `v`!
3. Even if `v` held the borrow, `Vec.pop()` or overwriting `v[0]` or `Vec`'s `Drop` cannot track element-wise lifetimes, and a non-`view` struct `Vec<T>` was never meant to hold class-2 elements in heap memory!

Why did `Option<mut u64>` and `[str, str]` work, while `Vec<mut u64>` and `Box<Scanner>` break?
Because `Option<T>` and tuples/records are **constructed by value** (where the constructed expression is the result of the expression and carries the union of its component borrows), whereas `Vec<T>`, `HashMap<K, V>`, `Channel<T>`, `Cell<R, T>`, `RegionList<R, T>` are **heap/region containers mutated through `&mut self` methods returning `void`**!
Wait: what if someone writes a user function that mutates a class-2 local through a `mut` parameter?
```ts
function stuffIntoOption(slot: mut Option<mut i32>, val: mut i32): void {
  slot = #Some(val); // stores `val`'s borrow into `slot` through a `mut` parameter, returns `void`!
}

function exploitOption(): void {
  let x = 1;
  let y = 2;
  let slot: Option<mut i32> = #None;
  stuffIntoOption(mut slot, mut x); // returns `void`! Does `slot` now hold the borrow of `x`?!
  x = 10;                           // UNSOUND if `stuffIntoOption` didn't transfer `val`'s borrow into `slot`!
}
```
Look at `exploitOption`! That is a fundamental soundness hole in `§4.2` even *without* `Vec<T>`:
- In `exploitOption`, `slot` has type `Option<mut i32>` (which is a legal class-2 local).
- `stuffIntoOption(mut slot, mut x)` takes `slot: mut Option<mut i32>` and `val: mut i32` and returns `void`.
- Inside `stuffIntoOption`, `slot = #Some(val)` writes the class-2 value `val` into the `mut` borrow `slot`!
- At the call site `stuffIntoOption(mut slot, mut x)`, the return type is `void`, so after the call returns, the borrow of `x` is released, while `slot` now holds `mut x`!

**Fix (two small, crisp rules that close both holes at once):**
1. **No writing class-2 values through a `mut` borrow (`mut T` where `T` is class 2):** A `mut` borrow of a class-2 type (`mut Option<str>`, `mut Scanner`) may mutate its class-1 fields (`sc.pos += 1` in `A.1`, where `sc.pos: usize` is class 1!), **never** assign a new class-2 value into a dereferenced `mut` parameter or field (`sc.src = otherSlice` or `slot = #Some(val)` where `slot` is a `mut` parameter). A local `let s: str = a; s = b;` is direct assignment to a local binding (whose borrow set `B(s)` unions `a` and `b`), whereas writing a class-2 value through a `mut` pointer/reference parameter would require flow-sensitive lifetime outlives constraints (`'val : 'slot`) — which is the exact reason Rust needs multiple lifetime parameters! Forbidding assignment of class-2 values into `mut`-borrowed places (`*p = class2_val`) keeps `sc.pos += 1` in `A.1` 100% legal while making `stuffIntoOption` impossible.
2. **Type parameters on non-`view` types and functions are class 1:** A type parameter `T` (unless on `Option`, `Result`, tuples, or a `view struct` / `view enum`) only ranges over **class-1** types! Specifically, `Vec<T>`, `Box<T>`, `HashMap<K, V>`, `Arc<T>`, `Channel<T>` are not declared `view`, so instantiating `Vec<Scanner>` or `Vec<str>` or `Vec<mut i32>` is rejected immediately at the type argument, with the same helpful diagnostic as `§3.3` (`use Vec<String> instead of Vec<str>`). Only `view` types, structural records/tuples/unions (including `Option<T>` and `Result<T, E>`), and functions may be instantiated with class-2 type arguments.

---

#### 3. Explicit `from` clauses can drop hidden borrows in type parameters and closures (`§4.2`)

`§4.2` says:
> **Results carry their sources' borrows.** A call's result can hold the borrows of its *sources*: the parameters named in its `from` clause; without one, the receiver for a method and every borrowed argument for a free function. Arguments whose types can hide a borrow — closures, generators, type parameters — are always sources.

Read those two sentences together:
- Sentence 1: *"the parameters named in its `from` clause; without one, the receiver for a method and every borrowed argument for a free function."*
- Sentence 2: *"Arguments whose types can hide a borrow — closures, generators, type parameters — are always sources."*

Wait: what if a function **has** an explicit `from` clause, or is a **method** (where the default source is *only* `self`, not the other arguments!), and also takes a closure, generator, or type parameter `T`?
Look at the method case first:
```ts
struct Builder { prefix: String; }

impl Builder {
  // Method with no `from` clause: by §4.2, default source is `self` (`Builder`, class 1).
  // What about `item: T`? Sentence 2 says "Arguments whose types can hide a borrow —
  // closures, generators, type parameters — are always sources."
  // Wait: what if the author writes an explicit `from self`?
  function wrap<T>(self: readonly Self, item: T): [str, T] from self {
    [self.prefix, item]
  }
}

function launderBorrow(): void {
  let b = Builder { prefix: "hi".toString() };
  let v = Vec.new<i32>();
  v.push(1);
  const slice: readonly i32[] = v[0..1]; // borrows `v`
  // If `from self` overrides `item: T` being a source, `res` only borrows `b`, NOT `v`!
  const res = b.wrap(slice);
  v.push(2);                             // UNSOUND if `res` forgot its borrow of `v`!
  println(`${res[1][0]}`);
}
```
And what if inside `wrap`, the body checker checks:
> *"The body is checked against the same rule: everything the returned value borrows must come from a source, never from a local."*

Inside `wrap<T>(self: readonly Self, item: T): [str, T] from self`:
When `wrap` is type-checked generically, what is the borrow set of the parameter `item: T`?
Inside `wrap`'s definition, `T` is an abstract type parameter! Does `item: T` have a non-empty borrow set inside `wrap`?
If `item: T` has an **empty** borrow set when checking `wrap`'s body (because `T` is not syntactically `readonly U` or `mut U`), then `wrap`'s body `[self.prefix, item]` appears to only borrow `self`! So `wrap`'s body passes the `from self` check!
And then at the call site `b.wrap(slice)`, if the caller trusts the explicit `from self` annotation and ignores `slice`, the borrow of `v` in `slice` is laundered and erased!

**Fix:**
State unconditionally in `§4.2`:
1. In the body of a generic function, every parameter `p` whose type is (or contains) a type parameter, closure, `Cont`, or `Gen` is seeded with a distinct abstract loan `loan(p)`.
2. Therefore, if the return value can hold `p` (e.g. returns `T` or wraps `p` into a `Gen` or closure), `loan(p)` will be present in the returned value's borrow set, so an explicit `from` clause that omits `p` will be **rejected when checking the function body**!
3. And as already intended by Sentence 2, make it explicit that arguments whose types can hide a borrow (closures, continuations, generators, type parameters) are sources **unless excluded by an explicit `from` clause (which the body check in (1)–(2) verifies)**.

---

#### 4. Escaping closures (`§4.3`) vs. `Send` and shared concurrency

`§4.3` says:
> *"A closure that escapes — returned, stored in a first-class value, or handed to a task — instead takes ownership of what it captures, by move, so it holds no borrows. Its mode follows from what its body does when called:*
> *`(A) => B` | only reads its captures | any number of times, concurrently"*

And `§4.4` says:
> *"`T` is `Send` when it is class 1 and owns no raw pointer."*

Look at what happens when an escaping closure `(A) => B` captures a **non-`Send`** class-1 value (one that owns a raw pointer `T*`, e.g. a foreign handle or custom allocator struct) OR when an escaping closure is shared across tasks:
Wait: is `(A) => B` itself a class-1 type when it escapes?
Yes! By `§4.3`, an escaping closure captures by move and holds no borrows, so it is **class 1**.
And by `§4.4`: *"T is `Send` when it is class 1 and owns no raw pointer."*
How does the compiler know whether an arbitrary value `f` of function type `(A) => B` owns a raw pointer in its hidden closure environment?!
```ts
struct ForeignDb { ptr: u8*; } // Class 1, NOT Send (owns raw pointer `u8*`, §4.4 & §8.2)

function makeQuery(db: ForeignDb): (str) => i32 {
  // Escaping closure captures `db: ForeignDb` by move!
  // It only reads `db`, so its type is `(str) => i32`.
  // Notice: the type `(str) => i32` does NOT mention `ForeignDb` or `u8*`!
  return (sql: str) => unsafe { (db.ptr).read() as i32 };
}

function sendNonSendAcrossThreads(db: ForeignDb): void uses Io {
  const query: (str) => i32 = makeQuery(db);
  // Is `query: (str) => i32` Send?!
  // Its surface type `(str) => i32` is class 1 and shows no `T*`!
  Io.scope((s) => {
    const f1 = s.fork(() => query("a")); // Sent to thread 1!
    const f2 = s.fork(() => query("b")); // Sent to thread 2!
    f1.join();
    f2.join();
  });
}
```
Look at `makeQuery`:
1. `ForeignDb` owns `u8*`, so `ForeignDb` is **not `Send`** (`§4.4`, `§8.2`).
2. `makeQuery` captures `db` by move into an escaping closure and returns it as type `(str) => i32`.
3. Once erased behind the function type `(str) => i32` (or `once () => void` or `Cont<A, B, E>`), the type no longer reveals that the closure's environment contains a `ForeignDb` (`u8*`)!
4. Then `sendNonSendAcrossThreads` sends `query` into `s.fork`, moving/sharing a non-`Send` `ForeignDb` across threads!

And there is a second issue with escaping closures in `§4.3`:
What is the **`Drop`** and **`Copy`** behavior of a first-class closure `(A) => B` that captured a `String` by move?
```ts
function makeGreeter(prefix: String): (str) => String {
  return (name: str) => `${prefix}, ${name}`; // owns `prefix: String`!
}

function copyClosure(): void {
  const g = makeGreeter("hello".toString());
  const g2 = g; // Is `(str) => String` Copy or affine?!
  // If `(str) => String` is NOT Copy, it moves on `const g2 = g`, and runs Drop on `prefix` when `g2` dies!
  // If `(str) => String` IS Copy, `const g2 = g` duplicates `String` without cloning — double free!
}
```
This is a classic systems-language design point (without a GC):
- If a closure `(str) => String` can own a `String` by move, then at runtime a value of type `(str) => String` is an owned fat pointer + drop glue (like `Box<dyn Fn(str) -> String>` in Rust), so `(A) => B` is **not `Copy`** (it is an affine owned value with a destructor that drops `prefix`), and an escaping closure must require its moved captures to be **`Send`** so that `(A) => B` is always `Send`!

**Fix:**
Add one sentence to `§4.3` / `§4.4`:
- **Function types `(A) => B`, `mut (A) => B`, `once (A) => B` are affine (not `Copy`; they may be borrowed `readonly` or `mut` like any other owned value, and dropped when their owner goes out of scope), and an escaping closure (or `Cont`) may only capture `Send` values by move, so every first-class closure is `Send`.**
Look how cleanly that works:
- In `Io.scope`, `s.fork(() => query("a"))` and `s.fork(() => query("b"))` borrow `query` as `readonly` across the two tasks (which is legal because `query` is `(str) => i32` and `Send`!).
- When `query` goes out of scope at the end of `sendNonSendAcrossThreads`, its environment (e.g. `prefix: String`) is dropped once.
- And `makeQuery(db: ForeignDb)` is rejected at the closure creation site because `ForeignDb` is not `Send`.

---

#### 5. `private` struct fields can be bypassed by record literals and destructuring (`§2.2`, `§3.3`)

`§3.3` adds `private` fields:
> *"Fields are public, as in TypeScript, unless marked `private`, which limits them to the declaring module."*

And `§2.2` / `§3.3` say:
> *"Record literals. `{ f: e, … }` builds the nominal struct named by the expected type, if there is one, and a structural record otherwise. `Point { … }` names the struct explicitly."*
> *"Construction and matching are identical to the structural forms."*

Look at what happens across module boundaries when a struct has a `private` field that maintains a safety or representation invariant:
```ts
// module a.fly
export struct NonZero {
  private val: i32;
}

// module b.fly
import { NonZero } from "./a";

export function bypassPrivate(): i32 {
  // 1. Explicit construction outside module `a`:
  const bad1 = NonZero { val: 0 };

  // 2. Implicit construction via expected type (§2.2) outside module `a`:
  const bad2: NonZero = { val: 0 };

  // 3. Pattern matching / destructuring outside module `a`:
  match (bad1) {
    { val } => val, // reads private field `val`!
  }
}
```
**Fix:**
State explicitly in `§3.3`: a `private` field may only be read, written, constructed (via `Name { ... }` or expected-type `{ ... }`), or matched in the module that declares the `struct`. Outside that module, the struct cannot be constructed by a literal or destructured by field patterns (or only its public fields may be matched with `{ pubField, ... }`).

---

#### 6. Iteration adaptors (`Gen.map`, `Gen.filter`) with borrow-capturing closures (`§4.2`, `§5.5`)

`§5.5` introduces iteration chains on `Gen`:
```ts
const firstEvens = xs.iter().filter((x) => x % 2 == 0).take(10).collect();
```
And `§4.2` says:
> *"A call's result can hold the borrows of its sources: the parameters named in its `from` clause; without one, the receiver for a method and every borrowed argument for a free function. Arguments whose types can hide a borrow — closures, generators, type parameters — are always sources."*

Now consider an iteration chain where the closure passed to `.filter(...)` or `.map(...)` captures a borrow of a **second** local variable ` banned`:
```ts
function filterWithCapturedBorrow(): void {
  let xs = Vec.new<i32>();
  xs.push(1);
  let banned = Vec.new<i32>();
  banned.push(1);

  // `.filter` is a method on `Gen` that takes a closure `(x) => !banned.contains(x)`
  // and returns a new `Gen<i32, []>`.
  // The closure captures a `readonly` borrow of `banned` (class 2)!
  let g = xs.iter().filter((x) => !banned.contains(x));

  // Question 1: Does `filter` accept a class-2 (borrow-capturing) closure?
  // Inside `Gen.filter(self: Self, pred: (readonly T) => bool): Gen<T, E>`,
  // `pred` is stored inside the returned `Gen`'s continuation frame!
  // Question 2: Is `banned` locked while `g` is live?
  banned.push(2); // MUST BE REJECTED while `g` is live!
  const out = g.collect();
}
```
Check how your two rules (`§4.2` and `§4.3`) interact here:
1. By `§4.3`: *"A closure that escapes — returned, stored in a first-class value, or handed to a task — instead takes ownership of what it captures, by move, so it holds no borrows."*
2. Wait: in `xs.iter().filter((x) => !banned.contains(x))`, does the closure passed to `.filter(...)` **escape** into the returned `Gen`?!
   - If the compiler treats the closure passed to `Gen.filter` as **escaping** (because `filter` returns a `Gen` whose continuation captures `pred`), then by `§4.3` the closure **moves `banned`**! That would mean `banned` is consumed by `xs.iter().filter(...)` and can never be used again even after the loop finishes!
   - Conversely, if the compiler treats the closure passed to `Gen.filter` as **borrowing `banned`** (class 2), then inside `Gen.filter`'s implementation:
     ```ts
     function filter(self: Self, pred: (readonly T) => bool): Gen<T, E>
     ```
     `Gen.filter` captures `pred` into `generate(() => { for (const x of self) { if (pred(x)) { yield x; } } })` and **returns** that `Gen`!
     By `§4.2`, returning a `Gen` that holds `pred`'s borrows is a **tied return** (tied to `self` and `pred`, both of which are automatic sources because `self` is the receiver and `pred` is a closure parameter!).
   - **Why is there a conflict with `§4.3`?** Because `§4.3` says *"A closure that escapes — returned, stored in a first-class value, or handed to a task — instead takes ownership of what it captures, by move"*, and *"A closure that holds a borrow is class 2: it can be passed down but not returned or stored."*

Look at that contradiction between `§4.2` and `§4.3`:
- `§4.2` says: a `Gen` (which is a struct `{ state: Option<Cont<...>> }` storing a continuation!) can hold a borrow (making that `Gen` value class 2) and can be **returned tied to its sources** (`xs.iter()` returns a `Gen` holding a borrow of `xs`; `g.filter(pred)` returns a `Gen` holding the borrows of `g` and `pred`).
- `§4.3` says: a closure that is returned or stored captures by move, and a closure holding a borrow cannot be returned or stored!

If `(x) => !banned.contains(x)` is passed to `xs.iter().filter(...)`, a TypeScript programmer 100% expects `banned` to be **borrowed** for the duration of the iteration chain, **not moved/consumed**!
**Fix:**
Clarify the boundary between borrowing and moving in `§4.3`:
- A closure passed as an **argument to a call** (`xs.iter().filter((x) => !banned.contains(x))`) captures by **borrow** (unless the parameter type requires `Send`, as in `s.spawn` / `s.fork`, or the call's return value outlives the borrowed variable!).
- A closure only captures by **move** when:
  1. It is passed to a parameter with a `Send` / class-1 bound (such as `s.spawn` / `s.fork`), **or**
  2. It would otherwise capture a local variable defined *inside* the current function and escape via `return` (e.g. `return (path) => \`${prefix}/${path}\`` where `prefix` is a local variable of the returning function!).
That distinction is completely natural, requires zero syntax (`move` keyword not needed), lets `return (path) => \`${prefix}/${path}\`` move `prefix` (because `prefix` is a local that dies on return), and lets `xs.iter().filter((x) => !banned.contains(x))` borrow `banned` for the lifetime of the iterator!

---

### Question 3: Is it now a high-quality language, and what is the single most valuable next change?

#### Direct assessment
**Yes.** Compared to 0.18, 0.19 crossed the threshold from "a clever calculus with ergonomic traps" to "a language you could actually write production services in." Specifically:
- `Io.scope` with `spawn` (infallible) vs `fork` (propagates failure) + `SimIo` is a genuinely better concurrency and testing story than Go, Rust (`tokio`), or TypeScript.
- Making `RegionList` and `Cell` copyable handles and making every `Ref<R, T>` `Send` (by freezing outer regions during scopes) eliminated the single worst ergonomic wart in 0.18 (`Ref<R, RegionList<R, Ref<R, Json<R>>>>` and the `Send` exception).
- `view struct`, `from` defaults, `Fail.map`, and `.iter().map().filter().collect()` make ordinary application code look and feel like clean TypeScript.

#### What would still stop me from recommending it to a TypeScript service team today?
Once the bugs above (especially #1, #2, and #6) are fixed, only **two practical gaps** remain for a networked service team:
1. **Wire serialization / schema validation (`JSON` ↔ typed structs/unions) via `comptime` (`§7.1`).**
   In TypeScript (`zod`) or Rust (`serde`), a networked service team defines a struct/union for an HTTP request or DB row and serializes/deserializes it in one line. In `A.1`, parsing JSON builds an untyped `Json<R>` AST, and `§10.2` slices fixed byte offsets `raw[0..8]`.
2. **Closures and method syntax on structural types (`§3.4`).**
   `§3.4` says only the standard library can give inherent methods to structural records, tag unions, slices, and `str`. That's fine, provided `comptime` derivations (`Eq`, `Hash`, `Show`, `Clone`, and user-defined `JsonCodec`) work uniformly on both `struct`/`enum` and structural types.

#### The single most valuable next change
**Implement `comptime` type reflection (`Type.fields`, `Type.variants`, `Type.struct`) and write a 40-line `comptime` JSON decoder/encoder in the appendix or standard library.**
Why this is the highest-value next step:
1. Law 5 (*"`comptime` is the metalanguage"*) is the **only** one of the five laws not yet exercised by the running prototype (`§11`).
2. Replacing built-in `Eq`/`Show`/`Clone`/`Soa` with real `comptime` code proves Law 5 works and simultaneously solves the #1 real-world need of a TypeScript backend team: turning raw bytes/JSON into typed Flyscript structs in a region with zero boilerplate.

---

### Smaller points

- **`Cell.get` effect (`§4.6` vs `A.5`):**
  In `§4.6`, `Cell.get` is declared as `export function get(self: Self): T uses Region<R>;`. That is right (reading a `Cell` observes region mutation, so it cannot be called from pure code or across concurrent tasks when `Region<R>` is frozen). Just double-check that `RegionList.len(self: Self): usize` in `§4.6` (which is currently marked pure, without `uses Region<R>`) is either `uses Region<R>` or allowed to be pure only because outer regions are frozen during `Io.scope` (once Problem #1 is fixed, `RegionList` cannot grow while tasks run, so a pure `len` and `Iterable.each` are indeed deterministic and race-free!).
- **Slice lending from `Ref<R, T>` (`§4.6`, `§10.2`):**
  In `§10.2`, `req.user` has type `Ref<R, str>`, and is passed to `db.fetchProfile(req.user)` expecting `str`. Since `str` is already a slice (`§3.1`), why do `§10.1`, `§10.2`, `A.1`, and `A.5` use `Ref<R, str>` instead of a region-allocated slice or `Ref<R, str>` lending `str`? Under `§4.1`, `Ref<R, T>` lends `readonly T`, and for `T = str`, `readonly str` is `str`. Make sure `copyUtf8` in `§10.1` (`Ref<R, str>`) is consistent with Rule 2 of `§4.6` (*"Region data contains only `Copy` values..."* — `str` is `Copy`, and its backing bytes live in the same region arena `R`).
