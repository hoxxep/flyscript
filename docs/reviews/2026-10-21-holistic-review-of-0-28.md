# Review: holistic-review-of-0-28

- spec: 062c99069d91
- request: 8d52a85938185c46
- tokens: prompt 34519, cached 0, answer 8871

## Question

Spec 0.28 (included). Since your review of 0.24, the changes came from writing three programs the way a TypeScript programmer would (Appendix A.10 inventory service, a log pipeline with a reader task and a channel, A.11 a rate limiter with injected Clock/Log effects), plus your 0.24 soundness fixes:

- 0.25: calls through borrows follow closure modes; associated types count as hiding borrows; template struct instances checked as structs; `ParSplit` impls need `Send` elements; `if (let …)`; A.9 via try/catch.
- 0.26: `match`, `handle`, `region`, `effect` are contextual words; list literals default to arrays when their items agree; a diverging branch does not meet the others for moves; libraries name failures for what failed (`#MissingField`, not `#Missing`), since failure rows merge by tag.
- 0.27: channels close (`tx.close()` consumes a sender; `recv` gives `#None`; `for…of` over a receiver stops); a forked task's failure cancels its scope including a body blocked on a channel; tasks may capture `str`; TypeScript's string methods.
- 0.28: continuations are `once` functions (`k(a)` resumes; `Cont`/`.resume` removed); several `with` clauses on one `handle`; expression arm bodies; prelude `min`/`max`.

Please review 0.28 holistically:

1. **Soundness** of the new pieces, and anything older that a TypeScript team would now trip over. In particular: continuations as plain `once` functions (can one be passed where a `once` function is expected and called elsewhere — is that fine?), channel closing and cancellation, contextual keywords (any grammar ambiguity: `match (x) { … }` vs a call `match(x)` followed by a block statement?), the array default (`[a, b]` inferring an array vs a tuple, and what changes if a later use wants a tuple).
2. **What is the weakest part of the design now?** Be blunt.
3. **Rank the three most valuable remaining changes**, with spec text.

## Answer

### Verdicts

- **Continuations as `once` functions (`§5.2`, `§5.3`)**: **Agree with changes.** Unifying `Cont` with `once (A) => B uses E` removes a redundant type and works cleanly for generators (`§5.5`), **except** that `§4.4` says *"Every function value is `Send`"* while a continuation is a fiber-local stack segment that captures its handler and cannot cross fibers (`§4.6`, `§6.1`). Passing `k` to `s.fork(k)` or sending `k` over a `Channel` is currently allowed by the rules and is unsound.
- **Multi-`with` `handle` and expression arms (`§2.3`, `§5.2`)**: **Agree with changes.** The syntax is a clear improvement, but `§5.2` ("the first innermost") leaves the effect environment and borrow ledger (`§5.3`) of outer vs. inner `with` clauses underspecified when an inner handler arm performs an effect handled by an outer `with` clause of the same `handle`.
- **Channels, `tx.close()`, and scope cancellation (`§6.1`, `§6.2`)**: **Agree.** Having `tx.close()` consume `tx` and cancellation wake `Io.park` (including channel `recv`/`send`) makes the reader/consumer pipeline in `§6.2` safe and deadlock-free on error. (One spec-vs-prototype discrepancy on `Drop` vs `close()` is noted below.)
- **Contextual keywords (`§2.3`)**: **Agree with changes.** `region (R) {` and `match (e) {` have concrete grammar ambiguities with function calls and record arguments in expression position (`match({ a: 1 }) { ... }`).
- **List literal array default (`§2.2`, `§3.1`)**: **Agree.** Defaulting homogeneous `[a, b]` to `T[2]` when unconstrained while allowing `const [x, y] = arr` to destructure fixed-size arrays (`§3.1`) avoids almost all friction.

---

### Problems

#### 1. Unsoundness: Continuations are `once` functions (`§5.2`, `§5.3`), and *"Every function value is `Send`"* (`§4.4`)

In `§0.1` and `§5.2`–`§5.3`, `Cont<A, B, E>` was replaced with `once (a: A) => B uses E`:
> *"A continuation is a `once` function: an affine value that may be stored, moved and returned like any other, and that is called at most once."* (`§5.3`)

Now check `§4.4` (Marker interfaces):
> *"Every function value is `Send`, since an escaping closure owns only `Send` values (§4.3); a closure that holds a borrow carries it as a loan, which a task cannot take (§6.1)."*

Because a continuation `k` now has the ordinary function type `once (a: A) => B uses E`, and every function value is `Send`, look at what happens when a continuation holds **no** class-2 borrows and its remaining effects `E` are `Io` (or `[]`):

**Program 1a (Resuming a continuation on another task/fiber):**
```ts
effect YieldOne { pause(): void; }

export function crossFiberResume(): void uses Io {
  // Capture a continuation `k: once () => void uses Io` that holds NO borrows (class 1).
  const step: Option<once () => void uses Io> = handle {
    YieldOne.pause();
    #None
  } with YieldOne {
    pause() resumes k => #Some(k),
  };

  if (const #Some(k) = step) {
    Io.scope((s) => {
      // `s.spawn` takes `once () => void uses Io`!
      // `k` has type `once () => void uses Io`, holds no loans, and function values are `Send`!
      s.spawn(k);
    });
  }
}
```
Even more dangerous, what if the suspended computation inside `k` is inside a `region (R)` block (so `Region<R>` is already handled **inside** `k` and does **not** appear in `k`'s outer effect row `E`)?

**Program 1b (Data race on a fiber-local region via a `Send` continuation):**
```ts
import { RegionList } from "std/region";

effect Step { step(): void; }

export function raceRegionViaCont(): void uses Io {
  region (R) {
    const list = RegionList.new<R, i32>(); // lives in fiber-local region R
    list.push(1);

    // Inside `handle`, `region (R2)` is internal, OR `list: RegionList<R, i32>` (`Copy` and `Send`!)
    // is read by one task while another task resumes a continuation that has a deep `Region` handler!
    const kOpt: Option<once () => void uses Io> = handle {
      region (R2) {
        const inner = RegionList.new<R2, i32>();
        Step.step();
        inner.push(42);
      }
      #None
    } with Step {
      step() resumes k => #Some(k),
    };

    // Or send `k` across a `Channel<once () => void uses Io>` to another worker thread!
  }
}
```
Why is this broken?
1. Look at `§4.4`:
   > *"`T` is `Send` when it is class 1 and owns no raw pointer or runtime handle (`Gen`, `Fiber`, `Scope`)"*
   Notice that `§4.4` explicitly says **`Gen` is NOT `Send`**! Why is `Gen<T, E>` not `Send`? Because `Gen<T, E>` (`§5.5`) is literally:
   ```ts
   export struct Gen<T, row E> { state: Option<once () => Step<T, E> uses ...E>; }
   ```
   A `Gen` is just a wrapper around a continuation `once () => ...`! If `once () => ...` is `Send`, why was `Gen` listed as a non-`Send` runtime handle, while the raw `once () => ...` inside `Gen.state` *is* `Send`?!
2. A continuation `k` holds a suspended stack segment tied to the fiber/thread state where it was created (including thread-local/fiber-local handler frames and `k`'s re-entry loan tracking `§5.3`: *"k(a) uses every binding from outside the `handle` that the body or any of its arms uses"*).
3. If `k` is passed to `s.spawn(k)`, sent over a `Channel<once () => void uses Io>`, or stored in a struct moved to another task, **the typechecker loses track of `k`'s handler re-entry borrows AND moves a fiber stack across tasks!**

Even on a single thread without concurrency, look at what happens when `k` escapes the `handle` block and its handler arm mutates a local variable `out`:

**Program 1c (Use-after-free / aliasing via escaping `k` whose deep handler arm mutates a local):**
```ts
effect Log { info(msg: String): void; }

function makeLogger(): once () => void {
  let out = Vec.new<String>(); // local to `makeLogger`!
  const step: Option<once () => void> = handle {
    Log.info(String.fromStr("first"));
    Log.info(String.fromStr("second"));
    #None
  } with Log {
    info(msg) resumes k => {
      // Deep handler arm! When `k` is resumed later, `Log.info("second")` runs THIS arm again!
      // And this arm mutates `out`, which is a local of `makeLogger`!
      out.push(msg);
      #Some(k)
    },
  };
  step.unwrap() // Returns `k` AFTER `makeLogger` returns and `out` is dropped!
}

export function crash(): void {
  const k = makeLogger();
  k(); // Resumes `k`, performs `Log.info("second")`, runs the deep `with Log` arm,
       // which pushes into `makeLogger`'s dead stack frame `out`! Use-after-free!
}
```
Read Program 1c carefully!
- In `makeLogger()`, the body performs `Log.info("first")`.
- The resumptive arm `info(msg) resumes k => { out.push(msg); #Some(k) }` pushes `"first"` to `out`, and **does not call `k()`** — instead, it returns `#Some(k)` as the value of the `handle` expression!
- Because handlers are **deep** (`§5.3`: *"Handlers are deep: the handler stays installed beneath the suspended computation"*), `k` carries the installed `with Log` handler with it!
- When `k()` is called later, the rest of the body performs `Log.info("second")`, which invokes the `with Log` arm again — and that arm accesses `out` (`out.push(msg)`), which belonged to `makeLogger()`!
- Look at `§5.3`:
  > *"A continuation holds every borrow its suspended computation holds: in a resumptive arm, `k` holds the borrows the body had taken when it performed the operation."*
  > *"Resuming re-enters. `k(a)` runs the rest of the body, which may perform the same operation again and re-enter an arm of the same handler. So, for ownership, `k(a)` uses every binding from outside the `handle` that the body or any of its arms uses, in the strongest mode any of them does: an arm cannot hold a borrow of such a binding across the call."*
- `§5.3` says `k` holds the borrows the **body** had taken, and says calling `k(a)` uses every binding the **arms** use — **but it forgot to say that `k` ITSELF holds the borrows that the deep handler's ARMS capture (`out` in Program 1c)!**
- Because the deep handler stays installed inside `k`, `k` closes over the handler arms! If an arm uses `out` from outside the `handle`, `k` itself holds a borrow of `out` (`mut out` in Program 1c), making `k` **class 2** so it cannot escape `makeLogger`!
- And in `Gen` (`§5.5`), why can `generate(f)` return `Gen<T, E>`? Because `generate`'s handler arm (`yield(item) resumes rest => #Item { item, rest }`) captures **nothing** from outside `handle`!

**Fix (two sentences in `§5.3` and `§4.4`, zero new concepts):**
1. **In `§5.3` (Continuations)**, replace bullet 4 and bullet 6 with one unified rule:
   > *"Because the handler stays installed inside `k`, **`k` holds every borrow that the suspended body holds AND every borrow of a binding outside the `handle` that any resumptive arm of the handler uses** (in the strongest mode it uses it). One holding a borrow is class 2 (§4.2), so `k` cannot outlive anything the body or the handler arms touch, and calling `k(a)` requires those borrows to be available."*
   Look what this single rule does:
   - It immediately rejects Program 1c (`k` holds `mut out` because the handler arm mutates `out`, so `k` is class 2 and cannot be returned from `makeLogger`).
   - It subsumes bullet 6 ("Resuming re-enters") automatically: because `k` holds `mut out` while `k` is live, the arm cannot hold another borrow of `out` across `k(a)`, and `out` is unlocked as soon as `k` is consumed!
   - And for `generate(f)` (`§5.5`), the `Yield` handler arm captures nothing from outside `handle`, so `k` only holds whatever borrows `f` itself holds!
2. **In `§4.4` (Marker interfaces)**, make `once` closures / continuations consistent with `Gen`:
   Either:
   - State in `§4.4` / `§5.3` that a continuation (or a value containing one, such as `Gen`) is not `Send` (so `k` cannot be passed to `s.spawn(k)` or sent across a channel to another fiber); **or**
   - If you want `once` function types not to need a separate "is-a-continuation" bit in the type system, note in `§6.1` that `spawn` and `fork` take a task closure literal or non-continuation `Send` function, or mark `once` closures created by `resumes k` as holding a fiber loan (class 2 with respect to `Send`, or non-`Send` like `Gen`). Wait: in `§4.2`, you **already** track per-value loans on closures and `Gen` (`"A value of such a type is class 2 when it actually holds a borrow"`). Tracking a fiber-affinity bit (or treating `k` as borrowing the current fiber for `Send` checks) means `k` and `Gen` are automatically non-`Send` without changing the surface type `once (A) => B`!

---

#### 2. Multi-`with` `handle`: ordering of effects and borrow tracking between clauses (`§5.2`, `§5.3`)

In `§2.3` and `§5.2`:
```ebnf
Handle = "handle" Block { "with" Path [ TypeArgs ] "{" { Arm } "}" } ; (* the first `with` innermost *)
```
And `§5.2`:
> *"`handle { body } with Eff { arms }` runs `body` and intercepts its `Eff` operations; further `with` clauses handle further effects, the first innermost."*

Define `handle { body } with E1 { arms1 } with E2 { arms2 }` explicitly as syntactic sugar for nested `handle` expressions:
```ts
handle {
  handle { body } with E1 { arms1 }
} with E2 { arms2 }
```
Why must the spec state that it is **exact desugaring to nested `handle`s** rather than just saying "the first innermost"?
Look at what happens when `arms1` (the inner handler for `E1`) performs `E2` (handled by the outer handler `with E2`), or when both `arms1` and `arms2` mutate the same local variable `out`:

**Program 2 (Two `with` clauses mutating the same binding `out` or `arms1` performing `E2`):**
```ts
effect E1 { op1(): void; }
effect E2 { op2(): void; }

export function multiWith(): Vec<str> {
  let out = Vec.new<str>();
  handle {
    E1.op1();
    E2.op2();
  } with E1 {
    op1() resumes k => {
      out.push("e1");
      E2.op2(); // Does `with E2` catch this? If it desugars to nested `handle`, YES!
      k()       // And while `k()` runs, `E2`'s arm also mutates `out`!
    },
  } with E2 {
    op2() resumes k => {
      out.push("e2");
      k()
    },
  };
  out
}
```
If `handle { body } with E1 { arms1 } with E2 { arms2 }` is defined by desugaring to `handle { handle { body } with E1 { arms1 } } with E2 { arms2 }`:
1. `arms1` runs inside `handle { ... } with E2 { arms2 }`, so `arms1` is allowed to perform `E2` (e.g., `with Clock` is outer and `with Log` is inner, so the `Log` handler can call `Clock.now()` to timestamp log entries!).
2. In the inner `handle`, `k` in `arms1` has type `once () => B uses E2, ...E`, so when `arms1` calls `k()`, `k()` performs `E2` which is caught by the outer `with E2` — and because `E2` is handled by the outer `handle`, the borrow checker knows `k()` can trigger `arms2` (which mutates `out`), so `arms1` cannot hold a conflicting borrow of `out` across `k()`!

**Fix:**
In `§5.2`, replace *"further `with` clauses handle further effects, the first innermost"* with:
> *"Multiple `with` clauses nest from left to right: `handle { body } with E1 { a1 } with E2 { a2 }` is `handle { handle { body } with E1 { a1 } } with E2 { a2 }`, so an inner arm may perform effects handled by an outer clause."*

---

#### 3. Contextual keywords (`match`, `handle`, `region`, `effect`) have concrete parser ambiguities (`§2.3`)

In `§2.3`:
> *"`from`, `of`, `with`, `resumes`, `row`, `view` and `private` are keywords only where the grammar expects them, and so are the words that begin `match (e) {`, `handle {`, `region (R) {` and `effect Name`; anywhere else they are names, so a request handler may be called `handle`."*

Look at the two lookahead rules implied by `"the words that begin match (e) {, handle {, region (R) { and effect Name"`:

**Program 3a (`match (e) {` vs a call `match(e)` where `e` is a struct/record literal or followed by a block):**
```ts
function match(x: { a: i32 }): i32 { x.a }

export function ambiguity1(): i32 {
  // 1. User calls `match({ a: 1 })`:
  // It starts with `match`, followed by `(`, an expression `{ a: 1 }`, `)`!
  // If it's followed by `{` on the next line (a block statement) or inside a match/if:
  const n = match({ a: 1 });

  // 2. Worse: what about `match (Foo { a: 1 }) { #Bar => 1 }` (a `Match` expression whose
  // scrutinee is a struct literal `Foo { a: 1 }`) vs a call `match(Foo)`?
  // 3. Even simpler: what if someone defines `function region(x: i32): void {}` and writes:
  //    `region(x);` vs `region (R) { ... }`?
  n
}
```
Look at how `match (e) {` and `region (R) {` differ:
1. For `region (R) {`:
   The token inside `(` `)` is always a single `Ident` followed immediately by `)` and `{`:
   `"region" "(" Ident ")" "{"`.
   A function call `region(x)` is followed by `;` (or an operator), **never** by `{` (because a call expression cannot be followed by `{` in Flyscript).
   So `"region" "(" Ident ")" "{"` is 100% unambiguous with bounded 4-token lookahead!
2. For `handle {`:
   `"handle" "{"` — a variable or function named `handle` can never be followed directly by `{` in expression or statement position (calls require `handle(...)`, and struct literals `Handle { ... }` only apply to type paths, or if a function is named `handle`, `handle {` is always the `handle` expression). So `"handle" "{"` is 1-token lookahead!
3. For `effect Name`:
   `Effect` is a top-level `Decl` (`§2.3`), so at module top-level `"effect" Ident` is 1-token lookahead!
4. **What about `match (e) {`?**
   In `match (e) {`, `e` is an arbitrary `Expr` inside balanced parentheses `(...)` followed immediately by `{`.
   Can a function call `match(e)` **ever** be followed immediately by `{` in valid Flyscript?
   Check the grammar (`§2.3`):
   - A call `match(e)` is an `Expr` (not a `BlockLike`!).
   - An `Expr` statement **must** end with `;` (`Stmt = ... | Expr ";" | BlockLike`).
   - Only a `BlockLike` statement needs no `;`!
   - And in expression position, `{` cannot follow `)` as an operator.
   **Therefore, `match (...) {` (where `{` immediately follows the closing `)` of `match(...)`) can NEVER be a call `match(e)` in valid Flyscript!**

**Fix:**
State the exact lexical/parser lookahead rule in `§2.3` so implementers don't guess:
> *"`match`, `handle`, `region` and `effect` are parsed as keywords when followed by `(…) {`, `{`, `(Ident) {` and `Ident` (at declaration level) respectively, and as identifiers everywhere else."*

---

### Question 2: What is the Weakest Part of the Design Now?

Be blunt: **There are two weak spots left — one in the prototype (`§11`) and one in the surface language (`§3.4` / `§3.5`).**

#### Weakness A (Prototype vs. Spec): `flyc` still does not run `Drop` or `defer` on scope exit (`§11` vs `§4.1`, `§5.5`, `§5.6`, `§6.2`)

Look at `§11`:
> *"The prototype compiler, `flyc`, implements this specification except code generation, and its evaluator does not run `Drop`: values are reclaimed by the host, and a channel closes only when a sender is closed explicitly."*

Why is this the single biggest gap in the prototype right now?
Because **three of the five laws (`Law 1: One owner`, `Law 4: Handlers for everything`, and deterministic resource cleanup in `§5.3`, `§5.5`, `§5.6`, `§6.2`) make promises whose observable behavior depends on `Drop` and `defer` running when scopes and continuations exit!**
Specifically:
1. In `§5.3` and `§5.5`: *"breaking from `for…of` drops the continuation, so the generator unwinds and its cleanup (`Drop` and `defer`) runs."* Look at `rows(db, sql)` in `§5.5`: `let cursor = db.open(sql); // Drop closes the cursor`. If `flyc`'s evaluator doesn't run `Drop`, that flagship example in `§5.5` doesn't actually close the cursor when you `break` out of `for (const r of rows(db, sql))`!
2. In `§6.2`: *"A channel closes when its last sender is dropped, or when a sender is closed with `tx.close()`."* Because `flyc` doesn't run `Drop`, you had to add `tx.close()` just so channels can close in the evaluator, and if a forked producer task **fails or panics** before reaching `tx.close()`, `tx` is dropped during unwinding — if `Drop` doesn't run in `flyc`, the receiver in the parent scope hangs instead of seeing the channel close or unwind!
3. Running `Drop.drop(mut self)` in the tree-walking evaluator (`§11`) when a block exits or a continuation is dropped is ~50 lines of interpreter code (you already have the live-binding table `Θ` at scope exit!). Implementing `Drop` in the evaluator will immediately test whether destructor order, partial moves (`§4.1`), `defer` (`§5.6`), generator `break` (`§5.5`), and channel closing on task exit (`§6.2`) actually work together.

#### Weakness B (Language Design): The "Owner vs. Lent View" seam on `String` / `str` and `Vec<T>` / `T[]` (`§3.1`, `§3.5`, `§4.1`, `A.10`)

Look at the *Awkward* note in `A.10` (`Appendix A.10`, Inventory service) and the string conversions scattered across `A.10`, `A.11`, and `§7.5`:
- In `A.10`: `self.items.insert(item.sku.clone(), item)`
- In `A.11`: `self.buckets.insert(client.toString(), ...)`
- In `§7.5`: `throw #MissingField(String.fromStr(f.name))`
- In `§3.5`: *"an owner compared with the type it lends is compared at that type (`name == "ada"` for a `String`, `b.name == name` for a `Ref<R, str>`)"*

Look at what a TypeScript team will trip over on day one:
1. Why are there **two** ways to turn a `str` into a `String` in the spec right now: `client.toString()` in `A.2`/`A.11` AND `String.fromStr(f.name)` in `§7.5`? Pick one canonical method (`s.toString()` or `String.from(s)`)!
2. Look at `§3.5`:
   > *"an owner compared with the type it lends is compared at that type (`name == "ada"` for a `String`, `b.name == name` for a `Ref<R, str>`)"*
   This special coercion rule exists ONLY for `==` / `!=` / `<` (`Eq` and `Ord`)!
   What happens when a user has `a: String` and `b: str`, and calls a generic function `min(a, b)` (`§0.1`) or puts them in a two-arm `if (cond) { a } else { "default" }` where `str` is expected?
   Wait: by `§4.1` (*"Wherever a borrow of `U` is expected, an owner that lends `U` may be passed"*), lending already works for **function arguments** when the parameter type is `str` or `readonly T`.
   Why did `name == "ada"` need a special rule in `§3.5`? Because `==` is a built-in operator whose left and right operands have no fixed parameter type before resolution!
   And why did `A.10` have to write:
   ```ts
   match (self.items.getMut(item.sku)) {
     #Some(existing) => { existing.qty += item.qty; },
     #None => { self.items.insert(item.sku.clone(), item); },
   }
   ```
   Because `HashMap` in `std/collections` has `getMut` and `insert`, but no `entry` or `upsert` API, AND because `match (self.items.getMut(sku))` in `#Remove` (`A.10`) had to write:
   ```ts
   #Remove { sku, qty } => {
     match (self.items.getMut(sku)) {
       #Some(it) => {
         if (it.qty < qty) { throw #Short { sku, have: it.qty }; }
         it.qty -= qty;
       },
       #None => throw #Unknown(sku),
     }
     self.log.push(`remove ${sku}`);
     stringify({ ok: true })
   }
   ```
   Wait: look closely at `#Remove { sku, qty }` in `A.10`!
   In `#Remove { sku, qty }`, `sku` has type `String` (owned).
   1. `self.items.getMut(sku)` lends `sku` as `str` (`§4.1`).
   2. Inside `#Some(it)`, `if (it.qty < qty) { throw #Short { sku, have: it.qty }; }` **moves `sku`**!
      Why is moving `sku` inside `#Some(it)` legal while `it: mut Item` is still in scope?
      Because:
      - `HashMap.getMut` has signature `function getMut(self: mut Self, key: str): Option<mut V> from self` (`§4.2`: *"counts.getMut(key) holds the borrow of counts but not of key"*), so `sku`'s borrow ended as soon as `getMut(sku)` returned!
      - And on the path where `it.qty < qty`, `throw #Short { sku, have: it.qty }` diverges (`§4.1`: *"a path that throws, returns, breaks or continues does not meet the others"*), so `sku` is still live after the `match` to be used in ``self.log.push(`remove ${sku}`)``!
   That interaction in `A.10` (lending `sku` to `getMut` with `from self` + moving `sku` on the diverging `throw` branch + using `sku` in `` `remove ${sku}` `` afterward) is genuinely impressive — it works with zero clones. The only clone in `A.10` is `self.items.insert(item.sku.clone(), item)` because `Item` itself also stores `sku: String`.

---

### Question 3: Top Three Most Valuable Remaining Changes (Ranked, with Spec Text)

#### Rank 1: Fix Continuation `Send` & Deep-Handler Arm Borrow Capture (`§4.4`, `§5.2`, `§5.3`)

**Why this is #1:**
This closes the soundness holes in **Problems 1 and 2** above (Program 1a, 1b, 1c, and Program 2) introduced by unifying `Cont` with `once` functions and adding multi-`with` handlers in 0.28. It adds zero new syntax or types; it simply makes `k`'s loan set include the handler arms that stay installed inside `k`, and keeps `k` on its fiber.

**Concrete spec text:**
- **In `§5.2` (Handlers)**, amend the first sentence:
  > *"`handle { body } with Eff { arms }` runs `body` and intercepts its `Eff` operations. Multiple `with` clauses nest from left to right (`handle { handle { body } with E1 { a1 } } with E2 { a2 }`), so an inner arm may perform effects handled by an outer clause."*
- **In `§5.3` (Continuations)**, replace the fourth and sixth bullets with:
  > - *"Because a handler is deep, `k` holds every borrow its suspended computation holds together with every borrow of a binding outside the `handle` that any resumptive arm of the handler uses, in the strongest mode any of them uses it. A continuation holding a borrow is class 2 (§4.2), so it can never outlive what the body or handler arms touch, and an arm cannot hold a conflicting borrow across `k(a)`."*
  > - *"A continuation is bound to the fiber of its handler and is not `Send`: it may be stored and moved within its task (as in `Gen`), but never sent or spawned onto another task."*

---

#### Rank 2: Make `Drop` Run in the Prototype & Specify Panic/Failure Order During Unwinding (`§5.6`, `§11`)

**Why this is #2:**
As noted in Weakness A, `flyc` not running `Drop` (`§11`) leaves `§5.5` (generator cleanup on `break`) and `§6.2` (closing a channel when a sender is dropped on task exit) untested in the reference evaluator. Furthermore, `§5.6` does not state whether a `defer` or `Drop.drop` is allowed to have effects (`Fail`? `Io`?), which matters directly for closing files, sockets, and channels in `Drop`!

Look at `§5.5`:
```ts
function rows(db: readonly Db, sql: str): void uses Io, Fail<DbErr>, Yield<Row> {
  let cursor = db.open(sql); // Drop closes the cursor
  while (cursor.hasNext()) { yield cursor.next(); }
}
```
And `A.2`:
```ts
let f = File.open(path);
```
Wait: closing a `File` or a database `Cursor` in `Drop.drop` or cancelling in-flight I/O when a `Gen` is dropped (`§5.3`, `§5.5`) happens inside `Drop.drop(self: mut Self)`!
What is the signature of `Drop`? The spec never writes `interface Drop` out!
If `interface Drop { function drop(self: mut Self): void; }` is pure (`uses []`), then:
1. `Drop.drop` ** cannot** throw (`Fail`) — which completely avoids C++'s double-exception termination problem during unwinding!
2. What if `Drop.drop` needs to close a file descriptor or release a runtime resource? Runtime types (`File`, `Socket`, `Sender`) release their OS/runtime handle in their runtime destructor without needing a user-level `Io` effect in `drop`'s signature, and user `defer` blocks run in the enclosing function's effect context (except they may not `return`, `break`, `continue`, or `throw` out of the block).

**Concrete spec text:**
- **In `§5.6` (Cleanup: `defer` and `Drop`)**, add:
  > *"`interface Drop { function drop(self: mut Self): void; }` has no effects: a destructor cannot fail or suspend. A `defer` expression may perform the effects of its enclosing block except `Fail` and `Yield`, and may not `return`, `break` or `continue`."*

---

#### Rank 3: Settle the Contextual Keyword Lookahead & Standardize Conversion Naming (`§2.3`, `§3.1`)

**Why this is #3:**
Closing the parser ambiguity in `§2.3` (Problem 3) and eliminating the `String.fromStr(s)` vs `s.toString()` inconsistency across the spec and stdlib (`§7.5`, `A.2`, `A.11`) removes the remaining surface paper-cuts before freezing the grammar.

**Concrete spec text:**
- **In `§2.3` (Grammar, Contextual words)**, replace the third bullet with:
  > - **Contextual words.** `from`, `of`, `with`, `resumes`, `row`, `view` and `private` are keywords only where the grammar expects them. `match`, `handle`, `region` and `effect` are keywords only when followed by `(…) {`, `{`, `(Ident) {` and `Ident` (at declaration level) respectively; anywhere else they are ordinary identifiers, so a function or variable may be named `match`, `handle`, `region` or `effect`. Any word may be used as a member name (`Yield.yield`, `{ default: 1 }`).
- **In `§7.5` (`FromJson`)**:
  Change `throw #MissingField(String.fromStr(f.name))` to `throw #MissingField(f.name.toString())` so `s.toString()` is the single universal way to turn a borrowed `str` (or any `Show` type) into an owned `String`.

---

### Smaller points

- **Array default for `[a, b]` (`§2.2`, `§3.1`) — your Question 1 check:**
  You asked: *what happens with `[a, b]` defaulting to an array `T[2]` when its items have one type, if a later use wants a tuple `[T, T]`?*
  Let's check every place a tuple `[T, T]` is used:
  1. **Destructuring (`const [x, y] = p`)**: `§3.1` says *"taken apart with a pattern (`const [a, b] = t`, which takes an array of the same length apart too)"*. So destructuring works identically on `T[2]` and `[T, T]`!
  2. **Constant indexing (`p[0]`, `p[1]`)**: `§3.1` says indexing works on both tuples and arrays (`p[0]`).
  3. **Passing to or returning from a function expecting `[T, T]`**: By `§3.6` (bidirectional inference), expected types flow inward into return expressions, call arguments, and typed bindings (`const p: [i32, i32] = [1, 2]`), so `[1, 2]` in any of those positions gets the expected type `[i32, i32]` and builds a tuple!
  4. **The only case where `[1, 2]` infers `i32[2]` and then fails** is when a user binds an untyped local `const p = [1, 2];` and *later* passes `p` to a function expecting `[i32, i32]`. And wait: in memory (`§3.1`), a 2-tuple `[T, T]` and a 2-element inline array `T[2]` have the exact same layout (`2 * sizeof(T)`), and `T[2]` is strictly more capable (it supports runtime indexing `p[i]`, slicing `p[0..2]`, and `for (const x of p)`). So defaulting unconstrained homogeneous `[a, b]` to `T[N]` is the right design.
- **`if (const Pat = e)` vs `if (let Pat = e)` in `§2.3`:**
  `IfConst` in `§2.3` allows both `if (const #Some(x) = e)` and `if (let #Some(x) = e)`, which matches `for (const x of e)` / `for (let x of e)`. Make sure `else if (const #Some(y) = e2)` works in the grammar: right now `§2.3` has:
  ```ebnf
  IfConst = "if" "(" ( "const" | "let" ) Pattern "=" Expr ")" Block [ "else" ( If | IfConst | Block ) ] ;
  ```
  Notice `IfConst` is in `BlockLike`, while `If` is not written out in `§2.3` — make sure `If`'s `"else"` clause also permits `IfConst` (`[ "else" ( If | IfConst | Block ) ]`) so `if (c) { ... } else if (const #Some(x) = e) { ... }` parses in that order too!
