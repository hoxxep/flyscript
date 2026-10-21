# Review: m2 checker design

- model: gemini-4-argon
- spec: 1d7ad675c65c
- request: 10245315e220b2ba
- tokens: prompt 15156, cached 0, answer 7386

## Question

We are about to build milestone 2 of the prototype compiler (Rust, no dependencies): the **type and effect checker**. Milestone 1 is done: a lexer and parser for the whole §2.3 grammar, and all nine programs in the spec (§10.2 and the appendix) parse. Milestone 3 (ownership: moves, the borrow ledger, class propagation, tied returns, region non-escape) and milestone 4 (an evaluator with handlers) come later.

Please review these four decisions for milestone 2.

**Decision 1: the standard library as declaration files, using TypeScript's `declare`.**
The examples import `Socket`, `Db`, `RegionList`, `Cell`, `HashMap`, `generate`, `par` and others from `std/...`. We would add `declare` to the grammar for ambient declarations without bodies (`declare function copyUtf8<region R>(bytes: readonly u8[]): Ref<R, str> uses Region<R>, Fail<#MalformedUtf8>;`, `declare struct Socket;`, and `declare` on `impl` methods), and write the standard library as ordinary `.fly` files of signatures. Native operations would be implemented by the runtime later. The alternative is hard-coding the library's types into the checker.

**Decision 2: one row representation, bidirectional checking directly over the surface syntax tree.**
Records, tag unions and effect rows share one internal row type (label → type, optional tail variable) and one Rémy-style unifier with label-sorted rows. Checking is bidirectional over the AST. `throw`, `try`/`catch`, `yield` and `for…of` are checked as the effect operations they denote (§5.4, §5.5) without first desugaring to a core language, so diagnostics point at source. Generic functions are checked once against their declared signature; calls instantiate. Implicitly open `Fail` rows (§3.2) are opened at instantiation. A separate core IR is deferred to the evaluator milestone.

Specific questions: (a) Are there interactions between the three row kinds that make a single unifier wrong — e.g. effect rows with duplicate labels at different type arguments (`Fail<#A>` and `Fail<#B>` in one row; `Region<R1>` and `Region<R2>` in one row), which Koka handles with scoped labels rather than Rémy's lacks-constraints? (b) How should `uses Fail<E1>` and `uses Fail<E2>` combine when both appear in one row: merge into `Fail<E1 ∪ E2>`, or keep duplicates?

**Decision 3: defer `comptime` to the end of the milestone.**
`Soa<T>` and `Ring(T, N)` start as built-in types in the checker, so the particle example can check early; the `comptime` evaluator (§7) is written last and replaces the built-ins with the spec's library definitions. Derived interfaces (§3.5) are likewise built-in until then.

**Decision 4: rejection tests as well as acceptance tests.**
Besides "all nine examples type-check", a suite of programs must be rejected, each naming the expected error: an effect not declared (an `Io` call from a function without `uses Io`), a non-exhaustive `match`, a `catch` whose `match` misses a failure tag the body can throw, a missing field, a type mismatch, an exported function performing an effect it does not declare, and so on.

Finally: is there anything in the spec (§2–§7, §9) that you believe cannot be type-checked as written, or whose typing rule is underdetermined, that we should settle before writing the checker? Please be concrete.

## Answer

### Verdicts

- **Decision 1 (`declare` for `std`)**: **Agree with changes.** Good for the checker; keep `declare` strictly `std`-internal or temporary, not a user-facing language feature, and fix the `Ref<R, T>` receiver rule before writing the `std` declarations.
- **Decision 2 (One row unifier, surface AST checking)**: **Agree with changes.** One row representation works, provided you make two distinctions: (a) `Region<R>` is indexed by `R` (so `Region<R>` is the label, not `Region`), whereas `Fail<E>` and `Yield<T>` have functional dependency from the effect name to the type argument (merging `Fail<E1>` and `Fail<E2>` by unifying `E1` and `E2`); and (b) you do not enforce strict "lacks" constraints on effect rows when instantiating polymorphic functions.
- **Decision 3 (Defer `comptime`)**: **Agree.** The right engineering trade-off for milestone 2.
- **Decision 4 (Rejection tests)**: **Agree.**

---

### Problems

#### 1. Decision 2(a/b): Effect rows vs. Record/Union rows (Duplicate labels and `Region<R>`)

In a record (`{ x: i32; x: f64 }`) or tag union (`#A(i32) | #A(f64)`), duplicate labels with different payloads are a type error. In effect rows, three cases arise:

**Case 1: Nested regions (`Region<R1>` and `Region<R2>`).**
A computation inside two nested `region` blocks uses both regions:
```ts
region (R1) {
  region (R2) {
    const a = alloc<R1, i32>(1);
    const b = alloc<R2, i32>(2); // body uses Region<R1>, Region<R2>
  }
}
```
If the row label is `"Region"` mapped to type argument `R`, a single-map row cannot represent `uses Region<R1>, Region<R2>`.
**Fix:** For region effects, the region variable `R` is part of the row label (i.e. `Label::Region(RegionVid)`), or `Region<R1>` and `Region<R2>` are distinct keys in the map. Two `Fail` effects in one row are *not* distinct; two `Region` effects with different regions *are*.

**Case 2: Combining `Fail<E1>` and `Fail<E2>` (`§3.2`).**
`§3.2` says: *"A tag union written as the argument of `Fail` in a signature is implicitly open: `uses Fail<#Eof | #Bad>` means `uses Fail<#Eof | #Bad | ...ρ>` for a fresh `ρ`. A caller that may fail in more ways simply unifies its larger row with the callee's; error sets compose by union with no conversion code."*
Consider `§10.2`:
```ts
const n = conn.read(mut buf);      // uses Io, Fail<IoErr | ...ρ1>
const req = parse(buf[0..n]);      // uses Region<R>, Fail<#Malformed | #MalformedUtf8 | ...ρ2>
```
If `Fail` is a single label in the effect row mapped to its payload type `E`, then checking the block unifies the effect row of line 1 with the effect row of line 2. Because both contain the label `Fail`, standard Rémy row unification **unifies their payloads**: `IoErr | ...ρ1` unifies with `#Malformed | #MalformedUtf8 | ...ρ2`. That automatically produces the union `#Reset | ... | #Malformed | #MalformedUtf8 | ...ρ3`!
Therefore, **do not allow duplicate `Fail` labels** in an effect row. Having one `Fail` entry per effect row whose payload `E` is unified across all operations in the scope is exact, and gets union composition for free from the tag-union row unifier.

**Case 3: Calling an effect-polymorphic function (`map`) from a context that already has the effect.**
```ts
function map<T, U, row E>(xs: readonly T[], f: (x: readonly T) => U uses ...E): Vec<U> uses ...E;

function readAll(fd: Fd, bufs: readonly (mut u8[])[]): Vec<usize> uses Io, Fail<IoErr> {
  map(bufs, (b) => Io.read(fd, b)) // callback uses Io, Fail<IoErr | ...>
}
```
If `Io.read` has effect `Io, ...E_inner`, and `map` has effect `...E`, works fine. But suppose a HOF itself performs `Io`:
```ts
function timed<T, row E>(f: () => T uses ...E): T uses Io, ...E { ... }
```
If the caller passes a closure `f` that *also* performs `Io`, then `...E` is instantiated with a row containing `Io`. In strict Rémy record unification, `{ l: T; ...E }` requires `E` to *lack* `l` (otherwise the record has duplicate fields). For effect rows, `Io, ...E` where `E` already contains `Io` is idempotent (`Io ∪ {Io, ...} = {Io, ...}`), not an error.
**Fix:** In your single row unifier, parameterize the row kind (`Record`, `Union`, `Effect`). On `Record` and `Union`, rewriting `{ l: A, ...R }` requires `R` lacks `l` (or in `Union`, merges identical tags if payloads unify). On `Effect`, row extension is idempotent: if label `l` (`Io`, `Fail`, `Yield`) appears on both sides or in a tail instantiation, unify their type arguments instead of failing a lacks-check. (Koka's scoped duplicate labels are only needed when a program deliberately shadows one `Yield<i32>` handler inside another `Yield<str>` handler using an unlabelled effect variable in between; nothing in the spec or appendix does this.)

---

#### 2. Underdetermined rule: Region elision and `Ref<R, T>` method dispatch (`§4.6`, `A.5`)

Look at `A.5` (`Scope<R>`):
```ts
export struct Scope<region R> {
  parent: Option<Ref<Scope>>;
  names: Ref<RegionList<{ name: Ref<str>; decl: Ref<Decl> }>>;
}

impl<region R> Scope<R> {
  export function define(self: Ref<Self>, name: Ref<str>): Ref<Decl> uses Region<R> {
    const d = alloc(Decl { name, ty: Cell.new(0), visiting: Cell.new(false) });
    self.names.push({ name, decl: d });
    d
  }
}
```
Three things happen here that the spec leaves underdetermined:
1. Inside `struct Scope<region R>`, `Ref<Scope>` is written with **1 type argument**, even though `Ref<R, T>` takes 2 (`§4.5`) and `Scope<R>` takes 1. `§4.6` says *"In a declaration or block with exactly one region in scope, `Ref<T>`, `RegionList<T>` and region-generic type names take that region implicitly."* Your type resolver must apply this elision rule recursively to every type constructor expecting a `region` parameter whenever 1 region is in scope (`impl<region R>`, `struct Foo<region R>`, `function f<region R>`, or `region (R) { ... }`).
2. `define` declares `self: Ref<Self>` (which elides to `Ref<R, Scope<R>>`). Standard `self` types in `§2.3` are `Self`, `readonly Self`, or `mut Self`. You must allow `Ref<R, Self>` as a valid method receiver in `impl`.
3. `self.names.push(...)`: `self.names` has type `Ref<R, RegionList<...>>`. In `A.1`, `items` is a `RegionList<...>` by value (`const items = RegionList.new(); items.push(...)`), whereas in `A.5`, `self.names` is a `Ref<R, RegionList<...>>`. Moreover, `self.names` is a field access through `self: Ref<R, Scope<R>>`!
`§4.1` says: *"Lending: ... `Ref<R, T>` lends `readonly T`."*
**Fix before milestone 2:** Specify auto-deref / lending for `Ref<R, T>`:
- Field access `r.f` on `r: Ref<R, S>` automatically projects through `Ref` (yielding `readonly F`, or a copy if `F: Copy`).
- Method calls `r.m(...)` auto-borrow `Ref<R, T>` to `readonly T`, *and* methods on `RegionList<R, T>` and `Cell<R, T>` (`push`, `set`, `get`) must take `readonly Self` (with `uses Region<R>`), **not** `mut Self`! Check `A.1`: `const items = RegionList.new(); items.push(...)` — `items` is `const`, so `push` cannot take `mut Self`. That works only because `RegionList.push` mutates via the `Region<R>` effect (`§4.6`), taking `readonly Self` (or `Ref<R, Self>`). Make sure your `std/region.fly` declarations give `RegionList.push` and `Cell.set` a `readonly Self` receiver with `uses Region<R>`.

---

#### 3. Underdetermined rule: `try`/`catch` and open vs. closed `Fail` rows (`§3.2`, `§5.4`, `§10.2`)

In `§10.2`:
```ts
export function serveOne(conn: Socket, db: readonly Db): void uses Io {
  try {
    ...
    if (!quota.allowed) { throw #Unauthorized; }
    ...
  } catch (e) {
    const code: u16 = match (e) {
      #Malformed | #MalformedUtf8 => 400,
      #Unauthorized               => 401,
      _                           => 502,
    };
    ...
  }
}
```
Inside the `try` block:
- `conn.read` has effect `Fail<IoErr | ...ρ1>`
- `parse` has effect `Fail<#Malformed | #MalformedUtf8 | ...ρ2>`
- `throw #Unauthorized` has effect `Fail<#Unauthorized | ...ρ3>`

When these unify, the `try` block's `Fail` payload is `IoErr | #Malformed | #MalformedUtf8 | #Unauthorized | ...ρ_tail`.
 Notice the uninstantiated row tail variable `...ρ_tail`!
If `e` in `catch (e)` is given the type with `...ρ_tail` still open, then a `match (e)` **without** a wildcard `_` (Decision 4 asks for a test where `catch`'s `match` is exhaustive or misses a tag) can *never* be exhaustive, because an open row tail `...ρ_tail` could always contain more tags!
**Fix:** Handling `Fail<E>` with `try { body } catch (e) { ... }` (where `try` removes `Fail` from the enclosing effect row) **closes** the unconstrained row tail variable `ρ_tail` of `E` to the empty row `[]` before checking the `catch` block. If `catch` rethrows part of `e` (or a wildcard arm rethrows `e`), that introduces a new `Fail` effect in the `catch` arm's effect row.

---

#### 4. Underdetermined rule: `Io.scope` and `s.spawn` failure propagation (`§5.1`, `§6.1`, `§10.2`, `A.7`)

Look at `Io.scope` in `§5.1` and `§6.1`:
```ts
scope<T, row E>(body: once (s: mut Scope<E>) => T uses Io, ...E): T uses Io, ...E;

interface Scope<row E> {
  function spawn<T extends Send>(self: mut Self, task: once () => T uses Io, ...E): Fiber<T, E>;
}
```
Now compare the two uses of `s.spawn` in the spec:
1. In `A.7`:
   ```ts
   export function serve(listener: mut Listener, db: readonly Db): void uses Io, Fail<IoErr> {
     Io.scope((s) => {
       for (const conn of listener.accept()) {     // accept() uses Io, Fail<IoErr>
         s.spawn(() => serveOne(conn, db));        // serveOne() uses Io  (NO Fail!)
       }
     });
   }
   ```
   Here, `body` uses `Io, Fail<IoErr>`, so `E` in `Scope<E>` is `Fail<IoErr>`.
   Wait: if `E` is `Fail<IoErr>`, then `s.spawn` expects a closure of type `once () => T uses Io, Fail<IoErr>`.
   `serveOne(conn, db)` has effects `uses Io`. For `() => serveOne(conn, db)` to match `uses Io, ...E`, the checker must give the closure an open effect row tail `uses Io, ...ρ` (or allow subeffecting) so that a pure/`Io`-only task can be spawned in a scope whose body fails!
2. Conversely, in `§6.1` Rule 4:
   *"Isolation is a type. A task whose effects are only `Io` cannot fail. A server that must survive a bad connection spawns tasks that handle their own errors, and the type checker proves it."*
   Wait: look at `A.7` again! Because `listener.accept()` is inside `Io.scope` and throws `Fail<IoErr>`, `E` for the whole `Scope<E>` is `Fail<IoErr>`. If `s.spawn` takes `once () => T uses Io, ...E` (with the *same* `E` as `Scope<E>`), then if `serveOne` accidentally threw `Fail<IoErr>`, **`A.7` would still type-check!** The `Fail<IoErr>` from `serveOne` would just unify with `E = Fail<IoErr>` from `listener.accept()`, silently violating §6.1 Rule 4 and the comment in `A.7` (*"`serveOne` is `uses Io` only, so a failing connection cannot cancel the server; if it could, this would not type-check without a `try`"*).

Let me show this as a concrete broken program:
```ts
// Suppose serveOne accidentally leaks Fail<IoErr>:
function badServeOne(conn: Socket, db: readonly Db): void uses Io, Fail<IoErr> { ... }

export function serve(listener: mut Listener, db: readonly Db): void uses Io, Fail<IoErr> {
  Io.scope((s) => {
    for (const conn of listener.accept()) { // forces Scope's E = [Fail<IoErr>]
      // BUG: Under §6.1's signature for Scope<E>, this type-checks!
      // Because task has type `() => void uses Io, ...E`, and E is already Fail<IoErr>!
      s.spawn(() => badServeOne(conn, db));
    }
  });
}
```
**Why it goes wrong:** Because `Scope<E>` shares a single row variable `E` between the scope body (`listener.accept()`), every `s.spawn(...)` call, and every `f.join()` call!And in `s.spawn(t);` where the `Fiber` is dropped without `.join()` (as in `A.7`), any error in `t` still cancels the scope (§6.1 Rule 2), so `spawn` *must* propagate the task's failure into the scope if tasks can fail; **or** if unjoined tasks are not allowed to fail, `spawn` and `join` have the wrong signatures.
Even worse: in `§10.2`, `p` and `q` *are* supposed to fail the scope:
```ts
const [profile, quota] = Io.scope((s) => {
  const p = s.spawn(() => db.fetchProfile(req.user)); // uses Io, Fail<IoErr>
  const q = s.spawn(() => db.checkQuota(req.token));  // uses Io, Fail<IoErr>
  [p.join(), q.join()]
});
```
Why did the author of `A.7` think `s.spawn(() => badServeOne(conn, db))` wouldn't type-check in `A.7`? Only if `s.spawn`'s closure effect is checked independently or if `spawn` without `join` requires `uses Io`!
Wait: if `spawn` takes its own effect row `<row Et>` and returns `Fiber<T, Et>`, then in `§10.2`, `p.join()` has effect `uses Io, ...Et`, which puts `...Et` into `Io.scope`'s `E`. What if the `Fiber` is *not* joined (dropped as a statement `s.spawn(...);` as in `A.7`)?
If a dropped `Fiber<T, Et>` is only legal when `Et` is `[]` (no failure), **or** if `s.spawn` has two methods / signatures:
- `s.spawn(task: once () => void uses Io): void` (fire-and-forget: task cannot fail, returns `void`)
- `s.spawnWithResult<T, row E>(...)` or `Fiber<T, E>` must be joined if `E` is non-empty!
Wait: you don't even need two methods if `Scope` is **not** parameterized by `E`:
```ts
// In effect Io:
scope<T, row E>(body: once (s: mut Scope) => T uses Io, ...E): T uses Io, ...E;

interface Scope {
  // A spawned task has its own effect row E.
  //Wait: what if it fails and is never joined?
}
```
If §6.1 Rule 1 & 2 say a spawned task can be dropped (`s.spawn(t);`) AND a failing task cancels the scope, then either:
- Fire-and-forget tasks (`s.spawn`) must not fail (`uses Io`), while tasks whose results/errors you await (`p.join()`) can fail; OR
- Every spawned task's failure row is merged into `Scope<E>`, in which case the comment in `A.7` (*"if `serveOne` could fail with `IoErr`, this would not type-check"*) is false because `listener.accept()` already puts `Fail<IoErr>` into `Scope<E>`.

**Fix:** Look at `§6.1` Rule 4 ("Isolation is a type") and `A.7`. In `A.7`, `listener.accept()` can fail with `IoErr`, while `serveOne` must not fail. To make `A.7`'s invariant actually checked by the type system:
Give `spawn` its own effect row `Et` on `Fiber<T, Et>` (removing `E` from `Scope`), AND require that **an unjoined/discarded `Fiber<T, Et>` in an expression statement `e;` has `Et = []`** (or only joins propagate `Et`, and tasks spawned with non-empty `Et` are only valid when joined). Even simpler:
If `s.spawn` is:
```ts
interface Scope<row E> { ... }
```
Ask yourselves whether `A.7`'s comment is what you want to enforce. If yes, a fire-and-forget task (`s.spawn` whose `Fiber` is discarded, or `s.spawn` vs `s.async`) cannot unify its effects with `listener.accept()`'s effects.

---

#### 5. Underdetermined rule: Bidirectional typing of Record Literals (`§2.2` vs `§10.2` and `A.5`)

`§2.2` says:
> **Record literals.** `{ f: e, … }` builds the nominal struct named by the expected type, if there is one, and a structural record otherwise. `Point { … }` names the struct explicitly.

Look at `§10.2`:
```ts
struct Request<region R> { user: Ref<str>; token: Ref<str>; }

function parse<region R>(raw: readonly u8[]): Ref<Request> uses Region<R>, Fail<#Malformed | #MalformedUtf8> {
  if (raw.len < 16) { throw #Malformed; }
  alloc({ user: copyUtf8(raw[0..8]), token: copyUtf8(raw[8..16]) })
}
```
And `A.5`:
```ts
export function new(parent: Option<Ref<Scope>>): Ref<Scope> uses Region<R> {
  alloc({ parent, names: RegionList.new() })
}
```
In both programs, `{ ... }` is passed to `alloc<region R, T>(v: T): Ref<R, T>`.
For `{ user: ..., token: ... }` to build the nominal `struct Request<R>` instead of an anonymous structural record `{ user: Ref<R, str>; token: Ref<R, str> }`, the expected return type of `parse` (`Ref<R, Request<R>>`) must push down through `alloc`'s return type `Ref<R, T>` to constrain `T = Request<R>` **before** checking `alloc`'s argument `{ ... }`!
**Fix:** In your bidirectional checker, when checking a call `f(arg1, ...)` against an expected return type `Expected`:
1. Instantiate `f`'s type parameters (`R`, `T`, etc.) with fresh unification variables.
2. **Unify `f`'s instantiated return type with `Expected` *before* checking the arguments.**
3. Then check each argument `arg_i` in **Check mode** against the now-partially-resolved parameter type `Param_i`.
If you infer argument types bottom-up before unifying the call's return type with `Expected`, `{ user: ..., token: ... }` will infer as a structural record instead of `Request<R>`, and `parse` and `Scope.new` will fail to type-check.

---

#### 6. Underdetermined rule: Exhaustiveness and typing of `match` and `handle` (`§2.3`, `§5.2`, `A.3`)

Two concrete cases in the examples require specific rules in milestone 2:

**Case A: Tuple patterns with open/closed tag unions in `A.3`.**
```ts
match ([ga.next(), gb.next()]) {
  [#Some(x), #Some(y)] => yield [x, y],
  _ => break,
}
```
Here `ga.next()` returns `Option<A>`, which is a type alias for the structural tag union `#Some(A) | #None`.
- When constructing `#Some(x)`, its inferred type must have an **open** tail `#Some(T) | ...ρ` so it can unify with any tag union containing `#Some`.
- When a tag union is written in a `type` alias or signature (`type Option<T> = #Some(T) | #None;`), it is **closed** (no `...R`), unless it is the argument of `Fail<...>` (`§3.2`).
- Notice the second arm in `A.3`: `_ => break,`. The first arm has type `void` (`yield` returns `void`), and the second arm is `break` (a statement inside a `Match` arm, even though `§2.3` grammar says `Pattern => ( Expr "," | Block )` and `break` is a `Stmt`, not an `Expr`!).
**Fix:** Since Milestone 1 already parsed `A.3`, your parser allows `break` as an `Expr` or arm body; in the type checker, give `break`, `continue`, `return`, and `throw` the type `never`, and unify `never` with any type `T` (or treat `never` as bottom).

**Case B: Typing `handle` arms and `Cont<A, B, E>` (`§5.2`, `§5.3`).**
In `§5.2`, for `handle { body } with Eff { op(x) resumes k => armBody }`:
- Suppose `body` has type `B` and effect row `Eff, ...E`.
- `op` is declared in `effect Eff` as `op(x: P): A uses ...E_op`.
- Then `k` has type `Cont<A, B, E>`.
- What effect row is `armBody` checked under? `...E` (the enclosing effects around `handle`, *without* `Eff` since the handler is deep and already wraps `k`, unless `armBody` itself re-performs `Eff` to an outer handler).
- What if `op` in the `effect` declaration itself declared secondary effects (`uses Fail<IoErr>`, as in `Io.read`)? Any secondary effects on `op` in the `effect` declaration must be part of `...E`.

---

#### 7. Decision 1: What `std` signatures need that isn't obvious from the text

When you write the `.fly` declaration files for `std` in Milestone 2, check these details from the 9 programs so you don't get stuck:
1. **String interpolation (`A.2`, `A.8`)**:
   - `A.2`: ``stdout.println(`${path}: ${e}`);`` (where `path: readonly String`, `e` is a tag union). What is the type of a template literal `` `...` ``? In `A.2` it is passed to `println(s: str)`. In `A.8` it is passed to `fmt(...)` inside a region: ``const label = fmt(`Count: ${m.count} (${m.clicks} clicks)`);``.
   - Specify the type of `` `...${e}...` `` now! If template literals have type `String` (or `str` when in a region, or a formatter), note that `A.8` wraps the template literal in `fmt(...)` to get a `str` in region `R`, whereas `A.2` passes the template literal directly to `stdout.println(...)` without `fmt`. The simplest consistent rule for Milestone 2: a template literal `` `...` `` checks each `${e}` for `Show`, and produces a `String` (which lends `str` per `§4.1`, so `stdout.println(s: str)` accepts it!), while `fmt` in `A.8` is `declare function fmt<region R>(s: str): Ref<R, str> uses Region<R>;`.
2. **Slices and indexing (`§10.2`, `A.1`, `A.4`)**:
   - `buf[0..n]` in `§10.2`: range syntax `a..b` is not in the `§2.3` EBNF, though your Milestone 1 parser handles it. `u8[512]` indexed with `0..n` produces `readonly u8[]` (or `mut u8[]`).
   - `repeat(0)` in `§10.2`: `declare function repeat<T extends Copy, comptime N: usize>(v: T): T[N];` — since Decision 3 defers `comptime`, make `repeat` a built-in in the type checker that unifies its return type with the expected array type `T[N]`.
   - `RegionList.new()` in `A.1` and `A.5`: called as an associated function `RegionList.new()`, not on an instance. In your checker, `Type.fn(...)` resolves to functions inside `impl<...> Type { ... }` that have no `self` parameter.
   - `counts.getMut(w)` in `A.2`: returns `Option<mut u64>`. And `n += 1` where `n: mut u64` requires `+=` to work on `mut T` where `T` is numeric (`§4.1` transparency).
   - `for (const x of expr)` in `A.2`, `A.3`, `A.5`, `A.6`, `A.7`:
     Notice that `expr` in `for (const x of expr)` is **two different things** across the examples!
     - In `A.2` (`for (const w of words(line))`) and `A.3` (`for (const [x, y] of zip(...))`), `expr` is a `void` expression that performs the **`Yield<T>` effect** (`§5.5`)!
     - What about `for (const path of args)` (`A.2`, where `args: readonly String[]`), `for (const line of f.lines())`, `for (const [w, n] of counts.sortedByValue())`?
     Check `§5.5`: *"A generator is any computation that uses `Yield<T>`; nothing else marks it. `for (const x of gen) { body }` handles `Yield` around `gen`."*
     Wait: in `A.2`, `args` is `readonly String[]` — a slice, NOT a call to a `Yield` function! Whereas in `A.3`, `xs.each()` is called, and in `A.5`, `self.names.each()` is called, and in `A.6`, `inbox.each()` is called!
     Why does `A.2` write `for (const path of args)` without `.each()`?
     **Fix:** In Milestone 2, `for (const p of expr)` should accept *either*:
     1. `expr` has type `void` and uses `Yield<T>` (the `§5.5` rule, used by `words(line)`, `zip(...)`, `f.lines()`, `self.names.each()`, `inbox.each()`, `listener.accept()`), **or**
     2. `expr` is a slice `T[]` / array `T[N]` / `Vec<T>` (used by `for (const path of args)` and `counts.sortedByValue()` in `A.2`).

---

### Smaller points

- **Implicitly open `Fail` in type aliases (`§5.1`, `A.1`)**:
  In `§5.1`, `read(fd: Fd, buf: mut u8[]): usize uses Fail<IoErr>;` where `type IoErr = #Reset | ...;`. And in `A.1`, `uses Region<R>, Fail<JsonErr>` where `type JsonErr = #Eof | ...;`.
  Wait: `§3.2` says *"A tag union written as the argument of `Fail` in a signature is implicitly open."* Make sure this rule applies **after expanding type aliases** in `Fail<IoErr>` and `Fail<JsonErr>`! In `§10.2`, `conn.read` (`Fail<IoErr>`) and `parse` (`Fail<#Malformed | #MalformedUtf8>`) and `throw #Unauthorized` are mixed in the same `try` block. If `Fail<IoErr>` is not opened because `IoErr` was defined via a `type` alias, `conn.read` and `parse` will fail to unify their `Fail` rows in `§10.2`!
- **`Option.cloned()` in `A.6`**:
  `store.get(key).cloned()` — `store.get(key)` returns `Option<readonly String>` (`#Some(readonly String) | #None`). Since `Option<T>` is a type alias for a structural tag union (`§3.2`), where does `.cloned()` come from? `§3.4` only defines `impl Type` for nominal types or structural types? `§2.3` allows `impl<T> Option<T> { ... }`. Make sure your checker allows inherent `impl` blocks on structural tag union aliases (`Option<T>`, `Result<T, E>`) or slices (`T[]` for `.each()`, `str` for `.splitWhitespace()`), so `std` can declare those methods.
