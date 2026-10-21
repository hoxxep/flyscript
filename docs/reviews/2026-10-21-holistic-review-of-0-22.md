# Review: holistic-review-of-0-22

- spec: 89001f0a71bd
- request: 1303bd6026c247e9
- tokens: prompt 31352, cached 0, answer 11957

## Question

Spec 0.22 (included) adopts your review of 0.21. Since then, also implemented and specified in §3.5:

- `Eq`, `Hash`, `Show`, `Clone` and `Ord extends Eq` are derivations written in Flyscript in the prelude (now a Flyscript module), over `Type.info`. The checker's structural stand-in for them is gone.
- `==`/`!=` call `Eq.eq`, `<`/`<=`/`>`/`>=` call `Ord.cmp`, and `${e}` calls `Show.show(self, out)` on anything but a primitive (strings are interpolated raw). A struct is compared, ordered or printed only if it asks (`impl Eq for Point;`); records, tuples and unions always can. `Show` writes a value as Flyscript would: `Point { x: 1, y: 2 }`, `#Some("a")`, and a multi-field payload whole, `#Line([a, b])`, which is valid Flyscript under the whole-payload rule.
- Enums keep their tags' declaration order for derivations; structural unions order tags by name, rows being sorted.

Every program in the appendix runs; 50+ rejection tests and 20+ run tests pass.

This is a holistic review, not a comptime one. Please:

1. **Soundness and coherence across the whole spec as it now stands.** Look especially at interactions between: operators calling interfaces and ownership (`a == b` borrowing both operands; `${e}` on a `view`), derivations and `Drop`/private fields/`view` types, `Ord`/`Eq` derived for float fields (NaN: is a derived `Ord` total?), `Hash`/`Eq` consistency for `HashMap` keys, effects in derived methods (a `Show` impl that wants `Io`), and `Clone` on types holding `Ref`s or `Arc`.
2. **The language as a TypeScript team would meet it.** Where would they first be surprised, blocked, or misled? Be concrete, with programs.
3. **Rank the three most valuable remaining changes** to the *design* (not the prototype), with the spec text you would write. `Soa<T>` as a template struct (`struct Soa<comptime T: Type> { comptime for … }`) is one candidate; it needs struct templates and type-level choice between `Vec<f.type>` and a nested `Soa<f.type>`. Is that worth its cost now, or is something else more important?

## Answer

### Verdicts

- **0.22 additions and prelude derivations (`§0.1`, `§2.3`, `§3.1`, `§3.2`, `§3.4`, `§3.5`, `§7.2`, `§7.3`)**: **Agree with changes.** Moving `Eq`, `Ord`, `Hash`, `Show` and `Clone` into prelude Flyscript code is a major milestone, and the 0.21 review fixes are cleanly integrated. However, several interactions between prelude derivations, ownership, floats, and `TypeInfo` have soundness or coherence holes (Problems 1–4 below).
- **Soundness and coherence across the whole spec (`Question 1`)**: **Agree with changes.** Four specific issues need fixing:
  1. `Clone` derived for `view` types or types containing `mut T` can duplicate exclusive `mut` borrows (unsound: breaks Law 1).
  2. `TypeInfo` (`§7.2`) collapses `Ref<R, T>`, `Cell<R, T>`, `RegionList<R, T>`, `Box<T>`, and structs with private fields into `#Opaque { name: str; args: Type[] }`, which creates an ambiguity between genuine opaque handles and foreign private structs, and leaves `Ref<R, T>`'s behavior in `Eq`/`Ord`/`Hash`/`Show`/`Clone` derivations underspecified.
  3. Float `NaN` and `-0.0` in derived `Eq`, `Ord`, and `Hash` break `HashMap` lookup and binary-search invariants unless specified.
  4. Operator evaluation order and two-phase borrowing when `a == b` or `` `${a} ${b}` `` desugars to `Eq.eq` / `Show.show`.
- **The language as a TypeScript team would meet it (`Question 2`)**: **Agree with changes.** Five concrete friction points will trip a TypeScript team on day one (Problems 5–8 below), most notably: closures in `map`/`filter` cannot use `throw` or `yield` or `return` from the enclosing function the way TS `for` loops do (`return` exits the closure, while `throw`/`yield` work via effect polymorphism!), and indexing a `Vec<T>` / slice with `v[i] = x` vs method borrows.
- **Top three remaining design changes (`Question 3`)**: Ranked below with concrete spec text: **(1) Lock down `Clone` / `Eq` / `Ord` / `Hash` derivation semantics (forbidding `Clone` on `mut T`, total float ordering/hashing, and `Ref<R, T>` transparency)**, **(2) Replace `comptime function Ring(...): Type` and built-in `Soa<T>` with template `struct`/`enum` declarations (`§7.1`, `§7.4`)**, and **(3) Specify indexing/slicing (`Index` / `v[i]` / `v[a..b]`) and `for...of` mutable iteration (`for (const x of mut xs)`)**.

---

### Problems

#### 1. Derived `Clone` on types containing `mut T` duplicates an exclusive borrow (`§3.5`, `§4.1`, `§4.2`, `§7.3`)

Look at `§3.5` and `§7.3`:
> *"Types that belong to no module — primitives, records, tuples and tag unions — get a derivation directly whenever they have no impl of their own... `Eq`, `Hash`, `Show` and `Clone` are derived this way in the prelude"*

And look at `TypeInfo` in `§7.2`:
```ts
| #Borrow { mutable: bool; type: Type }
```
What happens when `Clone` is called on a record, tuple, `Option`, or `view struct` that contains a `mut T` (or when `Clone`'s derivation inspects `#Borrow` or `#Record` fields)?
```ts
view struct Editor {
  buf: mut u8[];
}
impl Clone for Editor; // or a structural tuple `[mut u8[], usize]` which gets Clone automatically!

export function aliasMut(xs: mut u8[]): void {
  const pair: [mut u8[], usize] = [xs, 0];
  // `pair` is a tuple (belongs to no module), so `impl<comptime T: Type> Clone for T` applies!
  // And what is the return signature of `Clone.clone(self: readonly Self): Self`?
  const copy = pair.clone();
  // Now both `pair[0]` and `copy[0]` hold live `mut u8[]` borrows of `xs` simultaneously!
  pair[0][0] = 1;
  copy[0][0] = 2; // UNSOUND: two live `mut` borrows of the same memory!
}
```
Look closely at two things going wrong here:
1. **`Clone.clone`'s signature and borrow tracking (`§4.2`):**
   What is the signature of `Clone` in the prelude?
   ```ts
   interface Clone {
     function clone(self: readonly Self): Self;
   }
   ```
   Wait: `self` is `readonly Self`! By `§4.2`:
   > *"Results carry their sources' borrows. A call's result can hold the borrows of its sources: the parameters named in its `from` clause; without one, the receiver for a method..."*
   If `Self` is class 1 (e.g. `String`, `Vec<i32>`, `{ a: String }`), `clone` returns a **freshly owned** `Self` that holds **no borrow** of `self` (`§4.2`: *"A result whose type cannot hold a borrow at all (class 1...) holds nothing"*).
   **But** if `Self` is class 2 (e.g. `{ s: str }`, `readonly T`, or `[mut u8[], usize]`):
   - First, inside `clone(self: readonly Self)`, `self` is only borrowed `readonly`! A `readonly` borrow of a `mut T` can only be read as `readonly T`, **never** copied out as a new `mut T`!
   - Second, if `Clone` is allowed on `mut T` (or if `#Borrow { mutable: true, ... }` or field projection `self.[f.name]` in the derivation copies a `mut` borrow), it duplicates an exclusive `mut` reference from a `readonly` receiver!
   - Third, why would anyone ever `clone()` a class-2 borrow (`str`, `readonly T[]`, `view struct`) when `readonly T`, `str`, and `readonly T[]` are **already `Copy`** (`§4.1`), and `mut T` **must never** be cloned?
   Wait: what about a struct or record that mixes owned data and a `readonly` borrow, or a container of class-1 values? Containers (`Vec<T>`, `Box<T>`, `HashMap<K, V>`) only hold class-1 types (`§4.2`). Every `readonly` borrow (`str`, `readonly T`, `readonly T[]`) is already `Copy` (`§4.1`). A `mut` borrow (`mut T`, `mut T[]`) can *never* be cloned.

**Fix:**
1. In thechecker's ownership rules (`§4.1` / `§4.2`), reading a `mut U` field through a `readonly` receiver (`self: readonly Self`) must yield `readonly U`, not `mut U` — you can never obtain a `mut U` from a `readonly` path! (Verify that `flyc` enforces this when projecting `self.[f.name]` on a `readonly Self` whose field is `mut U`.)
2. Even simpler and cleaner: **`Clone` should only be implemented for class-1 types (or `#Borrow { mutable: false }` if class-2 `Clone` is desired, and never `#Borrow { mutable: true }`)**. In fact, if `interface Clone` is for duplicating owned values, rejecting `#Borrow { mutable: true }` in the `Clone` derivation (and ensuring `readonly` projection demotes `mut` fields to `readonly`) closes the hole completely.

---

#### 2. `Eq`, `Ord`, and `Hash` on `f32`/`f64` (`NaN` and `-0.0`) break `Ord` totality and `HashMap` invariants (`§3.5`)

In `§3.5`:
> *"`Eq`, `Hash`, `Show` and `Clone` are derived this way in the prelude, so an error union prints, compares and hashes with no code... `Ord extends Eq` is derived too... `==` and `!=` are built in for primitives and call `Eq.eq` on anything else, and `<`, `<=`, `>` and `>=` likewise call `Ord.cmp`"*

Now consider this program:
```ts
import { HashMap } from "std/collections";

type Key = { x: f64 }; // gets derived Eq, Ord, Hash automatically (§3.5)

export function floatBugs(): void {
  // 1. -0.0 vs +0.0 in HashMap:
  let map = HashMap.new<Key, i32>();
  map.insert({ x: 0.0 }, 1);
  // Under IEEE 754, `-0.0 == 0.0` is `true`, so `Eq.eq({ x: 0.0 }, { x: -0.0 })` is `true`.
  // But if `Hash` hashes the raw IEEE 754 bits of `f64` (0x0000000000000000 vs 0x8000000000000000),
  // then `hash({ x: 0.0 }) != hash({ x: -0.0 })`!
  // Violates the fundamental Hash/Eq law: k1 == k2 ==> hash(k1) == hash(k2)!
  const found = map.get({ x: -0.0 }); // returns #None even though { x: -0.0 } == { x: 0.0 }!

  // 2. NaN in Ord.cmp and HashMap:
  const nan = 0.0 / 0.0;
  // In IEEE 754, `nan < 1.0`, `nan > 1.0`, and `nan == 1.0` are all `false`!
  // How does `Ord.cmp(nan, 1.0)` return `Ordering = #Less | #Equal | #Greater`?
  // If `Ord.cmp` writes `if (a < b) { #Less } else if (a > b) { #Greater } else { #Equal }`,
  // then `Ord.cmp(nan, 1.0)` returns `#Equal` while `nan == 1.0` is `false`!
  // And `Ord.cmp(nan, 1.0) == #Equal` and `Ord.cmp(nan, 2.0) == #Equal` breaks transitivity (`1.0 == 2.0`),
  // corrupting `sortedByValue()` (A.2) or binary search!
}
```
Notice how serious both parts are:
1. If `Hash` for `f32`/`f64` hashes raw bits without normalizing `-0.0` to `+0.0`, `a == b` does not imply `hash(a) == hash(b)`.
2. Because `Ordering` in `§3.5` is `#Less | #Equal | #Greater` (total, not partial), a naive `if (a < b) #Less else if (a > b) #Greater else #Equal` makes `NaN` compare `#Equal` to **every number**, destroying sorting (`counts.sortedByValue()` in `A.2`!).
3. Meanwhile, for `==` and `<` on primitive `f64`, TypeScript/IEEE-754 programmers expect `0.0 == -0.0` to be `true`. What about `Eq.eq` and `Ord.cmp`?

**Fix:**
Keep primitive `<`, `<=`, `>`, `>=`, `==`, `!=` on `f32`/`f64` as standard IEEE 754 instructions, and specify in `§3.5` how `Eq`, `Ord`, and `Hash` behave on floats:
- In `Hash` for `f32`/`f64`: normalize `-0.0` to `+0.0` (and canonicalize all `NaN`s to a single bit pattern) before hashing bits.
- In `Eq.eq` and `Ord.cmp` for `f32`/`f64`: either use IEEE totalOrder (with `-0.0 == +0.0` and `NaN == NaN` ordered above `+∞`, just like Java `Double.compare` / Rust `total_cmp` / JS `SameValueZero`), **or** do not implement `Ord` / `Hash` for `f32`/`f64` (so structs/records with floats cannot be `HashMap` keys without a custom impl).
Wait: in `A.2`, `counts.sortedByValue()` sorts `u64`, but sorting structs or records containing `f64` (like `Particle` or `Point`) is super common! Using **canonical total ordering for `Eq.eq`, `Ord.cmp`, and `Hash.hash` on floats** (`-0.0 == +0.0`, `NaN == NaN` and `NaN > +∞`, with `-0.0` and `NaN` canonicalized in `Hash`) makes `Ord` genuinely total, preserves `x == y <=> cmp(x, y) == #Equal`, and preserves `x == y ==> hash(x) == hash(y)` with zero new interfaces (no `PartialEq` / `PartialOrd` split needed!).

---

#### 3. How do `Ref<R, T>`, `Box<T>`, and `Arc<T>` behave in `Type.info` and prelude derivations (`§3.5`, `§4.5`, `§4.6`, `§7.2`)?

Look at `§7.2`:
```ts
type TypeInfo =
  | #Int { signed: bool; bits: u8 } | #Float(u8) | #Bool | #Str | #Void | #Fn
  | #Record(Field[]) | #Tuple(Type[]) | #Union(TagInfo[])
  | #Struct { name: str; fields: Field[] } | #Enum { name: str; tags: TagInfo[] }
  | #Array { item: Type; len: usize } | #Slice(Type) | #Borrow { mutable: bool; type: Type }
  | #Opaque { name: str; args: Type[] };
```
Now look at `A.5` (the symbol table in a region):
```ts
export struct Decl<region R> { name: Ref<str>; ty: Cell<u32>; visiting: Cell<bool>; }
export struct Scope<region R> {
  parent: Option<Ref<Scope>>;
  names: RegionList<{ name: Ref<str>; decl: Ref<Decl> }>;
}
...
for (const b of self.names) { if (b.name == name) { return #Some(b.decl); } }
```
Look at `if (b.name == name)` in `A.5`!
- `b.name` has type `Ref<R, str>`.
- `name` has type `str`.
- Why does `b.name == name` work in `A.5`? Because `Ref<R, T>` lends `readonly T` (`§4.1`), or because `Ref<R, T>` is used as `readonly T` (`§4.6`)!
Wait: what if someone compares two region references `b.name == other.name` (both `Ref<R, str>`), or derives `Eq` / `Show` / `ToJson` on a struct or enum holding `Ref<R, T>` or `Box<T>` (like `enum Expr { #Num(f64), #Add(Box<Expr>, Box<Expr>) }` in `§3.3` or `enum Json<region R>` in `§4.6`)?
```ts
enum Expr { #Num(f64), #Add(Box<Expr>, Box<Expr>), #Neg(Box<Expr>) }
impl Eq for Expr;
impl Show for Expr;

export function testExpr(a: readonly Expr, b: readonly Expr): bool {
  println(`${a}`);
  a == b
}
```
What happens here?
1. `Expr` asks for `impl Eq for Expr;` and `impl Show for Expr;`.
2. Those derivations recurse into the payload of `#Add(Box<Expr>, Box<Expr>)`, which calls `Box<Expr>.eq` and `Box<Expr>.show`!
3. Does the prelude provide `impl<T extends Eq> Eq for Box<T>`, `Ord for Box<T>`, `Hash for Box<T>`, `Show for Box<T>`, `Clone for Box<T>` (and likewise for `Ref<R, T>` and `Arc<T>`)?
4. What about `Ref<R, str>` when `b.name == name` (`Ref<R, str> == str`)?
   Wait: `==` calls `Eq.eq(self: readonly Self, other: readonly Self): bool` (`§3.5`).
   In `b.name == name`:
   - Left operand `b.name` is `Ref<R, str>`.
   - Right operand `name` is `str`.
   - Those are **two different types** (`Ref<R, str>` vs `str`)!
   - If `==` resolves `Eq.eq` on the left operand's type `Ref<R, str>`, then `other` expects `readonly Ref<R, str>`, and a `str` does **not** lend `Ref<R, str>` (it's the other way around: `Ref<R, str>` lends `str`!)!
   - How did `b.name == name` in `A.5` type-check? Only if `Ref<R, T>` auto-derefs/lends to `T` on the left-hand side of `==`, or if `==` unifies both sides after lending!
   Wait: look at `§3.1` and `§4.1`:
   > *"Wherever a borrow of `U` is expected, an owner that lends `U` may be passed: `String` lends `str`, `Vec<T>` lends `T[]`, `Box<T>` lends `T`, and `Ref<R, T>` lends `readonly T`."*
   What if a TypeScript programmer writes:
   ```ts
   const s: String = "hello".toString();
   if (s == "hello") { ... } // `s` is `String`, `"hello"` is `str`!
   ```
   Look at `if (s == "hello")`!
   **Every TypeScript and Rust programmer will write `if (s == "hello")` where `s: String` and `"hello": str`!**
   Wait: what happens in Flyscript 0.22 when someone writes `s == "hello"` (comparing `String` with `str`) or `"hello" == s` (comparing `str` with `String`) or `b.name == name` (`Ref<R, str>` with `str`)?!
   Let's trace `s == "hello"` under `§3.5`:
   - `s` has type `String`.
   - `"hello"` has type `str`.
   - `Eq` has signature `function eq(self: readonly Self, other: readonly Self): bool`.
   - For `s == "hello"`, `Self = String`, so `self: readonly String` and `other: readonly String`.
   - The right operand `"hello"` is `str`. **A `str` is NOT a `readonly String`!** (You cannot lend a `str` as a `readonly String`; `String` lends `str`, not vice versa!)
   - So under `Eq.eq(self: readonly Self, other: readonly Self)`, **`s == "hello"` where `s: String` fails to typecheck** unless `"hello"` is converted or `==` lends both sides to their shared borrowed target `str`!
   - And in `A.5`, `b.name == name` has `b.name: Ref<R, str>` and `name: str`. If `Self = Ref<R, str>`, `other` expects `readonly Ref<R, str>`, which `name: str` is NOT!

**Fix:**
This is a crucial catch. Look at why `b.name == name` and `s == "hello"` must work:
1. When checking `a == b`, `a != b`, `a < b`, `a <= b`, `a > b`, `a >= b`: if one operand's type lends the other's (e.g., `String` or `Ref<R, str>` lends `str`; `Vec<T>` lends `T[]`; `Box<T>` or `Ref<R, T>` lends `readonly T`), the operator compares them at the borrowed type (`str`, `T[]`, `T`)!
2. And in the prelude, `Box<T>`, `Arc<T>`, and `Ref<R, T>` should implement `Eq`, `Ord`, `Hash`, `Show`, `Clone` (forwarding to `T`; for `Ref<R, T>` and `Arc<T>`, `Clone` just copies the `Ref` or increments the `Arc`).

---

#### 4. Operator desugaring and two-phase borrows (`§3.5`, `§4.1`)

In `§3.5`:
> *"`==` and `!=` are built in for primitives and call `Eq.eq` on anything else, and `<`, `<=`, `>` and `>=` likewise call `Ord.cmp`; `` `${e}` `` writes a primitive or a string as it is and anything else with `Show`"*

Consider this program:
```ts
export function check(mut v: Vec<i32>): bool {
  // In TypeScript, `v.pop() == v.pop()` or `v == { v.push(1); v }`
  // Wait: `Eq.eq(self: readonly Self, other: readonly Self)` borrows both operands `readonly`.
  // What if someone writes:
  v.pop() == #Some(1)
}
```
Here `v.pop()` returns an rvalue `Option<i32>`, while `Eq.eq` takes `self: readonly Self, other: readonly Self`.
In `§2.2` / `§4.1`:
- Does an rvalue (like `v.pop()` or `#Some(1)` or `` `${v.pop()}` ``) automatically lend a temporary `readonly` borrow when passed to `Eq.eq`, `Ord.cmp`, `Show.show`, or a `readonly` method receiver `(v.pop()).isSome()`?
Look at `§4.1`: `§4.1` defines borrows of *bindings* (`const`/`let`), and `A.9` relies on temporary borrowing:
> *"Each reply borrows its reason for exactly as long as `stringify` needs it, so the template strings need no `String`."*
Specifically, in `A.9`:
```ts
stringify(#Rejected { reason: `missing ${field}` })
```
Here `` `missing ${field}` `` evaluates to an rvalue `String`, which is lent as `reason: str` inside `#Rejected { reason }`, and that temporary `String` stays alive for the duration of the enclosing call `stringify(...)`!
That temporary lifetime rule is relied on in `A.9` and in `v.pop() == #Some(1)`, **but `§4.1` never states the temporary lifetime rule!**
Wait: what if someone writes:
```ts
const r = #Rejected { reason: `missing ${field}` };
// Does the temporary `String` live to the end of the block (like Rust's temporary lifetime extension)
// or is it dropped at the end of the statement `const r = ...;`, leaving `r.reason` dangling?!
```
Look at that program:
```ts
type Reply = #Rejected { reason: str };

export function danglingTemp(field: str): String {
  const r = #Rejected { reason: `missing ${field}` };
  // `` `missing ${field}` `` produces a temporary `String` and lends it as `str` into `r.reason`.
  // When is that temporary `String` dropped?!
  // If it is dropped at the `;` of `const r = ...;`, then `r.reason` is now a DANGLING POINTER!
  // If it lives as an anonymous local in the enclosing block (tracked in Θ and locked in Γ by `r`),
  // then `r` holds a borrow of that anonymous local until `r`'s last use, and the anonymous local is dropped when the block exits!
  r.reason.toString()
}
```
Read that again!
If every rvalue that is borrowed (such as `` `missing ${field}` `` lent as `str`, or `v.pop() == #Some(1)`) is simply materialized into an **anonymous local binding in the enclosing block** (so it is owned by the block in `Θ`, locked in `Γ` while `r` holds a borrow of it, and dropped at the end of the block by `§5.6`), then:
1. `stringify(#Rejected { reason: \`missing ${field}\` })` works.
2. `const r = #Rejected { reason: \`missing ${field}\` };` is **completely memory-safe** (never dangles!) because `r` holds the borrow of the anonymous local until `r`'s last use!
3. And you cannot return `r` from the function (`§4.2`: *"everything the returned value borrows must come from a source, never from a local"*), which catches returning a borrow of a temporary!

**Fix:**
Add one sentence to `§4.1`:
> *"Borrowing or lending a non-place expression stores its value in an anonymous local of the enclosing block."*

That single sentence makes `A.9`, `v.pop() == #Some(1)`, and `const r = #Rejected { reason: \`...\` }` 100% sound under the existing local-borrow rules!

---

#### 5. Where a TypeScript team will first be surprised or blocked (`Question 2`)

Here are the four places a TypeScript team will hit first, each with a concrete program:

##### 5a. Returning early from inside `.map` / `.filter` / `Io.scope` vs `for...of` (`§2.2`, `§5.1`, `§5.5`)
A TypeScript developer has a `for...of` loop and refactors it, or writes a helper with `.iter().map(...)`:
- In Flyscript, because effects (`Fail`, `Yield`, `Io`) are polymorphic on higher-order functions (`§5.1`), **`throw` and `yield` inside `xs.map((x) => ...)` work transparently!** (In TypeScript, `yield` inside `.map(...)` is a syntax error! In Flyscript, `xs.map((x) => { yield x; x + 1 })` works out of the box because `Yield` is just an effect in `...E`!)
- **However**, what if a TypeScript developer writes `forEach` or tries to mutate a local counter inside `.map`?
```ts
export function sumPositives(xs: readonly i32[]): i32 {
  let total = 0;
  // A TS programmer writes:
  const doubled = xs.iter().map((x) => {
    if (x > 0) { total += x; } // closure captures `total` by `mut` borrow!
    x * 2
  }).collect();
  total
}
```
Look at what happens in `xs.iter().map(...)` (`§4.3`, `§5.5`):
- The closure passed to `.map(...)` modifies `total`, so its type is `mut (i32) => i32` (`§4.3`).
- Does `Gen.map` accept a `mut (T) => U` closure, or only a shared `(T) => U` closure?
Check `§5.1` (`map` signature):
```ts
function map<T, U, row E>(xs: readonly T[], f: (x: readonly T) => U uses ...E): Vec<U> uses ...E
```
In `§5.1`, `f` is written `(x: readonly T) => U uses ...E` — **without `mut`!**
If `map`, `filter`, `Gen.map`, `Gen.filter` declare `f: (x: ...) => ...` instead of `f: mut (x: ...) => ...`, then **no closure passed to `map` or `filter` can ever mutate a local variable (`total += x`)!**
Wait: since a `(A) => B` closure (which only reads captures) can always be passed where a `mut (A) => B` is expected (because calling sequentially in `map`/`filter` only needs one caller at a time!), **every sequential higher-order function (`map`, `filter`, `fold`, `Fail.capture`, `Fail.map`, `generate`) should take `mut` (or `once` for single-call functions like `Fail.capture`, `Fail.map`, `generate`, `region`) closures!**
Only parallel functions (`par`, `parReduce` in `§6.5`) require non-`mut` `(A) => B` closures!
Check `§5.1`, `§5.4`, `§5.5`: if `map` or `filter` takes `(x: readonly T) => U` instead of `mut (x: readonly T) => U`, the TS programmer in `sumPositives` above gets rejected for `total += x` inside `.map(...)` for no reason!

##### 5b. Mutating elements in a `for...of` loop (`§5.5`)
A TypeScript programmer wants to zero out or update elements of an array or `Vec` in place:
```ts
export function zeroOut(xs: mut i32[]): void {
  for (let x of xs) {
    x = 0; // Wait: what does `for (let x of xs)` do?!
  }
}
```
Look at `§5.5`:
```ts
interface Iterable<T, row E = []> {
  function each(self: readonly Self): void uses Yield<T>, ...E;
}
```
`Iterable.each` takes `self: readonly Self`!
So `for (let x of xs)` iterates over `xs` by `readonly` borrow (yielding `i32` or `readonly T`), and `x = 0` only mutates the local copy `x`, **silently leaving `xs` unchanged** (or if `T` is not `Copy`, yielding `readonly T` where field assignment `p.x = 0` is rejected)!
How *does* a Flyscript programmer mutate elements of a slice or `Vec` in a `for...of` loop (like `counts.getMut(w)` in `A.2`)?
By calling `.iterMut()` (or `xs.eachMut()`):
```ts
for (const x of xs.iterMut()) { x = 0; } // `x: mut i32`, transparent borrow written in place!
```
Wait: look at `§4.1` (`match (counts.getMut(word)) { #Some(n) => { n += 1; } }`):
In `§4.1`, `n: mut u64` is a transparent mutable borrow, so `n += 1` mutates the entry in place, **whereas** `n = 0` on a `let n: mut u64` or `const n: mut u64` — wait:
Read `§4.1` carefully!
> *"Borrows are transparent: a borrow binding reads and writes as the value it refers to, and cannot be re-pointed."*
Look at that sentence in `§4.1`:
Because a borrow binding **cannot be re-pointed** and **writes as the value it refers to**, if `x` has type `mut i32` (from `xs.iterMut()`), then `x = 0` (even when `const x` is bound in `for (const x of xs.iterMut())`!) writes `0` into the borrowed slot of `xs`!
Wait: does `const n: mut u64` allow `n += 1` and `n = 0`?
Look at `A.2`:
```ts
match (counts.getMut(w)) {
  #Some(n) => { n += 1; },
```
In a `match` arm pattern `#Some(n)`, is `n` bound like `const` or `let`? And in `§2.1`:
> *"`const` forbids mutation as well as reassignment."*
Hold on! Look at `§2.1` vs `§2.2` vs `A.1` vs `A.2`:
- `§2.1`: *"`const` forbids mutation as well as reassignment. With one owner there is no aliasing, so 'shallow' and 'deep' immutability coincide."*
- `§2.2`: *"Parameters bind like `let`. An owned parameter may be mutated and lent `mut` by its function."*
- What about `const p: mut Point` or `for (const x of ...)` or `#Some(n)` where `n: mut u64`?
If `const` forbids mutation on owned values, why did `#Some(n) => { n += 1; }` work in `A.2`, and why did `par(mut ps, (p, _) => { p.pos.x += ... })` work in `A.4`? Because `n` has type `mut u64` (a mutable borrow, not an owned value)!
Make sure `§4.1` is explicit: a binding whose type is `mut T` can always write through the borrow (even if bound by `const` or a pattern), whereas an owned binding can only be mutated or lent `mut` if declared `let` (or a parameter). And make sure `xs.iterMut()` (or `for (const x of mut xs)`) is in the spec so TS programmers know how to mutate a slice/`Vec` in a loop!

##### 5c. Closures capturing a local variable in a loop or sequential helper (`§2.2`, `§4.3`)
In TypeScript, you do not write `mut` at call sites (`conn.read(mut buf)`).
In Flyscript (`§2.2`):
> *"Mutable borrows are visible at the call site. `read(mut buf)` lends `buf` mutably; `parse(buf)` lends it read-only. The one exception is a method's receiver, which is lent in whatever mode the method declares: `conn.read(mut buf)` borrows `conn` mutably."*
What about calling a local `mut` closure `f(x)`?
```ts
export function counter(): i32 {
  let count = 0;
  let inc = () => { count += 1; count }; // `inc` has type `mut () => i32`
  inc() + inc()
}
```
Calling `inc()` is a free-function-syntax call on a `mut` closure binding `inc`. It does not require `(mut inc)()` because `inc` is the callee (receiver of the call), just like a method receiver. Make sure `flyc` allows `let inc = ...; inc()` without ceremony.

##### 5d. Structural records vs nominal structs in TypeScript (`§2.2`, `§3.2`, `§3.3`)
In TypeScript, `interface Point { x: number; y: number }` is structural, so:
```ts
struct Point { x: f64; y: f64; }
function takePoint(p: Point): f64 { p.x + p.y }

export function tsSurprise(): f64 {
  const p = { x: 1.0, y: 2.0 }; // inferred as structural record `{ x: f64; y: f64 }`, NOT `Point`!
  takePoint(p) // ERROR: expected `Point`, found `{ x: f64; y: f64 }`!
}
```
Look at why `tsSurprise()` fails:
- `takePoint({ x: 1.0, y: 2.0 })` works (`§2.2`: *"`{ f: e, … }` builds the nominal struct named by the expected type, if there is one, and a structural record otherwise"*).
- **But** extracting `const p = { x: 1.0, y: 2.0 }; takePoint(p)` (the single most common refactoring in TypeScript!) changes `p`'s type from `Point` to `{ x: f64; y: f64 }`, which then fails at `takePoint(p)`!
Wait: this is an intentional consequence of nominal `struct` vs structural record (`§3.3`), and the error message can make it painless: when `{ f: T, ... }` fails to unify with `struct S` having the exact same fields, the diagnostic should say: `expected struct 'Point', found anonymous record; write 'const p: Point = ...' or 'Point { ... }'`.

---

### Question 3: Top Three Remaining Design Changes (Ranked by Value)

Here are the top three design changes remaining before freezing 1.0, with exact spec text.

---

#### Rank 1: Template `struct` and `enum` declarations — replacing `comptime function Ring(...): Type` and built-in `Soa<T>` (`§2.3`, `§7.1`, `§7.4`, `§11`)

**Why this is #1:**
You asked whether making `Soa<T>` a template struct (`struct Soa<comptime T: Type> { comptime for ... }`) is worth its cost now.
Look at what happens if you do this:
1. **It actually *shrinks* the grammar and removes a concept!**
   Right now, `§2.3` and `§7.1` have **two completely separate mechanisms** for type-level templates:
   - `TypeParam = ... | "comptime" Ident ":" Type` on `struct`/`enum`/`function`/`impl` (angle brackets: `Soa<Particle>`), **and**
   - `comptime function Ring(T: Type, N: usize): Type { ... struct { ... } }` called in type position via `Path "(" Expr { "," Expr } ")"` and anonymous `"struct" "{" { Field } "}"` in `Expr`!
   Why did `Ring(u8, 1024)` in `§7.1` use a `comptime function` returning an anonymous `struct { ... }` expression? Only because `comptime N: usize` was used as a parameter!
   Look at `§2.3` `TypeParam`:
   ```ebnf
   TypeParam = "region" Ident | "row" Ident [ "=" Type ] | "comptime" Ident ":" Type
             | Ident [ "extends" Bounds ] [ "=" Type ] ;
   ```
   `TypeParam` **already allows `"comptime" Ident ":" Type`** (where `Type` in the grammar is any type: `Type`, `usize`, etc.)!
   So `Ring` in `§7.1` can simply be a template `struct`:
   ```ts
   struct Ring<T, comptime N: usize> {
     comptime assert(N > 0 && (N & (N - 1)) == 0, "capacity must be a power of two");
     buf: T[N];
     head: usize;
     tail: usize;
   }
   type ByteRing = Ring<u8, 1024>;
   ```
   Look what that buys you:
   - **Deletes** `Path "(" Expr { "," Expr } ")"` from `Type` in `§2.3`!
   - **Deletes** `"struct" "{" { Field } "}"` from `Expr` in `§2.3`!
   - Now every generic type in Flyscript uses `<...>` consistently (`Ring<u8, 1024>`, `Soa<Particle>`), instead of splitting between `Ring(u8, 1024)` and `Soa<Particle>`!
   - Unlike an anonymous `struct { ... }` returned from a function, a template `struct Ring<T, comptime N: usize>` or `struct Soa<comptime T: Type>` is a real nominal `struct` declaration, so you can write `impl<T, comptime N: usize> Ring<T, N> { ... }` and `impl<comptime T: Type> ParSplit for Soa<T> { ... }`!
2. **And how does `Soa<T>` choose between `Vec<f.type>` and `Soa<f.type>` for each field?**
   With `comptime match` (which you just added to `Generate(X)` in 0.22!) inside `struct Soa<comptime T: Type>`:
   ```ts
   export struct Soa<comptime T: Type> {
     len: usize;
     comptime for (const f of fieldsOf(T)) {
       comptime match (Type.info(f.type)) {
         #Struct { .. } | #Record(_) => { [f.name]: Soa<f.type>; },
         _                           => { [f.name]: Vec<f.type>; },
       }
     }
   }
   ```
   Look at those 8 lines of Flyscript! Because 0.22 already added `comptime match` to `Generate(X)`, **you don't even need a type-level `if` expression or `comptime function Plane(T: Type): Type`!** `Generate(Field)` inside `struct Soa<comptime T: Type>` can already choose `{ [f.name]: Soa<f.type>; }` vs `{ [f.name]: Vec<f.type>; }` using the exact `comptime match` syntax already in `§2.3`!

**Concrete spec text to write:**
- In **`§2.3` (Grammar)**:
  Remove `Path "(" Expr { "," Expr } ")"` from `Type` and remove `"struct" "{" { Field } "}"` from `Expr`. Allow `comptime Expr ";"` (for `comptime assert`) inside `Struct`, or check it in `Soa`/`Ring`'s constructor.
- In **`§7.1` (Two kinds of type parameter)**:
  Replace the `Ring` paragraph and example with:
  > *"A `struct`, `enum`, `function` or `impl` may take `<comptime X: T>` parameters (where `T` is `Type` or a primitive type) and is specialized for each tuple of arguments it is used at:*
  > ```ts
  > struct Ring<T, comptime N: usize> {
  >   buf: T[N]; head: usize; tail: usize;
  > }
  > type ByteRing = Ring<u8, 1024>;
  > ```
  > *"*
- In **`§7.4` (`Soa<T>`)**:
  > *"`Soa<comptime T: Type>` is a template struct that flattens `T`'s fields recursively into planes — a `Vec<f.type>` for a scalar field and a nested `Soa<f.type>` for a struct or record field, chosen with `comptime match` — and implements `ParSplit` with a nested view record."*

---

#### Rank 2: Make Prelude Derivations (`Clone`, `Eq`, `Ord`, `Hash`, `Show`) Airtight (`§3.5`, `§4.1`, `§7.2`)

**Why this is #2:**
As shown in Problems 1–4 above, moving `Eq`, `Ord`, `Hash`, `Show`, and `Clone` into prelude Flyscript code exposed four sharp edges that need to be settled in the spec:
1. `Clone` must never duplicate a `mut T` borrow (`#Borrow { mutable: true }` is not `Clone`, and reading a `mut T` field through a `readonly` receiver yields `readonly T`).
2. Float `Eq.eq`, `Ord.cmp`, and `Hash.hash` must be consistent and total (`-0.0 == +0.0` with equal hashes, and `NaN` ordered deterministically in `Ord.cmp` / `Eq.eq` / `Hash.hash`) so `HashMap` and `Ord` sorting cannot corrupt data or lose keys.
3. Comparing or ordering a value that lends another (`s == "hello"` where `s: String`, or `b.name == name` where `b.name: Ref<R, str>` in `A.5`) lends the owner to the borrowed type, and `Box<T>`, `Ref<R, T>`, and `Arc<T>` forward `Eq`, `Ord`, `Hash`, `Show`, and `Clone`.
4. Higher-order sequential callbacks (`map`, `filter`, `forEach` / `each`, `Fail.capture`, `Fail.map`, `generate`) take `mut` or `once` closures so capturing and mutating local state (`total += x`) inside `.map` or `.filter` works as TypeScript programmers expect.

**Concrete spec text to write:**
- In **`§3.5` (Derived interfaces)**:
  Add:
  > *"`Clone` is derived for types that contain no `mut` borrow; `Box<T>`, `Vec<T>`, `String` and `HashMap<K, V>` clone their contents, while `Ref<R, T>`, `Arc<T>` and `readonly` borrows copy the reference. On floats, `Eq.eq`, `Ord.cmp` and `Hash.hash` use total ordering (`-0.0` and `0.0` are equal and hash alike, and `NaN` equals itself and orders after `+∞`). When `==`, `!=`, `<`, `<=`, `>` or `>=` compares an owner with the type it lends (`String` with `str`, `Ref<R, T>` with `T`), the owner lends."*
- In **`§4.1` (Values, moves and borrows)**:
  Add:
  > *"Reading a `mut T` field through a `readonly` borrow yields `readonly T`. Borrowing or lending a non-place expression stores its value in an anonymous local of the enclosing block."*

---

#### Rank 3: Specify Indexing, Slicing, and Mutable Iteration (`v[i]`, `v[a..b]`, `iterMut`) (`§2.3`, `§3.1`, `§5.5`)

**Why this is #3:**
Look across the spec and appendix:
- `A.1` uses `self.src[self.pos]`, `self.src[start..self.pos - 1]`.
- `§5.6` uses `v[0..1]`.
- `§10.2` uses `raw[0..8]`, `buf[0..n]`.
- `§3.1` says `t[0]` indexes a tuple by a constant.
Yet **nowhere in `§2.3` (Grammar) or `§3.1` or `§4.1` are slice/array/Vec indexing `e[i]`, range slicing `e[a..b]`, or mutable iteration `xs.iterMut()` specified!**
Look at `§2.3` `Expr`:
- `Expr` has `Expr "." "[" Expr "]"` (computed field access), but it doesn't even list `Expr "[" Expr "]"` or `Expr "[" [ Expr ] ".." [ Expr ] "]"`!
- And in `§4.1`: when `v` is a `Vec<T>` or `T[N]` or `mut T[]`, `v[i]` is a **place** (`v[i] = x` and `v[i].field += 1` work in place without moving `v[i]` out of the slice, and `mut v[i]` borrows it mutably), whereas `v[a..b]` borrows `v` as `readonly T[]` (or `mut T[]` when written `mut v[a..b]`).

**Concrete spec text to write:**
- In **`§2.3` (Grammar)**:
  Add `Expr "[" Expr "]"` and `Expr "[" [ Expr ] ".." [ Expr ] "]"` to `Expr`.
- In **`§3.1` (Primitives, strings, arrays)**:
  Add:
  > *"Indexing `xs[i]` on an array, slice or `Vec<T>` is a place of type `T` (checked against `0 <= i < xs.len()`, panicking on out-of-bounds); slicing `xs[a..b]` borrows `readonly T[]` from `xs` (`mut xs[a..b]` borrows `mut T[]`). `str[a..b]` borrows a `str` slice panicking if `a` or `b` is not on a UTF-8 char boundary."*
- In **`§5.5` (Iteration)**:
  Add:
  > *"`xs.iterMut()` on a mutable slice or `Vec<T>` yields `mut T` elements, so `for (const x of xs.iterMut()) { x += 1; }` updates `xs` in place."*

---

### Smaller points

- **`Show` with effects (`Question 1`):**
  You asked whether a `Show` impl might want `Io`. Keep `Show.show(self: readonly Self, out: mut String): void` **pure** (no `uses` clause). Why? Because string interpolation `` `…${e}…` `` is used everywhere in pure code, error construction (`A.9`), and assertions; if `Show` had an effect row, every string interpolation over a generic type would infect its caller with effects. Writing directly to an I/O stream is `Io.write` / `println`, which formats into a stack/region buffer or `String` first.
- **`Drop` and private fields in derivations (`Question 1`, `§4.1`, `§7.3`):**
  Can a `struct` that implements `Drop` also ask for `impl Clone for S;` or `impl Eq for S;`?
  - For `Eq`, `Ord`, `Hash`, `Show`: the derivation only takes `self: readonly Self` and reads `self.[f.name]` by `readonly` borrow, which never moves a field out of `self`, so it works cleanly with `Drop` (`§4.1`).
  - For `Clone`: the derivation reads `self.[f.name].clone()` (again by `readonly` borrow of `self`) and constructs a new `S { ... }`, which also never moves out of `self`! However, if `S` implements `Drop` (e.g. `File { fd: i32 }`), deriving a memberwise `Clone` that copies `fd: i32` would cause a double-close when both `File`s are dropped! Usually, a type implementing `Drop` manages a unique resource and has `private` fields, so it will only get `Clone` if its author explicitly writes `impl Clone for File;`. That is already safe by opt-in (`§3.5`).
- **`#Opaque` in `Type.info` (`§7.2`):**
  In `§7.2`, a struct with private fields outside its module returns `#Opaque { name: str; args: Type[] }`. Built-in/runtime types (`Vec<T>`, `String`, `Box<T>`, `Ref<R, T>`, `HashMap<K, V>`) also return `#Opaque` when inspected by `Type.info`, because their fields are hidden in `.d.fly` (`§8.1`). Since those types have explicit hand-written impls for `Eq`, `Ord`, `Hash`, `Show`, `Clone`, `ToJson`, `FromJson`, the template derivations never reach `#Opaque` for them unless a user struct with private fields lacks an impl, in which case the `_ => comptime panic(...)` arm fires with a clear message (`"Foo cannot be decoded from JSON"`). That works well.
