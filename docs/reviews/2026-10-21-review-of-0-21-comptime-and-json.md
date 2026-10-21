# Review: review-of-0-21-comptime-and-json

- spec: ad5eca9e6692
- request: 106b59c2d0c19055
- tokens: prompt 38326, cached 0, answer 7992

## Question

Spec 0.21 (included) adopts your comptime review: templates (`<comptime T: Type>`) beside parametric `<T>`, `comptime if/match/for` in code and in sequences (record fields and entries, match arms, list items), `[e]` computed names (`v.[e]`, `#[e]`, `{ [e]: … }`), `impl I for T;` derivation requests, the no-fallback impl rule, the whole-payload tag rule, the privacy line, ToJson/FromJson split with `FromJson extends Send`, memoized specialization, and omitted Option fields. Mapped types were cut. One deviation: the privacy rule lets a derivation requested by `impl I for S;` in S's module see S's private fields; plain templates called from S's module do not.

All of it is implemented and running. The context file is `std/json.fly`, the codec written in Flyscript (about 500 lines including the parser), which derives encoders and decoders for structs, enums, records and tuples; the prototype runs round trips, `\u` escapes with surrogate pairs, keys in any order, unknown keys, missing optional fields, and reports `missing address` / `syntax error at 8`. Type functions (`Ring(u8, 1024)` with `comptime assert`) work. Errors in a specialization point into the template and name it: `no method 'describe' on 'bool' (in 'describe' for 'Flag')`.

Interfaces as bounds were also made real in this round (they were only parsed): method and static calls through bounds, impl resolution, bound checks at call sites, and run-time dispatch through each frame's type arguments.

Please review 0.21 and the codec as a whole:

1. **Is the comptime design now right?** Read std/json.fly as the stress test. What is awkward, unsafe, or missing? Be concrete about surface syntax that reads badly (e.g. `({ comptime for … })` needing parentheses in tail position, `comptime f.name =>` patterns, `t.payload == #None`, `f.type.fromJson(mut p)`).
2. **Soundness of the new pieces**: templates checked per specialization with privileged access; `Send`-bounded parameters hiding no borrow; whole-payload `#A(x)`; dispatch through bounds; `FromJson extends Send`; derivations for `view` types or types holding borrows; recursion through `Box`.
3. **What remains before this is a high-quality language design?** Rank the top three changes by value, with the concrete spec text you would write. Consider, among others: derived `Eq/Hash/Show/Clone` in the prelude (currently satisfied structurally by the checker), `Soa<T>` as a template, operator overloading through interfaces, `if let`, tuple element syntax, and nested-pattern exhaustiveness (the checker does not see through `#Err(#Missing(f))` yet).

## Context files

- `std/json.fly`

## Answer

### Verdicts

- **0.20 soundness fixes (`§3.3`, `§4.2`, `§4.3`, `§4.4`, `§5.1`, `§6.1`)**: **Agree.** Every hole from the 0.19 review (`Io.start`, `Io.scope` suspension, class-1 container bounds, storing class-2 through `mut` borrows, explicit `from` body checks, escaping closure `Send` and affinity, `private` literal/pattern checks) is cleanly and completely closed.
- **`comptime` and template model (`§7.1`–`§7.5`)**: **Agree with changes.** `std/json.fly` is a strong validation of Law 5. Three issues remain in the `comptime` surface and `std/json.fly`: (1) `comptime match` cannot narrow `Option<Type>` in `TagInfo.payload`, forcing an awkward `t.payload == #None` + `payloadOf(t)` helper; (2) `isOption(T)` in `std/json.fly` checks structural union tags without checking `t.payload == #None` on `#None`, misclassifying `#None(i32) | #Some(String)` and causing a type error inside the expanded derivation; and (3) `impl I for S;` grants private-field access to *any* interface `I` (or does a derived `FromJson` on a struct with `private` fields bypass its constructor invariant if requested?).
- **Soundness of the new 0.21 rules (`Question 2`)**: **Agree with changes.** Two soundness issues: (1) `impl<comptime T: Type> FromJson for T` has `FromJson extends Send`, and `§7.3` says *"Records, tuples and tag unions have no module, so a derivation applies to them directly"* — if the checker does not check `T extends Send` when selecting a template derivation for a super-interface bound, `{ s: str }` satisfies `FromJson` unless super-interface bounds are enforced on template impls; and (2) `impl<T extends ToJson> ToJson for Option<T>` + the no-fallback rule (`§7.3`) collides with structural unions that *happen* to include `#Some` and `#None` (because `Option<T>` is a structural `type` alias in `§3.2`, not a nominal `enum`!).
- **Top 3 remaining language changes (`Question 3`)**: Ranked below with concrete spec text: **(1) Nested pattern matching & exhaustiveness** (plus `if (const #Some(x) = e)` or fixing `A.9`'s `#Err(#Missing(f))` blindness), **(2) Moving `Eq`, `Hash`, `Show`, `Clone` and `Soa<T>` to real `comptime` prelude code**, and **(3) Unifying tuple element access (`t.0` / `t.[0]`) and fixing `{ comptime for ... }` brace disambiguation (`§2.3`)**.

---

### Problems

#### 1. `Option<T>` is a structural type alias (`§3.2`), so `impl<T> I for Option<T>` and `isOption(T)` collide with structural tag unions (`§3.2`, `§3.4`, `§7.3`)

Look at `§3.2`:
```ts
type Option<T> = #Some(T) | #None;
```
And `§3.4` / `§7.3`:
> *"The impl for a type is chosen in one step: specific impls first, by matching their heads against the type after expanding aliases, then the derivation. A specific impl whose head matches is the answer even if its bounds fail."*

Because `Option<T>` is a **type alias** for the structural union `#Some(T) | #None` (not a nominal `enum`), expanding aliases turns `impl<T extends ToJson> ToJson for Option<T>` into:
```ts
impl<T extends ToJson> ToJson for #Some(T) | #None
```
Now look at two programs where this breaks:

**Program 1a (`isOption` in `std/json.fly` ignores tag payloads):**
In `std/json.fly`:
```ts
comptime function isOption(T: Type): bool {
  match (Type.info(T)) {
    #Union(tags) => tags.len() == 2 && tags.any((t) => t.name == "None") && tags.any((t) => t.name == "Some"),
    _ => false,
  }
}
```
What if a user defines a structural union that has `#None(Reason)` (with a payload!) and `#Some(i32)`?
```ts
import { parse, FromJson } from "std/json";

type CustomChoice = #None(String) | #Some(i32);
struct Config { choice: CustomChoice; }
impl FromJson for Config;

export function bug(): Config uses Fail<JsonError> {
  // `isOption(CustomChoice)` returns `true` because it only checks `t.name == "None"` and `t.name == "Some"`!
  // Then `FromJson` for `Config` generates:
  //   `#None => #None` (with NO payload!) for field `choice: CustomChoice`!
  // Which fails to type-check inside the expanded template with a baffling internal error!
  parse<Config>("{}")
}
```
Even worse, what if a user has `field: Option<Option<i32>>` or `type MaybeVal = #Some(i32) | #None` where the user *intended* a 2-variant union in their domain protocol (`{"Some": 1}` vs `"None"`), and it silently serializes as `1` / `null` instead of a union because `Option<T>` is just an alias for `#Some(T) | #None`?
Actually, having `Option<T>` be `#Some(T) | #None` is a core strength of Flyscript (`§2.1`, `§3.2`), so `Option<T>` *should* serialize as `T | null`. **But**:
1. In `isOption(T)` (`std/json.fly`), you must check that the `"None"` tag has `t.payload == #None` and the `"Some"` tag has `t.payload != #None`!
2. Even better: in `§7.1` / `§7.2`, if `Type` supports `==` (type equality) or `Type.info`, can `isOption` check `t.name == "None" && t.payload == #None`? Yes:
```ts
comptime function isOption(T: Type): bool {
  match (Type.info(T)) {
    #Union(tags) =>
      tags.len() == 2
        && tags.any((t) => t.name == "None" && t.payload == #None)
        && tags.any((t) => t.name == "Some" && t.payload != #None),
    _ => false,
  }
}
```

---

#### 2. Super-interface bounds (`interface FromJson extends Send`) on template derivations (`§3.4`, `§7.3`, `§7.5`)

In `§7.5`:
```ts
export interface FromJson extends Send {
  function fromJson(p: mut JsonParser): Self uses Fail<JsonError>;
}
```
And the derivation in `std/json.fly` is:
```ts
impl<comptime T: Type> FromJson for T { ... }
```
Notice that `<comptime T: Type>` does **not** write `extends Send` (indeed, `§2.3` grammar is:
`TypeParam = "region" Ident | "row" Ident [ "=" Type ] | "comptime" Ident ":" Type | Ident [ "extends" Bounds ] [ "=" Type ] ;`
so a `comptime T: Type` parameter *cannot* even write `extends Bounds` in the grammar!).
Now, what happens if someone calls `parse` (or `T.fromJson`) on a structural record or struct that is **not `Send`** (for example, it holds a `str` borrow or a raw pointer `u8*`), or calls a method on an interface `interface Foo extends Copy` implemented by `impl<comptime T: Type> Foo for T`?
```ts
import { parse } from "std/json";

// Structural record containing `str` (class 2, not Send) and `u8*` (class 1, not Send)
type BorrowedMsg = { name: str };
type RawMsg = { ptr: u8* };

export function testBadDecode(s: str): void uses Fail<JsonError> {
  // 1. At `parse<BorrowedMsg>(s)`: `parse` has bound `<T extends FromJson>`.
  // Does `FromJson extends Send` automatically require `T extends Send` at every bound check `T extends FromJson`?
  // 2. What if someone calls `RawMsg.fromJson(mut p)` directly without going through `parse`?
  let p = JsonParser.new(s);
  const m = RawMsg.fromJson(mut p); // Calls `impl<comptime T: Type> FromJson for T` directly!
}
```
Look at line `RawMsg.fromJson(mut p)`:
- `RawMsg` is `{ ptr: u8* }`. It is not passed to a generic function `<T extends FromJson>`; it is a direct static call `RawMsg.fromJson(mut p)` (`§3.4`).
- `FromJson` declares `interface FromJson extends Send`.
- Because `impl<comptime T: Type> FromJson for T` has no `Send` bound on `T`, does `RawMsg` satisfy `FromJson` if someone implements `FromJson for u8*` (or for a struct with a `u8*` or `str`)?
- More generally: **`§3.4` never states that implementing `interface Sub extends Super` for `T` (including via a template `impl<comptime T: Type> Sub for T`) requires `T` to satisfy `Super`!**

**Fix:**
Add one rule to `§3.4`:
> *"An `impl I for T` (including a template specialization) requires `T` to satisfy every interface that `I` extends."*

With that single sentence in `§3.4`, `impl<comptime T: Type> FromJson for T` automatically checks `T extends Send` whenever `FromJson` is resolved for any `T` (whether via `parse<T>` or `T.fromJson(mut p)`), without needing bounds syntax on `comptime T: Type`.

---

#### 3. Surface ergonomics in `std/json.fly`: `comptime match` cannot bind `Option<Type>` inside `TagInfo` (`§7.2`, `§7.5`)

You asked specifically about what reads badly in `std/json.fly`:
1. **`t.payload == #None` + `payloadOf(t)` in `std/json.fly`:**
   Look at lines 135–147 and 390–406 of `std/json.fly`:
   ```ts
   comptime for (const t of tags) {
     comptime if (t.payload != #None) { comptime t.name => #[t.name](payloadOf(t).fromJson(mut p)), }
   }
   ```
   Why did the author of `std/json.fly` have to write a top-level helper `comptime function payloadOf(t: TagInfo): Type` that panics on `#None`, right after checking `comptime if (t.payload != #None)`?
   Because:
   - `Generate(X)` in the grammar (`§2.3`) only allows `comptime for` and `comptime if` inside `Record`, `RecordLit`, `ListLit`, and `Match` — it does **not** allow `comptime match`!
   - Even in statement/expression position (`ToJson` lines 135–145), inside `#[t.name](x) =>`, `x`'s type is known to the typechecker, whereas in `FromJson` (line 402), you need the `Type` value `P` inside `t.payload: Option<Type>` to call `P.fromJson(mut p)`, and `comptime if` cannot destructure `#Some(P)`!

   Look how much cleaner `FromJson` and `ToJson` become if `Generate(X)` in `§2.3` allows `comptime match` (which it already allows in `BlockLike`!):
   ```ebnf
   Generate(X) = "comptime" "for" "(" "const" Pattern "of" Expr ")" "{" { X } "}"
               | "comptime" "if" "(" Expr ")" "{" { X } "}" [ "else" "{" { X } "}" ]
               | "comptime" "match" "(" Expr ")" "{" { Pattern "=>" "{" { X } "}" } "}" ;
   ```
   Then `payloadOf` disappears completely, and `FromJson`'s union arm is simply:
   ```ts
   comptime for (const t of tags) {
     comptime match (t.payload) {
       #Some(P) => { comptime t.name => #[t.name](P.fromJson(mut p)), }
       #None => {}
     }
   }
   ```
   That removes a concept discrepancy (`comptime match` worked in blocks, but not in generated sequences `Generate(X)`) and eliminates `payloadOf` and `t.payload != #None`.

2. **`({ comptime for (const f of fields) { [f.name]: ... } })` needing parentheses in tail position (`§2.3`, `§7.5`):**
   Look at `§7.5`:
   ```ts
        ({
          comptime for (const f of fields) {
            [f.name]: match (slots.[f.name]) { ... },
          }
        })
   ```
   Why are the outer `(` `)` required around `{ comptime for ... }` at the end of the block?
   Because `§2.3` says:
   > *"Braces. A `{` in expression position begins a record literal. A block appears only as the body of a block-like construct, after `=>` in a lambda or match arm, or at the start of a statement."*
   Since the last item of a `Block` (`"{" { Stmt } [ Expr ] "}"`) can start at the same token position as a `Stmt`, `{` at the start of a statement/tail-expression is parsed as an inner `Block` (`BlockLike`), **unless** disambiguated!
   Wait: can an inner `Block` ever start with `{ comptime for (const f of fields) { [f.name]: ... }` or `{ ident: expr }` or `{ [expr]: expr }`?
   In JavaScript/TypeScript, `{ a: 1 }` at statement start is a labeled statement only because JS has `label: stmt`. **Flyscript has no labeled statements (`§2.3`)!**
   Read `§2.3` `Stmt` and `Block`:
   - In Flyscript, `{` at the start of a statement can only be either a `Block` or a `RecordLit`!
   - A `RecordLit` starts with `{` followed by `}` (empty), `Ident ":"`, `Ident ","`, `Ident "}"` (punned field), `"[" Expr "]" ":"`, or `"comptime"` whose body contains `Entry` (`FieldName [ ":" Expr ]`).
   - Even simpler: if a `RecordLit` is the tail expression of a block (`§7.5`), when is a bare `{ ... }` block ever used as the *value-returning tail expression* of another block? Never — you are already inside a block!
   - Even if you keep the TypeScript brace rule for `{ x }` vs block, a `{` followed by `Ident ":"`, `"["`, or `"comptime"` with field entries is syntactically **never** a statement block. Allowing `{ [f.name]: ... }` or `{ a: 1, b: 2 }` without `({...})` (or at least noting why `({...})` was written if you prefer strict TS `{` rules) removes a classic JS/TS wart.

3. **`comptime f.name =>` in match patterns (`§2.3`, `§7.2`, `§7.5`):**
   In `std/json.fly`:
   ```ts
   match (key.asStr()) {
     comptime for (const f of fields) {
       comptime f.name => { slots.[f.name] = #Some(f.type.fromJson(mut p)); },
     }
     _ => p.skip(),
   }
   ```
   Wait: why is `comptime` needed before `f.name` in `comptime f.name =>`?
   Because in a pattern (`Pattern`), a bare identifier `x` is a variable binding, and `f.name` is a field access expression, not a literal pattern! Using `comptime Expr` in `Pattern` (`§2.3`: `Pattern = … | "comptime" Expr ;`) to evaluate any `comptime` expression to a literal pattern is actually **very clean and general** — it also lets you match against module constants (`comptime MAX_BUF =>`) or computed integers (`comptime (i + 1) =>`) without inventing special constant-pattern lookup rules. **Keep `comptime Expr` in patterns.**

4. **`f.type.fromJson(mut p)` (`§3.4`, `§7.2`):**
   Calling a static interface method on a `Type` value (`f.type.fromJson(mut p)`) is completely natural and reads like normal TypeScript property access. **Keep it.**

---

#### 4. `std/json.fly` bugs: negative `u64` / float integers and duplicate keys (`std/json.fly`)

Since `std/json.fly` is part of the review and standard library, two concrete bugs in `std/json.fly` should be fixed:

1. **`u64` / `usize` truncation in `std/json.fly` (lines 324–336):**
   `p.int()` returns `i64`. `impl FromJson for u64` calls `const n = p.int(); if (n < 0) { throw #Range(at); } n as u64`. Any JSON integer in `2^63 .. 2^64 - 1` fails `parseInt` (which parses `i64`) and throws `#Syntax` instead of decoding `u64`! And for `i32` / `u32`, `JsonParser.number()` accepts `.` and `e` (`isNumberByte`), so `"1.5"` in an `i32` field fails `parseInt` and throws `#Syntax(start)` instead of distinguishing syntax vs integer errors if intended.
2. **In `FromJson` for `#Tuple(items)` (lines 374–384):**
   ```ts
   const v = [
     comptime for (const t of items) {
       if (!p.nextItem()) { throw #Syntax(p.at()); }
       t.fromJson(mut p)
     }
   ];
   ```
   Look at the grammar for `ListLit` in `§2.3`:
   ```ebnf
   ListLit = "[" [ Item { "," Item } ] "]" ;
   Item    = Expr | "comptime" ( For | If ) ;
   ```
   And `For` is `"for" "(" ( "const" | "let" ) Pattern "of" Expr ")" Block`.
   In `#Tuple(items)`, the body of `comptime for` inside `[ ... ]` is a `Block` (`{ if (!p.nextItem()) { ... } t.fromJson(mut p) }`) which evaluates to one expression per iteration, building a tuple literal `[e0, e1, ...]`.
   Wait: `[a, b]` builds either a **tuple** `[A, B]` or an **inline array** `T[N]` (`§3.1`) depending on expected type!
   In `#Tuple(items)` (line 376 of `std/json.fly`):
   ```ts
   const v = [
     comptime for (const t of items) { ... }
   ];
   ```
   Notice that `const v` has **no type annotation** (`const v: T = [...]`), so when `items` all have the same type (e.g. `[i32, i32]`), what tells `[ ... ]` whether to build a 2-tuple `[i32, i32]` vs an inline array `i32[2]` until `v` is returned two lines later?!
   By `§3.6` (local bidirectional inference), `const v = [...]` infers `v`'s type at its declaration before seeing the trailing `v` return expression! In `#Union` (line 399), the author wrote `const v: T = match ...`, whereas in `#Tuple` (line 376), `const v` omitted `: T`! Add `const v: T = [ ... ];` on line 376 so `[i32, i32]` is unambiguously checked with expected type `T`.

---

### Question 3: Top Three Remaining Changes (Ranked by Value)

With Laws 1–5 now working end-to-end in the prototype, Flyscript is very close to a complete 1.0 specification. Here are the **top three changes by value**, with the exact spec text to add.

---

#### Rank 1: Deep Pattern Matching, Exhaustiveness, and `if (const Pat = e)` (`§2.2`, `§2.3`, `§3.2`)

**Why this is #1:**
Look at the *Awkward* note at the end of `A.9` (`§10` / `A.9`):
> *"The failure arm reads well because `JsonError` is a closed union; a decoder that wanted to say which field was missing would match `#Missing(f)` and build a `String`..."*
And as you noted in Question 3, the checker currently does not see through nested patterns like `#Err(#Missing(f))` for exhaustiveness, nor is there a concise way to unwrap a single pattern without a 4-line `match`.
In real Flyscript code (`Result<T, E>`, `Option<T>`, ASTs, protocol messages), matching `#Ok(#Some(x))` or `#Err(#Missing(field))` or `if (const #Some(x) = map.get(k))` happens in almost every function.

**What it removes / adds:**
- **Removes:** compiler special-casing for flat-only tag exhaustiveness, and boilerplate 2-arm `match` expressions when only one tag matters.
- **Adds:** standard Maranget pattern-matrix exhaustiveness (which works uniformly over nested tags, tuples, records, and `bool`) and allows a refutable pattern in `if (const #Some(x) = e) { ... }` (using existing `if`, `const`/`let`, and `Pattern` tokens — zero new keywords!).

**Concrete spec text to add:**
- In **`§2.3` (Grammar)**:
  Change `If` (inside `BlockLike`) to allow an optional pattern binding in the condition:
  ```ebnf
  If = "if" "(" ( Expr | ( "const" | "let" ) Pattern "=" Expr ) ")" Block [ "else" ( If | Block ) ] ;
  ```
- In **`§3.2` (Open and closed unions)**:
  Replace the final two sentences of the *Open and closed unions* paragraph with:
  > *"Exhaustiveness is checked over nested patterns (tags, tuples, records and `bool`) once a function's types are final; a union whose tail is still open at that point was built only from the tags the function saw, so it is closed rather than requiring a `_` arm. A union with a row-parameter tail always needs one."*

**Example unlocked in `A.9`:**
```ts
export function respond(body: str, nextId: u64): String {
  match (Fail.capture(() => parse<Signup>(body))) {
    #Ok(s)                 => stringify(#Created { id: nextId, name: s.name }),
    #Err(#Missing(field))  => stringify(#Rejected { reason: `missing ${field}` }),
    #Err(#Syntax(pos))     => stringify(#Rejected { reason: `syntax error at ${pos}` }),
    #Err(_)                => stringify(#Rejected { reason: "invalid signup" }),
  }
}
```
(Notice also that inline `stringify(#Rejected { reason: \`missing ${field}\` })` borrows the temporary `String` as `reason: str` for the duration of the `stringify` call, solving `A.9`'s second awkwardness too!)

---

#### Rank 2: Move `Eq`, `Hash`, `Show`, `Clone`, and `Soa<T>` into `comptime` Prelude Code + Operator Interfaces (`§3.4`, `§3.5`, `§7.4`, `§11`)

**Why this is #2:**
`§11` notes:
> *"`Soa<T>` is still built in rather than written as a template, and the checker satisfies `Eq`, `Hash`, `Show` and `Clone` structurally until their derivations move into the prelude."*
Right now, `std/json.fly` uses `==` on `str` (`f.name == "None"`) and `Option<Type>` (`t.payload == #None`), and `A.2` uses `${e}` on a tag union via `Show`.
Once `Eq`, `Hash`, `Show`, and `Clone` are real interfaces with `impl<comptime T: Type>` derivations in the prelude:
1. `==` and `!=` desugar to `Eq.eq`, `<, <=, >, >=` to `Ord.cmp`, and `${e}` to `Show.show(e, mut out)` (just like `ToJson.toJson(self, mut out)`, avoiding intermediate `String` allocations when interpolating multiple values!).
2. A struct without `impl Eq for Point;` cannot be accidentally compared with `==` (respecting nominal identity and `private` invariants in `§3.3`), while records, tuples, and tag unions get `Eq`, `Hash`, `Show`, and `Clone` automatically via `§7.3`.
3. Writing `Soa<T>` as a real `comptime function Soa(T: Type): Type` in `std/layout.fly` deletes the last built-in layout magic from `flyc`.

**What needs attention when moving `Eq` and `Soa<T>` to `comptime`:**
Look at `Soa<T>` in `§7.4`:
```ts
comptime function Soa(T: Type): Type
```
In `§7.1`, `Ring(u8, 1024)` returns an anonymous `struct { buf: T[N]; head: usize; tail: usize; }`.
For `Soa(Particle)` to work in `par(mut ps, ...)` (`A.4`), `Soa(T)` must implement `ParSplit` (`§6.5`)!
Wait: **how does a `struct { ... }` returned by a `comptime function Soa(T: Type): Type` implement an interface like `ParSplit` or inherent methods like `.push()`?**
Check `§7.1` and `§2.3`:
- `Ring(T: Type, N: usize): Type` returns an anonymous `struct { ... }`.
- Where do `impl ParSplit for Soa<T>` or `impl<comptime T: Type> ParSplit for Soa(T)` live if `Soa` is a `comptime function` returning a fresh `struct { ... }` rather than a generic `struct Soa<comptime T: Type>`?
Look at that!
In `§7.4` and `A.4`, `Soa<Particle>` is written with angle brackets `<Particle>`, NOT parens `Soa(Particle)`!
And `§2.3` already has:
```ebnf
Struct    = [ Layout ] [ "view" ] "struct" Ident [ TypeParams ] "{" { [ "private" ] Ident ":" Type ";" } "}" ;
TypeParam = ... | "comptime" Ident ":" Type | ... ;
Field     = FieldName ":" Type ";" | Generate(Field) ;
```
Because `Struct` already accepts `<comptime T: Type>` in `TypeParams` AND `Generate(Field)` (`comptime for` / `comptime if`) inside `{ ... }`, **`Soa<T>` does NOT need to be a `comptime function` returning a `struct { ... }` expression!**
`Soa<T>` is simply a normal nominal `struct` with a template parameter `<comptime T: Type>` and generated fields:
```ts
export struct Soa<comptime T: Type> {
  len: usize;
  comptime for (const f of fieldsOf(T)) {
    [f.name]: Plane<f.type>;
  }
}
impl<comptime T: Type> ParSplit for Soa<T> { ... }
```
Look how much cleaner that is:
1. You don't even need the anonymous `"struct" "{" { Field } "}"` expression in `Expr` (`§2.3`)! Even `Ring<T, comptime N: usize>` can just be a `struct Ring<T, comptime N: usize> { buf: T[N]; ... }` if `comptime N: usize` is allowed, or `struct Soa<comptime T: Type>` for type-driven layout!
2. And because `struct Soa<comptime T: Type>` is a nominal `struct` declaration, `impl<comptime T: Type> ParSplit for Soa<T>` works with the exact same `impl` head matching rule (`§3.4`, `§7.3`) as every other type in the language!

**Concrete spec text to add:**
- In **`§3.4` (Interfaces and `impl`)**:
  > *"The operators `==` and `!=` call `Eq.eq`, `<`, `<=`, `>` and `>=` call `Ord.cmp`, and string interpolation `` `…${e}…` `` calls `Show.fmt(e, mut out)`."*
- In **`§7.4` (`Soa<T>`)**:
  > *"`Soa<comptime T: Type>` is a template struct whose fields are generated with `comptime for` — one `Vec` per scalar field, a nested `Soa` per struct field — and whose `impl<comptime T: Type> ParSplit for Soa<T>` builds a nested view record."*

---

#### Rank 3: Unify Tuple Indexing (`x.0` / `x.[i]`) and `Type.info` for `#Array` (`§2.3`, `§3.1`, `§7.2`)

**Why this is #3:**
Look at how tuples are accessed in `0.21`:
- In `std/json.fly` (line 130): `self.[i].toJson(mut out)` (where `i: usize` is a `comptime` integer).
- In `prev_reviews` (`Problem 3`, `launderBorrow`): `res[1][0]` was written using array indexing syntax `e[i]`, or destructuring `const [x, y] = pair`.
- Meanwhile, `§2.3` and `§3.1` never actually state how to index a single element of a tuple `[A, B]` without destructuring or writing `x.[0]`!
And look at `std/json.fly` for fixed-size inline arrays `T[N]` (`§3.1`):
- `TypeInfo` in `§7.2` has `#Array { item: Type; len: usize }`, which exposes `len: usize` as a `comptime` value, **but** to construct a `T[N]` or index a tuple, `x.[0]` (with a dot before `[`) is required for tuples while `x[0]` (no dot) is used for arrays/slices!

**Concrete spec text to add:**
- In **`§3.1` (Primitives, strings, arrays)**:
  > *"A tuple `[A, B]` is indexed by a constant integer with `t.[0]` (or destructured with `const [a, b] = t`)."*
  (Or allow `t[0]` on a tuple when the index is a constant integer literal or `comptime` integer, which matches TypeScript's `tuple[0]` syntax! In TypeScript, a tuple `[A, B]` is indexed with `t[0]`, not `t.[0]` or `t.0`! If `t[i]` where `i` is a constant / `comptime` integer works on tuples, then `self[i].toJson(mut out)` in `std/json.fly` is valid TypeScript *and* valid Flyscript, and `.[e]` is only needed for string field names!)

---

### Smaller points

- **`Fail.capture` type inference in `A.9` (`§3.6`, `A.9`):**
  In `A.9`, you noted:
  > *"`parse<Signup>` names its type because the closure passed to `Fail.capture` gets no expected type from the `match`."*
  Why didn't `match (Fail.capture(() => parse(body)))` get an expected type? Because `match` checks its scrutinee without an expected type. If the user writes:
  ```ts
  const res: Result<Signup, JsonError> = Fail.capture(() => parse(body));
  ```
  or if `parse(Signup, body)` / `Signup.fromJson` is used, expected-type propagation (`§3.6`) flows into `Fail.capture`'s closure return type. Mentioning in `§3.6` that expected types flow into lambda bodies (`() => e` checked against `() => R` checks `e` against `R`) ensures `const r: Result<Signup, _> = Fail.capture(() => parse(body))` works when annotated.
- **`FromJson` for `i8`, `i16`, `u8`, `u16`, `isize`, `f32` (`std/json.fly`):**
  Since `TypeInfo` has `#Int { signed: bool; bits: u8 }` and `#Float(u8)`, all integer and float `ToJson` / `FromJson` impls could either be handled in the `#Int` / `#Float` arms of the template derivation or given explicit impls in `std/json.fly` so `Vec2 { x: f32; y: f32; }` from `A.4` can be JSON-encoded and decoded out of the box.
