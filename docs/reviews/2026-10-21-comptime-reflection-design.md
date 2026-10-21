# Review: comptime-reflection-design

- spec: 98bce39e8956
- request: 02ed453f2e708af7
- tokens: prompt 31532, cached 0, answer 10647

## Question

Spec 0.20 (included) adopts all six fixes from your review of 0.19. Your review named `comptime` reflection, proven by a JSON codec written in Flyscript, as the most valuable next change. Before implementing it I want your critique of the design below. Treat this as a major design decision: be direct about what is wrong and what is missing, propose concrete alternatives, and show programs.

## Goals

- Law 5: generics, reflection, layout and derived interfaces are ordinary Flyscript run by the compiler. `Soa<T>`, `Eq`/`Hash`/`Show`/`Clone` and a serde-quality JSON codec must be library code, with nothing built into the compiler beyond the reflection primitives.
- The tagline, *Church on the outside, Turing on the inside*: what users call should look like ordinary typed, parametric code; the machinery inside a derivation may compute.
- Small: as few new concepts as possible, each familiar to a TypeScript programmer where it can be.

## Proposed design

**1. Two kinds of type parameter.** `<T>` is parametric, as now: the body is checked once, against `T`'s bounds. `<comptime T: Type>` is a *template* parameter: the compiler specializes the body for each `T` it is instantiated at and checks each specialization (Zig's model). Callers cannot tell the difference: `T` is inferred from the arguments as usual (`encode(user, out)`). An error in a specialization is reported at the template's line with an "in `encode<User>`" note.

**2. Reflection.** `Type` is a comptime-only type. `Type.info(T)` returns

```ts
type TypeInfo =
  | #Record(Field[]) | #Tuple(Type[]) | #Union(Tag[])
  | #Struct({ name: str; fields: Field[] }) | #Enum({ name: str; tags: Tag[] })
  | #Int({ signed: bool; bits: u8 }) | #Float(u8) | #Bool | #Str | #Opaque({ name: str; args: Type[] });
type Field = { name: str; type: Type };
type Tag = { name: str; payload: Option<Type> };
```

Reflection respects privacy: `Type.info` shows a nominal type's private fields only to code specialized on behalf of its own module (see 6); elsewhere a struct with private fields is `#Opaque`.

**3. One device for generating code: `comptime` before a construct evaluates it in the compiler and leaves the chosen or repeated code behind.**

- `comptime if (c) { … } else { … }` and `comptime match (e) { … }`: the condition or scrutinee is evaluated by the compiler; only the selected branch is specialized and checked.
- `comptime for (const x of xs) …` repeats its body once per element of a comptime list, with `x` a comptime constant in each copy. It may appear wherever a *sequence* appears: statements in a block, entries in a record literal, arms in a `match`, and fields in a record type.

**4. Computed names: `[e]`, where a name is expected and `e` is a comptime `str`** (TypeScript's computed keys and indexed access): `v[f.name]` is field access, `{ [f.name]: e }` a record entry, `#[t.name](x)` a tag pattern or constructor. A comptime `Type` value is usable wherever a type is (`Option<f.type>`). TypeScript's mapped types are sugar: `{ [K in keyof T]: Option<T[K]> }` means `{ comptime for (const f of Type.fields(T)) [f.name]: Option<f.type>; }`.

**5. Comptime evaluation** is the ordinary language on an interpreter in the compiler: no effects, deterministic, a step budget, values that include `Type`. Module constants and `comptime function`s returning `Type` (`Ring(u8, 1024)`, `Soa<T>`) use the same interpreter.

**6. Derivation is a template `impl`, requested by an empty `impl`.**

```ts
// In the interface's module: how to derive `Json` for any type whose shape is visible.
impl<comptime T: Type> Json for T { … }
// In User's module: User asks for it (specialized with User's module's view, so private fields are visible).
impl Json for User;
```

A template impl applies automatically to structural types (records, tuples, tag unions) that have no other impl, and to nominal types that request it. The orphan rule is unchanged: the template lives with the interface, the request with the type. Bounds on fields (`f.type` implements `Json`) are checked in the specialization.

## The JSON codec, written against this design

```ts
// std/json.fly
export type JsonError = #Syntax(usize) | #Missing(String) | #Unknown(String) | #Type(usize);

export interface Json {
  function encode(self: readonly Self, out: mut String): void;
  function decode(p: mut JsonParser): Self uses Fail<JsonError>;
}

impl Json for i64 {
  function encode(self: readonly Self, out: mut String): void { out.push(fmt(self)); }
  function decode(p: mut JsonParser): i64 uses Fail<JsonError> { p.int() }
}
impl Json for String { … }      // likewise bool, f64, the other integers
impl<T extends Json> Json for Vec<T> { … }
// Option is a structural union, so the template would give it {"Some":…}; serde's convention is value-or-null.
impl<T extends Json> Json for Option<T> {
  function encode(self: readonly Self, out: mut String): void {
    match (self) { #Some(x) => x.encode(out), #None => out.push("null") }
  }
  function decode(p: mut JsonParser): Option<T> uses Fail<JsonError> {
    if (p.null()) { #None } else { #Some(T.decode(p)) }
  }
}

impl<comptime T: Type> Json for T {
  function encode(self: readonly Self, out: mut String): void {
    comptime match (Type.info(T)) {
      #Record(fields) | #Struct({ fields }) => {
        out.push("{");
        comptime for (const [i, f] of fields.enumerate()) {
          comptime if (i > 0) { out.push(","); }
          writeKey(f.name, out);
          self[f.name].encode(out);
        }
        out.push("}");
      }
      #Union(tags) | #Enum({ tags }) => match (self) {
        comptime for (const t of tags)
          comptime match (t.payload) {
            #Some(_) => #[t.name](x) => { out.push("{"); writeKey(t.name, out); x.encode(out); out.push("}"); },
            #None => #[t.name] => writeString(t.name, out),
          }
      },
      #Tuple(items) => { … },
      _ => comptime panic(`${Type.name(T)} cannot be encoded as JSON`),
    }
  }

  function decode(p: mut JsonParser): T uses Fail<JsonError> {
    comptime match (Type.info(T)) {
      #Record(fields) | #Struct({ fields }) => {
        let slots: { [K in keyof T]: Option<T[K]> } = { comptime for (const f of fields) [f.name]: #None };
        for (const key of p.keys()) {
          match (key) {
            comptime for (const f of fields) f.name => { slots[f.name] = #Some(f.type.decode(p)); },
            _ => throw #Unknown(String.from(key)),
          }
        }
        T {
          comptime for (const f of fields)
            [f.name]: match (slots[f.name]) { #Some(v) => v, #None => throw #Missing(String.from(f.name)) },
        }
      }
      #Union(tags) | #Enum({ tags }) => { … },
      _ => comptime panic(`${Type.name(T)} cannot be decoded from JSON`),
    }
  }
}
```

Use:

```ts
import { Json } from "std/json";
struct User { id: i64; name: String; email: Option<String>; private hash: String; }
impl Json for User;

export function roundTrip(u: readonly User): User uses Fail<JsonError> {
  let s = String.new();
  u.encode(mut s);
  User.decode(mut JsonParser.new(s.asStr()))
}
```

`Eq`, `Hash`, `Show`, `Clone` and `Soa<T>` would be written the same way.

## Questions

1. **Templates vs the alternatives.** Is per-specialization checking (Zig, C++ templates) the right model here, given the cost of errors that appear only at instantiation? Compare honestly with (a) staged, typed quotes (MetaOCaml, Scala 3 macros), and (b) shape induction over the row calculus (GHC Generics, Scala 3 `Mirror`, frunk), where derivations stay parametric and are checked once. Which best fits *this* language's five laws and its audience?
2. **The generation device.** Is "`comptime` before a construct, `comptime for` wherever a sequence appears, `[e]` wherever a name appears" the right minimal set? What does the JSON codec need that it lacks (the `comptime if (i > 0)` in a repeated statement, `f.type.decode(p)` as a static call on a comptime type, building `T { … }` from repeated entries)? Propose better surface syntax where mine is wrong.
3. **Soundness and ownership.** Interactions with affine values and second-class borrows: `self[f.name]` on a `readonly Self` lends a field; the `slots` record of `Option`s moved into `T { … }`; a template impl for a `view` type or a type with borrowed fields; `Drop` types; private fields and the empty-`impl` request; coherence between the template impl and specific impls (`Option<T>`).
4. **Templates and effects/rows.** A template body is checked per specialization, but rows are polymorphic; how should `uses` clauses and effect rows in templates work, e.g. a derived `Hash<row E>`?
5. **What would you cut, and what is missing** for this to be the best comptime design of any systems language (Zig, D, Nim, Rust proc macros, C++26 reflection, Jai)?

## Answer

### Verdicts

- **1. Two kinds of type parameter (`<T>` vs `<comptime T: Type>`)**: **Agree.** Per-specialization checking for `<comptime T: Type>` is the right choice for Flyscript, while ordinary `<T>` keeps parametric checking for 95% of code (*Church on the outside, Turing on the inside*). Neither staged typed quotes nor shape induction over rows can express `Soa<T>` (`§7.2`) or flat state-machine codecs without turning the type system into dependent types.
- **2. Reflection (`Type.info`)**: **Agree with changes.** `Tag` payload representation in `TypeInfo` does not match Flyscript's grammar (`§2.3`, `§3.2`), where a tag has **three** forms (`#None`, `#Some(A, B)`, `#Get { key: String }`), not `Option<Type>`. Also needs field/tag attributes or a way to handle region-generic types (`Json<region R>`).
- **3. Generation device (`comptime if`, `comptime match`, `comptime for`)**: **Agree with changes.** Minimal and readable, but `T { ... }` in `decode` fails when `T` is a structural record (`#Record`), because `T` is not a nominal struct path and `{ ... }` with an expected type of `T` works for both `#Record` and `#Struct` (`§2.2`)! Also, recursive types (`enum Expr` in `§3.3`) will cause infinite template expansion unless specialization is memoized by `(Template, Type)` signature before expanding the body.
- **4. Computed names (`[e]`) and mapped types**: **Agree with changes.** Cut mapped-type sugar `{ [K in keyof T]: ... }` (it adds two new keywords `in` and `keyof` that duplicate `comptime for`), and fix the ambiguity between array indexing `v[i]` and computed field access `v[f.name]`.
- **5. Comptime evaluation**: **Agree.**
- **6. Template `impl` and `impl I for User;`**: **Disagree with the privacy rule and coherence rule as stated; agree with changes.** Allowing `impl Json for User;` to expose `private` fields to a foreign template breaks encapsulation (`§3.3`) and serializes secrets (like `private hash: String` in your own `User` example!). And coherence between `impl<T extends Json> Json for Option<T>` and `impl<comptime T: Type> Json for T` is ambiguous when `Option<T>` is just a `type` alias (`§3.2`) for a structural union `#Some(T) | #None`!

---

### Problems

#### 1. `Option<T>` is a type alias for `#Some(T) | #None`, so `impl Json for Option<T>` collides with the structural union template (`§3.2`, Proposed #6)

In `§3.2`:
```ts
type Option<T> = #Some(T) | #None;
```
`Option<T>` is **not** a nominal `enum`; it is a transparent `type` alias for the structural tag union `#Some(T) | #None`!
Now look at your proposed `std/json.fly`:
```ts
// 1. Specific impl for the type alias Option<T>:
impl<T extends Json> Json for Option<T> { ... }

// 2. Template impl that "applies automatically to structural types (records, tuples, tag unions)
//    that have no other impl":
impl<comptime T: Type> Json for T { ... }
```
Look at what happens in these three programs:
```ts
// Program A: Open union construction (§3.2)
const x = #Some(42); // Inferred type: `#Some(i32) | ...ρ`, closed at end of fn to `#Some(i32)`
// `#Some(i32)` is NOT `#Some(i32) | #None`, so it gets the #Union template (`{"Some": 42}`),
// whereas `const y: Option<i32> = #Some(42)` gets `42`!

// Program B: Another alias or direct structural union with the same tags
type Maybe<T> = #Some(T) | #None;
function test(m: Maybe<i64>, u: #Some(i64) | #None, n: Option<Option<i64>>): void {
  // `Maybe<i64>`, `#Some(i64) | #None`, and `Option<i64>` are the EXACT SAME structural type!
  // Which impl does `#Some(i64) | #None` use?
  // Wait: what if `T` inside `Option<T>` does NOT implement `Json` directly, or is checked via the template?
}

// Program C: Overlapping structural impls
impl<T extends Json> Json for #Ok(T) | #Err(String) { ... }
impl<comptime T: Type> Json for T { ... }
```
More importantly, how does the compiler decide whether `#Some(User) | #None` matches `impl<T extends Json> Json for Option<T>` vs `impl<comptime T: Type> Json for T`?
Because `Option<T>` is identical to `#Some(T) | #None`, checking whether a structural union has an explicit `impl` requires unifying the structural union against every generic `impl<...> I for UnionType` header *before* falling back to `impl<comptime T: Type> I for T`.
And what if someone writes `Option<NonJsonType>`? Does `Option<NonJsonType>` fail `T extends Json` in the specific `impl` and then **fall back** to the template `impl<comptime T: Type> Json for T` (which succeeds if `NonJsonType` happens to be a record, encoding `Option` as `{"Some": ...}` instead of value-or-null!), or is `Option<U>` unconditionally claimed by the more specific `impl` head?

**Fix:**
State a strict two-step **Impl Resolution & No-Fallback Rule**:
1. Specific `impl` heads (whose target type is not a bare `<comptime T: Type>`) are matched against the target type **by structure (after expanding `type` aliases)** *ignoring* where-bounds on type parameters.
2. If a specific `impl` head matches the type structure (e.g. `#Some(U) | #None` matches `Option<T>`), that `impl` is selected **exclusively** — if `U extends Json` fails, compilation fails immediately and **never** falls back to `impl<comptime T: Type>`.
3. The blanket template `impl<comptime T: Type> I for T` is only used when **no** specific `impl` head matches the type's structure (for structural types) or when explicitly requested by `impl I for NominalType;`.

---

#### 2. `impl Json for User;` exposing `private` fields violates `§3.3` invariants and leaks secrets (`§3.3`, Proposed #2 & #6)

Look at your own example in Proposed #6:
```ts
struct User { id: i64; name: String; email: Option<String>; private hash: String; }
impl Json for User;
```
Look at what `roundTrip(u)` in your example actually does when `Type.info(User)` exposes `private hash: String` to `std/json`:
1. **`u.encode(mut s)` serializes the user's `private hash: String` into the outbound JSON response!**
2. Even worse, look at `§3.3`'s motivating example for `private` fields:
   > *"Fields are public, as in TypeScript, unless marked `private`, which limits them to the declaring module: outside it, a struct with private fields cannot be built with a literal or taken apart with a pattern, only through the functions its module exports. That is what lets a type keep an invariant (`NonZero`)."*

Now watch what happens when `NonZero` or a bounded type derives `Json` or is inside a struct that derives `Json`:
```ts
// module nonzero.fly
import { Json } from "std/json";

export struct NonZero { private val: i32; }
// Suppose nonzero.fly requests `Eq`, `Show`, or `Json`:
impl Json for NonZero;

// module main.fly
import { NonZero } from "./nonzero";
import { Json, JsonParser } from "std/json";

function breakInvariant(): NonZero uses Fail<JsonError> {
  // Decodes `{"val": 0}` straight into the private field `NonZero.val = 0`,
  // bypassing `NonZero`'s constructor and breaking its safety invariant!
  NonZero.decode(mut JsonParser.new(`{"val": 0}`))
}
```
Why did this happen? Because in `std/json.fly`, `T { comptime for (const f of fields) [f.name]: ... }` is code written in **`std/json`**, which has no idea what `NonZero`'s invariant is, or whether `User.hash` is a secret cache/password field vs an encapsulated state field!
Wait: what if `User` has `private` fields and wants `Eq` or `Clone`, vs `Json`?
Even more importantly: if a struct has **any** `private` field, why did the author make that field `private`?
Either:
- Every field is `private` because the struct is an encapsulated data type (`SecretToken`, `NonZero`), in which case `impl Eq for NonZero;` inside `nonzero.fly` **wants** the derivation to access its private fields (because the author of `nonzero.fly` explicitly wrote `impl Eq for NonZero;` inside `nonzero.fly`!).
-Wait: if `impl Json for NonZero;` is written **inside `nonzero.fly`** by the author of `NonZero`, then the author of `nonzero.fly` *asked* for `Json` to be generated as if written in `nonzero.fly`!
Then why was `private hash: String` in `struct User` bad in `User`?
Because in `struct User { id: i64; name: String; email: Option<String>; private hash: String; }`, a TypeScript programmer marks `hash` `private` expecting public serialization (`Json`, `Show`) to either **reject** `impl Json for User;` (unless custom) or **only reflect public fields**, whereas `Clone` must copy all fields!

Look closely at that tension:
- If `User` has both public fields (`id`, `name`) and a `private` internal field (`cachedSlug` or `hash`), what happens if someone in `user.fly` writes `impl Clone for User;`? `Clone` **must** see `private` fields, or it can't construct `User { ... }`!
- And if `impl Json for User;` is written in `user.fly`, `Json.decode` ALSO constructs `User { ... }`! If `Type.info(User)` hid `private hash` from `Json`, then `T { ... }` inside `Json.decode` would fail to compile because `hash` is missing from the struct literal!
- Therefore, your rule (*"`impl I for User;` specializes the template with `User`'s module's view, so private fields are visible"*) is **actually the only rule that allows `T { ... }` to construct `User`**!
- **Wait:** then why did `NonZero` and `User` look dangerous?
  1. For `NonZero`, the author of `nonzero.fly` should **not** write `impl Json for NonZero;` (a raw field-wise derivation) if `NonZero` has an invariant on `val`; they should write a 4-line custom `impl Json for NonZero` that calls `NonZero.new(p.int())`!
  2. What if a struct in module `A` contains a field of type `NonZero` (from module `B`), and module `B` did **not** write `impl Json for NonZero;`?
     Under your rule #6, because `impl<comptime T: Type> Json for T` only applies automatically to *structural* types and *nominal types that request it* (`impl Json for NonZero;`), module `A` **cannot** force `NonZero` to use the template `impl`!
  3. **What is the real hole in Proposed #2 & #6?**
     Look at Proposed #2:
     > *"Reflection respects privacy: `Type.info` shows a nominal type's private fields only to code specialized on behalf of its own module (see 6); elsewhere a struct with private fields is `#Opaque`."*
     What if a function in module `A` takes `<comptime T: Type>` directly — **not** via `impl I for User;`, e.g.:
     ```ts
     // module sneak.fly
     export function dumpAllFields<comptime T: Type>(x: readonly T): void { ... }
     ```
     When `user.fly` calls `dumpAllFields(u)` (where `u: User`), is `dumpAllFields<User>` "specialized on behalf of `User`'s module" just because `user.fly` called it?!
     If calling any helper function `foo(u)` from `user.fly` grants `foo` access to `User`'s private fields via `<comptime T: Type>` inference, then **any third-party generic function called by `user.fly` can silently read and mutate `User`'s `private` fields** without `user.fly` knowing `foo` used reflection!

**Fix:**
Draw a bright line for privacy in `Type.info(T)`:
- `Type.info(T)` exposes `private` fields of a nominal type `S` **only** when the specialization is:
  1. defined in `S`'s declaring module, **or**
  2. an `impl I for S;` declaration explicitly written in `S`'s declaring module (and **only** for `T = S` itself, not for other private structs that `S`'s module happens to import).
- An ordinary `<comptime T: Type>` function called from `S`'s module (like `log(u)`) does **not** gain private-field access to `S` unless `S` is declared in the same module as `log`.

---

#### 3. Moving out of `&readonly self` and `Drop` types in template impls (`§4.1`, `§4.2`, Proposed #3 & #4)

Look at your `Json.decode` and `Json.encode` implementations and ask how ownership checking (`§4.1`, `§4.2`) interacts with computed field projections `self[f.name]` and `slots[f.name]`:

**Case 3a: Partial moves out of `slots` via `slots[f.name]` in `Json.decode`**
In `Json.decode`:
```ts
let slots: { [K in keyof T]: Option<T[K]> } = { comptime for (const f of fields) [f.name]: #None };
...
T {
  comptime for (const f of fields)
    [f.name]: match (slots[f.name]) { #Some(v) => v, #None => throw #Missing(String.from(f.name)) },
}
```
Trace the ownership of `slots`:
1. Suppose `T` is `struct Pair { a: String; b: String; }`.
2. In the first iteration (`f = a`), `match (slots["a"]) { #Some(v) => v, #None => throw ... }` **moves** `slots.a` (`Option<String>`) out of `slots`!
3. If `slots.b` is `#None`, the second iteration executes `throw #Missing("b")`!
4. When `throw #Missing("b")` unwinds the frame, `slots.a` has **already been moved** into the partially constructed `T { a: ..., b: ... }` record literal, while any remaining fields `slots.c` (`#Some(String)`) are still live in `slots` and must be dropped!
5. This works **only if** `slots[f.name]` (where `f.name` is a `comptime str`) is elaborated into a real first-class field path `slots.a` before ownership checking (`§11` step 3: *"Check ownership after typing"*), so the borrow/move tracker sees per-field moves `slots.a`, `slots.b` rather than an opaque dynamic index `slots[expr]` (since you cannot move an element out of an array by dynamic index `arr[i]`, `§4.1`!).

**Case 3b: What if `T` implements `Drop` (`§4.1`)?**
`§4.1` states:
> *"Moving a field out of a value moves only that field, unless the value's type implements `Drop`, from which no field may be moved."*

What if a template takes `self: Self` by move (for example, ` Into` or a consuming transformation) and projects `self[f.name]` on a type `T` that implements `Drop`?
Because ownership checking runs on the specialized AST (`§11`), moving `self[f.name]` out of a `Drop` type `T` will be caught and rejected by `§4.1`.

**Case 3c: What if `T` is a `view` type or class-2 type (`readonly U`, `str`, `Scanner`) in `Json.decode`?**
Look at `Json`:
```ts
export interface Json {
  function encode(self: readonly Self, out: mut String): void;
  function decode(p: mut JsonParser): Self uses Fail<JsonError>;
}
```
Notice `decode(p: mut JsonParser): Self`!
By `§4.2`, `decode` is a free/associated function (no `self` parameter) whose only borrowed argument is `p: mut JsonParser`.
What if someone encodes/decodes a type containing `str` (like `type Msg = { text: str }`)?
- `encode` works fine on `{ text: str }`!
- What about `decode(p: mut JsonParser): Self`?
  By `§4.2` (*"without a `from` clause, the receiver for a method and every borrowed argument for a free function"*), `decode`'s return type `Self` would automatically borrow from `p: mut JsonParser` if `Self` is class 2 (`{ text: str }`)!
  Wait: is `Self` in `interface Json` allowed to be class 2, or do interface `Self` and type parameters range over **class-1** types (`§0.1` / `§4.2`)?
  Check `§0.1` and `§4.2` in Spec 0.20:
  > *"A nominal type's parameters range over class-1 types unless it is a `view` (§4.2)"*
  What about `<T>` and `<comptime T: Type>` on functions and interfaces, and `Self` on interfaces?
  In `A.1` / `§4.6`:
  ```ts
  impl<region R, T> Iterable<readonly T> for RegionList<R, T>
  ```
  Here `Iterable<T>` is an interface instantiated with `readonly T` (class 2!).
  And for `Show` or `Eq` or `Json.encode`, you **definitely** want `str` and `readonly T[]` and `{ name: str }` (which are class 2!) to implement `Eq`, `Hash`, `Show`, and `JsonEncode`!
  Look at what happens if `encode` and `decode` are in the **same** `interface Json`:
  ```ts
  // I just want to serialize a log line with a borrowed `str`!
  const msg = { level: "info", text: "started" }; // `{ level: str; text: str }` — class 2!
  let out = String.new();
  msg.encode(mut out); // ERROR if `Json` requires `decode` to exist for `str`!
  ```
  Look at `msg.encode(mut out)`:
  - Almost every outgoing JSON payload or log entry in a server contains borrowed `str` or `readonly T[]` slices (`{ status: "ok", user: req.user }`) so it doesn't have to heap-allocate `String`s just to serialize JSON!
  - `str` can be **encoded** to JSON trivially (`writeString(self, out)`), and `readonly T[]` can be encoded to JSON trivially (`[1, 2, 3]`)!
  - Neither `str` nor `readonly T[]` can be **decoded** into an owned value without an allocator/region (or unless `Json` is split or `str` decodes from a zero-copy parser)!
  - If `encode` and `decode` are forced into a single `interface Json`, then **no record containing `str` or `readonly T[]` can be encoded to JSON** unless `str` implements `decode(p: mut JsonParser): str`!

**Fix:**
Either:
1. Split `JsonEncode` and `JsonDecode` (just like Rust's `Serialize` / `Deserialize`), **or**
2. Have `JsonParser` borrow the input `src: str` (`view struct JsonParser { src: str; pos: usize; }`) so `str.decode(p: mut JsonParser): str` (zero-copy slice of `p.src` when unescaped!) or region-allocated `JsonDecode<region R>` works, **or** split `Encode` / `Decode` so any `{ name: str; items: readonly i32[] }` can be encoded without needing `Decode`! Splitting `JsonEncode` / `JsonDecode` (with `interface Json extends JsonEncode, JsonDecode {}` as a convenience alias using `§3.4`!) costs nothing and lets every `str` and slice be serialized with zero allocations.

---

#### 4. Infinite recursion in `comptime` template specialization on recursive types (`§3.3`, Proposed #1 & #6)

Look at `enum Expr` from `§3.3`:
```ts
enum Expr { #Num(f64), #Add(Box<Expr>, Box<Expr>), #Neg(Box<Expr>) }
impl Json for Expr;
```
Or `Scope<R>` from `A.5`:
```ts
struct Scope<region R> {
  parent: Option<Ref<Scope>>;
  ...
}
```
Trace what happens when `impl<comptime T: Type> Json for T` is specialized for `T = Expr`:
1. The compiler starts specializing and type-checking `Json.encode<Expr>`.
2. Inside `Json.encode<Expr>`, the `#Add` arm calls `x.encode(out)` where `x: [Box<Expr>, Box<Expr>]`.
3. That specializes `Json.encode<[Box<Expr>, Box<Expr>]>`, which calls `Box<Expr>.encode(out)`.
4. `impl<T extends Json> Json for Box<T>` checks the bound `Expr extends Json` and calls `Expr.encode(out)`.
5. If the compiler expands and type-checks `Json.encode<Expr>` eagerly without registering `(Json, Expr)` in a specialization memo table **before** checking the body of `Json.encode<Expr>`, the compiler loops forever (hitting the comptime step budget and rejecting every recursive type)!
6. Worse: what if a template function does **not** state its return type or effects (e.g. a local helper function), vs an `impl` method whose signature `function encode(self: readonly Expr, out: mut String): void` is ** completely known before checking its body**?

**Fix:**
Because every template `impl` method and exported template function has an explicit signature (`§3.6`), specialization must be **memoized by `(DeclId, ComptimeArgs)` header first**:
1. When instantiating `impl<comptime T: Type> I for T` at `T = Expr` (or calling `f<Expr>`), record the instantiation key `(impl_id, Expr)` with its instantiated method signatures in a worklist/table *before* specializing its body.
2. Any recursive call to `Expr.encode` inside the body resolves against the already-registered signature and breaks the cycle.

---

#### 5. `TypeInfo` in Proposed #2 cannot represent Flyscript's three tag forms or region parameters (`§2.3`, `§3.2`, `§4.6`)

Look at `§2.3` and `§3.2` for tag unions and enums:
```ebnf
Tag = "#" Ident [ "(" Type { "," Type } ")" | Record ] ;
```
In Flyscript (`§3.2`, `§5.5`, `A.6`):
- A tag can have **no payload**: `#None`, `#Stop`
- A tag can have a **tuple payload** (one or more types): `#Some(T)`, `#Add(Box<Expr>, Box<Expr>)`
- A tag can have a **record payload**: `#Item { item: T; rest: Cont<...> }`, `#Get { key: String; reply: Reply<...> }`

Look at your proposed `Tag` in `TypeInfo`:
```ts
type Tag = { name: str; payload: Option<Type> };
```
If `payload` is just `Option<Type>`, then:
1. In `Json.encode`:
   ```ts
   #Some(_) => #[t.name](x) => ...
   ```
   What if the tag is `#Add(Box<Expr>, Box<Expr>)` (2 positional arguments) or `#Get { key: String; val: String }` (a record payload, matched with `#Get(x)` or `#Get { ... }`)?
   Wait: in Flyscript's grammar (`§2.3`), is `#Get { key: String; val: String }` a tag whose payload is a structural `#Record` type, or is its constructor syntax different from `#Get({ key, val })`?
   Look at `§5.5` and `A.6`:
   - In `§5.5`: `#Item { item, rest } => ...`
   - In `A.6`: `#Get { key, reply } => ...`
   If `#Get { key: String }` is matched as `#Get { key }` and not `#Get(x)`, then `#[t.name](x)` in your `Json.encode` fails to parse or fails to match record-payload tags and multi-argument tuple tags (`#Add(a, b)`)!
2. What if a unified rule in the grammar says: a tag payload is always 0 types (`#None`) or 1 type (`#Some(T)`), where `#Add(A, B)` is sugar for a tuple payload `#Add([A, B])` and `#Get { k: V }` is sugar for a record payload `#Get({ k: V })`, so that **`#Tag(x)` always binds the entire payload (whether single value, tuple, or record) to `x`**?
   Check that! If `#Tag(x)` in a pattern or constructor is legal whenever `#Tag` has a payload (binding `x` to the single value, tuple `[a, b]`, or record `{ key, val }`), then your `#[t.name](x)` in `Json.encode` and `#[t.name](t.payload.decode(p))` in `Json.decode` handles **all three tag forms in one arm**!

**Fix:**
Make that an explicit grammar/elaboration rule in `§3.2`:
- A tag has either no payload (`#A`) or a single payload type `T` (`#A(T)`), where `#A(T1, T2)` is sugar for `#A([T1, T2])` and `#A { f: T }` is sugar for `#A({ f: T })`.
- Therefore, in both expressions and patterns, `#A(x)` is valid for **every** payload-carrying tag (including multi-element tuple tags and record tags!), and `Tag = { name: str; payload: Option<Type> }` in `TypeInfo` is 100% sufficient and exact!

---

#### 6. `T { ... }` in `Json.decode` fails when `T` is a structural `#Record` (`§2.2`, Proposed #3)

Look at the end of `Json.decode` in your code:
```ts
        T {
          comptime for (const f of fields)
            [f.name]: match (slots[f.name]) { #Some(v) => v, #None => throw #Missing(String.from(f.name)) },
        }
```
Look at the `comptime match` arm it is inside:
```ts
      #Record(fields) | #Struct({ fields }) => {
```
When `T` is a structural record `{ x: i64; y: i64 }` (`#Record(fields)`), `T` is **not** a nominal `struct`!
And even when `T` is a `comptime` parameter `T: Type`, look at `§2.2`:
> *"Record literals. `{ f: e, … }` builds the nominal struct named by the expected type, if there is one, and a structural record otherwise. `Point { … }` names the struct explicitly."*

Because the return type of `decode` is **already `T`**, the expected type of the final expression in `decode` is **`T`**!
So under `§2.2`, writing a plain record literal `{ comptime for (const f of fields) [f.name]: ... }` (without `T` in front of `{`) builds **both** a structural `#Record` when `T` is `#Record` **and** the nominal `#Struct` when `T` is `#Struct`!
You don't need `T { ... }` (where `T` is a `Type` value rather than a `Path`) at all — `{ ... }` with expected type `T` already works in Flyscript by `§2.2`!

---

### Answers to your 5 Questions

#### Question 1: Templates vs. Staged Quotes vs. Shape Induction (`Mirror` / `Generic`)

**Verdict: Templates (`<comptime T: Type>`) win decisively for Flyscript.** Here is the honest comparison:

1. **Why Shape Induction (`GHC.Generics`, Scala 3 `Mirror`, Rust `frunk`) is the wrong fit for Flyscript:**
   - Shape induction encodes every struct/enum as nested binary products/sums (`Field<"x", f64> * (Field<"y", f64> * Empty)`).
   - It **cannot** express `Soa<T>` (`§7.2`), which recursively flattens nested structs (`Particle` -> `Vec2`) into a single flat struct of planes and generates a nested class-2 `View` record (`{ pos: { x: mut f32; y: mut f32 } }`).
   - It **cannot** write the imperative single-pass `for (const key of p.keys()) { match (key) { ... } }` loop in `Json.decode` without closures/trait-objects per field or horrific recursive trait-level state machines (`HList` of `Option`s).
   - And Flyscript already has a row calculus (`§3.2`), not recursive type-level `Cons`/`Nil` lists (`§3.3`: *"Structural rows are always finite"*).

2. **Why Staged Typed Quotes (`'[ ... ]` / `${ ... }` as in MetaOCaml / Scala 3) are the wrong fit for Flyscript:**
   - Staged quotes cannot be checked once when the quote **synthesizes new types or projects fields that depend on `T`** (`self[f.name]`, `Soa<T>`, `{ comptime for ... }`). In Scala 3, as soon as a macro inspects fields of `T` or builds a struct type, it drops out of typed quotes into untyped AST reflection (`Quotes.reflect`), which is a huge compiler-internal API.
   - Staged quotes introduce two syntax worlds (value-level vs AST-quote-level).

3. **Why `<comptime T: Type>` (per-specialization checking) + `<T extends I>` (parametric checking) is the sweet spot:**
   - Users never write `<comptime T: Type>` in application code; they write `<T extends Json>` (parametric, checked once!) or `impl Json for User;` (checked immediately at the `impl Json for User;` line!).
   - Because `impl Json for User;` is checked where `User` is declared, **template errors for nominal types are caught at the type declaration site, not deep inside a call stack!**
   - The only case where a template is instantiated at a call site is an ad-hoc structural type (`{ a: 1, b: fnPtr }.encode(mut out)`), where the error `"in Json.encode<{ a: i32; b: () => void }>: () => void cannot be encoded as JSON"` points directly to the offending field type.

---

#### Question 2: The Generation Device & Surface Syntax

Your core trio (`comptime if/match`, `comptime for`, `[e]`) is very close to minimal. Four concrete adjustments will make it completely solid:

1. **Drop `{ [K in keyof T]: Option<T[K]> }` mapped-type sugar (Proposed #4).**
   - It adds two TypeScript type-operator keywords (`in` in type position and `keyof`) for something that is used ~3 times in the entire standard library and is already written clearly as `{ comptime for (const f of fields) [f.name]: Option<f.type>; }`!
   - Cutting `keyof` and `in`-mapped-types obeys Review Rule 3 (*"Prefer fewer concepts"*).

2. **Resolve the syntactic ambiguity between computed field access `v[f.name]` and indexing `v[i]`.**
   - In Flyscript, what if `v` is a `HashMap<str, i32>` or a custom struct with indexing, vs a struct with a field accessed by `v[f.name]`?
   - Better syntax: **`v.[f.name]`** (with the dot!) for computed field access, and **`#[t.name]`** (with the hash!) for computed tags, while `{ [f.name]: val }` is unambiguous in record types and record literals.
   - Look at `self.[f.name].encode(out)` vs `slots.[f.name]`: the `.` makes it 100% unambiguous to both the parser and the human reader that this is **field projection** (`v.field`), not container subscripting (`v[key]`)!

3. **Clarify `f.type.decode(p)` when `f.type` is a comptime `Type` value:**
   - In `Json.decode`, you wrote `f.type.decode(p)`.
   - What if `f.type` is a structural record `{ x: i32 }`, a tuple `[i32, i32]`, or a generic type `Vec<i32>`? In ordinary Flyscript syntax, you cannot write `{ x: i32 }.decode(p)` or `[i32, i32].decode(p)` in expression position because `{` begins a record literal and `[` begins an array literal!
   - Allow either `Type`-variable qualification `const F = f.type; F.decode(p)` / `f.type.decode(p)` (when the receiver is a comptime expression of type `Type`) **or** interface-qualified calls `Json.decode<f.type>(p)`. Supporting `Json.decode<T>(p)` (calling an interface function with an explicit type argument) is useful across the whole language, not just in `comptime`!

4. **Complete the `#Union(tags) | #Enum({ tags })` arm of `Json.decode` to be sure nothing is missing:**
   Let's write the `#Union | #Enum` arm of `Json.decode` in your exact syntax to verify it works:
   ```ts
   #Union(tags) | #Enum({ tags }) => {
     if (p.isString()) {
       const tag = p.str();
       match (tag) {
         comptime for (const t of tags)
           comptime if (t.payload == #None)
             t.name => #[t.name],
         _ => throw #Unknown(String.from(tag)),
       }
     } else {
       const key = p.singleKey();
       match (key) {
         comptime for (const t of tags)
           comptime match (t.payload) {
             #Some(P) => t.name => { const v = P.decode(p); p.endObj(); #[t.name](v) },
             #None    => {}, // omitted from this match!
           }
         _ => throw #Unknown(String.from(key)),
       }
     }
   }
   ```
   Look at the `#None => {}` case inside `match (key)` above!
   When iterating `comptime for (const t of tags)` to generate `match` arms, sometimes you want to **skip** generating a `match` arm for certain elements (e.g. skip `#None`-payload tags when matching object-encoded tags, and skip `#Some`-payload tags when matching string-encoded tags)!
   **Crucial syntax rule for Proposed #3:**
   Inside a sequence context (match arms, record fields, record literal entries, statements), a `comptime if (c) { ... }` (with no `else`) or a `comptime match` arm with an empty block `{}` must contribute **zero items** to the enclosing sequence!
   Verify that your parser/expander allows `comptime if` and `comptime match` around match arms and record entries to emit 0, 1, or many items.

---

#### Question 3: Soundness and Ownership

Beyond **Problem 1** (coherence of `Option<T>`), **Problem 2** (`private` field visibility), and **Problem 3** (`slots.[f.name]` partial moves and `JsonEncode` vs `JsonDecode` for class-2 types), check one more case:

**How does `Soa<T>` (`§7.2`) work under this design without `unsafe`?**
Look at `§7.2`:
```ts
// Soa<Particle> stores planes pos.x, pos.y, vel.x, vel.y, mass and has
// View = { pos: { x: mut f32; y: mut f32 }; vel: { x: mut f32; y: mut f32 }; mass: mut f32 }
```
Can `Soa<T>` actually be written in pure Flyscript with the primitives in Proposed #1–#6?
Let's check!
```ts
export comptime function Soa(comptime T: Type): Type {
  struct {
    len: usize;
    comptime for (const f of Type.fields(T))
      [f.name]: Plane(f.type); // recursive: if f.type is a struct, Plane(f.type) is Soa(f.type), else Vec<f.type>!
  }
}
```
Wait: look at that recursive definition of `Soa(T)`!
Instead of flattening into a single untyped byte buffer with pointer arithmetic, if `Soa(Particle)` recursively expands to:
- for a primitive field `mass: f32` -> `mass: Vec<f32>` (or `f32[]` when split!)
- for a nested struct field `pos: Vec2` -> `pos: Soa(Vec2)` (which has `x: Vec<f32>; y: Vec<f32>`)!
Then:
1. `Soa(Particle)` requires **zero `unsafe` pointer arithmetic**!
2. `split(self: mut Self, at: usize)` on a slice-backed view `SoaSlice<T>` simply calls `.split(at)` on each field (`self.[f.name].split(at)`) using `comptime for`!
3. `viewAt(self: mut Self, i: usize)` is simply `{ comptime for (const f of fields) [f.name]: self.[f.name].viewAt(i) }` — which produces `{ pos: { x: mut f32; y: mut f32 }; vel: ...; mass: mut f32 }` completely safely in ~25 lines of Flyscript!
That is a huge validation of your design: recursive `Soa<T>` + `SoaSlice<T>` implementing `ParSplit` works in 100% safe Flyscript using only `comptime for` and `.[f.name]`.

---

#### Question 4: Templates and Effects / Rows (`Hash<row E>`)

Look at `interface Hash` from `§3.4`:
```ts
interface Hash<row E = []> {
  function hash(self: readonly Self, h: mut Hasher): void uses ...E;
}
```
Now write the derived template `impl` for `Hash`:
```ts
impl<comptime T: Type, row E = []> Hash<E> for T {
  function hash(self: readonly Self, h: mut Hasher): void uses ...E {
    comptime match (Type.info(T)) {
      #Record(fields) | #Struct({ fields }) => {
        comptime for (const f of fields) {
          self.[f.name].hash(mut h);
        }
      }
      ...
    }
  }
}
```
How does `row E` work when checking a specialization of `impl<comptime T: Type, row E = []> Hash<E> for T`?
- `T` is a `comptime` parameter (known concrete type at specialization time).
- `row E` is a **normal parametric row variable** (`§3.2`)!
- When the compiler specializes `Hash` for `User`, the specialized method is still polymorphic in `<row E>` (or defaults to `E = []` in `impl Hash for User;`), and inside the specialized body, each call `self.[f.name].hash(mut h)` unifies its effect row with `...E` using the existing row unifier (`§3.2`)!
- One rule is needed: when `impl Hash for User;` is written without row arguments, it uses the interface's default row `E = []` (pure hashing).

---

#### Question 5: What to cut, and what is missing to beat Zig / Rust / D / C++26

1. **Cut:**
   - **Cut `{ [K in keyof T]: Option<T[K]> }` mapped-type syntax.** Keep one way to build record types from fields: `{ comptime for (const f of fields) [f.name]: Option<f.type>; }`.
   - **Cut `Type.fields(T)` as a separate primitive if `Type.info(T)` exists** (or make `Type.fields(T)` a 4-line standard-library `comptime function` over `Type.info(T)`).

2. **What is missing (one small feature required by every real-world `serde` user):**
   - **Field and tag metadata? No — keep it smaller: `comptime` constants on types or default field values?**
   Wait: what is the #1 thing a TypeScript service author writes after `struct User { id: i64; name: String; email: Option<String>; }`?
   In JSON APIs, an optional field `"email"` is very often **omitted** from the JSON object (`{"id": 1, "name": "Ada"}`) rather than sent as `"email": null`!
   Look at your `Json.decode`:
   ```ts
   [f.name]: match (slots.[f.name]) { #Some(v) => v, #None => throw #Missing(String.from(f.name)) }
   ```
   If `"email"` is omitted from the JSON input `{"id": 1, "name": "Ada"}`, `slots.email` is `#None` (because the `"email"` key never appeared in `p.keys()`!), so your `Json.decode` throws `#Missing("email")` even though `email`'s type is `Option<String>`!
   Look how easily your `comptime` design fixes that **without any new language feature** if `Json` has a default hook or `Type.info` recognizes `Option<U>`:
   In `Json`, add a default method on the interface (or a helper `comptime function isOption(comptime T: Type): bool`):
   ```ts
   // In Json.decode: if a key was omitted from the JSON object and its field type is `Option<U>`,
   // its missing value defaults to `#None`!
   ```
   Wait: with your `Type.info(f.type)`, since `Option<U>` is `#Union([{ name: "None", payload: #None }, { name: "Some", payload: #Some(U) }])`, a 3-line `comptime function isOption(comptime T: Type): bool` can check if `f.type` is `Option<U>`, and if so, emit `#None` instead of `throw #Missing(...)` when the key is omitted from JSON!
   Show that in `std/json.fly`! Handling both `{"email": null}` and omitted `{}` for `Option<T>` fields automatically via a 3-line `comptime` check in `Json.decode` is a showcase that neither Rust `serde` (which requires `#[serde(default)]` or a trait) nor TypeScript can do as cleanly.

---

### Smaller points

- **Syntax in `comptime match` (`#[t.name](x) =>` inside `=>`):**
  In your `Json.encode` union arm:
  ```ts
  comptime match (t.payload) {
    #Some(_) => #[t.name](x) => { ... },
    #None => #[t.name] => writeString(t.name, out),
  }
  ```
  Having `=> #[t.name](x) =>` (two `=>`s on one line: the outer `comptime match` arm's `=>` followed immediately by the generated runtime `match` arm's pattern `#[t.name](x) =>`) is hard to parse visually and in a recursive-descent parser. Requiring braces around generated match-arm blocks in `comptime if` / `comptime match`:
  ```ts
  comptime match (t.payload) {
    #Some(_) => { #[t.name](x) => { ... } }
    #None    => { #[t.name] => writeString(t.name, out), }
  }
  ```
  eliminates the double-`=>` ambiguity cleanly.
