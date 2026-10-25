# Core interfaces: conversion, lending, operators, defaults and collecting — a design

A proposal, for review, to widen the prelude's interfaces. Today the prelude has three kinds of interface:

- the markers `Copy`, `Send` and `LentBy`, which the compiler decides from structure, and `Drop`;
- the derived interfaces `Eq`, `Ord`, `Hash`, `Show` and `Clone` (§3.5);
- `Iterable`, for `for…of` (§5.5).

That covers comparing, hashing, printing, cloning and iterating. It does not cover converting one type to another, letting a type of the program's own stand in for a borrow, arithmetic on a type of the program's own, a type's empty value, or collecting into anything but a `Vec`. Each gap is worked around in the repository today: `parseInt` and `parseFloat` are free functions, `std/simd` declares its own `Lane` interface with `laneAdd`, `laneSub` and `laneMul` and gives `Simd` methods called `add`, `sub` and `mul`, `str.toString()` and `Box.into()` are methods of one type each, and the codec design (`2026-10-25-codec-design.md`, item 7 of section 6) already asks for a derived `Default`.

This design adds interfaces for those five things, and answers whether Flyscript needs Rust's split between `Debug` and `Display`. Three of the language's rules constrain every part of it, and the design keeps all three:

- **Lending is the only implicit conversion** (§4.1). A conversion that allocates or computes is always a call someone wrote.
- **Errors are not converted** (§12.2). Failure rows compose by union, so `throw` never calls a conversion, and nothing here gives Rust's `?` a `From`.
- **Dispatch is static and effects are visible** (goal 2, §5.1). Every interface here is resolved at compile time, and the methods an operator or a lending calls perform no effects.

Nothing here is implemented, and `docs/spec.md` is not changed. A `§` number refers to the specification, and a "section" to this document. The design needs no default method bodies on interfaces, which the codec design (its open question 9) and the Rust-surface proposal (its finding 9) both raise.

## The design in brief

1. **Conversions are `From<T>` and `TryFrom<T>`**, called through the type (`String.from(s)`, `u16.tryFrom(n)`). `TryFrom` fails through `Fail`, like everything else. `Into<T>` and `TryInto<T>` are their bound forms, given to every type by blanket impls, so a function can take `<N extends Into<String>>`. No conversion is ever inserted by the compiler.
2. **A call's type argument that nothing else fixes is taken from what is expected.** That makes `const n: Name = "ada".into()` and `const s: HashSet<String> = g.collect()` work. If nothing is expected, the parameter's default is used, so `collect()` still makes a `Vec`. Without a default, the call is an error that says what to write.
3. **The orphan rule also counts the interface's type arguments.** So `impl From<Celsius> for f64` and `impl Mul<Vec2> for f64` may be written in the module that declares `Celsius` or `Vec2`. Acyclic imports keep this coherent, and impls that overlap are an error.
4. **Lending becomes an interface.** `Lends<U>` and `LendsMut<U>` replace the compiler's fixed list (`String` lends `str`, `Vec<T>` lends `T[]`, and so on), and the prelude's types implement them. A type of the program's own can then be passed where a borrow of what it lends is wanted, be compared with it, be used to search a map, and reach its methods. Lending is pure, takes at most one step through such an impl, and must agree with `Eq`, `Ord` and `Hash`.
5. **Operators are `std/ops` interfaces**: `Add<Rhs = Self, Out = Self>` and the rest, `Neg`, the compound forms such as `AddAssign`, and `Index`/`IndexMut`. Operands are lent `readonly`, so `a + b` moves nothing. The primitives implement all of these, so generic numeric code can be written at last. `==`, `<`, `&&` and `||` do not change.
6. **`Default` is a derived prelude interface**, as the codec design asks. A record literal may begin with a spread, `{ ...Config.default(), port: 8080 }`, and `take(place)` moves a value out of a `mut` borrow and leaves the default behind.
7. **Collecting is `FromIterable<T, row E>` and `Extend<T, row E>`.** `collect()` makes any collection, while a `Vec` stays the default. A failure while collecting is an effect that passes through, so Rust's `collect::<Result<…>>()` is not needed.
8. **`Display` joins `Show`, never derived.** Templates and `join` use it when a type has it, and use `Show` otherwise. That is exactly what they do now for strings and numbers, so no existing output changes.

## 1. What the compilers do today

These programs were run against the Rust prototype (`flyc run`) and, where noted, the self-hosted compiler (`selfhost/seed.js`, to JavaScript), at `01457c3`. The interfaces were declared by hand in the test program.

| # | Finding | Compilers |
| :- | :--- | :--- |
| 1 | **Arithmetic on a struct is accepted by the checker.** For `struct V { x: f64; y: f64; }`, `a + b` checks without error. `flyc` then panics at run time with `bad operands for +`, and the self-hosted compiler emits JavaScript that prints `.und`. The checker requires only that the two operand types unify (`selfhost/check.fly`, the binary-operator case before `pendingOps`). | both |
| 2 | **A generic `From`/`Into` written in a program works for direct calls.** With `impl<T, U extends From<T>> Into<U> for T`, both `Name.from("ada")` and `const m: Name = "bob".into()` run. | both |
| 3 | **A type with two impls of one generic interface picks the first.** With both `From<str>` and `From<u32>` for `Name`, `Name.from(7)` reports ``expected `str`, found `?0` ``. | both |
| 4 | **A generic impl and a specific impl of one interface for one type** give ``` `Name` has no function `from` ```, rather than an error about the overlap or a choice between them. | `flyc` |
| 5 | **A bound is not met through a blanket impl.** `greet<N extends Into<Name>>` called with a `str` reports `` `str` does not implement `Into<Name>` ``, even though the call in finding 2 used that same impl. | `flyc` |
| 6 | **A method's type-parameter default is ignored.** `build<C extends Make = Vec<i32>>()` with nothing expected does not use `Vec<i32>`, and the error names an unrelated type. | `flyc` |
| 7 | **`Self` cannot be used in an interface's type-parameter default** (`interface Mul<Rhs = Self>`). | `flyc` |
| 8 | **A primitive cannot be named as a type in a call.** `u8.mk(3)` reports ``unknown name `u8` ``. | `flyc` |

Finding 1 is a bug whatever happens to this design. Findings 3 to 8 are what the design needs from interface resolution, and section 12 lists them as work.

## 2. Conversions

```ts
// The prelude, sketch.
// `Self` made from a `T`, losing nothing: `String.from("ada")`, `i64.from(n)` for an `i32` n.
export interface From<T> { function from(v: T): Self; }

// `Self` made from a `T` when it can be: `u8.tryFrom(300)` fails with `#OutOfRange`.
export interface TryFrom<T> {
  type Error;
  function tryFrom(v: T): Self uses Fail<Self.Error>;
}

// The bound forms. Every type has them through the blanket impls below.
export interface Into<T> { function into(self: Self): T; }
export interface TryInto<T> {
  type Error;
  function tryInto(self: Self): T uses Fail<Self.Error>;
}

impl<T> From<T> for T { function from(v: T): T { v } }
impl<T, U extends From<T>> Into<U> for T { function into(self: Self): U { U.from(self) } }
impl<T, U extends TryFrom<T>> TryInto<U> for T {
  type Error = U.Error;
  function tryInto(self: Self): U uses Fail<U.Error> { U.tryFrom(self) }
}
```

**`From` is implemented, `Into` is used as a bound.** Flyscript's bounds constrain a type parameter, `<N extends …>`, and there is no `where` clause to constrain another type. So "a `String` can be made from `N`" has to be written as a bound on `N`, which is `N extends Into<String>`. This is why Rust has both traits, and the reason holds here:

```ts
struct User { name: String; }
impl User {
  // A `str` is copied once; a `String` is moved in, not copied.
  export function new<N extends Into<String>>(name: N): User { User { name: name.into() } }
}
User.new("ada");
User.new(line.trim().toString());
```

`impl<T> From<T> for T` is what makes `User.new(aString)` legal.

**Blanket impls.** An impl whose head is a bare type parameter, such as `impl<T, …> I<…> for T`, is a *blanket impl*. Only `I`'s own module may declare one. It ranks with derivations (§7.3): every specific impl whose head matches comes first. A derivation is a blanket impl whose parameter is `comptime`. Two things differ:

- **A parametric blanket impl reaches nominal types without being asked.** A derivation reads a type's private shape, so a struct must ask for one (`impl Eq for Point;`). A parametric blanket impl sees nothing but its bounds, so there is nothing to ask for.
- **A bound is met through a blanket impl** exactly when the blanket impl's own bounds are met. That is finding 5.

**Choosing among a type's impls.** A type may have several impls of one generic interface: `f64` is `From<f32>`, `From<i32>` and, through the blanket impl, `From<f64>`. A call through the type, `String.from(x)`, or through a value, `x.into()`, chooses by the argument's type. The argument is checked first with nothing expected, and then the impl it fits is used. An exact fit beats a fit by lending. A number literal takes the argument type of the one impl whose argument is a number, and if there are several, the call is an error that asks for a typed literal. That is finding 3.

**Never implicit.** A `From` is never inserted at a call, a return or a `throw`. Converting allocates or computes, and lending stays the only conversion nobody writes. At a failure boundary, a conversion is written where the code already says what happens, `Fail.map(() => load(p), (e) => #Config(e))` (§5.4), and nothing here changes that.

**`TryFrom` fails like everything else.** Its error is the impl's own associated type, a tag union, so `TryInto`'s error is whatever `U.Error` is. A caller's `Fail` row takes it up by union, as it would from any other call.

**Parsing text is `TryFrom<str>`.** A number is read with `u16.tryFrom(raw)` or `const port: u16 = raw.tryInto();`, which fails with `#NotANumber` or `#OutOfRange`. `std/time`'s `Timestamp` and `std/uuid`'s `Uuid` would do the same with their own errors. Rust needs a separate `FromStr` because a `&str` argument carries a lifetime. A `str` argument here carries nothing that needs spelling out, so one interface is enough. `parseInt` and `parseFloat` stay, because they are TypeScript's.

**The standard impls:**

| Type | `From` | `TryFrom` |
| :--- | :--- | :--- |
| Integers | Each narrower integer that fits every value: `i64.from(i32)`, `u32.from(u8)`, `i32.from(u16)` | Every other integer, failing with `#OutOfRange`; `str`, failing with `#NotANumber` or `#OutOfRange` |
| `f64` | `f32`, and integers of up to 32 bits | `str`, failing with `#NotANumber` |
| `f32` | Integers of up to 16 bits | `str` |
| `bool` | — | `str`, `"true"` or `"false"` |
| `String` | `str` (copied) | `Vec<u8>`, failing with `#MalformedUtf8`, as `String.fromUtf8` does |
| `Vec<T>` | `T[N]` (moved), `readonly T[]` with `T extends Clone` (cloned) | — |
| `Box<T>`, `Arc<T>` | `T` | — |

Every type is also `From` itself, through the blanket impl. `as` does not change. `From` is the lossless subset of what it does, and `TryFrom` is the checked form.

Conversions to and from types of the program's own are the reason section 4 widens the orphan rule:

```ts
// celsius.fly, which declares Celsius and neither f64 nor From.
export struct Celsius { degrees: f64; }
impl From<Celsius> for f64 { function from(c: Celsius): f64 { c.degrees } }
impl From<f64> for Celsius { function from(d: f64): Celsius { Celsius { degrees: d } } }
```

## 3. Type arguments from what is expected

§3.6 says: "A method's result that is only a type variable takes its type from the receiver and the arguments, not from what is expected of it." That rule is what makes `map.get(k).unwrap()` give the map's value type, which a borrow then lends where one is expected. `into()` and `collect()` need the other direction. Their result is a type parameter that neither the receiver nor the arguments fix:

- for `"ada".into()`, `str` has an `Into<U>` for every `U` that is `From<str>`;
- for `g.collect()`, the generator says what its items are, but not what holds them.

The rule this design adds to §3.6 is: **a type argument of a call that neither the receiver nor the arguments fix is taken from the expected type when one is known. Failing that, the parameter's default is used. Failing that, it is an error.**

- The existing rule is unchanged. `unwrap()`'s `T` is fixed by its receiver, so the new rule never applies to it.
- "Known" means more than a type variable, as it already does for branches (§3.6). A call whose result goes straight into another inference variable uses the default.
- Without a default, the error says what to write: ``cannot tell what `into` makes here; write `Name.from(x)` or give the binding a type``.
- Free functions already take the expected type before their arguments (§3.6), as `parse<T extends FromJson>(text)` does. This rule gives methods the same.

Both compilers already take the expected type for `into()` (finding 2), but neither uses a default (finding 6). That is section 12's work.

```ts
const n: Name = "ada".into();                      // Name, from what is expected
const words: HashSet<String> = text.splitWhitespace().map((w) => w.toString()).collect();
const firstEvens = xs.iter().filter((x) => x % 2 == 0).take(10).collect();   // Vec, the default
```

## 4. The orphan rule and overlapping impls

§3.4 allows `impl I for T` only in the module that declares `I` or the one that declares `T`. That forbids `impl From<Celsius> for f64` and `impl Mul<Vec2> for f64` everywhere but the prelude and `std/ops`. Rust's rule allows them, and they are most of the reason a program writes operator and conversion impls at all.

**The rule this design proposes.** `impl I<A1, …, An> for T` may appear in:

- the module that declares `I`;
- the module that declares `T`'s outermost name;
- a module that declares the outermost name of one of the arguments `Ai`, provided that type parameters appear only inside that argument.

So `impl Mul<Vec2> for f64` and `impl<T> From<Wrapper<T>> for Wrapper2` are allowed in `Wrapper`'s module. `impl<X> I<Vec2, X> for f64` is not, because `X` stands outside `Vec2`.

**Coherence comes from acyclic imports.** To write an impl, a module must name every type in its head, so it imports the modules that declare them. Call the declaration that allows an impl its *anchor*. Take two impls that could match the same types and are written in two different modules:

- **One is anchored by the interface.** The other names the interface, so its module imports the interface's module, and sees the first impl.
- **One is anchored by `Self`, a type `T`.** The other's `Self` must match `T`. It cannot be a bare type parameter, which only a blanket impl in the interface's module has, so it names `T`, and its module imports `T`'s.
- **Both are anchored by arguments.** If they are anchored at the same position, both name one declaration, so they are in one module. If they are anchored at different positions, the first has no type parameter outside its own anchor. So at the second's position it names the second's anchor, and its module imports the second's.

In every case one of the two modules sees the other's impl. The restriction on type parameters is there for the last case. Without it, two impls each anchored by one argument could leave the other's position open, and neither module would see the other. So **an impl that overlaps one its module can see is an error where it is written**:

``impl `From<str>` for `Name` overlaps `impl<T extends Show> From<T> for Name` (name.fly:3); a type has one way to be made from a `str` ``

The one exception is a blanket impl (section 2), which every specific impl outranks, as a derivation is outranked today. This is finding 4.

This needs the import graph to be acyclic, as §8.1 says it must be. The Rust-surface proposal finds that today's compiler does not enforce that (its finding 5), and does not enforce the orphan rule either (its finding 3). Both have to be fixed before this rule can be relied on.

## 5. Lending as an interface

§4.1 lists who lends what: `String` lends `str`, `Vec<T>` lends `T[]`, `Box<T>` lends `T`, and `Ref<R, T>` and `Arc<T>` lend `readonly T`. The list is closed. A program's `Name`, `Path` or `Matrix` cannot join it, so a function that wants text takes `str`, and the caller writes `name.asStr()` at every call.

```ts
// The prelude, sketch.
// `Self` stands in for a `readonly U` wherever one is wanted.
export interface Lends<U> { function lend(self: readonly Self): readonly U from self; }
// …and for a `mut U`.
export interface LendsMut<U> extends Lends<U> { function lendMut(self: mut Self): mut U from self; }

impl Lends<str> for String { … }
impl<T> LendsMut<T[]> for Vec<T> { … }
impl<T, comptime N: usize> LendsMut<T[]> for T[N] { … }
impl<T> LendsMut<T> for Box<T> { … }
impl<T extends Send> Lends<T> for Arc<T> { … }
impl<region R, T> Lends<T> for Ref<R, T> { … }
```

The prelude's impls are the compiler's, as `Copy`'s are, so lending through them stays what it is now, with no call. A program's impl is an ordinary method, which the back ends inline.

```ts
export struct Name { private s: String; }
impl Lends<str> for Name { function lend(self: readonly Self): str { self.s.asStr() } }
impl Eq for Name;
impl Hash for Name;

println(name);                       // println takes a str
if (name == "ada") { … }             // compared as a str (§3.5)
users.get("ada");                    // a HashMap<Name, User> searched with a str
name.trim().len();                   // str's methods, through the lending
```

**Where it applies.** Lending applies wherever lending applies today: where a borrow is expected (§4.1), when an owner is compared with what it lends (§3.5), in map lookups through `LentBy` (below), and in method lookup. A method that `T` does not have is looked up on what `T` lends, as `String` already reaches every method of `str` (§3.1). `T`'s inherent methods come first, then the methods of `T`'s interfaces, then those of the lent type.

**It is cheap by construction.** `lend` declares no effects, so it is pure. A pure function allocates only what it returns, and `lend` returns a borrow of `self`, so it can allocate nothing. Being a `from self` result, what it returns is a class-2 value tied to the receiver (§4.2), and that needs no new ownership rule. A program's `lend` is therefore a projection: it reads a field, or reads through one.

**One step.** Lending goes through any number of the prelude's pointers (`Box`, `Arc`, `Ref`) and at most one of a program's own impls. A `Box<Name>` lends `Name`, and through `Name`'s impl it lends `str`. A `Name` that lends a `Path` that lends `str` does not lend `str`: the second step is written as `name.lend()`. A type with two impls, both of which fit an expected borrow, is an error there that names both. Rust's chains of `Deref` let a method be found several types away. The single step keeps the type that supplied a method one look away.

**The law.** If `T` lends `U`, and both are `Eq`, then `a == b` exactly when `a.lend() == b.lend()`. The same goes for `Ord`'s `cmp` and for `Hash`. A map searched with a lent key depends on this, as it depends on `Hash` agreeing with `Eq`. The checker cannot prove the law. A struct that lends its one field, with derived interfaces, keeps it automatically. A type whose equality differs from what it holds, such as an `Email` compared without regard to case, should not lend. It offers `asStr()` instead. Rust splits `AsRef` (a cheap view) from `Borrow` (a view that agrees with `Eq` and `Hash`) to allow a type that is only one of them. This design takes the stricter of the two, because one interface that does both is the smaller language.

**`LentBy` stays, as the bound form.** `Q extends LentBy<K>` holds when `K` is `Q` or `K extends Lends<Q>`. It is to `Lends` what `Into` is to `From`. `HashMap.get<Q extends LentBy<K> & Hash & Eq>(key: readonly Q)` keeps its signature.

## 6. Operators

A new module, `std/ops`, declares one interface per operator. A program imports an interface to implement it. Writing the operator needs no import, as `==` needs none for `Eq`.

| Written | Interface | Method |
| :--- | :--- | :--- |
| `a + b`, `a - b`, `a * b`, `a / b`, `a % b` | `Add`, `Sub`, `Mul`, `Div`, `Rem`, each `<Rhs = Self, Out = Self>` | `add(self: readonly Self, rhs: readonly Rhs): Out`, and likewise |
| `a & b`, `a \| b`, `a ^ b`, `a << b`, `a >> b` | `BitAnd`, `BitOr`, `BitXor`, `Shl`, `Shr`, likewise | `bitAnd`, `bitOr`, `bitXor`, `shl`, `shr` |
| `-a` | `Neg<Out = Self>` | `neg(self: readonly Self): Out` |
| `a += b` and the other compound forms | `AddAssign<Rhs = Self>` and the like | `addAssign(self: mut Self, rhs: readonly Rhs): void` |
| `c[i]`, read or lent `readonly` | `Index<I>` | `index(self: readonly Self, i: I): readonly Self.Item from self` |
| `c[i] = v`, `c[i] += v`, `c[i]` lent `mut` | `IndexMut<I> extends Index<I>` | `indexMut(self: mut Self, i: I): mut Self.Item from self` |

```ts
import { Add, Sub, Mul, Neg } from "std/ops";

export struct Vec2 { x: f64; y: f64; }
impl Add for Vec2 { function add(self: readonly Self, o: readonly Vec2): Vec2 { Vec2 { x: self.x + o.x, y: self.y + o.y } } }
impl Sub for Vec2 { function sub(self: readonly Self, o: readonly Vec2): Vec2 { Vec2 { x: self.x - o.x, y: self.y - o.y } } }
impl Mul<f64> for Vec2 { function mul(self: readonly Self, k: readonly f64): Vec2 { Vec2 { x: self.x * k, y: self.y * k } } }
impl Mul<Vec2, f64> for Vec2 { function mul(self: readonly Self, o: readonly Vec2): f64 { self.x * o.x + self.y * o.y } }  // dot
impl Mul<Vec2> for f64 { function mul(self: readonly Self, v: readonly Vec2): Vec2 { v * self } }   // section 4
impl Neg for Vec2 { function neg(self: readonly Self): Vec2 { Vec2 { x: -self.x, y: -self.y } } }

const p = origin + velocity * dt;
const along = (b - a) * dir;   // f64, the dot product
```

The rules:

- **Operands are lent `readonly`.** `a + b` moves neither operand, as a TypeScript programmer expects, and a `String` or a matrix is still there afterwards. A type that can work in place, such as a big integer adding into its own digits, implements `AddAssign` too. Rust takes operands by value so that `a + b` can reuse `a`'s buffer. Here that reuse is written `a += b`.
- **`Out` is a parameter with a default, not an associated type.** `T extends Add` then means `Add<T, T>`, closed arithmetic, which is what generic code wants. It needs no equality constraint on an associated type, and Flyscript has none. `Out` is determined by `Self` and `Rhs`: two impls that differ only in `Out` are an error, as a row's `Fail` has one payload (§3.2). This needs `Self` in an interface's type-parameter defaults, which is finding 7.
- **The left operand chooses.** `a * b` uses the impl of `a`'s type whose `Rhs` fits `b`, chosen as section 2 chooses among impls. Nothing is commutative unless written, so `2.0 * v` needs `impl Mul<Vec2> for f64`. A literal on the right takes the type of the one numeric `Rhs`, so in `v * 2.5` the literal is an `f64`. If there are several, the operator is an error that asks for a typed operand.
- **Compound assignment.** `a += b` calls `addAssign` if `a`'s type has `AddAssign<B>`. Otherwise it is `a = a + b`, which needs `Out` to be `Self`. The place `a` is evaluated once.
- **Operators perform nothing.** The interfaces' methods declare no effects, so an impl performs none (§3.4). An operator cannot do I/O, throw, or allocate in a region. It may allocate what it returns, and it may panic, as integer `+` panics on overflow. Reading `a + b`, a reader knows nothing happened but arithmetic.
- **The primitives implement them.** Integers and floats are `Add`, `Sub`, `Mul`, `Div` and `Rem`, signed integers and floats are `Neg`, and integers are the bit operators. These impls are the compiler's: an operator on a primitive compiles as it does now, and the impls exist so that bounds hold. This is the first time numeric code can be generic without `comptime`:

  ```ts
  function dot<T extends Add & Mul & Default & Copy>(a: readonly T[], b: readonly T[]): T {
    let acc = T.default();
    for (const i of 0..a.len()) { acc += a[i] * b[i]; }
    acc
  }
  ```

  `std/simd`'s `Lane` and `IntLane` then become bounds over these interfaces, and `Simd<T, N>` gets `+`, `-`, `*`, `&`, `|` and `^` in place of its `add`, `sub` and `mul` methods.
- **Indexing** is a place, as `xs[i]` is now (§3.1). Reading it gives `readonly Self.Item`, copied where an owned value is expected. Assigning to it, or lending it `mut`, needs `IndexMut`. While it lives, the whole container is borrowed. Arrays, slices, `Vec`s and tuples keep their built-in indexing, with constant tuple indexes and bounds checks. Slicing (`xs[a..b]`) stays built in too, because a range is not a value a user's `Index` could take (open question 9).
- **What does not change.** `==`, `!=`, `<`, `<=`, `>` and `>=` stay `Eq` and `Ord` (§3.5). `&&`, `||` and `!` on `bool` keep their short-circuit evaluation and cannot be overloaded. Assignment, calls, field access and `as` cannot be overloaded either.
- **Finding 1 becomes an error at the operator:** `` `V` does not implement `Add`; implement it from `std/ops`: `impl Add for V { … }` ``.

## 7. `Default`

```ts
// The prelude, sketch. The value a type has when nothing is said: zero, false, empty, #None.
export interface Default { function default(): Self; }
```

This is the codec design's interface (its section 6, item 7). The codec reads it for `@wire(skip)`, `@wire(default)` and `@wire(omitDefault)`. It is derived like `Eq`:

| Type | `default()` |
| :--- | :--- |
| Integers, floats | `0`, `0.0` |
| `bool`, `void` | `false`, `void` |
| `str`, `readonly T[]` | `""`, the empty slice (static, so nothing is allocated) |
| `Option<T>` | `#None`. `Option` has its own impl, as it has for JSON (§7.3). |
| Records, tuples, arrays | Each part's default, when every part has one |
| A struct that asks (`impl Default for Config;`) | Each field's default; a hand-written impl when one field should be `8080` |
| `String`, `Vec<T>`, `HashMap<K, V>`, `HashSet<T>` | Empty, allocating nothing (`new()`) |
| `Box<T>` | `Box.new(T.default())`, which allocates, as `Box.new` does |
| Tag unions, enums, `mut` borrows | None (open question 6) |

The attributes design's rule that an unwritten argument "takes an empty value" (its section 5) is then this interface's derivation, applied to the attribute's struct.

**A record literal may begin with a spread.** A `{ ...base, port: 8080 }` builds a value of `base`'s type. Each field the literal does not write is moved out of `base`, and each field it writes takes the place of `base`'s, which is dropped. TypeScript programmers already write this, and it is what makes `Default` pleasant to use:

```ts
const cfg: Config = { ...Config.default(), port: 8080, host: "0.0.0.0".toString() };
```

The rules: the spread comes first, and there is one of them. `{ port: 1, ...d }` is an error that says which way round it goes. TypeScript lets the later entry win, so that literal would be a quiet trap. A spread is allowed only where a literal of the struct is allowed, so a struct with private fields is spread only in its own module (§3.3). A value whose type implements `Drop` cannot be spread, because no field may be moved out of it (§4.1). A spread of a structural record gives the same record type, and every field written must already be one of its fields (open question 7).

**`take(place)`** moves a value out of a `mut` borrow and leaves its default behind: `take<T extends Default>(place: mut T): T`, which is `replace(place, T.default())`. `Option.take()` is the case of it for `Option`. A compiler's passes, which move a `Vec` out of `mut self.pending` and start a new one, use it constantly. `o.unwrapOrDefault()` joins `unwrapOr`.

## 8. Collecting and extending

```ts
// The prelude, sketch. A collection made from a generator's items.
export interface FromIterable<T, row E = []> { function fromIter(items: Gen<T, E>): Self uses ...E; }
// A collection that takes a generator's items in.
export interface Extend<T, row E = []> { function extend(self: mut Self, items: Gen<T, E>): void uses ...E; }

impl<T, row E> Gen<T, E> {
  export function collect<C extends FromIterable<T, E> = Vec<T>>(self: Self): C uses ...E { C.fromIter(self) }
}
```

The row sits on the interface, as on `Iterable`, so an impl covers every row: `impl<T extends Hash & Eq, row E> FromIterable<T, E> for HashSet<T>`. The interfaces take a `Gen` and not any `Iterable`. Iterating a `Vec` gives `readonly T`, which a container of owned values cannot keep, so one signature over `Gen` is clearer. `xs.iter()`, `xs.drain()` and `xs.iter().cloned()` say which items are meant.

| Type | `FromIterable` and `Extend` of |
| :--- | :--- |
| `Vec<T>` | `T` |
| `HashSet<T>` | `T` |
| `HashMap<K, V>` | `[K, V]`; a later equal key replaces an earlier one, as `insert` does |
| `String` | `str` and `String`, written one after another |

```ts
const byId: HashMap<u64, User> = users.drain().map((u) => [u.id, u]).collect();
seen.extend(batch.drain());
const text: String = parts.iter().map((p) => p.asStr()).collect();
```

**Failures pass through.** A closure in the chain that throws adds `Fail` to the generator's row `E`, and `collect` performs `E`. A failing item stops the collection, and the caller's `try` sees the failure. Rust needs `FromIterator` for `Result` and `Option`, so that `collect::<Result<Vec<_>, _>>()` can stop at the first error. That falls out of effects here, as error conversion does (§12.2).

**`Vec.extend` is renamed.** Today `Vec.extend(items)` copies a slice of `Copy` elements (std.md §1.5). It becomes `extendFromSlice`, Rust's name, so that `extend` is the interface's. The repository calls `extend` in 12 places, in `std/io`, `std/http`, `std/json`, `web/http`, `selfhost/rt` and two tests.

## 9. `Display` and `Show`

**The split already exists.** A template's `${e}` writes a string or a number as it is, and anything else with `Show`, which quotes strings (`#Some("a")`). `join(sep)` does the same ("each element shown, strings as they are", std.md §1.5). So Flyscript already has Rust's two forms, `Display` for text meant for people and `Debug` for values meant for programmers. It just has them only for built-in types, and a program cannot give one of its own types the first form.

**Where that hurts:**

- **A type that holds text.** `${name}` for `struct Name { s: String }` writes `Name { s: "ada" }`. If `Name` implements `Show` by hand to write `ada`, it breaks `Show`'s promise. A `Vec<Name>` then prints as `[ada, bob]`, which no longer reads as Flyscript and is ambiguous when a name contains `, `.
- **Units and money.** `Money` wants `$12.50` in a message and `Money { cents: 1250 }` in a test failure.
- **The time design** (`2026-10-25-time-design.md`, its item 5) has `Show` print RFC 3339 text for a `Timestamp`. That is the right text for a person, and it bends `Show`'s contract to get there.
- **A failure `main` does not catch** ends the program by showing what was thrown (§8.1). That is for a programmer today, and a command-line tool's user sees it.

**The proposal:**

```ts
// The prelude, sketch. The value as text for a person: what a template writes.
export interface Display { function display(self: readonly Self, out: mut String): void; }
```

- **Never derived.** There is no general answer to how a person would read a record, so a type that has `Display` wrote it.
- **The primitives, `str` and `String` have it**, writing themselves as they are. That is what templates do with them now.
- **`${e}` writes `e` with `Display` if its type has it, and with `Show` otherwise.** `join` does the same, and so does `main` with an uncaught failure. Everything that prints today prints the same, because no type has `Display` yet except those that already print this way.
- **`Show` keeps its contract**: the value as Flyscript would write it. It stays what `assertEq`, a failing test and a `Vec`'s own `Show` use. The time design would give `Timestamp` a `Display` and leave its `Show` to that design.

Rust makes `{}` an error for a type without `Display`. Here that would break every template that interpolates a record, and falling back to `Show` is what templates already do. A lint for interpolating a nominal type that has no `Display` is open question 8.

So the split is worth having, in a small form. It costs one interface that is never derived and one rule in templates, and it gives types that hold text, units, times and errors a way to read well without breaking `Show`.

## 10. Rust's core traits, and Flyscript's answer to each

| Rust | Flyscript after this design |
| :--- | :--- |
| `Copy`, `Clone` | `Copy` (structural), `Clone` (derived) |
| `Send`, `Sync` | `Send`. `Sync` is not needed (§4.4). |
| `Drop` | `Drop` |
| `PartialEq`/`Eq`, `PartialOrd`/`Ord`, `Hash` | `Eq`, `Ord`, `Hash`: derived and total, with no partial forms (§3.5) |
| `Debug`, `Display` | `Show` (derived), `Display` (section 9) |
| `Default` | `Default` (section 7) |
| `From`/`Into`, `TryFrom`/`TryInto` | The same names (section 2) |
| `FromStr` | `TryFrom<str>` (section 2) |
| `AsRef`/`AsMut`, `Borrow`/`BorrowMut`, `Deref`/`DerefMut` | `Lends`/`LendsMut`, one step, with the law of section 5 |
| `ToOwned` | `Clone` and `From`: `String.from(s)`, `s.toString()` |
| `Iterator`, `IntoIterator` | `Gen` and `Iterable`, built on `Yield` (§5.5) |
| `FromIterator`, `Extend` | `FromIterable`, `Extend` (section 8) |
| `Add` … `ShrAssign`, `Neg`, `Not`, `Index`/`IndexMut` | `std/ops` (section 6), with no `Not` (open question 11) |
| `Fn`, `FnMut`, `FnOnce` | Closure modes in the type: `(A) => B`, `mut (A) => B`, `once (A) => B` (§4.3) |
| `Error`, `?` with `From` | Tag unions in `Fail` rows (§5.4); nothing to implement |
| `Future` | None: I/O is an effect (§5.1) |
| `Any`, `Sized`, `Unpin` | None |

## 11. What was weighed

- **Implicit conversions** at calls, the way Scala's implicits or C++'s converting constructors work. Rejected: lending is the only implicit conversion, and that is what keeps "no hidden allocation" true at a glance.
- **`From` in `throw`**, as Rust's `?` uses it. Rejected by §12.2: error unions do the job with no code. A library that wraps failures says so with `Fail.map`.
- **Three lending interfaces**, Rust's `AsRef`, `Borrow` and `Deref`. One interface with the agreement law is a smaller language. What is lost is a type that lends without agreeing with `Eq`, which should be a method anyway.
- **Operands by value**, as in Rust. Moving `a` into `a + b` would surprise every TypeScript programmer and would make `+` the only operator that consumes. `readonly` operands with `AddAssign` for in-place work keep both the intuition and the speed.
- **`Output` as an associated type**, as in Rust. Then `T extends Add` says nothing about the result, and generic code needs `Add<Output = T>`, a constraint Flyscript does not have. A defaulted parameter that is determined by the others gives the same coherence without it.
- **One `Num` interface** for all of arithmetic. An impl must have exactly the interface's methods (§3.4), so a `Vec2` would have to define `%`. One interface per operator is how a type takes only what makes sense for it.
- **`+` on strings.** Templates already build strings, and their allocation is visible where they are written. `s + t` would allocate a new `String` with `readonly` operands, and `s += t` is `s.push(t)`. Not proposed.
- **A separate `Parse` interface** for text, Rust's `FromStr`. `TryFrom<str>` says the same thing with nothing new to learn.
- **Generic methods on these interfaces** (`fromIter<I extends Iterable<T, E>>`). Rows on the interface follow `Iterable`'s pattern, and the codec design reports that nothing in the standard library yet uses a type parameter on an interface method.
- **`Display` derived for structs**, as fields joined by spaces. There is no form a person would want for every struct, and a derived one would be used where a written one was needed.

## 12. Where it would be built

To give the reviewer a sense of size, not as a plan to follow. Each item applies to both compilers, `selfhost/` and `src/check/`.

- **Bugs first.** Finding 1: arithmetic operands must be numbers, or must implement the operator's interface. Finding 8: a primitive can be named as a type in a call.
- **Interface resolution** (`traits.fly`, `impls.fly`): choosing among one type's impls by their arguments (finding 3), blanket impls ranked after specific ones, bounds met through blanket impls (finding 5), the widened orphan rule, and the overlap check (finding 4).
- **Inference** (`check.fly`): type arguments taken from what is expected, and defaults used when nothing is (finding 6). Also `Self` in an interface's type-parameter defaults (finding 7).
- **The prelude and `std/ops`**: the interfaces, the conversions table, `Default`'s derivation and impls, `FromIterable` and `Extend` impls, `collect`, `take`, `Display` for the primitives and strings, and `extendFromSlice` with its 12 callers.
- **Lending** (`lends` in `check.fly`, and `own.fly`): `Lends` impls consulted after the prelude's pointers, one step, method lookup through the lent type, and `LentBy` solved from `Lends`.
- **Operators** (`check.fly`'s binary-operator case, `lower.fly`): operator calls go into `typed.ops` as `==` and `<` do today, so lowering reuses that path. Compound assignment evaluates its place once.
- **Record spread** (`parse.fly`, `check.fly`, `own.fly`): a leading `...e` entry, and the moves out of `e`.
- **Templates and `join`**: `Display` before `Show`, where `pendingOps` now records `Show`.
- **Docs**: spec §3.4 (the orphan rule, blanket impls, choosing impls), §3.5 (`Display`, `Default`), §3.6 (the new rule), §4.1 (lending as an interface), §2.3 (spread), a new section on operators, and std.md §1.

The order would be: the bugs and interface resolution; conversions and the inference rule; `Default`, spread and collecting; lending; and last, operators and `Display`. That is two roadmap steps, split after collecting. The codec design's need for `Default` is met by the first.

## Open questions

1. **Lending depth.** One step through a program's impl, or as many as Rust's auto-deref takes? One keeps the type that supplied a method one look away. More would let a `Path` that lends `PathBuf`-like views chain.
2. **Methods through a program's lending.** Section 5 lets `Name` reach `str`'s methods, which is `Deref` and not only `AsRef`. Should a program's `Lends` stand in only for borrows and comparisons, and leave methods to the prelude's types?
3. **Should `HashMap` have `Index`**, so that `m[k]` panics when `k` is missing, as `xs[i]` does out of bounds? Rust gives it `Index` and not `IndexMut`.
4. **Type parameters covered by a foreign type** in the orphan rule: `impl<T> From<Wrapper<T>> for Vec<T>`, which Rust allows and section 4 does not.
5. **`Box.into()`** gives a box's contents. With `Into` in the prelude, the name now means two things: the inherent method, which wins, and the conversion. Rename it `unbox()`?
6. **`Default` for enums**, through an attribute on one tag (`@default #Empty`, under the attributes design). The codec's `@wire(default)` on a tag means something else, so the name would need care.
7. **A spread that adds fields** to a structural record, `{ ...r, extra: 1 }`, which is a row extension (§3.2) and what TypeScript allows. Section 7 allows only the record's own fields.
8. **A lint for `Show` in templates**: interpolating a nominal type that has no `Display` is often a mistake in output meant for people. A warning, with `${x:?}`-style syntax to say `Show` on purpose?
9. **Ranges as values**, so that a type of the program's own can implement `Index<Range<usize>>` and be sliced.
10. **`toString()` for every `Display` type**, as TypeScript has it. A template does the same in a way that can be seen, so it is not proposed.
11. **Bitwise not.** Flyscript's `!` is for `bool`, and the integers have no unary bitwise operator for a `Not` interface to stand for.
12. **`as` for numbers**, now that `From` and `TryFrom` cover the lossless and checked cases. Should `as` become only a truncating cast, named for what it does, or stay as TypeScript programmers read it?
