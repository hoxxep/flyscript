# Review: holistic-review-of-0-24

- spec: 4e41df0d997f
- request: 77f3406f1d8c3780
- tokens: prompt 32323, cached 0, answer 8952

## Question

Spec 0.24 (included) adopts your last two reviews: derived `Eq/Hash/Show/Clone/Ord` in the prelude with the operators through them; closure modes enforced (this closed a real data race through `par`); total floats; owners compare as what they lend; temporaries; indexing and `iterMut`; template structs replacing type functions and `struct { … }` expressions; associated types in impls; your `ParSplit` with a `Slice` view; and `Soa<T>`, its views, `par` and `parReduce` written in Flyscript (`std/layout`, `std/par`). The prototype runs all of it — A.4 unchanged — with no layout or parallel loop known to the compiler.

Please do a holistic review of 0.24:

1. **Soundness.** Especially the newest pieces: `ParSplit` as now specified and implemented in library code (`split` consuming a `Slice`; `viewAt` on a `Slice` by value; `par` calling `f` through `readonly (v, i) => void`); template structs and their instances' identity; associated types resolved through impls (including through template impls); the recursion rule (assumed pure until the body says otherwise); calling a function through a borrow.
2. **Coherence.** Is anything now redundant or inconsistent after these changes — rules that say the same thing twice, sections that contradict, examples that no longer fit?
3. **Rank the three most valuable remaining changes** to the design, with the spec text you would write. Be bold if something structural should change; be concrete.

## Answer

### Verdicts

- **Calling a function value through a borrow (`§4.3`)**: **Disagree as written.** `§4.3` allows calling *any* function value through a borrow without restricting the borrow mode to match the closure's call mode (`(A) => B` vs `mut (A) => B` vs `once (A) => B`), which allows calling a `mut` or `once` closure through a `readonly` borrow — causing both use-after-move and data races.
- **`ParSplit` and library `Soa<T>` (`§6.5`, `§7.4`)**: **Agree with changes.** `split` consuming `Self.Slice` is the right core idea, but two holes exist in `§6.5`: (1) `Self.Slice` is not constrained to be non-`Copy`, so any `Copy` slice type (`readonly T[]`, `usize`) can be duplicated before calling `split` or `viewAt(s, i)` (which takes `s: Self.Slice` by value!); and (2) `par` and `parReduce` lack `Send` bounds on `C.Slice`, `C.View`, and `C.ReadView` (or `C extends Send`) for parallel execution across worker threads.
- **Recursion effect inference rule (`§3.6`)**: **Agree with changes.** Assuming an unannotated recursive function is pure while checking its body is clean and sound *provided* its effects are checked against `[]` (empty row) at the end of its body; however, for higher-order recursive helpers (like `par`'s divide-and-conquer helper), how it interacts with polymorphic or pure callbacks needs one clarifying sentence.
- **Template structs and associated types in impls (`§3.4`, `§7.1`, `§7.4`)**: **Agree with changes.** Eliminating type functions and `struct { ... }` expressions in favour of template structs was a major simplification. One soundness gap remains: `§4.2` says *"A nominal type's type parameters range over class-1 types unless the type is a `view`"*, which template parameters `<comptime T: Type>` bypass because `T` is not checked as a parametric type parameter, and `struct Ring<T, comptime N: usize>` has no `==` rule for `comptime` value arguments in type identity (`Ring<u8, 1024>` vs `Ring<u8, 512 + 512>`).
- **Coherence of 0.24 (`Question 2`)**: **Agree with minor cleanups.** Two contradictions / leftovers remain in the text: `§2.3` (`IfConst` restricts `if (const ...)` to `const` only and omits `let`, unlike `For`), and `§7.4`'s `Soa<T>` has no `len` field when `T` is an empty struct `{}` and its `ParSplit` snippet omits `view struct` on `SoaSlice` / `SoaView` / `SoaRead`.

---

### Problems

#### 1. Calling a `mut` or `once` function value through a `readonly` borrow is unsound (`§4.3`)

Look at `§4.3`:
> *"A function value is called through a borrow of it as well as directly, so a helper that passes its callback on lends it: `f: readonly (x: T) => void` may be given to two calls."*

Notice what this sentence does **not** say: it does not restrict which borrow mode (`readonly` vs `mut`) can call which function mode (`(A) => B` vs `mut (A) => B` vs `once (A) => B`)!
Look at what happens when a `once` or `mut` closure is borrowed as `readonly` (or `mut`) and called:

```ts
function callTwice(f: readonly (once () => String)): [String, String] {
  // If a function value can be called through a borrow of it,
  // calling `f()` through `readonly (once () => String)` does not move `f`!
  [f(), f()]
}

export function useAfterFree(): [String, String] {
  let s = String.fromStr("owned");
  const consume: once () => String = () => s; // owns `s`, moves it out when called
  callTwice(consume) // `s` is moved out twice! Double-free on drop!
}
```
And the exact same bug happens with `mut` closures:
```ts
function callMutThroughReadonly(f: readonly (mut () => i32)): i32 {
  f() + f()
}

export function raceOnMutClosure(): void {
  let count = 0;
  let inc: mut () => void = () => { count += 1; };
  // Lending `inc` as `readonly (mut () => void)` lets two tasks or aliases call it concurrently!
}
```
Even for `mut (A) => B` borrowed as `mut (once (A) => B)`, calling a `once` closure through a `mut` borrow would leave the caller holding a live `once` closure whose captures have already been moved out and dropped!

**Fix:**
State the exact correspondence between closure modes and borrow modes in `§4.3`:
- A shared function `(A) => B` may be called through `readonly` (or `mut`, or by value).
- A `mut (A) => B` function may be called through `mut` (or by value), never through `readonly`.
- A `once (A) => B` function may be called **only by value (consuming it)**, never through a borrow.

Replace the sentence in `§4.3` with:
> *"A `(A) => B` function value may be called through a `readonly` or `mut` borrow, a `mut (A) => B` function through a `mut` borrow, and a `once (A) => B` function only by move."*

---

#### 2. `ParSplit.viewAt` takes `s: Self.Slice` by value, and `Self.Slice` is not prevented from being `Copy` (`§6.5`, `§7.4`)

Look closely at `ParSplit` in `§6.5`:
```ts
interface ParSplit {
  type Slice;       // a splittable mutable view of a run of elements
  type View;        // a mutable view of one element
  type ReadView;    // a read-only view of one element
  function len(self: readonly Self): usize;
  function slice(self: mut Self): Self.Slice from self;
  function split(s: Self.Slice, at: usize): [Self.Slice, Self.Slice] from s;
  function viewAt(s: Self.Slice, i: usize): Self.View from s;
  function readAt(self: readonly Self, i: usize): Self.ReadView from self;
}
```
Look at two things here:

**First (Soundness): What if a user implements `ParSplit` where `type Slice` is `Copy`?**
Remember `§4.4`:
> *"`Copy`: bitwise copyable; no field owns a resource and the type has no `Drop`."*
And `§4.1`:
> *"`readonly T` is `Copy`; `mut T` is not."*
So a `SoaSlice<T>` containing `mut F[]` fields is not `Copy`. **What if `T` is an empty struct `struct Empty {}`?**
Then `SoaSlice<Empty>` has **zero fields**, so by `§4.4` it is `Copy`!
Even worse, what if a user implements `ParSplit` for a custom container (say, an arena or matrix wrapper) where `type Slice = { ptr: mut Matrix; start: usize; len: usize }` is non-`Copy`, vs a wrapper where `Slice` accidentally holds an index or `Ref` (`Copy`), or what if `viewAt(s: Self.Slice, i: usize)` is called in a loop inside `par`?

Wait: **how DOES `par` call `viewAt(s: Self.Slice, i: usize)` when `s: Self.Slice` is passed by value (move)?!**
Look at the signature of `viewAt`:
```ts
function viewAt(s: Self.Slice, i: usize): Self.View from s;
```
`s` is passed **by move** (`s: Self.Slice`, not `s: mut Self.Slice`)!
If `s` is moved into `C.viewAt(s, 0)`, then `s` is **consumed** on the very first element!
How can `par` iterate over a leaf slice of length `> 1`, or even check the length of `s` if `ParSplit` has no `sliceLen(s: readonly Self.Slice)` method?
Wait: in `par`, if it splits all the way down to `len == 1` at every leaf (`split(s, mid)` until `hi - lo == 1`) and then calls `C.viewAt(s, 0)` consuming `s`, Look what happens to `from s` on `viewAt(s: Self.Slice, i: usize): Self.View from s`!
Read `§4.2`:
> *"A call's result can hold the borrows of its sources: the parameters named in its `from` clause... Inside the body, everything the returned value borrows must come from a source, never from a local."*
Wait: in `impl<T> ParSplit for Vec<T>` (or `T[]`), `Self.Slice` is `mut T[]` and `Self.View` is `mut T`:
```ts
function viewAt(s: mut T[], i: usize): mut T from s {
  mut s[i]
}
```
When `par` calls `f(C.viewAt(s, 0), base)`, `s` is a moved value, and `C.viewAt(s, 0)` returns a `Self.View` borrowing from `s` (which itself holds the borrow from `c.slice()`).
Now ask: what if someone implements `ParSplit` and in `split(s: Self.Slice, at: usize)` they **don't** split into disjoint halves, or what if `viewAt(s, i)` is called twice when `Self.Slice` is `Copy`?
Actually, in safe Flyscript, can `split(s: mut T[], at: usize): [mut T[], mut T[]] from s` be written **without** a primitive `slice.splitAt(at)`?
No! Because `s[0..at]` and `s[at..len]` would both borrow `s` mutably at the same time, so `mut T[].splitAt(at)` is a built-in/primitive method on `mut T[]`, and `SoaSlice<T>.split` calls `.splitAt(at)` on each field (`§7.4`)!
Why was `SoaSlice<T>.split` forced to move `s`?
Because in `SoaSlice<T>`:
```ts
function split(s: SoaSlice<T>, at: usize): [SoaSlice<T>, SoaSlice<T>] from s
```
when you destructure or move each field `s.[f.name].splitAt(at)`, moving each field out of `s: SoaSlice<T>` moves `s` field-by-field (`§4.1`: *"Moving a field out of a value moves only that field"*)!
That's why `s` is taken by move (`s: Self.Slice`)!

**Second (Soundness on multi-threaded workers): Missing `Send` requirement in `§6.5`!**
Look at `par` and `parReduce` in `§6.5`:
```ts
function par<C extends ParSplit>(c: mut C, f: (v: C.View, i: usize) => void): void;
function parReduce<C extends ParSplit, A extends Send>(
  c: readonly C, zero: A, one: (v: C.ReadView, i: usize) => A, both: (a: A, b: A) => A,
): A;
```
What if `C` is a container of **non-`Send`** elements, such as `Vec<u8*>` (raw pointers, `§8.2`: *"T* is a raw pointer: Copy, not Send"*) or `Vec<Rc>`?
```ts
export function sendRawPointerAcrossThreads(ptrs: mut Vec<u8*>): void {
  // `Vec<u8*>` implements `ParSplit`!
  // `par` has NO `Send` bound on `C`!
  // On native targets (§8.3), `par` sends slices of `u8*` to parallel worker threads!
  par(mut ptrs, (p, i) => {
    // Runs on another worker thread with a non-Send `u8*`!
  });
}
```
Look at `§4.4`:
> *"`Send`: may move to another task, and `readonly T` may be shared with other tasks."*
`parReduce` remembered `A extends Send` for the accumulator, but neither `par` nor `parReduce` required `C extends Send`!
Wait: if `C` is `mut T[]` (a slice, which is class 2), is `mut T[]` `Send`?
By `§4.4`:
> *"`T` is `Send` when it is class 1 and owns no raw pointer or runtime handle"*
Because `mut T[]` is class 2, `mut T[]` is **not** `Send`, whereas `Vec<T>` and `Soa<T>` (when `T extends Send`) **are** class 1 and `Send`!
What if someone passes a `mut T[]` slice to `par`? If `C` can be `mut T[]` (or `Vec<T>`), when is a slice safe to split across worker threads? When the underlying elements are `Send` — i.e., `ParSplit` itself is a parallel-splitting interface, so every `impl ParSplit for T` must require its element type to be `Send` (`impl<T extends Send> ParSplit for Vec<T>`, `impl<comptime T: Type> ParSplit for Soa<T>` where `T extends Send`)!

**Fix:**
In `§6.5`, make `ParSplit` extend `Send` (or state that `ParSplit` implementations require `Send` elements):
1. Either `C extends ParSplit & Send` (if `par` is called on containers `Vec<T>`, `Soa<T>`, `T[N]`), or if `par` also accepts `mut T[]` slices directly, state in `§6.5`:
   > *"Impls of `ParSplit` for slices, arrays, `Vec<T>` and `Soa<T>` require `T extends Send`."*
2. And in `§7.4`, add `comptime assert(fieldsOf(T).len() > 0, "Soa requires at least one field");` (or a `len: usize` field on `Soa<T>`) so `Soa<Empty>.len()` works! Look at `§7.4`:
   ```ts
   export struct Soa<comptime T: Type> {
     comptime for (const f of fieldsOf(T)) {
       comptime if (nested(f.type)) { [f.name]: Soa<f.type>; } else { [f.name]: Vec<f.type>; }
     }
   }
   ```
   Wait: how does `Soa<T>.len()` work in `std/layout`? It probably reads the `.len()` of the first field `fieldsOf(T)[0]`! If `T` is a struct with 0 fields (or a nested struct with 0 fields), `fieldsOf(T)[0]` panics at comptime with an out-of-bounds index unless `Soa<T>` asserts `fieldsOf(T).len() > 0`!

---

#### 3. Template structs bypass the class-1 container rule (`§3.3`, `§4.2`, `§7.1`, `§7.4`)

Look at `§3.3`:
> *"A struct or enum that holds a borrow (§4.2) must say so: `view struct Scanner { src: readonly u8[]; pos: usize; }`. ... Without `view`, a borrow field is an error that suggests the owned alternative"*

And `§4.2`:
> *"Containers hold first-class values. A nominal type's type parameters range over class-1 types unless the type is a `view`: `Vec<String>` and `HashMap<String, u64>` are fine, `Vec<str>` is an error that suggests `Vec<String>`."*

Now look at template structs in `§7.1` and `§7.4`:
```ts
struct Partial<comptime T: Type> {
  comptime for (const f of fieldsOf(T)) { [f.name]: Option<f.type>; }
}
```
And in `§7.4`:
> *"`Soa<T>` (`std/layout`) is a template struct that lays `T` out as planes — a `Vec` per scalar field, a nested `Soa` per struct field — with three template views: `SoaSlice<T>`, a `mut` slice of each plane; `SoaView<T>`, one element as a borrow of each field; and `SoaRead<T>`, its `readonly` counterpart"*

Now ask two questions:
1. Must `SoaSlice<T>`, `SoaView<T>`, and `SoaRead<T>` be declared `view struct`?
   Yes! Because their expanded fields are `mut F[]`, `mut F`, and `readonly F` (all class 2)! By `§3.3`, any struct whose fields hold a borrow must be declared `view struct`.
2. What if someone instantiates a **non-`view`** template struct `Partial<comptime T: Type>` with a type `T` that contains a borrow, e.g. `Partial<{ name: str }>` or `Partial<Scanner>`?
   ```ts
   struct Partial<comptime T: Type> {
     comptime for (const f of fieldsOf(T)) { [f.name]: Option<f.type>; }
   }

   export function sneakBorrowIntoNonViewStruct(s: str): Partial<{ name: str }> {
     // `Partial` is NOT declared `view struct`!
     // Its parameter is `comptime T: Type`, not a parametric `<T>`.
     // When expanded for `{ name: str }`, `Partial<{ name: str }>` has field `name: Option<str>` (class 2)!
     Partial { name: #Some(s) }
   }
   ```
   If the checker only checks the `view` rule on syntactic struct declarations *before* template expansion, or only checks class-1 on parametric `<T>`, then `Partial<{ name: str }>` is a non-`view` struct holding a class-2 field `Option<str>`!
   Conversely, if the checker checks the `view` rule on the **expanded fields of each template struct specialization**, then `Partial<{ name: str }>` is properly rejected because `Partial` is not a `view struct`, while `view struct SoaSlice<comptime T: Type>` is accepted!

**Fix:**
In `§7.1`, state explicitly:
> *"Each specialization of a template struct is checked as an ordinary struct declaration: unless the template is declared `view struct`, its expanded fields and type arguments must be class 1."*

---

#### 4. Associated types in impls can hide second-class types (borrows) behind parametric bounds (`§3.4`, `§4.2`, `§6.5`)

This is a subtle interaction between **associated types (`§3.4`)** and **second-class values (`§4.2`)**.
Read `§4.2`:
> *"Every type has a class, 1 or 2... Some types can hold a borrow without showing it: closures, continuations (`Cont`, §5.3), anything built from them (`Gen`), and type parameters. A value of such a type is class 2 when it actually holds a borrow... Arguments whose types can hide a borrow — closures, generators, type parameters — are always sources. A result whose type cannot hold a borrow at all (class 1, with no closure, continuation or type parameter once instantiated) holds nothing."*

Now look at `ParSplit` (`§6.5`):
```ts
interface ParSplit {
  type Slice;
  type View;
  type ReadView;
  function slice(self: mut Self): Self.Slice from self;
  function split(s: Self.Slice, at: usize): [Self.Slice, Self.Slice] from s;
  function viewAt(s: Self.Slice, i: usize): Self.View from s;
  function readAt(self: readonly Self, i: usize): Self.ReadView from self;
}
```
Inside the body of the generic function `par`:
```ts
export function par<C extends ParSplit>(c: mut C, f: (v: C.View, i: usize) => void): void {
  const s: C.Slice = c.slice();
  ...
}
```
Wait: inside `par<C extends ParSplit>`, what is the **class** of the associated type projection `C.Slice` or `C.View`?!
`C.Slice` is not a type parameter `T`; it is an **associated type projection** `C.Slice` on a type parameter `C`!
When `C` is instantiated with `Vec<f32>`, `C` itself is **class 1** (`Vec<f32>` holds no borrows)!
**HOLD ON!**
Look at what happens when `par(mut v, f)` is called with `v: Vec<f32>`:
1. `C` is `Vec<f32>`, which is **class 1**!
2. Inside `par`, `c.slice()` returns `C.Slice`.
3. For `C = Vec<f32>`, `C.Slice` is `mut f32[]`, which is **class 2**!
4. Now look at `§4.2`:
   - If a generic function `<C extends ParSplit>` is type-checked parametrically (or if a function returns `C.Slice` or stores `C.Slice` in a `Vec<C.Slice>`), how does the borrow checker know inside `<C extends ParSplit>` whether `C.Slice` can hold a borrow (`class 2`) when `C` itself is `class 1`?!
   Look at this program:
   ```ts
   function leakSlice<C extends ParSplit>(c: mut C): Vec<C.Slice> {
     let v = Vec.new<C.Slice>();
     // Is `Vec<C.Slice>` allowed inside `leakSlice`?
     // If `C.Slice` is treated as class 1 until instantiated, or if `c.slice()`'s return type `C.Slice`
     // is checked for whether it can hold a borrow from `c`:
     v.push(c.slice());
     v // Returns a `Vec<mut f32[]>` dangling after `c`'s borrow ends!
   }
   ```
   Look at both lines of `leakSlice`:
   - Line 1: `Vec<C.Slice>` instantiates `Vec<T>` (a non-`view` nominal struct whose type parameter `T` must be class 1) with `C.Slice`.
   - Line 2: `c.slice()` has signature `function slice(self: mut Self): Self.Slice from self`. In `§4.2`, *"A result whose type cannot hold a borrow at all (class 1, with no closure, continuation or type parameter once instantiated) holds nothing."*
   When `C` is instantiated as `Vec<f32>`, if the checker only checks whether `C` is class 1 instead of expanding `C.Slice` to `mut f32[]` (or treating unexpanded associated types `C.Assoc` just like type parameters that can hide a borrow), then `c.slice()` would be thought to hold no borrow!

**Fix:**
In `§4.2`, everywhere "type parameter" is mentioned as capable of hiding a borrow (and not being class 1 unless bounded by `Send`), include **associated types** (`T.Assoc`):
1. Change *"closures, continuations (`Cont`, §5.3), anything built from them (`Gen`), and type parameters"* to:
   > *"closures, continuations (`Cont`, §5.3), anything built from them (`Gen`), type parameters, and associated types."*
2. And when a call is instantiated (`C = Vec<f32>`), associated types in its signature (`C.Slice`) are resolved through `C`'s impl (`mut f32[]`) before checking class and borrow propagation.

---

### Coherence Review (Question 2)

 The specification is remarkably tight — 0.24 cut type functions and `struct { ... }` expressions cleanly without leaving dead references. Four small coherence issues should be cleaned up:

1. **`IfConst` in `§2.3` vs `For` in `§2.3`:**
   In `§2.3`:
   ```ebnf
   IfConst = "if" "(" "const" Pattern "=" Expr ")" Block [ "else" ( If | IfConst | Block ) ] ;
   For     = "for" "(" ( "const" | "let" ) Pattern "of" Expr ")" Block ;
   ```
   Why does `IfConst` only allow `"const"` and not `( "const" | "let" )`?
   If a user writes `if (let #Some(x) = iter.next()) { x += 1; }`, forbidding `let` in `if (...)` while allowing `for (let x of ...)` and `let #Some(x) = ...` is an arbitrary inconsistency. Change `IfConst` to allow `( "const" | "let" )`.
2. **`§7.4` `Soa<T>` omits `view` on its three view structs and `len` on empty structs:**
   In `§7.4`, the prose says *"with three template views: `SoaSlice<T>` ... `SoaView<T>` ... `SoaRead<T>`"*. Make sure the spec text (and `std/layout`) declares them as `export view struct SoaSlice<comptime T: Type>`, `export view struct SoaView<comptime T: Type>`, and `export view struct SoaRead<comptime T: Type>` so `§3.3` and `§7.4` agree.
3. **`§3.5` owner-to-lent comparison vs `HashMap` lookup in `§4.1`:**
   - `§3.5` says: *"an owner compared with the type it lends is compared at that type (`name == "ada"` for a `String`, `b.name == name` for a `Ref<R, str>`)"*.
   - `§4.1` says: *"Lookups in `HashMap<K, V>` accept any `Q` that `K` lends, so a `HashMap<String, V>` is searched with a `str` without allocating."*
   These two rules fit together nicely, and explain why `b.name == name` in `A.5` (`Ref<str> == str`) and `counts.getMut(w)` in `A.2` (`HashMap<String, u64>` with `w: str`) work without ceremony.
4. **Template struct identity with `comptime` value parameters (`§7.1`):**
   `§7.1` says: *"two uses with the same arguments are the same type: `type ByteRing = Ring<u8, 1024>;`"*.
   Just make sure the checker evaluates `comptime` value arguments in type position (`Ring<u8, 512 * 2>`) to their canonical constant value (`1024`) before comparing type identity and memoizing template specializations.

---

### Top Three Most Valuable Remaining Changes (Question 3)

Since Laws 1–5, `comptime`, derivations, and `Soa`/`par` are now all complete and running, the remaining opportunities are where small rules unlock disproportionate ergonomics or eliminate footguns. Here are the **top three**, ranked by value:

---

#### Rank 1: Expected-Type Propagation Through Wrapper Calls and Closures (`§3.6`, `A.9`)

**Why this is #1:**
Look at the **only remaining `Awkward:` note in the entire Appendix** (`A.9`):
> *"`Awkward:` `parse<Signup>` names its type because the closure passed to `Fail.capture` gets no expected type from the `match` around it."*

Why did `A.9` have to write `parse<Signup>(body)`?
Look at `A.9`:
```ts
match (Fail.capture(() => parse<Signup>(body))) {
  #Ok(s) => stringify(#Created { id: nextId, name: s.name }),
  ...
}
```
Actually, even if `Fail.capture` weren't inside `match`, what if someone wrote:
```ts
const r: Result<Signup, JsonError> = Fail.capture(() => parse(body));
```
Wait: why wouldn't `const r: Result<Signup, JsonError> = Fail.capture(() => parse(body))` infer `Signup` unless expected types flow **into lambda bodies**?
Read `§3.6`:
> *"Expected types flow into calls. A call checked against an expected type unifies the callee's instantiated return type with it before checking the arguments."*
Now trace `const r: Result<Signup, JsonError> = Fail.capture(() => parse(body))`:
1. `Fail.capture<T, E>(f: () => T uses Fail<E>): Result<T, E>` is called with expected type `Result<Signup, JsonError>`.
2. By `§3.6`, the return type `Result<T, E>` unifies with `Result<Signup, JsonError>` *before* checking the argument `() => parse(body)`, so `T = Signup` and the argument `() => parse(body)` is checked against expected type `() => Signup uses Fail<JsonError>`.
3. Now the lambda `() => parse(body)` is checked against expected type `() => Signup`. Does `§3.6` say that checking a lambda `(params) => body` against an expected function type `(P) => R` checks `body` against expected type `R` (and `if`/`match`/`block`/`try`/`region` expressions pass their expected type to their tail expressions)?
`§3.6` only states expected-type propagation for *calls*, not for **blocks, branches (`if`/`match`/`try`/`region`), and lambdas**!

And what about `A.9` itself, where `match (Fail.capture(() => parse(body)))` has no type annotation on the `match` scrutinee?
Look at `parse` in `std/json` (`§7.5`):
```ts
export function parse<T extends FromJson>(text: str): T uses Fail<JsonError>;
```
Because `Type` is a first-class comptime value that can be passed as an argument (`§7.1`: `comptime T: Type`), or if `parse` is called in `match`, why did `A.9` even use `Fail.capture(() => parse<Signup>(body))` instead of `try { ... } catch (e) { match (e) { ... } }` like `§10.2` does?!
Look at `A.9` written with `try / catch` (the idiomatic Flyscript error handler from `§5.4` and `§10.2`!):
```ts
export function respond(body: str, nextId: u64): String {
  try {
    const s: Signup = parse(body);
    stringify(#Created { id: nextId, name: s.name })
  } catch (e) {
    match (e) {
      #Missing(field) => stringify(#Rejected { reason: `missing ${field}` }),
      #Syntax(at)     => stringify(#Rejected { reason: `not JSON at byte ${at}` }),
      _               => stringify(#Rejected { reason: "not a signup" }),
    }
  }
}
```
Look at that:
1. With `try / catch`, `const s: Signup = parse(body)` needs **no turbofish `<Signup>`**, `Fail.capture` isn't needed at all, and **all nine Appendix programs have `"Awkward: none"`**!
2. And making sure `§3.6` explicitly propagates expected types through **blocks, `if`/`match`/`try`/`region`/`handle` arms, and lambda bodies** ensures that `const r: Result<Signup, _> = Fail.capture(() => parse(body))` also works without `<Signup>`.

**Concrete spec text to add to `§3.6`:**
> *"Expected types flow into blocks, branches (`if`, `match`, `try`, `region`, `handle`), lambda bodies, and calls: a call checked against an expected type unifies the callee's instantiated return type with it before checking the arguments."*

---

#### Rank 2: Lock Down Closure-Borrow and `ParSplit` Soundness Rules (`§4.2`, `§4.3`, `§6.5`, `§7.1`)

**Why this is #2:**
As shown in Problems 1–4 above, the 0.24 additions (`calling a function through a borrow`, `ParSplit`, `template structs`, and `associated types`) are the right features, but their boundary conditions in `§4.2`, `§4.3`, `§6.5`, and `§7.1` have four concrete soundness holes that a user program can trigger. Fixing all four requires no new concepts and only 4 sentences of spec text:

**Concrete spec text to write:**
- **In `§4.2` (Second-class values):**
  > *"Some types can hold a borrow without showing it: closures, continuations (`Cont`, §5.3), anything built from them (`Gen`), type parameters, and associated types."*
- **In `§4.3` (Closures):**
  > *"A `(A) => B` function value may be called through a `readonly` or `mut` borrow, a `mut (A) => B` function through a `mut` borrow, and a `once (A) => B` function only by move."*
- **In `§6.5` (Data parallelism):**
  > *"Impls of `ParSplit` for slices, arrays, `Vec<T>` and `Soa<T>` require `T extends Send`, and `Self.Slice` and `Self.View` may not be `Copy`."*
- **In `§7.1` (Two kinds of type parameter):**
  > *"Each specialization of a template struct is checked as an ordinary struct declaration: unless the template is declared `view struct`, its expanded fields and type arguments must be class 1."*

---

#### Rank 3: Exhaustive Pattern Matching over `enum` and Constant/Range Patterns (`§2.3`, `§3.2`, `§3.3`)

**Why this is #3:**
Look at `§3.2`:
> *"Exhaustiveness is checked once a function's types are final, over nested patterns — tags, tuples, records, structs and `bool` — and an incomplete `match` names a value it misses: `does not handle '#Err(#Unknown(_))'`."*
And now look at `A.1` (`Json` parser):
```ts
match (sc.src[sc.pos]) {
  b'n' => { sc.expect("null"); alloc(#Null) },
  b't' => { sc.expect("true"); alloc(#Bool(true)) },
  b'"' => alloc(#Str(copyUtf8(sc.quoted()))),
  b'[' => { ... },
  _ => throw #Unexpected(sc.pos),
}
```
Notice two things in `A.1` and `§3.2`:
1. `§3.2` lists *"tags, tuples, records, structs and `bool`"*, omitting **`enum`** (`§3.3`)! (Even if `enum` is represented internally as a closed tag union, stating `enums` in `§3.2` makes it clear that nominal `enum`s are checked for exhaustiveness just like structural tag unions.)
2. In `A.1` (`Json` parser) and `std/json.fly`, lexing digits `'0'..'9'` or `'a'..'z'` currently requires a helper function `isDigit(b)` with `if` chains because `match (b)` has no byte/integer range pattern `b'0'..b'9'` (even though `..` is already a token in slice expressions `xs[a..b]`!), and `§2.3` omits `Pattern`'s full production (`Pattern = … | "#" "[" Expr "]" [ … ] | "comptime" Expr ;`).
Writing out the full `Pattern` production in `§2.3` (including `let` in `IfConst`, or-patterns `P1 | P2` which `§5.4` already uses in `#NotANumber | #OutOfRange(_) =>`, struct/record patterns, tuple patterns, and literal patterns) makes the grammar in `§2.3` self-contained rather than elided with `…`.

**Concrete spec text for `§2.3` (`Pattern` and `IfConst`):**
```ebnf
IfConst = "if" "(" ( "const" | "let" ) Pattern "=" Expr ")" Block [ "else" ( If | IfConst | Block ) ] ;
Pattern = PatAtom { "|" PatAtom } ;
PatAtom = "_" | Literal | "comptime" Expr | Ident
        | ( "#" Ident | "#" "[" Expr "]" ) [ "(" [ Pattern { "," Pattern } ] ")" | PatRecord ]
        | [ Path ] PatRecord
        | "[" [ Pattern { "," Pattern } ] "]" ;
PatRecord = "{" [ PatField { "," PatField } ] "}" ;
PatField  = Ident [ ":" Pattern ] ;
```

---

### Smaller points

- **Recursive helpers with higher-order callbacks (`§3.6`):**
  In `§3.6`:
  > *"Recursion. A function that is called again while its effects are being inferred — itself, or through others — is assumed pure there; if its body then performs an effect, it must state its effects with `uses`."*
  This rule works cleanly for `par` and `parReduce` in `std/par` because `par`'s recursive helper is pure (`f` has no effects). What if someone writes a private recursive helper `walk(node, f)` that calls a callback `f` polymorphic in its effects? Because non-exported functions can still write an explicit `uses ...E` clause (`§2.3`), the error diagnostic when a recursive function performs an unannotated effect should simply say: `recursive function 'walk' performs effects; add a 'uses' clause`. That is simple, predictable, and avoids fixpoint effect inference.
