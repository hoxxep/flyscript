### Verdicts

- **(1) Match arm binds by the strongest use it makes of what it binds (`§4.1`):** **Agree with changes.** It is ergonomic and directly mirrors closure capture (`§4.3`), **except** for three sharp edges: (a) it lacks the `mut` case on an owned `let` place (which is the exact compiler-author gap you noted!), (b) guards (`Pattern if guard => body`) that fail after moving a binding or while holding a borrow need an explicit rule, and (c) multi-binding patterns (`#Pair(a, b)`) where one binding is moved and the other is only read interact subtly with partial moves and `Drop` (`§4.1`, `§5.6`).
- **(2) Match through a `mut` borrow lends `mut` only if an arm changes a part it binds (`§4.1`):** **Agree with changes.** Sound if and only if "changes a part it binds" is defined transitively over **reborrows that escape the binding into a local or call result** (not just direct assignment, `mut` argument, or `mut self` method call on the pattern variable itself).
- **(3) A call's result holds a borrow of an argument's place only if its declared result type can hold a borrow itself, not only through a type argument (`§4.1`, `§4.2`):** **Disagree as stated; Agree with a sharper rule.** The rule as phrased in `§4.1` is **unsound** for associated types (`Self.View`, `Self.Slice`), `<comptime T: Type>` templates, and functions taking both `self: mut Container<T>` and a callback `(mut T) => R` (or returning a type parameter `R` instantiated with a borrow).
- **(4) Loans taken through a local reference binding pass through the reference's own loans for return/yield checks (`§4.1`, `§4.2`, `§5.5`):** **Agree.** This is a direct consequence of transparent borrows (`§4.1`: *"There is no dereference operator, and no borrow of a borrow: lending a borrow lends what it refers to"*), provided reborrowing a local `mut T` binding still locks that local binding while the yielded/returned borrow is live.
- **(5) Lookup key literal unifies with the map's key type before literal defaulting (`§4.1`):** **Agree.** Clean, predictable, and removes a real paper cut.
- **(6) Next steps:** Ranked concrete plan below.

---

### Problems

#### 1. Decision (3) is unsound for associated types, `<comptime T: Type>` templates, and HOFs over `mut` containers (`§4.1`, `§4.2`, `§6.5`, `§7.1`)

In `§4.1`, the new rule states:
> *"a borrow taken for an argument is held by the call's result if the result can hold it (§4.2) — if its declared type can hold a borrow itself: a result that can hold one only through a type argument, as `take(self: mut Self): Option<T>` gives, holds what the arguments held but not a borrow of their places, which generic code cannot put into a `T`"*

Here are **three concrete Flyscript programs** where a function's declared return type is a type parameter, an associated type, or a template parameter, and the function **does** put a borrow of the argument's place into its result:

**Program 1A (Hiding a borrow of `self`'s place inside a type parameter `R` via a callback):**
```ts
struct Boxed<T> { val: T; }

impl<T> Boxed<T> {
  // Declared return type is `R` — a bare type parameter!
  // By the new rule in §4.1, `R` is "only a type argument", so the call's result
  // holds what the arguments (`self` and `f`) ALREADY held, and NOT a borrow of `self`'s place!
  function withMut<R>(self: mut Self, f: once (x: mut T) => R): R {
    f(mut self.val)
  }
}

export function main(): void {
  let b = Boxed { val: "hello".toString() };
  // Instantiate `R = mut String`. The closure captures nothing (holds no loans).
  // `b` is an owned Boxed<String> (holds no loans).
  // If `withMut`'s result does not hold the borrow of `b`'s place:
  let r: mut String = b.withMut((x) => x);
  // `b` is now considered unlocked while `r: mut String` is still live!
  drop(b);
  r.push(" world"); // USE-AFTER-FREE!
}
```
Why did that happen? Because `withMut` is parametric in `R`, yet it acquired a borrow of `self`'s place (`mut self.val`) and handed it to `f`, which returned it inside `R`! Saying *"generic code cannot put [a borrow of an argument's place] into a `T`"* is only true when the function has **no callback parameter** that receives a borrow of that argument's place and returns `T`!

**Program 1B (Associated types in `ParSplit` or custom interfaces, `§3.4`, `§6.5`):**
```ts
// From §6.5:
// interface ParSplit {
//   type Slice;
//   function slice(self: mut Self): Self.Slice from self;
// }
function getSlice<C extends ParSplit>(c: mut C): C.Slice {
  c.slice()
}
```
What is the declared return type of `c.slice()` or `getSlice`? It is `Self.Slice` / `C.Slice` — an associated type on a type parameter, which contains no syntactic `readonly` or `mut`! If "its declared type can hold a borrow itself" treats `Self.Slice` like a type parameter `T`, then `c.slice()` would not borrow `c`'s place! (`§4.2` notes that associated types "can hold a borrow without showing it", so `§4.1` and `§4.2` must not disagree here.)

**Program 1C (`<comptime T: Type>` templates, `§7.1`):**
```ts
function project<comptime T: Type, comptime Out: Type>(v: mut T): Out {
  // Out is specialized to `mut i32`, returning `mut v.x`!
  mut v.x
}
```
Here `Out` is a `<comptime Out: Type>` parameter, which *can* synthesize a borrow of `v`'s place because `comptime` code is checked after specialization (`§7.1`).

**Fix:**
State the exact parametricity condition in `§4.1` / `§4.2`:
A call's result does **not** acquire a fresh loan of an argument's *place* (`self` in `self.state.take()`, or `place` in `replace(mut place, v)`) when **all** of the following hold:
1. Every position in the declared return type that can hold a borrow is a **parametric type parameter `T`** (not `readonly`/`mut`/`str`/`[]`, not a `view`, not `Cont`/`Gen`, not a closure, not an associated type `C.Assoc`, and not a `<comptime T: Type>` parameter); **and**
2. No parameter of the function is a closure/function whose parameter types can hold a borrow and whose return type shares `T`.

Under that exact rule:
- `Option<T>.take(self: mut Self): Option<T>`, `Vec<T>.pop(self: mut Self): Option<T>`, `Vec<T>.remove(self: mut Self, i: usize): T`, and `replace<T>(place: mut T, v: T): T` all satisfy (1) and (2): their return types (`Option<T>`, `T`) can only hold a borrow through the parametric type variable `T`, and they take no callback. Therefore, their result inherits only the loans *already inside* `self` (and `v`), **not** the loan of `self`'s place!
- Meanwhile `Boxed<T>.withMut`, `ParSplit.slice`, and `<comptime>` templates still soundly lock `self`'s place.

---

#### 2. Decision (2) ("match through a `mut` borrow lends `mut` only if an arm changes a part it binds") can be bypassed by reborrowing or matching further (`§4.1`)

Look at the wording in `§4.1`:
> *"Reached through a `mut` borrow, it is lent `mut` if an arm changes a part it binds — assigns to it, lends it `mut`, or calls a method that takes it `mut` — and `readonly` otherwise"*

What if the arm does **not** directly assign to `x`, lend `mut x` in a call, or call a `mut` method on `x`, but instead:
1. Binds `x` (which through a `mut` borrow has type `mut Part`), and **assigns `x` to a local variable `const y = x;`** (or returns `x` from the `match` expression!), and then mutates `y`?
2. Or matches on `x` again (`match (x) { #Sub(z) => { z += 1; } }`)?

Here is the program:
```ts
type Wrapper = #Wrap(i32);
struct State { w: Wrapper; other: i32; }

impl State {
  function readOther(self: readonly Self): i32 { self.other }

  function sneak(self: mut Self): void {
    // Matches `self.w` through `self: mut Self`.
    // Does the arm assign to `x`, lend `mut x`, or call a `mut` method on `x`?
    // No! It just evaluates to `x` (or binds `const p = x`)!
    const p = match (self.w) {
      #Wrap(x) => x,
    };
    // If `match (self.w)` lent `self.w` only `readonly` because `x` was not directly mutated in the arm,
    // while `x` still got type `mut i32` from matching through `self: mut Self`:
    const r = self.readOther(); // Allowed if `self.w` was only lent `readonly`!
    p += r;                     // Mutates `self.w` through `p: mut i32`!
  }
}
```
Wait: if an arm does *not* change `x`, what is `x`'s **type** inside that arm?
- If `x`'s type in a read-only arm is downgraded to **`readonly Part`** (or a copy if `Copy`), then `const p = x` gives `p: i32` (or `readonly Part`), so `p += r` is rejected by the type checker!
- Conversely, if `x`'s type is **`mut Part`** whenever `x` is used as a `mut` value (including being returned from the `match`, assigned to a local, or matched again with a mutating inner arm), then any arm where `x` is used as `mut Part` **must** lend the matched place `mut`!

**Fix (`§4.1`):**
Make the type of the pattern binding and the borrow mode of the matched place say the **exact same thing**:
- In a `match` on a place reached through a `mut` borrow, each arm binds its pattern variables as `mut` iff that binding is **used mutably** (assigned to, lent `mut`, has a `mut` method called on it, is nested-matched with a `mut` arm, or escapes the arm as a `mut` value in a local/return), and binds them as `readonly` (or by copy for `Copy`, per `§4.1`) otherwise.
- The `match` lends the place `mut` in an arm iff that arm has at least one `mut` binding; otherwise that arm lends the place `readonly`.
Then in `while (const #Some(#Op(op)) = self.peek())`, or `if (const #Alias(n) = self.defs[d].kind)`, `n` is not used mutably, so `n` is bound as `readonly` (or copied if `Copy`) and `self.defs[d].kind` is lent `readonly`!

---

#### 3. Decision (1) ("A match arm binds by the strongest use it makes of what it binds") has three edge cases: `let` mutation in place, guards, and partial moves (`§4.1`, `§5.6`)

Let's test Decision (1) on three concrete programs.

**Edge Case 3A (The compiler-author gap you noted: mutating a bound part of an owned `let` local in place):**
Look at `§4.1`:
> *"an arm that moves an owned, non-`Copy` part it binds takes the place, moving it; an arm that only reads what it binds borrows the place, `readonly`, for as long as those bindings are used; an arm that binds nothing, or only copies, reads it."*

What if `o` is an owned **`let` local** (`let o: Option<String> = #Some("hi".toString());`), and an arm wants to **mutate `x` in place** without moving `o`?
```ts
export function main(): void {
  let o: Option<String> = #Some("hello".toString());
  match (o) {
    #Some(x) => { x.push(" world"); }, // Mutates `x`, does NOT move `x` out!
    #None => {},
  }
  // We want `o` to still be live and contain `#Some("hello world")`!
  println(`${o}`);
}
```
Under the current `0.55` wording:
- `o` is an owned `let` place, not a `mut` borrow.
- In `#Some(x) => { x.push(" world"); }`, `x.push(...)` takes `mut self`.
- If `x` is bound by move, `o` is moved and dead after the `match` (and `x.push` mutated a moved copy/value that gets dropped at the end of the arm!).
- If `x` is bound by `readonly` borrow, `x.push(" world")` is a compile error (`cannot borrow readonly x as mut`)!
- So the author is forced to write a dummy helper `function asMut<T>(x: mut T): mut T { x }` and `match (asMut(mut o))`!

Why not complete the table so that matching an owned `let` place has all **four** modes, identical to closure capture (`§4.3`)?
For an arm matching an owned place `p`:
1. **Moves a non-`Copy` bound part:** moves `p` (binds by move).
2. **Mutates a bound part in place (without moving it out), and `p` is a mutable place (`let` or owned parameter):** lends `p` **`mut`** for the arm (binds `x: mut T`, mutating `p` in place!).
3. **Only reads a non-`Copy` bound part:** lends `p` **`readonly`** for as long as the binding is used (binds `x: readonly T`).
4. **Binds nothing or only `Copy` parts (not mutated in place):** reads `p` (`Copy` parts copied).

Look what adding row (2) does:
- It eliminates the "need a helper taking `mut Option<T>`" language gap completely!
- It makes matching a `let` local and matching a `mut` parameter 100% uniform!
- It adds **zero** new syntax or concepts; it is literally the `mut` row of closure capture (`§4.3`) applied to `match` arms (`§4.1`).

**Edge Case 3B (Match guards `Pattern if guard => body`):**
What happens if an arm's **body** moves a bound part `x`, so the arm binds `x` by **move**, or mutates `x` in the **guard**, and the guard evaluates to `false`?
```ts
export function main(): void uses Io {
  const o: Option<String> = #Some("hello".toString());
  match (o) {
    // `x` is moved in the arm body (`take(x)`), so does `#Some(x)` move `o` before the guard runs?
    #Some(x) if x.len() > 10 => take(x),
    // Guard was false! Fall through to the second arm:
    #Some(x) => println(x), // Is `o` still alive here?!
    #None => {},
  }
}
```
And even worse: what if the **guard itself** moves `x`:
```ts
  match (o) {
    #Some(x) if consumeAndCheck(x) => println("yes"),
    #Some(x) => println(x), // `x` was already moved and dropped inside the failed guard!
    #None => {},
  }
```
**Fix (`§4.1`):**
State explicitly in `§4.1`:
- **A `match` guard may only read pattern bindings (`readonly`); it may not move or mutate them.**
- The move or `mut` borrow for an arm takes effect **only after its guard succeeds** (while the guard runs, the matched place is lent `readonly`).
That rule is 1 sentence, prevents use-after-move across fallthrough arms when a guard returns `false`, and matches Rust's and OCaml's guard semantics.

**Edge Case 3C (Mixed move + read in the same arm on a `Drop` type):**
Suppose a struct `S` implements `Drop` (`§4.1`: *"unless the value's type implements `Drop`, from which no field may be moved"*), or a tuple `[String, String]` is matched:
```ts
const pair: [String, String] = ["a".toString(), "b".toString()];
match (pair) {
  [a, b] => {
    take(a);          // Moves `a`
    println(b.asStr()); // Only reads `b`
  }
}
```
When the arm `[a, b]` moves `a` and only reads `b`:
- Does "an arm binds by the strongest use it makes of what it binds" decide per **arm** (the whole matched place `pair` is moved, so `a` and `b` are both bound by move, and `b` is dropped at the end of the arm), or per **binding** (`a` is moved out of `pair[0]` while `b` borrows `pair[1]`)?
- Look at `§4.1`: *"an arm that moves an owned, non-`Copy` part it binds takes the place, moving it"*.
- If the arm moves the whole place `pair`, then what if the matched value is an `enum` that implements `Drop` (`enum Resource { #Pair(String, String) }` with `impl Drop for Resource`)? You **cannot** move `a` out of `Resource` at all (`§4.1`: *"unless the value's type implements `Drop`, from which no field may be moved"*).
- Make sure the checker enforces that an arm cannot bind by move any payload of a type that implements `Drop`, and that when an arm takes a non-`Drop` place by move, any non-moved sibling pattern bindings in that arm are owned and dropped when the arm exits.

---

### Ranked Next Steps Toward a High-Quality Language

With the self-hosted compiler reaching a 3-second fixpoint and passing all 54 run tests, you are at the pivotal transition from *"the language works"* to *"the language is fast, rock-solid, and ready for real systems code"*. Here is the highest-leverage order of work:

#### 1. Fix the 3 soundness/ergonomic corners in `§4.1` above (1–2 days)
- Allow `match` on a mutable owned place (`let` / owned param) to lend `mut` in place when an arm mutates a bound part without moving it (Problem 3A — directly fixes the `mut Option<T>` compiler-author papercut).
- Forbid moves/mutations inside `match` guards so failed guards cannot consume values before fallthrough arms run (Problem 3B).
- Tighten the "result holds borrow only through a type argument" rule so callbacks and associated types cannot smuggle a place borrow through a type parameter (Problem 1) and ensure `mut` binding in `match` through `mut` is checked on any escaping `mut` binding (Problem 2).

#### 2. JS Backend Codegen Optimization: Native `number` (SMI/f64) for `i8..i32`/`u8..u32`/`usize` and unboxed locals (~3–5x faster `selfhost`)
Right now `selfhost` compiles itself in ~3s using `BigInt` for every integer (`u8`, `i32`, `usize`) and `{ v }` cells. Because your JS backend is now **fully typed and monomorphized**:
- **Use JS `number` for `i8`, `u8`, `i16`, `u16`, `i32`, `u32`, and `usize`!**
  - Every JS engine (V8, JSC, SpiderMonkey) represents 32-bit integers as unboxed tagged SMIs and up to 53-bit integers (`Number.MAX_SAFE_INTEGER`) exactly in `number` with zero heap allocation.
  - Checked 32-bit addition/subtraction/multiplication is a single fast check (`const r = a + b; if ((r | 0) !== r) $rt.overflow();` for `i32`, where V8 JITs `(r | 0) === r` to a single hardware `jo` overflow branch!), and `wrappingAdd` on `i32` is `((a + b) | 0)`!
  - Only `i64`, `u64`, and `i128` need `BigInt`.
  - Since a compiler (`selfhost`) spends 90% of its time indexing arrays/slices (`usize`), scanning bytes (`u8`), and manipulating node/type IDs (`u32`/`usize`), switching `i8..u32`/`usize` from `BigInt` to `number` removes almost all `BigInt(i)` / `Number(i)` conversions at array/string boundaries and speeds up `selfhost` by **2–4x**.
- **Retire or replace the Rust tree-walking interpreter (`flyc run`, 12 minutes to build `selfhost`) for bootstrap:**
  - Keep `flyc check` in Rust as a fast second-opinion type/ownership oracle if you want, or retire the Rust interpreter's `eval.rs` in favor of running the compiled JS output via `node`. Waiting 12 minutes for `flyc run` to interpret `selfhost` is no longer earning its keep when `node stage1.js` does the exact same job in 3 seconds and tests the real backend!

#### 3. C Backend (`gen_c.fly`) from the Monomorphized IR (~1,200 lines of Flyscript)
Flyscript's #1 promise in `§0` is: *"Flyscript is an ahead-of-time compiled systems language... It compiles to native code and to WebAssembly, has no garbage collector"*, with unboxed values, deterministic destruction, `@layout(c)` / `@layout(packed)`, and bump-allocated regions (`§4.6`).
- Because `selfhost` already monomorphizes every function, resolves every interface method, expands all `comptime` templates, and records exact move/drop facts from `own.fly`, **80% of a native compiler is already built**.
- Writing `gen_c.fly` (emitting C11/C99 compiled by `cc`/`clang` and `clang --target=wasm32-wasi`) is the shortest path to proving that Flyscript's systems claims hold:
  1. **Unboxed representation:** `struct` and canonical `record` -> C `struct`; `enum` and closed `#tag` union -> tagged C `struct { uint8_t tag; union { ... }; }`; `T[N]` -> inline array; `readonly T[]` / `mut T[]` / `str` -> `{ T* ptr; size_t len; }`; `mut T` -> `T*`.
  2. **Regions (`§4.6`):** A `region (R) { ... }` is a 50-line bump-arena (`RegionArena r = region_open(); ... region_close(&r);`), where `Ref<R, T>` is literally `const T*`! This will immediately validate that `own.fly`'s region-escape rules are 100% watertight under real arena deallocation (which JS's GC hides!).
  3. **Effects in C (`§11`):**
     - Pure and `Region<R>` functions -> direct C functions (passing `RegionArena*` for `Region<R>`).
     - `Fail<E>` -> two-value return `struct Result_T_E { bool failed; union { T ok; E err; }; }`.
     - Tail-resumptive handlers (the common case: `for…of` over a `Yield` generator, `Clock.now`, `Log.info`) -> pass handler vtable/context pointer down the call chain; zero stack switching!
     - Resumptive handlers that capture `Cont` (`generate`, `Io` tasks) -> small stackful coroutines (e.g. `minicoro` / `ucontext` / 40 lines of x86_64 + aarch64 stack-switch assembly).
  4. **Self-hosting natively:** Once `gen_c.fly` compiles `selfhost` to a native binary, `selfhost` will compile itself in **< 0.2 seconds** with zero JS/Node dependency.

#### 4. Language Ergonomics Discovered While Writing `selfhost`
Beyond the `match` on `let` locals (item 1 above), check which patterns in `selfhost/*.fly` caused the most friction. Three candidates worth evaluating against `selfhost`'s codebase:
1. **Mutating a `Vec` element or `HashMap` entry while reading another field of `self`:**
   - Because `self.items[i]` borrows all of `self.items` (`§4.1`), `self.items[i].field = self.compute()` (where `self.compute()` is `readonly self`) is rejected if `self.compute()` reads `self.items`, or even if `self.items[i]` is evaluated before `self.compute()` and locks `self.items` `mut` before the arguments are evaluated.
   - Verify that index assignment `xs[i] = rhs` and `xs[i].f = rhs` uses the same **two-phase borrow** (`§4.1`) as method calls (`readonly` while evaluating index and `rhs`, `mut` only for the write).
2. **`if (const Pat = expr)` with `&&` conditions (let-chains):**
   - In a compiler (`check.fly`, `own.fly`, `gen.fly`), you constantly write `if (const #Some(x) = opt) { if (x.isReady()) { ... } }`.
   - Allowing `if (const #Some(x) = opt && x.isReady()) { ... }` (or chaining multiple `const Pat = expr` with `&&` in `IfConst`, desugared to nested two-armed `match`es where the `else` branch is shared!) removes deeply nested `if`/`else` duplication with zero new core semantics.
3. **Diagnostic quality (multi-span notes for borrow and effect errors):**
   - Right now diagnostics report a single span. For ownership/borrow errors (`cannot borrow x as mut because it is borrowed as readonly`), emitting a secondary note pointing at the **loan creation site** and the **last-use site keeping the loan alive** (both of which `own.fly` already computes!) transforms the user experience of the borrow checker.
