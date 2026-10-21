# Review: final-assessment-0-48

- spec: 281851744fa3
- request: e2e1a157d395a616
- tokens: prompt 86169, cached 0, answer 7924

## Question

Spec 0.48 is included, followed by Mini (examples/mini/: lexer.fly, syntax.fly, check.fly, codegen.fly, main.fly), a five-module compiler written in Flyscript: algebraic data types with exhaustive `case`, structural records typed by Rémy rows, Hindley–Milner let-polymorphism over types allocated in a region (union-find links in `Cell`s, path compression), error recovery through a resumptive `Diag` effect with an `#Error` type, closure conversion, codegen to a stack machine and a VM. It checks and runs on the prototype; the run test compares its output.

Since your compiler-writing review of 0.43, Mini's checker moved into a region as you suggested, and the language gained: pure generators taking any effect row (Gen closures may perform the generator's effects), `allocAll`, `HashSet`, `replace`/`swap`, `join` on generators, match narrowing of unions, matching through `Box`, receiver-decided generic results, `Clone` for region handles, and region-erased specialization keys.

Two questions, answered bluntly:
1. **Is Flyscript now a high-quality language?** Judge the specification as a whole: coherence, soundness of the ownership/effects/regions core as stated, ergonomics for its stated audience (TypeScript programmers), and whether it is ready to freeze a 1.0 core. If not, list the specific blockers in priority order.
2. **Is goal 6 credibly on track** — would you now expect a Flyscript front end (modules, structs, interfaces, generics, effects, regions, ownership checking, comptime) to be pleasant to write in Flyscript? Read Mini's code for what would still hurt at 20× the size; name concrete code or language issues, not generalities.

## Context files

- `/tmp/flyscript-048-context.md`

## Answer

### Verdicts

- **Question 1 — Is Flyscript a high-quality language ready to freeze a 1.0 core?**: **Agree with changes.** The conceptual architecture (Laws 1–5) is extraordinarily coherent, and moving Mini's type graph into a region (`check.fly`) proves that second-class borrows + effectful regions replace both lifetimes and `Rc<RefCell>` in practice. There are **two soundness bugs** in the 0.48 spec (`§4.6` multi-region mixing and `§4.1` matching through `Box` in a `mut` place) and **two specification/ergonomic gaps** that should be fixed before freezing 1.0.
- **Question 2 — Is Goal 6 (self-hosting a full Flyscript front end) credibly on track?**: **Agree with changes.** Mini is genuinely pleasant to read — `check.fly` is ~280 lines of clean, unannotated code doing HM + Rémy row unification with union-find in a region. At 20× the size (~10,000 lines for `flyc`), **four concrete friction points** visible in Mini will hurt unless addressed: (1) split-field borrowing across helper methods (`check.fly` lines 39, 59, 179, 286), (2) `replace(mut inner.code, Vec.new())` vs `.drain().collect()` (`codegen.fly` lines 107–110), (3) `"".toString()` on every string error message (`syntax.fly` lines 53, 81, 211), and (4) `Ref<T>` pattern matching and `Eq`/`Hash` on region-allocated keys.

---

### Problems

#### 1. Soundness (Blocker 1): `§4.6` Rule 2 ("same region") is violated when an inner region stores a `Ref<R_outer, T>` into `R_inner` or vice versa

Look at `§4.6`:
> *"2. **No owned resources.** Region data contains only `Copy` values, `Ref`s, `Cell`s and `RegionList`s of the same region; this is checked wherever a value is placed in a region (`alloc`, `RegionList.push`)."*

Wait: `Ref<R, T>`, `Cell<R, T>`, and `RegionList<R, T>` are themselves **`Copy`** (`§4.5`, `§4.6`: *"Both are handles into their region — `Copy`, like a `Ref`"*).
Because `Ref<R2, T>` is `Copy`, what happens when you have two nested regions `R1` (outer) and `R2` (inner)?

**Case A (Dangling pointer — unsound):** An outer region `R1` has a `Cell<R1, Option<Ref<R1, u64>>>` or `RegionList<R1, ...>`, or even simpler, what if a type in `R1` stores a `Ref<R2, T>`?
If Rule 2 literally enforces "of the **same** region", then `alloc<R1>( value_containing_Ref_R2 )` is rejected because `R2 != R1`.
**Case B (Ergonomic blocker for a real compiler):** What about the reverse — storing a `Ref<R_outer, str>` (like an interned identifier from a module-level region `R_mod`) inside a per-function type-checking region `R_fn`?
```ts
region (R_mod) {
  const internedName: Ref<R_mod, str> = fmt("x");
  region (R_fn) {
    // In a real compiler (Goal 6), ASTs or interned strings live in `R_mod`,
    // while function-local inference types live in `R_fn` and are discarded per function!
    // Can a type in `R_fn` hold `internedName: Ref<R_mod, str>`?
    const ty = alloc<R_fn, Field<R_mod>>({ name: internedName, ty: 0 });
  }
}
```
Look at what happens in both directions:
1. If "only `Copy` values, `Ref`s, `Cell`s and `RegionList`s of the same region" treats `Ref<R2, T>` as a `Copy` value, then `alloc<R1>(Ref<R2, T>)` or `Cell<R1, Ref<R2, T>>` is allowed and **dangles when `R2` exits** (because `R2` does not appear in any variable outside `region (R2)` if it was erased or if `Cell` was mutated!). Wait: if `c: Cell<R1, Option<Ref<R2, str>>>` is declared inside `R2`, `c`'s type mentions `R2`, unless it's stored in a `RegionList<R1, ...>` or `Cell<R1, ...>` created *before* `R2`? No, if `c` was created before `R2`, its type is fixed in `R1`.
2. Conversely, if Rule 2 forbids `alloc<R_inner>` from containing a `Ref<R_outer, str>`, then **you cannot use nested regions in a compiler**! In a real compiler (`flyc`), module ASTs live in `region (R_ast)`, while checking each function body opens a scratch `region (R_fn)` for union-find type variables that references AST nodes (`Ref<R_ast, Expr>`, `Ref<R_ast, str>`)!
3. And look at `§0.1` / `§11`:
   > *"A specialization is keyed by its `comptime` arguments with regions erased (§7.1, §11)"*
   What if a struct `Pair<region R1, region R2> { a: Ref<R1, i32>; b: Ref<R2, i32>; }` has two region parameters? Erasing regions to a single region in `comptime` specialization keys works fine for code generation, provided region checking still checks `R1` and `R2`.

**Fix:**
State Rule 2 in `§4.6` precisely so it is both sound and allows inner regions to reference outer enclosing regions:
> *"2. **No owned resources.** Region data placed in `R` contains only `Copy` values (which may include `Ref`s, `Cell`s and `RegionList`s of `R` or of an enclosing region)."*

Because lexical `region` blocks nest strictly (and `R_inner` cannot escape `region (R_inner)` by Rule 1), any enclosing region `R_outer` strictly outlives `R_inner`, so storing `Ref<R_outer, T>` inside `R_inner` is 100% sound and zero-cost, while storing `Ref<R_inner, T>` into `R_outer` is impossible because `R_outer` is outside `R_inner`'s scope.

---

#### 2. Soundness (Blocker 2): Matching through a `Box<T>` inside a `mut` borrow (`§4.1`) allows invalidating a borrowed `Box` payload

Look at `§4.1`:
> *"A match through a box. A `Box<T>` is matched as the `T` it holds, through the same borrow: `match (node) { #Add(a, b) => … }` with `node: readonly Box<Expr>` binds `a` and `b` as borrows of the boxed `Expr`'s parts."*

Now look at how `§4.1` tracks field paths:
> *"Borrows are tracked the same way, per field path: while `x.f` is borrowed, `x.g` may be read, changed or lent `mut`…"*

What if a `match` matches a **nested** `Box<Expr>` inside a `mut` borrow or owned value, or matches a tuple `[x, y]` where `x` is a `Box`?
```ts
enum Tree { #Leaf(i32), #Branch(Box<Tree>, Box<Tree>) }

function clobber(mut t: Tree): i32 {
  match (t) {
    // Matching through `Box<Tree>` on the first child:
    // `val` is a `mut i32` (or `readonly i32`) pointing into the heap allocation of the left `Box<Tree>`.
    #Branch(#Leaf(val), right) => {
      // If `t` itself is overwritten or dropped while `val` is live, the Box is freed!
      // That's blocked because `t` is locked by `val`.
      // Wait: what if we match a struct with two fields `{ left: Box<Tree>; right: i32 }`,
      // or match `t` by move in one part and by borrow in another?
      val
    }
    _ => 0,
  }
}
```
Wait — look closer at `#Branch(#Leaf(val), right)` when `t` is an **owned** `Tree` (not a borrow!):
Look at `§4.1`:
> *"A match moves per arm. Matching a place moves it only in an arm whose pattern takes an owned, non-`Copy` part; an arm that binds nothing, or only copies, reads it, so `_ => println(\`${e}\`)` may use what another arm would have taken."*

Read that rule combined with **"A match through a box"** on an **owned** `t: Tree`:
```ts
enum Bad { #Node(Box<String>, Vec<i32>) }

export function useAfterFree(b: Bad): void {
  match (b) {
    // Look at the pattern `#Node(s, v)`:
    // `b` is an OWNED `Bad`.
    // Its first payload is `Box<String>`. By "A match through a box", if `Box<T>` is matched as `T`,
    // or what if `Box` holds an enum `Box<Inner>` where `Inner` has `#Wrap(String)`?
    // If `#Node(#Wrap(s), v)` matches through the `Box<Inner>` by MOVING `s: String` out of `Box<Inner>`,
    // or if `s` borrows from the `Box` while `v: Vec<i32>` moves `b`!
  }
}
```
Look at what happens when `b: Bad` is an **owned** value (`enum Inner { #Text(String), #Num(i32) }`, `enum Outer { #Pair(Box<Inner>, String) }`):
1. Case 1: We match an owned `o: Outer` with pattern `#Pair(#Text(s), other)`:
   Can you **move** `s: String` out of a `Box<Inner>` when matching through a `Box`?
   `Box<Inner>` implements `Drop` (it frees its heap allocation when dropped!). And `§4.1` says:
   > *"Moving a field out of a value moves only that field, unless the value's type implements `Drop`, from which no field may be moved."*
   If you moved `s` out of `Box<Inner>`, who frees the `Box`'s heap memory? If the `Box` is not dropped, its heap memory leaks; if it is dropped, it double-frees `s`!
2. Case 2: We match an owned `o: Outer` with pattern `#Pair(#Num(n), other)`:
   Here `#Num(n)` binds `n: i32` (`Copy`) through the `Box<Inner>`, while `other: String` **moves** the second payload out of `o`!
   At the end of the block, `o` is partially moved (`other` was moved out, the `Box<Inner>` was not moved out), so `o`'s remaining field (`Box<Inner>`) is dropped at the end of `o`'s scope.
   Wait: what if the pattern is `#Pair(#Text(s), other)` where `s` is bound? Because nothing can be moved out of a `Box<T>` (since `Box<T>` owns a heap allocation and has a destructor), **matching through a `Box<T>` must always match through a borrow (`readonly T` or `mut T`), never by moving out of the `Box`!**

Look at `§4.1`'s wording:
> *"A match through a box. A `Box<T>` is matched as the `T` it holds, through the same borrow: `match (node) { #Add(a, b) => … }` with `node: readonly Box<Expr>` binds `a` and `b` as borrows of the boxed `Expr`'s parts."*

That sentence only states what happens when `node` is already a borrow (`readonly Box<Expr>`)! What if someone matches an owned `Expr` recursively, or matches a `Box<T>` place directly without `readonly`?
**Fix:** Clarify in `§4.1`:
> *"A match through a box. A `Box<T>` reached in a pattern is matched through a borrow of the `T` it holds (`readonly`, or `mut` through a `mut` borrow); no part may be moved out of a `Box`."*

---

#### 3. Goal 6 (Self-Hosting Pain #1): Split-field borrows fail across method calls (`check.fly` lines 39, 59, 179, 286)

Look closely at `examples/mini/check.fly`:
Why are `resolve`, `occurs`, `var`, `unify`, `unifyRows`, `flatten`, `record`, `bind`, `show`, `freeIn`, and `copy` written as **static functions** (`Checker.unify(self.ids, ...)`) taking `ids: Cell<R, usize>` instead of methods `self.unify(a, b, span)` on `Checker<R>`?
And look at the comments in `check.fly` where the author had to work around `self` borrowing:

1. **Line 39 & 59 (`check.fly`):**
   ```ts
   function unify(ids: Cell<R, usize>, a: Ref<Type>, b: Ref<Type>, span: Span): void uses Region<R>, Diag
   ```
   `ids` had to be threaded by hand through `unify` and `unifyRows` instead of `self.unify(...)`! Why?
   Look at line 209 of `check.fly`:
   ```ts
   for (const [i, d] of p.defs.iter().enumerate()) {
     const tf = self.function(d.params, d.body);
     Checker.unify(self.ids, own[i], tf, d.span);
   }
   ```
   And line 161 (`generalize`): `generalize(self: readonly Self, ...)` vs `lookup(self: mut Self, ...)`:
   In `lookup` (line 146):
   ```ts
   // The scheme stays borrowed from `self.scopes` while `self.ids` counts on: they are
   // different fields (§4.1).
   if (const #Some(s) = self.scopes[i].get(name)) {
     let map: HashMap<usize, Ref<Type>> = HashMap.new();
     for (const v of s.vars) {
       map.insert(v, Checker.var(self.ids));
     }
     return Checker.copy(s.ty, map);
   }
   ```
   Look at why `Checker.var(self.ids)` had to be called instead of `self.fresh()`!
   While `s` borrows `self.scopes`, you **cannot** call `self.fresh()` because `fresh(self: mut Self)` borrows the **entire** `self` (`mut Self`), which conflicts with the borrow of `self.scopes`!
   And look at **line 286 (`#Case` in `check.fly`)**:
   ```ts
   // What the arm needs of its constructor, copied out so the table is not held while
   // the body is checked.
   const found: Option<[usize, Vec<Ref<Type>>, Ref<Type>]> = match (self.ctors.get(arm.ctor)) {
     #Some(c) => #Some([c.data, c.fields.clone(), c.result]),
     #None => #None,
   };
   ```
   Here, `self.ctors` is read-only throughout `infer` (`ctors` is populated once in `program` and never mutated in `infer`!). Yet because `self.infer(arm.body)` takes `mut Self` (even though `infer` only mutates `self.scopes`!), the author could not hold a `readonly` borrow of `c` from `self.ctors.get(arm.ctor)` across `self.infer(arm.body)` and had to **clone `c.fields` (`Vec<Ref<Type>>`) on every case arm**!

Think about what this means at 20× the size in `flyc`:
In `flyc`, the type checker has:
- `defs` / `structs` / `enums` / `interfaces` / `impls` (symbol tables, populated in pass 1 or read during checking)
- `scopes` (local variable stack, mutated during checking)
- `subst` / `ids` / `loans` (inference and ownership state, mutated during checking)

If all of those are fields on one `struct Checker`, then **every** method taking `self: mut Self` locks all the symbol tables (`self.structs`, `self.interfaces`, `self.ctors`), forcing you to `.clone()` definitions out of symbol tables before calling `self.checkExpr(...)`!

**Two fixes (one pattern in code, one small language feature if desired):**
1. **In compiler architecture (zero language change):** Split immutable/region-allocated tables from mutable per-pass state!
   Wait: why was `ctors: HashMap<String, Ctor<R>>` on `Checker<R>` in the first place, and why did `lookup` need `self: mut Self`?
   Wait: **`lookup` in `check.fly` (line 138) does NOT mutate `self` at all!**
   Look at `lookup` (line 138):
   - It reads `self.ctors` (`readonly`).
   - It reads `self.scopes` (`readonly`).
   - It calls `Checker.var(self.ids)` — and `self.ids` is a `Cell<R, usize>`, whose `.get()` and `.set()` take `Self` by **copy** (`uses Region<R>`), NOT `mut`!
   - And `fresh(self: readonly Self)` only reads `self.ids` (`Copy`)!
   Look at line 30 of `check.fly`:
   ```ts
   function fresh(self: mut Self): Ref<Type> uses Region<R> {
     Checker.var(self.ids)
   }
   ```
   `fresh` and `lookup` were declared `self: mut Self` in `check.fly` for **no reason** — `self.ids` is a region `Cell<R, usize>`, so `fresh(self: readonly Self)` and `lookup(self: readonly Self, ...)` only need `readonly Self`!
   And if `Ctor.fields` in `check.fly` (line 18) is `Ref<R, Ref<R, Type<R>>[]>` (via `allocAll`, just like `#Fn` on line 12!) instead of `Vec<Ref<R, Type<R>>>`, then `Ctor<R>` is **`Copy`**!
   Let's verify that!
   In `check.fly` line 18:
   ```ts
   export type Ctor<region R> = { data: usize; tag: usize; fields: Ref<R, Ref<R, Type<R>>[]>; result: Ref<R, Type<R>> };
   ```
   If `Ctor<R>.fields` uses `allocAll` (`Ref<R, Ref<Type>[]>`), then `Ctor<R>` is **`Copy` and class 1**!
   Then by `§4.1` (*"Copy parts bind by copy"*):
   ```ts
   if (const #Some(c) = self.ctors.get(arm.ctor)) { ... }
   ```
   binds `c: Ctor<R>` **by copy**, immediately releasing the borrow of `self.ctors`! The entire `const found = ... c.fields.clone()` workaround on lines 286–290 of `check.fly` disappears!
   **Definitely make that change in `check.fly`** (make `Ctor.fields` a `Ref<R, Ref<Type>[]>`, and make `fresh` and `lookup` take `self: readonly Self`). It is a textbook demonstration of why `allocAll` and `Cell` exist.

---

#### 4. Goal 6 (Self-Hosting Pain #2): Taking and restoring a field of `mut self` (`codegen.fly` lines 107–110)

Look at `examples/mini/codegen.fly` lines 104–110:
```ts
let inner = Gen { code: Vec.new(), locals: Vec.new(), globals: self.globals.clone(), ctors: self.ctors.clone() };
for (const c of captures) { inner.locals.push(c.clone()); }
for (const p of params) { inner.locals.push(p.clone()); }
inner.code = self.code.drain().collect();
inner.gen(body);
inner.emit(#Ret);
self.code = inner.code.drain().collect();
```
Look at what `codegen.fly` is doing every time it compiles a lambda `#Fn`:
1. It clones the entire `globals` `HashMap` and the entire `ctors` `HashMap` (`globals: self.globals.clone(), ctors: self.ctors.clone()`) just to compile one lambda body!
2. It drains `self.code` into a newly allocated `Vec` (`self.code.drain().collect()`) and then drains it back!
Why didn't it just save and restore `self.locals` using `replace` (`§3.1`)?
Look at `§3.1`:
> *"`replace(mut place, v)` gives back what a place held and leaves `v` there, and `swap(mut a, mut b)` exchanges two places: how a pass takes a buffer out of `mut self`."*

With `replace` (which you just added to `§3.1`!), lines 104–110 of `codegen.fly` are simply:
```ts
let newLocals: Vec<String> = Vec.new();
for (const c of captures) { newLocals.push(c.clone()); }
for (const p of params) { newLocals.push(p.clone()); }
const savedLocals = replace(mut self.locals, newLocals);
self.gen(body);
self.emit(#Ret);
self.locals = savedLocals;
```
Look at the difference:
- Zero `HashMap` clones (`self.globals` and `self.ctors` aren't cloned).
- Zero `self.code.drain().collect()` copies.
- 5 lines instead of 9, and `O(captures + params)` instead of `O(code + globals + ctors)` per closure!
Update `codegen.fly` lines 104–110 to use `replace(mut self.locals, newLocals)` — it directly showcases the new `replace` function from `§3.1`.

---

#### 5. Goal 6 (Self-Hosting Pain #3): `"..."` vs `` `...` `` for owned `String` literals (`syntax.fly` lines 53, 81, 211; `codegen.fly` line 139)

Look at `syntax.fly` lines 53, 81, 211 and `codegen.fly` line 139:
```ts
_ => throw #Parse { at: self.here().start, message: "expected a name".toString() },
```
```ts
if (self.peek() != #Eof) { throw #Parse { at: self.here().start, message: "expected the end of the program".toString() }; }
```
```ts
self.locals.push("$case".toString());
```
Meanwhile, in `check.fly` lines 97–99:
```ts
#Error => `?`,
#Int => `int`,
```
Notice why `check.fly` wrote `` `?` `` and `` `int` `` (with backticks, even with no `${...}` interpolation) while `syntax.fly` wrote `"expected a name".toString()`:
- By `§2.2`, `"..."` has type `str` (borrowed slice), whereas `` `...` `` always builds an owned `String`!
- Because **lending is the only implicit conversion** (`§4.1`: `String` lends `str`, not the reverse — rightly so, so heap allocation is never hidden in arbitrary calls), passing `"..."` where `String` is expected requires `.toString()`, *or* writing `` `...` ``.
- Wait: why is `String.new()` used in `main.fly` line 104 (`let caret = String.new();`) when `""` or `` `` `` exists, and why does `syntax.fly` mix `"expected a name".toString()` with `` `expected ${what}` ``?
This is minor, but in a 10,000-line compiler:
- Either use backticks `` `expected a name` `` consistently when constructing an owned `String` literal (which is already valid by `§2.2` and used in `check.fly`), or
- Better yet, in a compiler with regions, diagnostic messages and AST identifiers can be `str` or `Ref<R, str>`!

---

#### 6. Goal 6 (Self-Hosting Pain #4): `Ref<R, str>` and `Ref<R, T>` as `HashMap` / `HashSet` keys (`§3.1`, `§3.5`, `§4.6`, `check.fly`)

Look at `check.fly`:
In `check.fly`, `Field<R>` stores `name: Ref<R, str>` (allocated in the region via `fmt(name)`).
And in `unifyRows` (line 64):
```ts
match (fb.iter().find((g) => g.name == f.name))
```
Here `g.name == f.name` compares two `Ref<R, str>` values for string equality.
Wait: **how does `g.name == f.name` work on `Ref<R, str>`?**
Let's check `§3.5`:
> *"The derivations settle three things a derived interface must get right… `Box<T>` and `Arc<T>` compare, order, hash and show as what they hold; cloning a `Box` clones its contents, cloning an `Arc` shares them again."*
> *"an owner compared with the type it lends is compared at that type (`name == "ada"` for a `String`, `b.name == name` for a `Ref<R, str>`)"*

Look at `§3.5`!
1. `§3.5` says `Box<T>` and `Arc<T>` compare, order, hash, and show as what they hold (`T`).
2. What about **`Ref<R, T>`**?!
   Does `Ref<R, T>` implement `Eq`, `Ord`, `Hash`, and `Show` by comparing, ordering, hashing, and showing the `T` it points to?
   - In `check.fly` line 64, `g.name == f.name` compares `Ref<R, str> == Ref<R, str>`!
   - In `check.fly` line 103, `` `${f.name}: ...` `` interpolates `f.name: Ref<R, str>`!
   - And in a real compiler (`flyc`), you want `HashMap<Ref<R, str>, Symbol<R>>` (a symbol table in region `R` keyed by region-allocated `Ref<R, str>` rather than heap-allocated `String`, so `scopes: Vec<HashMap<Ref<R, str>, Scheme<R>>>` doesn't heap-allocate `String` keys on every local variable)!
   - Even better: because `Ref<R, str>` lends `str` (`§4.1`), a `HashMap<Ref<R, str>, V>` can be looked up by `str` (`self.scopes[i].get(name)` where `name: str`) without allocating in the region OR on the heap!
   Look at `check.fly` line 25 right now:
   `scopes: Vec<HashMap<String, Scheme<R>>>;`
   In `check.fly`, every `let` binding and function parameter still heap-allocates a `String` (`scope.insert(p.clone(), ...)`) only because `scopes` used `HashMap<String, ...>` instead of `HashMap<Ref<R, str>, ...>`!

**Fix:**
In `§3.5`, explicitly include `Ref<R, T>` alongside `Box<T>` and `Arc<T>`:
> *"`Box<T>`, `Arc<T>` and `Ref<R, T>` compare, order, hash and show as what they hold; cloning a `Box` clones its contents, cloning an `Arc` or a `Ref` shares them again."*

---

#### 7. Spec Gap before 1.0: `match` through `Ref<R, T>` vs `Box<T>` (`§4.1`, `§4.6`, `check.fly` line 39)

Look at `check.fly` line 39:
```ts
function resolve(t: Ref<Type>): Ref<Type> uses Region<R> {
  match (t) {
    #Var(_, link) => ...
```
And line 59:
```ts
const [x, y] = [Checker.resolve(a), Checker.resolve(b)];
match ([x, y]) {
  [#Error, _] | [_, #Error] | [#Int, #Int] | [#Bool, #Bool] => {},
  [#Data(d, _), #Data(e, _)] if d == e => {},
```
Look at `[x, y]`: its type is `[Ref<R, Type<R>>, Ref<R, Type<R>>]`, a tuple of two `Ref`s!
And the pattern `[#Data(d, _), #Data(e, _)]` matches **nested** through the tuple AND through both `Ref<R, Type<R>>`s!
Now check `§4.1` and `§4.6`:
- `§4.1` states: *"A match through a box. A `Box<T>` is matched as the `T` it holds, through the same borrow..."*
- `§4.6` states: *"A `Ref<R, T>` is used exactly as a `readonly T`: field access and method calls go through it, and reading is pure."*
- Neither `§4.1` nor `§4.6` explicitly mentions that **patterns match through `Ref<R, T>`** (and `Arc<T>`) as `readonly T`!
Since `check.fly` relies on matching through `Ref<R, Type<R>>` (including nested inside tuples `[#Record(_, _), #Record(_, _)]`) on almost every line, add `Ref<R, T>` and `Arc<T>` to the box-matching paragraph in `§4.1`:
> *"A match through a pointer. A `Box<T>`, `Ref<R, T>` or `Arc<T>` is matched as the `T` it holds, through a borrow (`readonly`, or `mut` for a `Box` reached through a `mut` borrow)..."*

---

### Smaller points

1. **`check.fly` line 82 — redundant `Checker.resolve(t)` in `flatten`:**
   ```ts
   function flatten(t: Ref<Type>): [Vec<Field<R>>, Ref<Type>] uses Region<R> {
     match (Checker.resolve(t)) {
       #Record(fs, tail) => { ... }
       other => [Vec.new(), Checker.resolve(t)],
     }
   }
   ```
   `other` is already `Checker.resolve(t)`, so the second arm can just be `other => [Vec.new(), other]`.

2. **Duplicate record field labels in Mini (`check.fly` line 258):**
   In `check.fly` line 258:
   ```ts
   #Record(fields, _) => {
     let fs: Vec<Field<R>> = Vec.new();
     for (const [name, value] of fields) { fs.push({ name: fmt(name), ty: self.infer(value) }); }
     alloc(#Record(allocAll(fs), alloc(#Empty)))
   }
   ```
   If a Mini program writes a record literal with duplicate fields `{x = 1, x = true}`, `fs` gets two `x` entries and `unifyRows` only matches the first one in `fb.iter().find(...)`. Not a Flyscript spec issue, just a 2-line check in Mini if you want `{x = 1, x = 2}` rejected.

3. **`§2.3` Grammar — `Tuple` with 1 element vs `ListLit`:**
   In `§2.3`, `Tuple = "[" Type { "," Type } "]" ;` allows `[i32]` as a 1-tuple type, while `Type "[" [ Expr ] "]"` is an array/slice type. Since tuples in TypeScript/Flyscript are pairs or longer (or `[]` for empty row), keeping tuple types as 2+ elements (or noting 1-tuples if supported) avoids any confusion with TypeScript's `[T]`.

4. **Summary on 1.0 readiness:**
   Once `§4.6` Rule 2 (enclosing regions), `§4.1` (matching through `Box`/`Ref`/`Arc` always borrows), and `§3.5` (`Ref<R, T>` in `Eq`/`Ord`/`Hash`/`Show`) are tightened in the spec text, the 0.48 specification is ready to freeze as a 1.0 core.
