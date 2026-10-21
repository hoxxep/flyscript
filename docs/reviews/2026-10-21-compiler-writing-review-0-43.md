# Review: compiler-writing-review-0-43

- spec: 5a1367333f90
- request: 1693ffac9d86cdd5
- tokens: prompt 76803, cached 0, answer 10909

## Question

Goal 6 (§1) is now that Flyscript must be a language its own compiler is written well in. As a first test I wrote Mini (included below the spec as context): a compiler for a small functional language with lexer, recursive-descent parser, Hindley–Milner inference with let-polymorphism over a union-find arena, closure conversion, codegen to a stack machine, a VM, and line:col diagnostics. It checks and runs on the prototype.

Read Mini as an experienced compiler writer (think rustc, OCaml's compiler, TypeScript's checker) and answer:
1. **Where does Flyscript make this code worse than it should be?** Point at specific lines: clones forced by ownership, awkward lookups, missing library pieces, verbose patterns, places where a Flyscript compiler (which would be ~20× larger, with modules, structs, generics, effects, regions, comptime) would suffer. Distinguish language problems from library gaps from my own style.
2. **What will hurt at scale** when the compiler grows to a real Flyscript front end: arenas and indices versus `Box` trees, interning, symbol tables, mutable state shared between passes, error recovery and accumulating many diagnostics, incremental compilation, parallel checking. Which of these does the language support well, and which need a change to the language (not just the library)?
3. **The three changes that would most improve Flyscript for compiler writing**, with spec text.

## Context files

- `/tmp/flyscript-043-context.md`

## Answer

### Verdicts

- **Goal 6 (`§1`) and `Mini` as a first benchmark**: **Agree.** A compiler is the canonical stress test for a systems language without a GC. `Mini` reads well on the surface, but only because it is 400 lines and compensates for ownership friction by deep-cloning strings, types, schemes, and code arrays on nearly every operation.
- **Ownership & borrowing ergonomics in `Mini` (`Question 1`)**: **Agree with changes.** Five concrete places in `Mini` are worse than they should be: (1) `HashMap.get(k).cloned()` fails on structural types (`Scheme`), forcing manual field-by-field cloning in `Checker.lookup`; (2) `Parser`, `Tok`, and `Expr` allocate and `.clone()` `String` identifiers everywhere instead of borrowing `str` from `src` via a `view` or region; (3) `Types.resolve` deep-clones `Type` trees (`#Fn(Vec<Type>, Box<Type>)`) on every `occurs`, `unify`, `show`, `freeIn`, and `copy` call because returning `readonly Type` from a recursive union-find lookup is thwarted by temporary `#Var(v)` construction; (4) `Inner` codegen steals and restores `self.code` via `self.code.drain().collect()` (two full vector moves/allocations per lambda) because `Gen` combines the code buffer and the local variable table in one struct; and (5) `Vec.includes` requires a `String` when `Vec<String>` is queried with a `str`, or vice versa, and `HashSet` is missing.
- **Scaling to a 20× larger self-hosted `flyc` (`Question 2`)**: **Agree with changes.** A real compiler needs four things `Mini` sidesteps: (1) **Accumulating diagnostics with error recovery** (built-in via `effect Diag` + `handle`, whereas `Mini` uses abortive `Fail<CompileError>`); (2) **Interned symbols (`Sym`) and arena/index trees (`TypeId`)** (where Flyscript's lack of disjoint field borrowing across helper calls and lack of region-allocated growable maps hurts); (3) **Disjoint field borrows on `self`** (`§4.1`); and (4) **Parallel module checking** (`Io.scope` + `Region` interaction in `§6.1`).
- **Top 3 language changes for compiler writing (`Question 3`)**: Ranked below with exact spec text: **(1) Disjoint field borrows (splitting structs across borrows and method arguments, `§4.1`)**, **(2) `Option<readonly T>.cloned()` working on all `Clone` types (including structural records/tuples) + `mem.swap` / `mem.replace` (`§3.2`, `§3.5`, `§4.1`)**, and **(3) Lifting the `Io.scope` outer-region freeze for read-only region data or allowing pure parallel work (`par` / `Io.scope`) to read `Ref<R, T>` while building per-module outputs (`§4.6`, `§6.1`)**.

---

### Problems (Question 1 & Question 2)

#### 1. Disjoint field borrows on `self` and structs (`§4.1`) — **Language problem**

Look at `Checker.lookup` in `Mini`:
```ts
impl Checker {
  function lookup(self: mut Self, name: str, span: Span): Type uses Fail<CompileError> {
    let i = self.scopes.len();
    while (i > 0) {
      i -= 1;
      const found: Option<Scheme> = match (self.scopes[i].get(name)) {
        #Some(s) => #Some({ vars: s.vars.clone(), ty: s.ty.clone() }),
        #None => #None
      };
      match (found) {
        #Some(s) => return self.instantiate(s),
        #None => {},
      }
    }
    throw #Unbound { span, name: name.toString() }
  }
```
Why couldn't `Checker.lookup` be written simply as:
```ts
if (const #Some(s) = self.scopes[i].get(name)) {
  return self.instantiate(s); // taking `s: readonly Scheme`!
}
```
Two reasons:
1. `self.scopes[i].get(name)` returns `Option<readonly Scheme>`, which borrows `self.scopes` (and therefore, if field borrows are not tracked disjointly, borrows all of `self`).
2. `self.instantiate(s)` takes `self: mut Self`, which mutates `self.types.fresh()` (`self.types.links.push(#None)`). It **never touches `self.scopes`!**
Yet because `self.instantiate` takes `self: mut Self`, `lookup` cannot hold `s: readonly Scheme` (borrowed from `self.scopes[i]`) across `self.instantiate(s)` — nor could it even call `self.types.instantiate(s)` if `self.scopes` and `self.types` are not tracked as **disjoint field paths** of `self`!
So `Mini` had to deep-clone `s.vars` (`Vec<usize>`) and `s.ty` (`Type` tree) into an owned `Scheme` *before* calling `self.instantiate(s)`, and `instantiate(self: mut Self, s: Scheme)` takes `s` by value only to read `s.vars` and `s.ty`!

Look at what happens in `Gen` (lines 324–332 of `Mini`) for the same reason:
```ts
let inner = Gen { code: Vec.new(), locals: Vec.new(), globals: self.globals.clone() };
for (const c of captures) { inner.locals.push(c.clone()); }
for (const p of params) { inner.locals.push(p.clone()); }
inner.code = self.code.drain().collect();
inner.gen(body);
inner.emit(#Ret);
self.code = inner.code.drain().collect();
```
Why did `Gen.gen` have to:
- `.clone()` the entire `self.globals: HashMap<String, usize>` for every single `#Fn` expression in the program, AND
- `.drain().collect()` the entire bytecode buffer `self.code` into `inner.code` and then `.drain().collect()` it back into `self.code`?!
Because `code`, `locals`, and `globals` were put in one `struct Gen`, or because if `globals` were borrowed (`readonly HashMap<String, usize>`) `Gen` would have to be a `view struct`. Even without a `view struct`, if `Gen` is split or if methods on sub-fields (`self.types.fresh()` while `self.scopes` is borrowed `readonly`) are called, **`§4.1` never states that borrowing `x.f` and `x.g` (distinct fields of a struct or record) are disjoint borrows!**
Wait: check `§4.1` and `§9`:
- `§4.1` says: *"Moving a field out of a value moves only that field, unless the value's type implements `Drop`..."*
- `§9` says: *"Γ is the borrow ledger: each live borrow, its mode (`ro` or `mut`) and the path it locks. A `mut` entry locks its path against all use; a `ro` entry locks it against moves and `mut` borrows."*
Does `§4.1` state that a borrow of `x.f` locks `x.f` (and prefixes `x`), leaving sibling field `x.g` free to be borrowed `mut` or `readonly` at the same time?
**No!** `§4.1` mentions per-field moves, and says *"while it is borrowed the whole collection is"* for `xs[i]`, but never states the disjoint field borrow rule for structs/records/tuples (`x.f` vs `x.g`, `t[0]` vs `t[1]`)!

In a real compiler (`flyc`), your context struct has:
```ts
struct Checker {
  types: TypeArena;
  scopes: ScopeStack;
  defs: DefTable;
  diags: Vec<Diagnostic>;
}
```
Every 5 lines in a type checker, you read a symbol or signature from `self.scopes` or `self.defs` (`readonly`) while allocating/unifying in `self.types` (`mut`) or pushing to `self.diags` (`mut`).
If borrowing `self.scopes` locks `self.types`, or if `Checker.instantiate` takes `self: mut Self` instead of `self.types.instantiate(s)` with disjoint field borrows on `self.scopes` and `self.types`, a 20,000-line compiler turns into a sea of `.clone()`s.

**Fix (both language rule in `§4.1` and style in `Mini`):**
1. Explicitly state **disjoint field borrowing** in `§4.1`: borrowing a field `x.f` (or tuple element `t[0]`) locks that field path and prevents moving or borrowing `x` as a whole, but leaves other fields `x.g` free to be borrowed (`readonly` or `mut`) or moved.
2. In `Mini`, make `instantiate` a method on `Types` (`self.types.instantiate(s)` taking `s: readonly Scheme`), so `self.scopes[i].get(name)` holds a `readonly` borrow of `self.scopes` while `self.types.instantiate(s)` mutates `self.types` — zero clones of `s.vars` or `s.ty`!

---

#### 2. `Option<readonly T>.cloned()` fails on structural types (`Scheme`), and `Types.resolve` clones entire `Type` trees on every step (`§3.2`, `§3.5`, `§4.1`) — **Language / Prelude bug + Style**

Look again at line 206 of `Mini`:
```ts
const found: Option<Scheme> = match (self.scopes[i].get(name)) {
  #Some(s) => #Some({ vars: s.vars.clone(), ty: s.ty.clone() }),
  #None => #None
};
```
Why didn't you write `self.scopes[i].get(name).cloned()` here, the way you wrote `store.get(key).cloned()` in `A.6`?
Look at `Scheme`:
```ts
type Scheme = { vars: Vec<usize>; ty: Type };
```
`Scheme` is a **structural record** whose fields (`Vec<usize>` and `Type`) both implement `Clone`.
And `§3.5` says:
> *"An interface can come with a derivation: an impl, written in Flyscript with `comptime` reflection, that works for any type whose shape it can see (§7.3). Records, tuples and tag unions get it whenever they have no impl of their own... `Eq`, `Hash`, `Show` and `Clone` are derived this way in the prelude"*
And `§3.2` says:
> *"an `Option<readonly T>` also has `cloned()`."*
Wait: if `Scheme` is a structural record of `Clone` fields, so `Scheme` automatically gets `Clone` from the prelude derivation (`§3.5`), **why couldn't `Mini` write `self.scopes[i].get(name).cloned()` (or `s.clone()`)?!**
Either:
1. `Option.cloned()` in the prototype is restricted to `Copy` or nominal types instead of `<T extends Clone>`, OR
2. Calling `.clone()` on `s: readonly Scheme` (or `Option<readonly Scheme>.cloned()`) did not resolve the derived `Clone` impl for the structural record `Scheme`!
Check which one happened in `flyc`: if `s.clone()` or `.cloned()` does not work when `Scheme` is a structural record `{ vars: Vec<usize>; ty: Type }`, that is a direct bug in `flyc`'s `Clone` derivation / `Option.cloned()` bound resolution against `§3.2` and `§3.5`.

Now look at `Types.resolve` in `Mini` (lines 142–150):
```ts
  function resolve(self: readonly Self, t: readonly Type): Type {
    match (t) {
      #Var(v) => match (self.links[v]) {
        #Some(bound) => self.resolve(bound),
        #None => #Var(v),
      },
      other => other.clone(),
    }
  }
```
Look at what `resolve` does when `t` is `#Fn(ps, r)`:
It executes `other.clone()`, which **recursively allocates a new `Vec<Type>` and `Box<Type>` on the heap**!
And when is `self.resolve(t)` called?
- Inside `occurs(v, t)` — on every node of `t`!
- Inside `unify(a, b)` — on every recursive step of unification!
- Inside `show(t)` — on every node of `t`!
- Inside `freeIn(t, mut out)` — on every node of `t`, for every variable in every scope during `generalize`!
- Inside `copy(t, map)` — on every node of `t`!

Why did `resolve` return an owned `Type` (forcing `other.clone()`) instead of returning `readonly Type`?!
Look closely at what happens if you try to write:
```ts
function resolve(self: readonly Self, t: readonly Type): readonly Type from self, t {
  match (t) {
    #Var(v) => match (self.links[v]) {
      #Some(bound) => self.resolve(bound),
      #None => t, // <-- `t` is already a `readonly Type` that is `#Var(v)`!
    },
    _ => t,
  }
}
```
**Wait a second!**
In `resolve(self: readonly Self, t: readonly Type)`, when `t` matches `#Var(v)` and `self.links[v]` is `#None`, **`t` itself is already the `#Var(v)` you want to return, and `t` is a `readonly Type` parameter!**
You didn't need to construct a fresh `#Var(v)` or call `other.clone()` at all!
Look at that:
```ts
function resolve(self: readonly Self, t: readonly Type): readonly Type {
  match (t) {
    #Var(v) => match (self.links[v]) {
      #Some(bound) => self.resolve(bound),
      #None => t,
    },
    _ => t,
  }
}
```
Check `§4.2` (*Results carry their sources' borrows*):
> *"A call's result can hold the borrows of its sources: the parameters named in its `from` clause; without one, the receiver for a method and every borrowed argument for a free function."*
Wait: look at that sentence in `§4.2`!
**"without one [a `from` clause], the receiver for a method and every borrowed argument for a free function."**
STOP AND READ THAT AGAIN!
For a **method** (`function resolve(self: readonly Self, t: readonly Type): readonly Type`), if there is **no `from` clause**, `§4.2` says the result's default source is **only `self` ("the receiver for a method")**, NOT `t` ("and every borrowed argument for a free function")!
So in `function resolve(self: readonly Self, t: readonly Type): readonly Type`, if you don't write `from self, t`, returning `t` from a method is **rejected** because a method without `from` only ties its return value to `self`, not to its other borrowed parameters!
And in `unify(self: mut Self, a: readonly Type, b: readonly Type, span: Span)`:
If `resolve` returns `readonly Type from self, t`, then calling `self.resolve(a)` borrows `self` (`readonly`), which prevents `self.links[v] = #Some(t)` (mutating `self.links`) while the result of `self.resolve(a)` is still live!

**That is a major insight into how Flyscript's ownership interacts with compiler data structures:**
1. Because `Type` in `Mini` is a recursive heap tree (`#Fn(Vec<Type>, Box<Type>)`) stored *inside* `self.links: Vec<Option<Type>>`, borrowing a `Type` out of `self.links` locks `self.links` against mutation (`self.links[v] = ...` or `self.fresh()`).
2. In real compilers (rustc's `TyCtxt` / `Ty<'tcx>`, OCaml's `type_expr`, TypeScript's `Type`, Zig's `InternPool`), **types in a union-find / type checker are NEVER `Box<Type>` heap trees cloned by value!**
   Why? Because in Flyscript you have **two** zero-clone idiomatic ways to represent `Type` in a compiler:
   - **Way A (Indices / `TypeId = usize`, `Copy`):** Every `Type` is a `TypeId` (`usize`, which is `Copy` and class 1, holding **no borrow** of `self`!). `Types` holds `nodes: Vec<TypeNode>`. `self.resolve(id: TypeId): TypeId` returns a `usize` (`Copy`, locks nothing!), and can even do **path compression** (`self.links[v] = #Some(root)`) during `resolve`!
   - **Way B (Region `Ref<R, Type<R>>`, `Copy`):** Every `Type<R>` lives in the compilation region `R`:
     ```ts
     enum Type<region R> {
       #Int,
       #Bool,
       #Var(Cell<Option<Ref<Type>>>), // union-find link right in the Var node!
       #Fn(Ref<Ref<Type>[]>, Ref<Type>),
     }
     ```
     Wait: look at Way B with `Cell<R, Option<Ref<R, Type<R>>>>` (`§4.6`)!
     Is `Option<Ref<R, Type<R>>>` `Copy`?
     - `Ref<R, T>` is `Copy` (`§4.5`).
     - `Option<T>` is `Copy` when `T` is `Copy` (`§4.4`).
     - So `Cell<R, Option<Ref<R, Type<R>>>>` is **completely legal under `§4.6`** (`Cell<R, T>` requires `T extends Copy`)!
     - And `Ref<R, Type<R>>` is `Copy` and class 1 (`§4.2`, `§4.5`), so passing types around, storing them in `Scheme`, resolving `#Var(cell)` via `cell.get()`, and linking `#Var(cell)` via `cell.set(#Some(t))` (with path compression!) requires **zero `Clone`s, zero `Box`es, zero index tables, and zero borrow conflicts on `self`!**

Look at the contrast between `Mini`'s `Box<Type>` + `Vec<Option<Type>>` vs Flyscript's own `region (R)` + `Ref<Type>` + `Cell<Option<Ref<Type>>>`:
`Mini` didn't use regions (`§4.6`) at all! It wrote a Rust-101 `Box<Expr>` and `Box<Type>` compiler with `.clone()` everywhere, instead of using the exact feature (`region (R)` + `Ref` + `Cell` + `RegionList`) that Flyscript designed in `§4.6` and `A.5` for compilers!

---

#### 3. Where Regions (`§4.6`) shine in a compiler — and the ONE place they hit a wall at scale (`Question 2`)

Let's test what happens if you rewrite `Mini` (and then scale to `flyc`) using a region `region (R)`:
1. **Source strings & identifiers (`str` / `Ref<R, str>`):**
   In `Mini`:
   - `Tok` is `#Ident(String)` (`impl Clone for Tok`).
   - `Parser.peek` returns `readonly Tok`, so `Parser.ident()` has to do `#Ident(n) => n.clone()`, allocating a new heap `String` for every identifier in the AST!
   - Then `Checker` clones every variable name `String` into `scopes: Vec<HashMap<String, Scheme>>`!
   - Then `freeVars` clones every variable name `String` into `bound` and `out`!
   - Then `Gen` clones every variable name `String` into `locals` and `globals`!
   Wait: why did `Tok`, `Expr`, `Def`, `Checker`, and `Gen` use heap `String` for source identifiers when the source string `src: str` outlives the entire `compile(src: str)` call?!
   Even without regions, `src: str` is passed into `compile(src: str)`! Or with a region `R` (or interner), `Ref<R, str>` (or `Sym = u32`) is `Copy`!
   If identifiers are `Ref<R, str>` (or `Sym`), `Tok`, `Expr`, `Scheme`, `Checker`, and `Gen` **never clone a single string**!

2. **Now, where do Regions (`§4.6`) hit a wall in a real compiler (`flyc`)?**
   Look at `§4.6` Rule 2:
   > *"2. No owned resources. Region data contains only `Copy` values, `Ref`s, `Cell`s and `RegionList`s of the same region; this is checked wherever a value is placed in a region (`alloc`, `RegionList.push`). Nothing in a region needs a destructor, so releasing the arena is constant-time."*
   Now try to build `flyc`'s AST, `Type`, and `Scope` in `region (R)`:
   - In `Mini`, `#Fn(Vec<String>, Box<Expr>, Span)` and `#Call(Box<Expr>, Vec<Expr>, Span)` have `Vec<Expr>` (a list of child expressions) and `Type` has `#Fn(Vec<Type>, Box<Type>)`.
   - If `Expr<R>` and `Type<R>` live in `region (R)`, they **cannot contain `Vec<T>`** (because `Vec<T>` owns heap memory and has `Drop`, violating Rule 2 of `§4.6`!).
   - Instead, in `region (R)`, a node with children uses `RegionList<R, Ref<R, Expr<R>>>` (as `Json<R>` does in `A.1`: `#Arr(RegionList<Ref<Json>>)`).
   - **Look at what `RegionList<R, T>` (`§4.6`) has and what it is MISSING:**
     In `§4.6`:
     ```ts
     impl<region R, T> RegionList<R, T> {
       export function new(): RegionList<R, T> uses Region<R>;
       export function push(self: Self, v: T): void uses Region<R>;
       export function len(self: Self): usize;
     }
     impl<region R, T> Iterable<readonly T> for RegionList<R, T> { … }
     ```
     **Look closely at `RegionList<R, T>` in `§4.6`:**
     1. **Can you index a `RegionList<R, T>` (`list[i]`)?!**
        `§3.1` says: *"Indexing an array, a slice or a `Vec` (`xs[i]`) is a place of the element type"*. It does **not** include `RegionList`!
        In `Mini`, `unify` indexes `ps[i]` and `qs[i]`, `Checker.program` indexes `own[i]`, `Parser` indexes `self.toks[self.pos]`. If `ps` is a `RegionList<R, Ref<Type>>`, you cannot even write `ps[i]` or `ps.iter().zip(qs.iter())` (unless `xs.iter()` works on any `Iterable`, which `§5.5` says it does, or `RegionList` supports indexing `list[i]`)!
     2. **Does `RegionList` implement `Eq`, `Hash`, `Ord`, `Show`, `Clone`?**
        In `Type.info(T)` (`§7.2`), `RegionList` is `#Opaque`, so the prelude derivations (`§3.5`) don't see inside it unless `RegionList` implements `Eq`, `Hash`, `Ord`, `Show`!
     3. **Can you allocate a fixed slice `Ref<R, T[]>` in a region from a `Vec` or iterator (`allocSlice`)?**
        In a compiler, once the parser parses `args: Vec<Ref<Expr>>` or `params: Vec<Ref<str>>`, the list of arguments of a `#Call` node is **fixed forever** — it never grows again! Storing a growable `RegionList` header in every AST node when a flat `Ref<R, T[]>` (allocated once in the region from a slice/vec) supports O(1) indexing `args[i]`, slicing, and all slice methods (`§3.1`) is much simpler and faster.

---

#### 4. Error recovery and accumulating diagnostics at scale (`Question 2`) — **Effect system shines, if you use `effect Diag` instead of `Fail`**

In `Mini`, `CompileError` uses `Fail<CompileError>` (`throw #Type { ... }`).
That aborts the entire compiler on the **first** type error (`let f = fn(x) => x + 1 in f(true)`).
In a real compiler (`flyc`, TypeScript, rustc), aborting on the first type error is unacceptable: an IDE or CLI user wants to see **all** type errors in the file/module, with poison/error types (`#Error`) preventing cascading errors.

How does Flyscript handle error recovery and diagnostic accumulation?
**Law 4 (`§5.2` Resumptive handlers) makes Flyscript uniquely great at this — without changing the language!**
Look:
```ts
effect Diag {
  report(err: CompileError): void;
}
```
In the parser and type checker:
- When a non-fatal error occurs, call `Diag.report(#Type { span, message })` and return ` Type.#Error` (an error type that unifies silently with anything)!
- Only fatal syntax errors (or a bailout threshold) use `Fail`.
- At the top level (`compile`), a 3-line resumptive handler collects all diagnostics into a `Vec<CompileError>` (or caps them at 20 and aborts!):
  ```ts
  let errors: Vec<CompileError> = Vec.new();
  const result = handle {
    checkModule(ast)
  } with Diag {
    report(e) resumes k => {
      errors.push(e);
      if (errors.len() < 50) { k() } else { #Aborted }
    }
  };
  ```
Look at that: a resumptive handler can **both** accumulate diagnostics and **abort** after 50 errors by simply dropping `k`! That is a textbook validation of Law 4 (`§5.2`–`§5.3`) for compiler architecture.

---

#### 5. Parallel compilation and the `Io.scope` outer-region freeze (`§4.6`, `§6.1`, `§6.5`) — **Language problem at scale**

In `§8.1`:
> *"The import graph must be acyclic, so modules compile in parallel in dependency order."*
Now suppose `flyc` compiles a dependency level of modules in parallel, or checks the functions of a module in parallel.
How does `flyc` run work in parallel?
 Flyscript has two concurrency/parallelism mechanisms:
1. `Io.scope((s) => { s.fork(() => ...); })` (`§6.1`)
2. `par` / `parReduce` (`§6.5`)

Now look at what happens when `flyc` tries to check 100 functions (or 20 modules at the same DAG rank) in parallel, where the parsed AST or resolved module signatures live in a `region (R)`:
- Suppose `region (R)` holds the immutable parsed AST and module exports (`Ref<R, ModuleAst>`).
- Can `parReduce` (`§6.5`) run type-checking over `functions: readonly FunctionAst[]` in parallel?
  Wait: `parReduce` takes `one: (v: C.ReadView, i: usize) => A` with **no `uses` clause** (pure!).
  And `§5.1` says: *"A function with no `uses` clause is pure: it may allocate on the heap, open and use its own regions, and mutate its `mut` parameters"*.
  And is `Ref<R, T>` `Send`?
  Yes! `§4.6` says: *"an outer region is frozen while it is shared, so every `Ref<R, T>` is `Send`."*
  **Wait**: what if `one` inside `parReduce` reads a `Cell<R, T>` in the outer region `R`? It can't, because `Cell.get` performs `Region<R>` (`§4.6`), and `one` has no `uses` clause!
  What if a worker in `Io.scope` (`s.fork(...)`) wants to read the outer region `R`?
  Look at `§4.6`:
  - Reading a `Ref<R, T>` or iterating/reading existing elements of `RegionList<R, T>` is **pure** (does not perform `Region<R>`)!
  - Reading a `Cell<R, T>` (`cell.get()`) **performs `Region<R>`** (`§4.6`), which a forked task **cannot perform** (`§6.1` Rule 4: *"its effects are `Io` and `Fail` and nothing else"*)!
  This means: if your AST / symbol table uses `Ref<R, T>` and `RegionList<R, T>`, parallel tasks in `Io.scope` and workers in `parReduce` **can** read it concurrently with zero copying, **as long as** anything read during the parallel phase is stored in `Ref<R, T>` or `RegionList<R, T>`, not `Cell<R, T>` (or each function's union-find table is in its own inner `region (R_fn)` opened inside the worker!).
  That actually works — **except** for one missing method on `RegionList<R, T>`: `RegionList` has `.len()` and `Iterable`, but no `list[i]` (random-access read) and no `ParSplit` impl!

---

#### 6. Line-by-line issues in `Mini` (`Question 1`)

Here is the exact classification of every awkward spot in `Mini`:

| Line(s) in `Mini` | What is awkward | Category | Fix |
| :--- | :--- | :--- | :--- |
| **L45** `src.slice(start, i)` and **L397** `src.slice(lineStart, lineEnd)` | `§3.1` defines `s[a..b]` as string slicing and also lists `slice` from TS; `Mini` uses `src.slice(a, b)` while `A.1` and `§10.2` use `raw[0..8]`. | Style (both work) | Prefer `src[start..i]` or keep both. |
| **L83–88** `Parser.peek` returns `readonly Tok`, then **L94** `#Ident(n) => n.clone()` | Every identifier token is heap-allocated as `String` in `lex`, then cloned in `Parser.ident()`, cloned into `scopes`, cloned into `freeVars`, cloned into `Gen.locals`. | Style + Library | Either `Tok<region R>` / `Ref<R, str>`, or an `Interner` (`Sym = u32`, `Copy`), or `view struct Parser` over `src: str` where `#Ident(str)` is `Copy`!Wait: `str` is `Copy` (`§4.1`)! If `Tok` is `view enum Tok { #Ident(str), ... }`, `Tok` is `Copy` and `lex` allocates **zero** `String`s! |
| **L95, 118, 170, 181** `"expected a name".toString()` | Every constant error message in `CompileError` has to call `.toString()` to convert a `"…"` literal (`str`) into `String` because other errors use `` `expected ${what}` `` (`String`). | Library / Ergonomics | Either `String` literal/conversion ergonomics, or in a compiler with `src: str` / `region (R)`, error messages use `Ref<R, str>` (`fmt(...)` for interpolated, `alloc("...")` or `Ref<str>` for static). |
| **L142–150** `Types.resolve` calls `other.clone()` | Deep-clones `#Fn(Vec<Type>, Box<Type>)` on every `resolve` call in `occurs`, `unify`, `show`, `freeIn`, `copy`. | Style + Language (`§4.2` method `from` rule) | Represent `Type` in `Types` by `TypeId = usize` (`Copy`) into an arena `Vec<TypeNode>`, or in `region (R)` as `Ref<R, Type<R>>` (`Copy`). |
| **L167–168** `let i: usize = 0; while (i < ps.len()) { self.unify(ps[i], qs[i], span); i += 1; }` | Manual index loop instead of `for (const [p, q] of ps.iter().zip(qs.iter())) { self.unify(p, q, span); }`. Why? Did `ps.iter().zip(qs.iter())` lock `self` or fail to infer? No, `ps` and `qs` are owned locals destructured from `[x, y]`! | Style | `for (const [p, q] of ps.iter().zip(qs.iter())) { self.unify(p, q, span); }` (which `A.3` already shows!). |
| **L174** `ps.iter().map((p) => self.show(p)).collect().join(", ")` | Has to `.collect()` into a temporary `Vec<String>` just to `.join(", ")` because `join` is on slices/`Vec` (`§3.1`), not on `Gen` (`§5.5`). | Library gap (`§5.5`) | Add `join(sep: str): String` to `Gen` in `§5.5`, so `.map(...).join(", ")` needs no `.collect()`! |
| **L206** `match (self.scopes[i].get(name)) { #Some(s) => #Some({ vars: s.vars.clone(), ty: s.ty.clone() }), #None => #None }` | Two problems: (1) couldn't hold `s: readonly Scheme` across `self.instantiate(s)` because `instantiate` takes `mut self` (locking all of `Checker`), and (2) couldn't even write `self.scopes[i].get(name).cloned()`! | **Language (`§4.1` disjoint field borrows) + Prelude bug (`Option.cloned`)** | Fix disjoint field borrows (`self.types.instantiate(s)` while `self.scopes` is borrowed) + ensure `Option<readonly T>.cloned()` works for any `T extends Clone` (including structural records). |
| **L221–229** `inEnv: Vec<usize>`, `!s.vars.includes(v) && !inEnv.includes(v)` and **L296–306** `bound: Vec<String>`, `out: Vec<String>` | Linear `Vec.includes` scans for set membership and manual `bound.push` / `bound.pop` stack management because there is no `HashSet<T>` in `std/collections`, or `HashMap<T, void>`. | Library gap (`§3.1`) | Add `HashSet<T>` to `std/collections` (or use `HashMap<usize, bool>`). |
| **L324–332** `inner.code = self.code.drain().collect(); ... self.code = inner.code.drain().collect();` | Drains and reallocates the entire bytecode `Vec<Instr>` twice for every `#Fn` node just to compile a lambda body with a different `locals: Vec<String>`! | Style + **Language (`§4.1` disjoint field borrows)** | `code: Vec<Instr>` is shared across the whole module, while `locals: Vec<String>` is per-function! Either pass `mut locals: Vec<String>` to `self.gen(e, mut locals)`, or temporarily swap `self.locals` (`mem.replace` / `mem.swap`), or split `Emitter { code }` from `FnScope { locals, globals }`! |
| **L361–363** `for (const _ of 0..n) { caps.push(#Int(0)); } let i = n; while (i > 0) { i -= 1; caps[i] = stack.pop().unwrap(); }` | Fills `caps` with dummy `#Int(0)` values just to pop `n` items in reverse order, whereas 8 lines later (**L369–371**) `Call` writes `for (const _ of 0..n) { args.push(stack.pop().unwrap()); } args.reverse();`! | Style | Use `caps.push(stack.pop().unwrap());` + `caps.reverse();` just like L370. |

---

### Question 3: The Three Most Valuable Changes for Compiler Writing (Ranked, with Spec Text)

#### 1. Disjoint Field Borrowing (`§4.1`)

**Why this is #1 for compilers:**
A compiler's state (parser state, type-checker context, IR builder, codegen state) is always a struct with 4–10 fields (`types`, `scopes`, `defs`, `interner`, `diags`, `code`). Almost every operation reads from one field (e.g. `self.scopes` or `self.defs`) while mutating another field (e.g. `self.types`, `self.code`, or `self.diags`), or passes `self.a` and `mut self.b` to a helper function. Without path-sensitive disjoint field borrows in `§4.1`, the programmer is forced to `.clone()` data out of `self.a` before calling a method on `mut self.b` (as happened in `Checker.lookup` and `Gen.gen` in `Mini`).

**What it removes / adds:**
- **Removes:** unnecessary `.clone()` and `.drain().collect()` workarounds when accessing multiple fields of the same struct/record/tuple.
- **Adds:** no new syntax or concepts — `§9` already defines Γ as locking *paths*, and `§4.1` already tracks per-field moves! Making `§4.1`'s borrow ledger track field paths (`x.f` vs `x.g`, `t[0]` vs `t[1]`) brings borrows in line with moves.

**Concrete spec text for `§4.1` (after the first paragraph on field moves, or in the paragraph on loans):**
> *"Borrows, like moves, are tracked per field path: borrowing `x.f` (or a tuple's `t[0]`) locks `x.f` and prevents moving or mutably borrowing `x` as a whole, while leaving `x`'s other fields free to be moved or borrowed (`readonly` or `mut`) at the same time. Indexing a collection (`xs[i]`), by contrast, borrows the whole collection."*

---

#### 2. Region Ergonomics for ASTs & IRs: Indexing `RegionList` (`list[i]`) and `allocSlice` (`§3.1`, `§4.6`)

**Why this is #2 for compilers:**
Flyscript's `region (R)` (`§4.6`) is its flagship answer to how a GC-free language builds cyclic ASTs, symbol tables (`A.5`), and type graphs without `Box` or `Clone` noise. Yet `Mini` avoided `region (R)` completely!
Why? Because in `§4.6`:
1. A recursive AST (`Expr`) or type (`Type`) in a region cannot hold `Vec<T>` (Rule 2: no owned heap resources in a region); it must hold `RegionList<R, T>` or `Ref<R, T[]>`.
2. But `RegionList<R, T>` in `§4.6` **cannot be indexed with `list[i]`** (only iterated with `for…of`), and has no `Eq`/`Show` derivation, while `alloc` only allocates a single value `Ref<R, T>`, not a slice `Ref<R, T[]>`!
In a compiler (`unify` checking `ps[i]` vs `qs[i]`, `Checker.program` indexing `own[i]`, bytecode jumps `code[pc]`), random-access indexing `xs[i]` on region-allocated lists is essential.

**What it removes / adds:**
- **Removes:** the pressure to fall back to heap `Vec<T>` + `Box<T>` + `.clone()` (as `Mini` did) instead of regions.
- **Adds:** random-access indexing `list[i]` (and `Eq`/`Show` when `T` has them) on `RegionList<R, T>` in `§3.1` / `§4.6`.

**Concrete spec text:**
- In **`§3.1` (Primitives, strings, arrays, final paragraph)**:
  > *"Indexing an array, a slice, a `Vec` or a `RegionList` (`xs[i]`) is a place of the element type, checked against the length at run time (a panic out of bounds)..."*
- In **`§4.6` (Regions)**:
  > *"`RegionList<R, T>` is indexed with `list[i]` (which is pure, since existing elements never move or change) and implements `Eq`, `Ord`, `Hash` and `Show` when `T` does."*

Look at how `Mini`'s `Type` and `Types` look with this:
```ts
enum Type<region R> {
  #Int,
  #Bool,
  #Var(Cell<Option<Ref<Type>>>),
  #Fn(RegionList<Ref<Type>>, Ref<Type>),
}
```
Now `Type<R>` is allocated in `region (R)`, `Ref<Type>` is `Copy` (8 bytes, no `Box`, no `.clone()`), `#Var` holds its own union-find `Cell` directly (no separate `links` table!), and `ps[i]` indexes the parameter list in O(1) time!

---

#### 3. Library & Prelude Completeness for Compilers: `HashSet<T>`, `Gen.join`, `Option<readonly T>.cloned()` on all `Clone` types, and `mem.swap` (`§3.1`, `§3.2`, `§5.5`)

**Why this is #3 for compilers:**
Every remaining pain point in `Mini` came from small standard-library gaps that force manual loops or clones in compiler passes:
1. **`HashSet<T>` (`std/collections`, `§3.1`):** Compilers constantly compute free variable sets (`freeVars`, `generalize`), visited node sets, and exported symbol sets. In `Mini` (L186, L221–229, L296–306), you had to use `Vec<usize>` and `Vec<String>` with O(N²) `!vec.includes(x)` scans.
2. **`Gen.join(sep: str): String` (`§5.5`):** Compilers constantly format comma-separated parameter lists, argument types, and paths. In `Mini` (L174), `ps.iter().map((p) => self.show(p)).collect().join(", ")` had to allocate a temporary `Vec<String>` via `.collect()` just to join an iterator of strings.
3. **`Option<readonly T>.cloned()` on structural records (`§3.2`, `§3.5`):** In `Mini` (L206), `self.scopes[i].get(name)` returned `Option<readonly Scheme>`, and instead of `.cloned()`, you had to pattern-match and clone each field manually (`#Some(s) => #Some({ vars: s.vars.clone(), ty: s.ty.clone() })`).

**Concrete spec text:**
- In **`§3.1` (Primitives, strings, arrays)**:
  > *"`HashSet<T>` (in `std/collections`, where `T` is `Eq` and `Hash`) has `new`, `insert`, `has`, `remove` (looked up by anything `T` lends), `len`, ` isEmpty`, `clear`, and the generator `iter()`; it is `Clone` when `T` is."*
- In **`§5.5` (Iteration: `yield` and `for…of`)**:
  > *"A `Gen<T, E>` has `next()`, the lazy adaptors `map`, `filter`, `take`, `zip` and `enumerate`, `collect()` into a `Vec`, `join(sep)` (each item shown, strings as they are), and, under TypeScript's names, `find`, `some`, `every` and `reduce((acc, x) => …, init)`; a `Gen<readonly T, E>` also has `cloned()`, which gives owned copies of any `Clone` element."*

---

### Smaller points

- **String literals when a `String` is expected (`Mini` L95, L118, L170, L181):**
  Notice how in `Mini`, every non-interpolated error message had to write `"expected a name".toString()` while interpolated ones wrote `` `expected ${what}` ``. Of course, writing `` `expected a name` `` (with backticks!) already has type `String` (`§2.2`: *"templates `` `…${e}…` ``, which build a `String`"*), so `` `expected a name` `` in `Mini` avoids `.toString()` with zero language changes! (Make sure the parser/checker allows a template literal `` `…` `` with zero `${…}` interpolations to have type `String`, as `§2.2` implies.)
- **Default source for methods returning a borrow (`§4.2`):**
  In `§4.2`, *"without one [a `from` clause], the receiver for a method and every borrowed argument for a free function."* Keep this rule in mind when writing compiler helper methods like `Types.resolve(self: readonly Self, t: readonly Type): readonly Type from self, t` — if a method can return one of its borrowed arguments (not just `self`), it needs `from self, t` (or a diagnostic hint that suggests adding `from self, t` when a method returns a borrowed parameter `t`). Make sure `flyc`'s error message when returning a borrowed non-`self` parameter from a method without `from` explicitly suggests `from self, t`!
