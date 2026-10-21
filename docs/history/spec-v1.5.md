# Flyscript Language Specification (v1.5 — Complete Consolidated Specification, Part 1 of 3)

File extension: `.fly`

**Changelog (v0.1 $\to$ v1.5):** Evolved from an initial Rust-syntax sketch (v0.1) to a TypeScript-surface specification (v0.2–v1.0), unified around a four-pillar core of affine ownership, one row calculus, effect handlers, and `comptime` type functions (v1.1–v1.4), and finalized in v1.5 with **universal second-class propagation across all nominal and structural types**, **transparent non-rebindable borrows** (eliminating `*slot`), **deep-handler effect forwarding and Scope-owned vs. Generator-owned continuation lifecycles**, **single-region elision (`Ref<T>`, `RegionList<T>`)**, and **call-wide polymorphic numeric literal inference**.

---

## 0. What Changed in v1.5 & Concept-Count Reduction

### 0.1 What Changed in v1.5
1. **Universal Second-Class Propagation Across All Types (Nominal and Structural):** Replaced the ban on second-class components inside nominal `struct`/`enum` definitions and generic containers with a single, uniform classification function across the entire type algebra: **$\text{class}(\tau) = \max_i \text{class}(\tau_i)$ over all field types, variant payloads, and generic type arguments.** Consequently, `Option<mut u64>`, `Result<readonly T, E>`, and `struct Scanner { src: readonly u8[]; pos: usize; }` are completely legal **second-class types** ($\text{class} = 2$). Only one invariant governs them: a second-class value cannot escape its lexical borrow scope (it cannot be stored inside a $\text{class} = 1$ heap container, captured by an escaping closure, sent across fibers via `Send`, or returned without tying via `from param`).
2. **Transparent Borrows (No `*` Dereference Operator):** Borrow bindings (`slot: mut u64` or `p: readonly Point`) behave transparently like the value they reference (as in Hylo `inout` or C++ references). Reading `slot` reads the referent; writing `slot += 1` or `slot = 5` mutates the referent in place through a `mut` borrow; borrow bindings cannot be re-pointed after initialization. Raw FFI pointers (`T*`) use explicit `unsafe` methods (`ptr.read()`, `ptr.write(v)`, `ptr.add(i)`), removing the `*` prefix operator from the language completely.
3. **Continuation Ownership Split (`Gen<T>` Owns, `Scope` Owns `Fiber<T>`) & Deep-Handler Effect Forwarding:**
   * Both `Gen<T, E>` and `Fiber<T, E>` wrap the same runtime primitive (a suspended stackful fiber segment `Cont<In, Out, E>`), but have distinct ownership: **`Gen<T, E>` uniquely owns its continuation** (so dropping `Gen<T, E>` unwinds the suspended generator and runs its `defer`/`Drop` cleanups), whereas **a spawned concurrent fiber is owned by its enclosing `Scope<E>`** (`s.spawn(...)` returns a lightweight `Fiber<T, E>` join handle whose drop merely detaches the handle while the `Scope` still awaits or cancels the fiber before `Io.scope` exits).
   * Stored continuations use **deep-handler semantics**: when `g.next()` resumes a `Gen<T, E>`, the `Yield<T>` handler stays installed at the root of the generator segment, while any other effect `E` performed inside the generator (`Io`, `Fail<Err>`, `Region<R>`) forwards dynamically to the handlers active at the `g.next()` call site.
4. **Region Parameter Elision (`Ref<T>`, `RegionList<T>`):** Inside any `struct`, `enum`, `type`, `impl`, or `function` declaration that has **exactly one** `<region R>` parameter in scope (or inside a single `region (R) { ... }` block), writing `Ref<T>`, `RegionList<T>`, or a single-region generic `Json` elides the region argument and supplies `R` automatically.
5. **Grammar & Inference Refinements:**
   * Added inline record payloads to variant tags (`#Get { key: String; reply: ReplyPort }` alongside `#Tag(Type)`).
   * Removed the region-value argument from `Region.fmt(`...`)` (which now uses `uses Region<R>` like all other region operations).
   * Specified **call-wide bidirectional constraint solving** before numeric literal defaulting, so `parReduce(slice, 0.0, (p, _i) => ...)` infers `0.0: f32` from the sibling closure arguments without needing `0.0 as f32`.

### 0.2 Concept-Count Reduction Table: v1.0 vs. v1.5

| Concept / Mechanism in v1.0 | Status in v1.5 | How v1.5 Unifies It |
| :--- | :--- | :--- |
| 1. Separate `struct`/`enum` syntax vs structural `{...}` and `[ #Tag ]` | **Unified into 1 Product & 1 Sum System** | `#Tag` syntax (with tuple or `{...}` record payloads) everywhere. `struct` and `enum` are nominal wrappers over record/variant rows; methods live in `impl`. |
| 2. Dual error model (`Result` + `Fail` + `From` + `try...else` + `@mustUse` `ignore`) | **Unified into `Fail<VariantRow>`** | Implicitly open `uses Fail<[ #Tag1 \| #Tag2 ]>` composes by automatic row union. `Result` is just `Fail.capture(...)`. |
| 3. Five effects (`Io`, `Fail`, `Alloc`, `Yield`, `Shared`) + `Async.scope` vs `Io.runScope` | **Reduced to 4 Standard Effects** | **`Fail<E>`**, **`Io`** (includes locks/channels/atomics & `Io.scope`), **`Yield<T>`**, and **`Region<R>`** (heap allocation is unobservable). |
| 4. Three handler arm kinds (`resumes`, abortive, `return(v)`, `finally`) | **Reduced to 1 Arm Form + `defer`** | Handler arms are `op(args) [resumes k] => body`. `return(v)` and `finally` arms are replaced by lexical `defer expr;`. |
| 5. Push-only `Yield<T>` vs Pull `Iterator` + separate `Fiber<T>` | **Unified by Affine `Cont<In, Out, E>`** | Deep-handled one-shot continuations unify push streams (`Yield<T>`), pull generators (`Gen<T>`), and `Scope`-owned tasks (`Fiber<T>`). |
| 6. Mutable `In<R, T>` + `Region<R>` value API + verbose `<R>` repetition | **Replaced by Append-Only `Ref<R, T>` + `Cell<T>` + `RegionList<T, R>` + Region Elision** | `Ref<R, T>` is immutable; only `Cell<T extends Copy>` and append-only `RegionList<T, R>` mutate via `uses Region<R>`. Single-region declarations elide `R`. |
| 7. Five Marker Traits (`Pod`, `Send`, `Sync`, `val`, `Drop`) + special borrow bans | **Reduced to 3 (`Copy`, `Send`, `Drop`) + Universal $\text{class}(\tau) \in \{1, 2\}$** | Second-classness propagates uniformly through `Option<mut T>`, `Scanner`, and view records. `Send` requires $\text{class}(\tau) = 1$ and covers `Sync`. |
| 8. `par for` keyword + `@layout(soa)` + `SoaSlice<T>` + integer refinement solver | **Replaced by library `par`/`parReduce` + `comptime` `Soa<T>`** | Propagating second-class view types + `comptime` recursive flattening express `Soa<T>` and parallel loops in library code. |

---

## 1. Goals and Non-Goals

### 1.1 Goals
1. **TypeScript surface, systems semantics:** Familiar syntax for developers who read TypeScript (`function`, `(x) => expr`, `const`/`let`, `<T extends U>`, `{ field: value }`, `#Tag`, `interface`, `impl`, `type`, ES modules) compiled ahead-of-time to native machine code (`x86_64`, `aarch64`) and WebAssembly (`wasm32`) with unboxed layouts and deterministic destruction.
2. **One product system and one sum system over a unified row calculus:** Anonymous records `{ x: f64; y: f64 }` and polymorphic variants `[ #Ok(T) | #Err(E) ]` are structural and support row polymorphism (`<row R>`). Nominal `struct` and `enum` declarations wrap a record or variant row with a generative type identity for module privacy, iso-recursion, `@layout(c | packed)`, and `Drop`.
3. **Static affine ownership with universal second-class view propagation:** Every heap allocation (`Box<T>`, `Vec<T>`, `String`, `HashMap<K, V>`) is a first-class value ($\text{class} = 1$) with a single unique owner. Borrows (`readonly T`, `mut T`, `str`, `T[]`) and any record, tuple, `struct`, or `enum` containing them (`Option<mut T>`, `Scanner`) are **second-class views ($\text{class} = 2$)** restricted to lexical scopes—eliminating `'a` lifetime annotations while allowing rich composite views.
4. **Append-only immutable regions with effect-gated `Cell` and `RegionList`:** Lexical regions (`region (R) { ... }`) handle the fiber-local `Region<R>` effect. Region pointers `Ref<R, T>` are `Copy` and point to immutable data; intra-region mutation occurs exclusively through unborrowable `Cell<T extends Copy>` slots and append-only `RegionList<T, R>` collections via `uses Region<R>`.
5. **Four standard effects (`Fail<E>`, `Io`, `Yield<T>`, `Region<R>`) with first-class one-shot continuations:** Delimited continuations (`Cont<In, Out, E>`) are affine values with deep-handler semantics, unifying push iteration (`Yield<T>`), pull generators (`Gen<T>`), and concurrent tasks (`Fiber<T>`), while enabling deterministic simulation testing by handling `Io`.
6. **Compile-time execution in the host language:** Generics, structural trait derivation (`Eq`, `Hash`, `Show`, `Clone`), and recursive `Soa<T>` layout flattening are ordinary Flyscript functions evaluated at `comptime`.

### 1.2 Non-Goals
1. **Width subtyping on structural records:** Handled statically via monomorphized row polymorphism (`<row R>`) so field offsets are always compile-time constants.
2. **Garbage collection:** No global or actor-local tracing garbage collector.
3. **Multi-shot continuations:** Continuations are strictly affine (resumed at most once; dropping a continuation unwinds its suspended frame).
4. **Equi-recursive structural types, integer refinement solvers, or automatic GPU lowering in v1:** Recursive types must go through nominal `struct` or `enum` declarations (iso-recursive); linear integer refinements and GPU kernel lowering are deferred to post-v1 work.

---

## 2. Core Design Decisions and Rationales

1. **Universal Second-Class Propagation ($\text{class}(\tau) \in \{1, 2\}$):**
   * Base second-class types ($\text{class} = 2$) are `readonly T`, `mut T`, `str`, `T[]`, `Grid2D<T>`, `Grid3D<T>`, and closures/continuations that capture second-class bindings.
   * Base first-class types ($\text{class} = 1$) are scalars, `Ref<R, T>`, `Arc<T>`, `T*`, and owned heap allocations (`Box<T>`, `Vec<T>`, `String`, `HashMap<K, V>`, `Pool<T>`), whose element type parameters require $\text{class}(T) = 1$.
   * **Uniform Propagation Rule:** For *any* composite type—whether a structural record `{ f_i: T_i }`, tuple `[T_i]`, polymorphic variant `[ #Tag(T_i) ]`, or nominal `struct S<T_i>` / `enum E<T_i>`—its class is $\text{class}(\tau) = \max_i \text{class}(T_i)$ over all its fields, variant payloads, and type arguments.
   * Thus `Option<mut u64>`, `Result<readonly Profile, Err>`, `struct Scanner { src: readonly u8[]; pos: usize; }`, and `ParticleView` are all valid $\text{class} = 2$ types without a single lifetime parameter (`'a`).
   * **The Single Escape Boundary:** A $\text{class} = 2$ type may appear only as a function parameter, a local variable binding, or a function return type tied via `from param`. It cannot be stored in a field of a $\text{class} = 1$ type, cannot instantiate a heap container (`Vec<T>`, `Box<T>`, `Arc<T>`, `RegionList<T, R>`), cannot satisfy `Send`, and cannot be captured by an escaping closure.
   * *Rationale:* Makes `Option<mut T>` from `HashMap.getMut` and helper structs holding slices (`Scanner`) work naturally under one rule instead of fighting a nominal-vs-structural split.

2. **Transparent Borrows (No Dereference Operator `*`):**
   * A binding `x` of type `mut T` or `readonly T` (whether a parameter or a local extracted from `match (map.getMut(k)) { #Some(slot) => ... }`) is **transparent**:
     * Evaluating `slot` in expression position reads the borrowed `T`.
     * Executing `slot = newVal` or `slot += 1` (when `slot: mut T`) writes `newVal` directly into the borrowed storage location.
     * Borrow bindings cannot be re-seated to point to a different location after binding.
   * Raw pointers `T*` have no `*` operator; they are manipulated exclusively inside `unsafe { ... }` via `ptr.read()`, `ptr.write(val)`, and `ptr.offset(isize)`.
   * *Rationale:* Matches TypeScript/Hylo syntax where `*slot += 1` is foreign, and avoids ambiguity between pointer re-assignment and referent mutation.

3. **Pointer Taxonomy Organized by One Principle:**

   | Pointer / Handle | Class | Scope & Lifetime | Aliasing | Mutability |
   | :--- | :--- | :--- | :--- | :--- |
   | **`Box<T>`** (`Vec<T>`, `String`) | 1st | Heap (unique owner) | Unique (affine move) | Mutable by owner (`let`) or `mut T` borrow |
   | **`Ref<R, T>`** | 1st | Lexical `region (R)` | `Copy` (shared in `R`) | **Immutable fields**; interior writes only via `Cell<U>` / `RegionList<U, R>` (`uses Region<R>`) |
   | **`Arc<T>`** (`T extends Send`) | 1st | Heap (atomic RC across tasks) | Shared (`Arc.clone`) | **Immutable** (synchronization requires `Mutex<U>` / `Atomic*` via `uses Io`) |
   | **`readonly T` / `mut T`** | 2nd | Lexical borrow scope | Shared (`readonly`) or Unique (`mut`) | `readonly` is 100% immutable under `uses []`; `mut` is exclusively mutable |

   Long-lived cyclic graphs outside a lexical region use library `Pool<T>` and `Handle<T>` (`{ index: u32; generation: u32 }`) built on `Vec<T>`.
   * *Rationale:* Guarantees that no aliasable reference (`Ref<R, T>`, `Arc<T>`, `readonly T`) can ever reallocate or invalidate an active borrow.

4. **Append-Only Regions (`Ref<R, T>`, `Cell<T>`, `RegionList<T, R>`), `Region<R>` Effect, and Region Elision:**
   * Heap allocation (`Box.new`, `Vec.new`, `String.new`) uses the global allocator and is observationally pure (`uses []`).
   * Region allocation and region mutation perform the fiber-local **`Region<R>`** effect, handled lexically by `region (R) { ... }`:
     * `Region.alloc<R, T>(val: T): Ref<R, T> uses Region<R>` allocates `val` in `R` (requiring `T` to be **Region-Storable**: $\text{class}(T) = 1$, containing only `Copy` primitives, `Ref<R, U>`, `Cell<U>`, or `RegionList<U, R>`—never heap-owned `Box`/`Vec`/`String` or `Drop` types).
     * `Cell<T extends Copy>` is unborrowable: `cell.get(): T uses Region<R>` copies `T` out; `cell.set(val: T): void uses Region<R>` writes `T` in.
     * `RegionList<T, R>` is an append-only chunked list: `RegionList.push(list, val)` (`uses Region<R>`) appends without ever moving prior elements, so `list.iter()` and `list.get(i)` are pure (`uses []`) and never invalidated by subsequent pushes.
   * **Single-Region Elision Rule:** Inside any declaration (`struct`, `enum`, `type`, `impl`, or `function`) that declares **exactly one** `<region R>` parameter in scope (or directly inside a `region (R)` block with one active region), writing `Ref<T>`, `RegionList<T>`, or a single-region nominal type `Json` without a region argument automatically supplies `R`.
   * *Rationale:* Eliminates both Problem A (aliasing unsoundness) and visual `<R>` noise in recursive arena data structures.

5. **First-Class Continuations (`Cont`), Deep-Handler Forwarding, and `Gen<T>` vs. `Fiber<T>` Ownership:**
   * **Deep-Handler Forwarding:** A `handle { body } with Eff { ... }` block installs a **deep handler**: when a captured continuation `k: Cont<In, Out, E>` is resumed later (e.g., inside `g.next()`), the `Eff` handler remains installed at the bottom of `k`'s delimited stack segment, while any other effect in `E` (`Io`, `Fail<Err>`, `Region<R>`) performed by the resumed computation forwards dynamically to the handlers enclosing the **`k.resume(...)` call site**.
   * **Ownership Split (`Gen<T, E>` vs. `Fiber<T, E>`):**
     * **Pull Generator (`Gen<T, E>`):** Uniquely owns its suspended `Cont<void, Step<T, E>, E>`. Calling `g.next(): Option<T> uses ...E` resumes it; dropping `g` before exhaustion drops the continuation, which immediately unwinds the generator's stack segment and runs all its `defer` and `Drop` cleanups.
     * **Concurrent Fiber (`Fiber<T, E>`):** Created by `s.spawn(once () => ...)` inside `Io.scope((s) => ...)`. **The `Scope` owns the running fiber**; `s.spawn` returns a `Fiber<T, E>` join handle. Calling `f.join(): T uses Io, ...E` awaits its result; dropping `f` without calling `.join()` (as in `const _ = s.spawn(...)` in a server accept loop) **detaches the handle without cancelling the fiber**—the `Scope` continues running the fiber and deterministically awaits all spawned fibers (or cancels them on sibling unhandled `Fail`) before `Io.scope` exits.
   * *Rationale:* Solves the collision between generator cleanup-on-drop and fire-and-forget server tasks while keeping both structured and leak-free.

6. **Four Standard Effects (`Fail<E>`, `Io`, `Yield<T>`, `Region<R>`) and Implicitly Open `Fail` Rows:**
   * `Fail<[ #Tag1 | #Tag2 ]>` in function signatures is **implicitly open** (`[ #Tag1 | #Tag2 | ..._e ]`), composing across calls by automatic row union.
   * Exported functions (`export function`) and `interface` methods annotate `uses` explicitly; non-exported module-private functions and closures infer `uses` automatically.

7. **Call-Wide Bidirectional Inference Before Numeric Literal Defaulting:**
   * Type inference for a function call `f(arg_1, ..., arg_n)` collects unification constraints across **all** arguments `arg_1 .. arg_n` and the expected return type before applying the fallback scalar defaults (`i32` for integer literals, `f64` for float literals).
   * *Rationale:* In `parReduce(particles.asReadonly(), 0.0, (p, _i) => ...f32..., (a, b) => a + b)`, the third argument fixes `Acc = f32`, which types `0.0` as `f32` without requiring `0.0 as f32`.

---

## 3. Flyscript for TypeScript Developers

| Construct | In TypeScript | In Flyscript (`.fly`) |
| :--- | :--- | :--- |
| **Variables (`const` vs `let`)** | `const` prevents variable reassignment, but object properties remain mutable because objects are aliased references. | **Affine ownership unifies shallow & deep immutability:** Because an owned value has no other aliases, `const x = v` makes `x` and all its owned fields unmodifiable (`mut x` is rejected). `let x = v` allows field mutation and `mut x` borrowing. |
| **Numbers** | Single `number` (`f64`) and `bigint`. | Explicit machine scalars (`i32`, `u64`, `u8`, `usize`, `f32`, `f64`). Unadorned literals (`42`, `200`, `0.5`) infer their type across the whole call; `x as u16` converts explicitly. |
| **Records & `struct`** | `{ x: 1, y: 2 }` and `type Point = { x: number; y: number }` are structural with width subtyping. | `{ x: 1.0, y: 2.0 }` is a structural record (extra fields accepted via `<row R>`). `struct Point { x: f64; y: f64; }` wraps a record row in a nominal type for methods (`impl Point`), privacy, or `Drop`. |
| **Variants (`#Tag`) & `enum`** | Discriminated unions `{ tag: "ok"; val: T } \| { tag: "err"; err: E }`. | **`#Tag` everywhere:** `[ #Ok(T) \| #Err { code: u16; msg: str } ]` is a structural variant row; `enum Option<T> { #None, #Some(T) }` is a nominal wrapper over a variant row. Matched exhaustively via `match (x) { ... }`. |
| **`interface` & `impl`** | Structural shape contract; methods inside `class`. | **Nominal trait with associated types:** Implemented via `impl Trait for Type { ... }`. Inherent methods live in `impl Type { ... }`. Records and variants auto-derive `Eq`, `Hash`, `Show`, and `Clone`. |
| **Nullability** | `T \| null \| undefined`. | **No `null` or `undefined`:** Use `Option<T>` (`#Some(T)` or `#None`), which also propagates second-class views (`Option<mut u64>`). |
| **Memory & Borrows** | Garbage collected; any reference can alias and mutate anything. | **Four pointer forms:** `Box<T>` (unique heap), `Ref<R, T>` (shared immutable in `region (R)`), `Arc<T>` (shared immutable across threads), and transparent 2nd-class borrows `readonly T` / `mut T` (no `*` deref operator). |
| **Cleanup (`defer` & `Drop`)** | `try { ... } finally { ... }` | **`defer expr;` + `Drop`:** `defer` schedules cleanup at block exit in LIFO order alongside RAII `Drop` destructors. |
| **Async, Generators & Errors** | `async`/`await`, `function*`, and untyped `throw`/`try`/`catch`. | **Four Algebraic Effects (`Fail<E>`, `Io`, `Yield<T>`, `Region<R>`):** Direct-style synchronous code on stackful fibers. First-class continuations unify `Yield<T>` push loops and `Gen<T>` pull iterators. |

---

## 4. Lexical Syntax and Complete Grammar (EBNF)

### 4.1 Lexical, Expression, and Disambiguation Rules
* **Expression-Oriented Blocks & Semicolons:** Blocks `{ stmt1; stmt2; finalExpr }`, `if`, `match`, `region`, and `handle` evaluate to their final operand expression. Inside `{ ... }`, a statement ending with `;` must have type `void` (non-`void` values are explicitly discarded with `const _ = expr;`). Omitting the trailing `;` on the last expression yields that expression as the block's value; ending the block with `;` yields `void`.
* **`defer expr;`:** Schedules `expr` (which must have type `void` and may perform effects in the enclosing function's `uses` row) to execute when the enclosing lexical block exits—whether by normal completion, `return`, `break`, or effect unwinding—interleaved in strict LIFO order with local variable `Drop` destructors.
* **`const` vs. `let` and Transparent Borrows:** `const x = expr` binds an immutable variable; `let x = expr` binds a mutable variable. If `x` has type `mut T`, assigning `x = val` or `x += val` mutates the borrowed referent in place; borrow bindings cannot be re-seated.
* **Numeric and Array Literals:** Numeric literals (`0`, `42`, `3.14159`) carry no type suffixes; their scalar type is solved across the full enclosing call or statement before defaulting to `i32` / `f64`. Fixed-size array initialization uses `[a, b, c]` or `repeat<N>(val)`.
* **Record, Struct, and Variant Literals:** `{ field: value, ... }` constructs a nominal `struct` when expected by context (or when prefixed `StructName { field: value }`), and otherwise a structural record. `#Tag`, `#Tag(expr)`, or `#Tag { field: value, ... }` constructs a nominal `enum` when expected by context (or prefixed `EnumName.#Tag(...)`), and otherwise an open structural variant.
* **Generic Call `<` Disambiguation:** In expression position, `Ident<TypeArgs>(...)` and `Expr.Ident<TypeArgs>(...)` are parsed by speculative lookahead: if `<` is followed by a balanced `TypeArgList` and immediately followed by `(` or `{`, it is parsed as generic instantiation; otherwise `<` is the binary less-than operator.
* **Explicit Mutable Borrow Call-Site Markers:** Passing a mutable borrow requires `mut expr` at both the parameter declaration and the call site (`conn.read(mut rawBuf)`). Passing a shared `readonly` borrow requires no keyword at the call site (`parse(rawBuf)`).

### 4.2 EBNF Grammar

```ebnf
Module          = { ImportDecl | ExportDecl | TopDecl } ;
ImportDecl      = "import" "{" IdentList "}" "from" StringLit ";" ;
ExportDecl      = "export" TopDecl ;

TopDecl         = StructDecl | EnumDecl | InterfaceDecl | ImplDecl
                | TypeAliasDecl | EffectDecl | FunctionDecl | ExternDecl ;

Attr            = "@" "layout" "(" ( "c" | "packed" ) ")" ;
StructDecl      = [ Attr ] "struct" Ident [ TypeParams ] "{" { FieldDecl } "}" ;
FieldDecl       = Ident ":" FieldType ";" ;
FieldType       = [ "mut" | "readonly" ] Type ;   (* Propagates class = 2 if mut/readonly or 2nd-class Type *)

EnumDecl        = [ Attr ] "enum" Ident [ TypeParams ]
                  "{" TagSpec { "," TagSpec } [ "," ] "}" ;

InterfaceDecl   = "interface" Ident [ TypeParams ] "{" { AssocTypeDecl | InterfaceSig } "}" ;
AssocTypeDecl   = "type" Ident [ "extends" ConstraintList ] ";" ;
InterfaceSig    = "function" Ident [ TypeParams ] "(" [ SelfParam [ "," ParamList ] | ParamList ] ")"
                  ":" ReturnType [ UsesClause ] ";" ;
SelfParam       = "self" ":" ( "Self" | "mut" "Self" | "readonly" "Self" ) ;

ImplDecl        = "impl" [ TypeParams ] TypeRef [ "for" TypeRef ] [ WhereClause ]
                  "{" { AssocTypeDef | ExportMethod | FunctionDecl } "}" ;
ExportMethod    = "export" FunctionDecl ;
AssocTypeDef    = "type" Ident "=" ReturnType ";" ;
WhereClause     = "where" TypeRef "extends" ConstraintList { "," TypeRef "extends" ConstraintList } ;
TypeAliasDecl   = "type" Ident [ TypeParams ] "=" Type ";" ;

EffectDecl      = "effect" Ident [ TypeParams ] "{" { OpSig } "}" ;
OpSig           = Ident [ TypeParams ] "(" [ ParamList ] ")" ":" ReturnType [ UsesClause ] ";" ;

FunctionDecl    = [ "comptime" ] "function" Ident [ TypeParams ]
                  "(" [ ParamList ] ")" ":" ReturnType [ UsesClause ] [ WhereClause ] Block ;

ExternDecl      = "extern" "\"C\"" "function" Ident "(" [ ParamList ] ")" ":" ReturnType [ UsesClause ] ";" ;

ReturnType      = [ "mut" | "readonly" ] Type [ "from" Ident ] ;

ParamList       = Param { "," Param } [ "," ] ;
Param           = [ "comptime" ] Ident ":" ParamType ;
ParamType       = [ "mut" | "readonly" | "once" ] Type ;

UsesClause      = "uses" EffectRow ;
EffectRow       = ( EffectRef | "..." Ident ) { "," ( EffectRef | "..." Ident ) } ;
EffectRef       = Ident [ TypeArgs ] ;

TypeParams      = "<" TypeParam { "," TypeParam } ">" ;
TypeParam       = "region" Ident
                | "row" Ident [ "=" ( RecordType | VariantType | "[" [ EffectRow ] "]" ) ]
                | "comptime" Ident ":" Type
                | Ident [ "extends" ConstraintList ] [ "=" Type ] ;
ConstraintList  = Constraint { "&" Constraint } ;
Constraint      = "Copy" | "Send" | "Drop" | TypeRef ;

TypeArgs        = "<" TypeArg { "," TypeArg } ">" ;
TypeArg         = FieldType | Expr | "[" [ EffectRow ] "]" ;

Type            = PrimType
                | "dyn" TypeRef
                | "Ref" "<" [ Ident "," ] Type ">"            (* 1-arg form uses Region Elision *)
                | "RegionList" "<" Type [ "," Ident ] ">"     (* 1-arg form uses Region Elision *)
                | "Cont" "<" Type "," Type [ "," "[" [ EffectRow ] "]" ] ">"
                | RecordType
                | VariantType
                | TupleType
                | TypeRef
                | Type "*"
                | Type "[" [ Expr ] "]"
                | [ "mut" | "once" ] "(" [ ClosureParamList ] ")" "=>" ReturnType [ UsesClause ] ;

RecordType      = "{" { FieldDecl } [ "..." Ident [ ";" ] ] "}" ;
VariantType     = "[" [ "|" ] TagSpec { "|" TagSpec } [ "|" "..." Ident ] "]" ;
TagSpec         = "#" Ident [ "(" FieldType ")" | "{" { FieldDecl } "}" ] ;
TupleType       = "[" FieldType { "," FieldType } "]" ;

TypeRef         = Ident { "." Ident } [ TypeArgs ] ;
PrimIntType     = "i8" | "i16" | "i32" | "i64" | "isize" | "u8" | "u16" | "u32" | "u64" | "usize" ;
PrimType        = PrimIntType | "f32" | "f64" | "bool" | "str" | "void" | "never" | "Type" ;

Block           = "{" { Stmt ";" } [ Expr ] "}" ;
Stmt            = ConstDecl | LetDecl | DeferStmt | AssignStmt | ReturnStmt | BreakStmt | ContinueStmt | Expr ;
DeferStmt       = "defer" Expr ;
Expr            = IfExpr | MatchExpr | RegionExpr | HandleExpr | ForExpr | UnsafeExpr | LambdaExpr | ... ;
IfExpr          = "if" "(" Expr ")" Block [ "else" ( IfExpr | Block ) ] ;
MatchExpr       = "match" "(" Expr ")" "{" { MatchArm } "}" ;
MatchArm        = Pattern [ "if" Expr ] "=>" ( Expr "," | Block ) ;
RegionExpr      = "region" "(" Ident ")" Block ;
ForExpr         = "for" "(" ( "const" | "let" ) Ident "of" Expr ")" Block ;
UnsafeExpr      = "unsafe" Block ;

HandleExpr      = "handle" Block "with" EffectRef "{" { HandlerArm } "}" ;
HandlerArm      = Ident "(" [ HandlerParamList ] ")" [ "resumes" Ident ] "=>" Block ;
HandlerParamList= Ident [ ":" Type ] { "," Ident [ ":" Type ] } ;
```

---

## 5. Types: Unified Rows, Nominal Wrappers, Strings, and Region Elision

### 5.1 Primitives, Strings, and Slices
* **Scalars (`Copy`, $\text{class} = 1$):** `i8`, `i16`, `i32`, `i64`, `isize`, `u8`, `u16`, `u32`, `u64`, `usize`, `f32`, `f64`, `bool`, `void`, `never`.
* **Strings:**
  * `str` ($\text{class} = 2$): a second-class borrowed UTF-8 slice `(ptr: readonly u8*, len: usize)`. String literals `"hello"` have static type `str` in read-only binary data.
  * `String` ($\text{class} = 1$): a first-class owned, growable UTF-8 heap buffer. Passing `s: String` to a `str` parameter borrows it automatically; `s.asStr(): str from s` borrows it explicitly.
  * `Ref<R, str>` (or `Ref<str>` with region elision; $\text{class} = 1$): a first-class immutable UTF-8 string slice bump-allocated inside `region (R)`, implementing `Copy`, and freely borrowable as `str` (`refStr.asStr(): str from refStr`) while `R` is in scope.
* **Arrays, Slices, and Multi-Dimensional Grids:**
  * `T[N]`: inline fixed-size array of `N` elements ($\text{class}(T[N]) = \text{class}(T)$; `Copy` if `T extends Copy`).
  * `T[]` ($\text{class} = 2$): second-class borrowed slice view (`readonly T[]` or `mut T[]`).
  * `Ref<R, T[]>` (or `Ref<T[]>`; $\text{class} = 1$): a first-class immutable slice allocated in `region (R)`, implementing `Copy`.
  * `Grid2D<T>` and `Grid3D<T>` ($\text{class} = 2$): second-class strided views indexed via `.get(row, col)`.

### 5.2 One Unified Row Calculus: Records, Variants, and Effects
Flyscript uses a single Rémy-style sorted row unifier across three type constructors:
1. **Structural Record Rows (`{ field: Type; ...R }`):** Anonymous records and `type` aliases of records are structural; physical layout is sorted by alignment descending then field name ascending:
   ```ts
   type Point2D<row R = {}> = { x: f64; y: f64; ...R };

   function distanceSq<row R>(p: readonly Point2D<R>): f64 {
     p.x * p.x + p.y * p.y
   }
   ```
2. **Polymorphic Variant Rows (`[ #Tag(Payload) | #RecTag { a: T; b: U } | ...R ]`):** Tags prefixed with `#` construct structural sum types without pre-declaration, carrying no payload (`#Null`), a tuple/single payload (`#Num(f64)`), or an inline record payload (`#Get { key: String; reply: ReplyPort }`). In `uses Fail<[ #A | #B ]>` positions, variant rows are **implicitly open** (`[ #A | #B | ..._ ]`), so calling two functions with different failure tags automatically unifies their tag sets into the combined variant row.
3. **Effect Rows (`uses Io, Fail<E>, ...Eff`):** Unhandled algebraic effects form a row of effect labels.

### 5.3 Nominal `struct` and `enum`, Separate `impl`, Associated Types, and Region Elision
`struct` and `enum` wrap a record row or closed variant row in a generative nominal type.
* **Single-Region Elision:** Inside any declaration with a single `<region R>` parameter in scope, `Ref<T>`, `RegionList<T>`, and single-region nominal types (`Json`) supply `R` automatically:
  ```ts
  export enum Json<region R> {
    #Null,
    #Bool(bool),
    #Num(f64),
    #Str(Ref<str>),                                              // Elides to Ref<R, str>
    #Arr(Ref<RegionList<Ref<Json>>>),                            // Elides to Ref<R, RegionList<Ref<R, Json<R>>, R>>
    #Obj(Ref<RegionList<{ key: Ref<str>; val: Ref<Json> }>>),    // Elides R throughout!
  }
  ```
* **Separate `impl` Blocks & Associated Types:** Methods live in `impl Type { ... }`; interface implementations live in `impl Interface for Type { ... }`. Interfaces may declare associated types (`type Item;`):
  ```ts
  export interface Borrow<Borrowed> {
    function borrow(self: readonly Self): Borrowed from self;
  }
  ```

### 5.4 Automatic Structural Derivation (`Eq`, `Hash`, `Show`, `Clone`) and Borrowed Lookup
* **Auto-Derived Value Traits:** Using `comptime` reflection over record and variant rows, the standard library provides blanket implementations of **`Eq`**, **`Hash`**, **`Show`**, and **`Clone`** for every first-class structural record, tuple, and variant row whose components implement that trait, and automatically derives them for any nominal `struct` or `enum` whose fields are public or within the defining module.
* **Borrowed Lookup (`HashMap<K, V>.get` / `.getMut`):** `String` implements `Borrow<str>` (and `Vec<T>` implements `Borrow<readonly T[]>`). `HashMap<K, V>` defines:
  ```ts
  impl<K, V> HashMap<K, V> {
    export function get<Q extends Hash & Eq>(
      self: readonly Self,
      key: Q,
    ): Option<readonly V> from self where K extends Borrow<Q>;

    export function getMut<Q extends Hash & Eq>(
      self: mut Self,
      key: Q,
    ): Option<mut V> from self where K extends Borrow<Q>;
  }
  ```
  Notice that `Option<readonly V>` and `Option<mut V>` are ordinary $\text{class} = 2$ instantiations of `enum Option<T> { #None, #Some(T) }` tied to `self` via `from self`!

### 5.5 Bidirectional Local Type, Region, Effect, and Literal Inference
Type checking runs **after** `comptime` specialization:
1. **Required Annotations:** Every `export function`, `interface` method signature, and `extern "C"` declaration must explicitly annotate its parameter types, return type, and `uses` clause (omitting `uses` on an `export function` means `uses []`).
2. **Inferred Locally:** Non-exported module-private `function` declarations may omit `uses` (their minimal polymorphic effect row is inferred). Inside function bodies, `const`/`let` variable types, struct/enum literal nominal types (when expected by context), generic type and row arguments at call sites, and closure signatures are inferred bidirectionally.
3. **Whole-Body Region Unification:** Region parameters `<region R>` introduce unification variables `?R` solved across the enclosing function body; any `?R` on a region primitive that is not unified with an in-scope `region (R)` parameter or block is rejected at compile time.
4. **Call-Wide Polymorphic Numeric Literals:** Unadorned integer (`0`, `42`) and float (`0.0`, `3.14`) literals generate constrained type variables `?Int` / `?Float` that are unified across **all** arguments and closure bodies of an enclosing call before defaulting unconstrained literals to `i32` or `f64`.

---

## 6. Ownership, Universal Second-Class Views, Closures, and Marker Traits

### 6.1 Universal Class Propagation and the Three Marker Traits (`Copy`, `Send`, `Drop`)

| Form | Class | Meaning | Allowed in $\text{class}=1$ Heap Container (`Vec`, `Box`, `Arc`)? | Allowed in `struct` / `enum` / Record / Tuple? |
| :--- | :--- | :--- | :--- | :--- |
| **`T`** (owned 1st-class) | $\text{class} = 1$ | Uniquely owned value; moves unless `T extends Copy` | Yes | Yes ($\text{class}$ stays $1$ if all fields are $1$) |
| **`Ref<R, T>`** ($\text{class}(T)=1$) | $\text{class} = 1$ | Unboxed immutable pointer in `region (R)`; is `Copy` | In `RegionList<T, R>` only | Yes ($\text{class} = 1$, scoped to `R`) |
| **`Arc<T>`** (`T extends Send`) | $\text{class} = 1$ | Atomically refcounted `Heap` handle | Yes | Yes ($\text{class} = 1$) |
| **`Cont<A, B, E>`** (`Gen<T, E>`) | $1$ or $2$ | One-shot continuation ($\text{class} = 2$ iff frame holds borrows) | Only if $\text{class} = 1$ | Yes (propagates $\text{class}$ to outer type) |
| **`readonly T` / `mut T`** | $\text{class} = 2$ | Transparent shared or exclusive lexical borrow | **Never** | Yes (makes enclosing type **$\text{class} = 2$**) |
| **Composite with $\text{class}=2$** | $\text{class} = 2$ | `Option<mut T>`, `Scanner`, `ParticleView`, etc. | **Never** | Yes (makes enclosing type **$\text{class} = 2$**) |

Marker traits apply to **first-class types ($\text{class}(\tau) = 1$)** and are derived structurally for first-class records, tuples, variants, and nominal types from their constituent fields:
1. **`T extends Copy`:** Requires $\text{class}(T) = 1$. Trivially copyable bits (scalars, `Ref<R, U>`, fixed arrays `U[N]`, and first-class composites whose fields are all `Copy` and do not implement `Drop`). Assigning a `Copy` value copies bits without invalidating the source binding.
2. **`T extends Send`:** Requires $\text{class}(T) = 1$. Safe to transfer across tasks or share as `readonly T` across worker threads. Satisfied by any first-class type whose fields are all `Send` and that contains **no `Cell<_>`**, **no `RegionList<_, R>`**, and **no raw pointers `U*`**. Because any mutation through a shared handle (`Mutex<T>`, `Atomic*`, `DbClient`) requires `uses Io` and any mutation in a region requires `uses Region<R>`, **`T extends Send` guarantees both safe ownership transfer and safe concurrent `readonly T` sharing (`Sync`)**, as well as safe wrapping in `Arc.new<T extends Send>(val: T): Arc<T>`.
3. **`T extends Drop`:** Requires $\text{class}(T) = 1$. Implemented only by nominal `struct` and `enum` types (`impl Drop for MyType { function drop(self: mut Self): void { ... } }`).

### 6.2 Second-Class View Rules and Tied Returns (`from paramName`)
* **Universal Propagation Law:** For any nominal or structural type constructor $F\langle \tau_1, \dots, \tau_k \rangle$ with fields/payloads $\phi_1, \dots, \phi_m$:
  $$\text{class}(F\langle \tau_1, \dots, \tau_k \rangle) = \max\big(\{1\} \cup \{\text{class}(\tau_i)\} \cup \{\text{class}(\phi_j)\}\big)$$
* **Lexical Confinement of $\text{class} = 2$ Types:** Any value of type $\tau$ with $\text{class}(\tau) = 2$ (such as `slot: mut u64`, `opt: Option<mut u64>`, `sc: Scanner`, or `p: ParticleView`) is tracked in the lexical borrow ledger $\Gamma$ by the multiset of root paths $\{\pi_1 : m_1, \dots, \pi_n : m_n\}$ its borrows lock:
  1. It may be bound to a local variable (`const` or `let`), passed downward as a function argument, or returned from a function tied to an input parameter (`from paramName`, or tied automatically when the function has a single $\text{class} = 2$ input parameter).
  2. Heap containers (`Box<T>`, `Vec<T>`, `HashMap<K, V>`, `Channel<T>`, `Arc<T>`) and region cells (`Ref<R, T>`, `Cell<T>`, `RegionList<T, R>`) require their element type arguments to satisfy $\text{class}(T) = 1$, statically preventing any second-class borrow view from being stashed on the heap or in an arena.

### 6.3 Closures and Capture Modes (`once`, `mut`, and Shared)
The compiler infers both the calling mode and class ($\text{class} \in \{1, 2\}$) of every lambda `(params) => body`:
1. **Calling Modes:**
   * **Shared (`(A) => B uses ...E`):** Captures outer bindings only by `readonly` borrow (or a $\text{class} = 2$ view containing only `readonly` borrows) or `Copy`; callable concurrently multiple times.
   * **Mutating (`mut (A) => B uses ...E`):** Captures at least one outer binding by `mut` borrow (or a $\text{class} = 2$ view containing a `mut` borrow); callable sequentially by a single holder.
   * **Consuming (`once (A) => B uses ...E`):** Moves at least one non-`Copy` owned binding out of its environment; callable at most once.
2. **First-Class ($\text{class} = 1$) vs. Second-Class ($\text{class} = 2$) Closures:** A closure has $\text{class} = 2$ if it captures any $\text{class} = 2$ binding or any non-`Heap` region reference `Ref<R, _>`. A $\text{class} = 2$ closure may be passed downward (e.g. to `Io.scope`, `s.spawn`, `par`, `parReduce`, `generate`, `Fail.capture`), but cannot escape into a $\text{class} = 1$ container or return untied.



---

## 7. The Four Standard Effects, First-Class Continuations, and Handlers

### 7.1 The Four Standard Effects (`prelude`)
Every side effect in the standard library belongs to one of four built-in algebraic effects:

```ts
// 1. Recoverable Failure (variant rows in `Fail<...>` signatures are implicitly open):
export effect Fail<E> {
  raise(err: E): never;
}

// 2. Stream Production:
export effect Yield<T> {
  yield(item: T): void;
}

// 3. Fiber-Local Append-Only Region Allocation & Cell/RegionList Mutation:
export effect Region<region R> {
  alloc<T>(val: T): Ref<R, T>;
  allocStr(s: str): Ref<R, str>;
  copyUtf8(raw: readonly u8[]): Ref<R, str> uses Fail<[ #MalformedUtf8 ]>;
  fmt(text: str): Ref<R, str>;
  cellGet<T extends Copy>(c: Ref<R, Cell<T>>): T;
  cellSet<T extends Copy>(c: Ref<R, Cell<T>>, val: T): void;
  listNew<T>(): Ref<R, RegionList<T, R>>;
  listPush<T>(list: Ref<R, RegionList<T, R>>, val: T): void;
}

// 4. External World, Clocks, Locks, Channels, Atomics & Structured Fiber Scheduling:
export effect Io {
  submitRead(fd: RawFd, buf: mut u8[]): usize uses Fail<IoErr>;
  submitWrite(fd: RawFd, buf: readonly u8[]): usize uses Fail<IoErr>;
  nowMonoNs(): u64;
  sleepNs(durationNs: u64): void;
  syncOp(token: u64): void; // Performed by Mutex, RwLock, Channel, and Atomic* operations
  scope<T, row E = []>(body: once (s: mut Scope<E>) => T uses Io, ...E): T uses Io, ...E;
}
```

### 7.2 Error Handling (`Fail<E>` and `Fail.capture`)
All recoverable failures use `uses Fail<E>`, where `E` in a function signature is an **implicitly open polymorphic variant row** (`[ #Tag1 | #Tag2(Payload) | ..._e ]`). Calling multiple fallible functions automatically unifies their failure tags into a combined open variant row without adapter boilerplate.
* At FFI boundaries or cleanup paths where an error should be reified as data rather than propagated, `Fail.capture(() => expr)` intercepts `Fail<E>` and returns `Result<T, E>` (`enum Result<T, E> { #Ok(T), #Err(E) }`). Conversely, `Fail.unwrap(result)` returns `v` on `#Ok(v)` or calls `Fail.raise(err)` on `#Err(err)`.

### 7.3 Append-Only Lexical Regions (`region (R)`)
Each stackful fiber owns a segmented bump-allocator chain (`FiberArena`). Entering `region (R) { body }` pushes a watermark `(slabPtr, offset)` on the current fiber's arena, introduces a rigid region type `R`, and installs a fiber-local, tail-resumptive handler for `Region<R>`:
* **Immutable `Ref<R, T>`:** `Region.alloc(val)` allocates `val` in `R` and returns `Ref<R, T>`, which implements `Copy` and points to immutable data.
* **Effect-Gated `Cell<T>` and `RegionList<T, R>`:**
  * `Cell<T extends Copy>` holds a single `Copy` value inside `R`. Reading (`cell.get()`) copies the value out and writing (`cell.set(v)`) overwrites it in place; both require `uses Region<R>`, and `Cell<T>` never yields a `readonly T` or `mut T` borrow.
  * `RegionList<T, R>` is an append-only chunked list inside `R`. Appending (`RegionList.push(list, val)`) requires `uses Region<R>` and allocates new chunks in `R` without ever moving or invalidating prior elements. Reading (`list.get(i)`, `list.iter()`) is pure (`uses []`) and yields `readonly T` borrows safely.
* **The Two Region Soundness Laws:**
  1. *Rank-2 Non-Escape Law:* In `region (R) { body } : RetType`, the region identifier `R` must not appear free in `RetType`, in any outer variable mutated by `body`, or in any unhandled effect payload escaping `body`.
  2. *Region-Storable Law (No-External-Drop):* Every type `T` allocated in `R` (`Ref<R, T>`, `RegionList<T, R>`) must have $\text{class}(T) = 1$ and contain only `Copy` primitives, `Ref<R, U>`, `Cell<U>`, or `RegionList<U, R>`—never heap-owned types (`Box`, `Vec`, `String`) or `Drop` implementations. When `region (R)` exits, the fiber's bump watermark is reset in $O(1)$ without running per-element destructors.

### 7.4 First-Class Affine Continuations (`Cont<In, Out, E>`), Deep Forwarding, and `Gen<T, E>`
In a resumptive handler arm `op(x) resumes k => armBody`, `k` is an affine value of type `Cont<OpRet, HandleOut, E>`, where `E` is the row of other unhandled effects performed by the handled computation:
* **Deep-Handler Forwarding Semantics:** `handle { body } with Eff { ... }` installs a **deep handler** at the delimiter of `body`'s stack segment. When `k` is stored inside a data structure (such as `Gen<T, E>`) and later resumed via `k.resume(val)` in a different dynamic scope:
  1. The handler for `Eff` remains active at the bottom of `k`'s stack segment (so subsequent `Eff` operations inside `k` are caught by the same handler, producing the next `Cont<In, Out, E>`).
  2. Any *other* effect operation in `E` (such as `Io` or `Fail<Err>`) performed while `k` is running is **forwarded dynamically through `k.resume(val)` to the handlers enclosing the `k.resume(val)` call site**.
* **Affine One-Shot & Drop Rule:** `k.resume(val)` consumes `k` by move. If `k` is dropped without being resumed (e.g., when a `Gen<T, E>` goes out of scope on an early `break`), `k`'s destructor immediately unwinds the suspended stack segment from its yield point outward—draining any in-flight kernel `Io` buffers and executing all pending `defer` statements and `Drop` destructors in strict LIFO order.
* **Pull Generators (`Gen<T, E>`) and Error Propagation Example:**
  ```ts
  enum Step<T, row E = []> {
    #Done,
    #Yielded { item: T; nextCont: Cont<void, Step<T, E>, E>; },
  }

  export struct Gen<T, row E = []> {
    state: Option<Cont<void, Step<T, E>, E>>;
  }

  impl<T, row E = []> Gen<T, E> {
    // Resuming `nextCont` forwards any effect in `...E` (such as `Fail` or `Io`)
    // directly to the caller of `g.next()`!
    export function next(self: mut Self): Option<T> uses ...E {
      match (self.state.take()) {
        #None => #None,
        #Some(k) => match (k.resume()) {
          #Done => #None,
          #Yielded { item, nextCont } => {
            self.state = #Some(nextCont);
            #Some(item)
          },
        },
      }
    }
  }
  ```
  If a generator function raises `Fail.raise(#ParseError)` on its third item, the first two calls to `g.next()` return `#Some(v1)` and `#Some(v2)`, and the third call to `g.next()` unwinds the generator frame (running its `defer`/`Drop` cleanups), leaves `self.state` as `#None`, and propagates `Fail.raise(#ParseError)` directly to the caller of `g.next()`.

### 7.5 Push Iteration (`for (const x of expr)`) and Loop Control
The loop `for (const x of streamExpr) { loopBody }` is syntax sugar for a deep handler of `Yield<T>` around `streamExpr`:
```ts
handle {
  streamExpr
} with Yield<T> {
  yield(x) resumes k => {
    loopBody;
    k.resume()
  }
}
```
* **Normal step & `continue;`:** Invokes `k.resume()` in tail position (compiled via evidence passing to a direct call with zero stack switch).
* **`break;`:** Drops `k` without calling `k.resume()` (synchronously unwinding `streamExpr` and running all its `defer` and `Drop` cleanups) and exits the `for` loop.
* **`return val;` inside `loopBody`:** Drops `k` (unwinding `streamExpr`), unwinds enclosing local scopes in LIFO order, and returns `val` from the enclosing function.

### 7.6 Handler Arm Semantics and `defer` / `Drop` LIFO Ordering
1. **Resumptive Arm (`op(args) resumes k => armBody`):** The handled block remains suspended on its fiber stack segment; all lexical borrows (`mut` and `readonly`) active inside the handled block are transferred into `k`'s borrow lock set $\Gamma_{\text{body}}$ and remain inaccessible to `armBody` until `k` completes or is dropped.
2. **Abortive Arm (`op(args) => armBody`, no `resumes` keyword):** Before `armBody` begins executing, the runtime unwinds the handled block's stack frames back to the `handle` delimiter, executing all inner `defer` statements and `Drop` destructors in reverse declaration order, resetting inner regions, and **releasing all inner lexical borrows $\Gamma_{\text{body}}$**. Consequently, variables or borrowed parameters (`conn: mut Socket`) that were re-borrowed inside the `handle` block are restored to their pre-`handle` state in $\Gamma_0$ and may be freely borrowed again inside `armBody`.
3. **Lexical `defer expr;` Ordering:** Within any block `{ ... }`, `defer expr;` statements and local variable `Drop` destructors share a single LIFO cleanup stack per scope: each cleanup runs in exact reverse order of the program point where the `defer` or variable binding was executed.

### 7.7 Panics and Observational Purity
* Out-of-memory on `Heap`, integer division by zero, arithmetic overflow in debug mode (wrapping arithmetic uses explicit `wrappingAdd`), and out-of-bounds slice indexing trigger an **unrecoverable fiber panic**, unwinding the fiber stack (running all `defer` and `Drop` cleanups) and aborting the enclosing `Io.scope` or process. Panics cannot be caught by `handle`.
* Global heap allocation (`Box`, `Vec`, `String`, `HashMap`) is unobservable and not tracked in `uses`. A function with `uses []` is observationally pure: it may allocate local heap memory, open local `region (R)` arenas, and mutate `mut` parameters in place, but cannot perform `Io`, `Fail`, `Yield`, or `Region<R>` on an outer region.

---

## 8. Concurrency, Parallelism, and Targets

### 8.1 Structured Concurrency (`Io.scope`) and `Scope`-Owned Fibers vs. `Gen<T>`
* **Shared Runtime Primitive, Distinct Ownership:** Both `Gen<T, E>` and a concurrent fiber spawned in `Io.scope` execute on a pooled, growable stackful fiber segment (`Cont`), but their ownership is opposite:
  * A **`Gen<T, E>`** owns its suspended stack segment directly; dropping `Gen<T, E>` unwinds and frees the segment.
  * A **spawned concurrent fiber is owned by its `Scope<E>` nursery**, not by the returned `Fiber<T, E>` handle! `s.spawn(task)` registers the fiber in `s` and returns a lightweight `Fiber<T, E>` join token. Calling `f.join()` awaits completion and extracts the `T` result; **dropping `f` without calling `.join()` (e.g., `const _ = s.spawn(...)` in a server accept loop) detaches the result token while the fiber continues running under `s`'s ownership**.
* **`s.spawn` Closure Capture Rules:** `s.spawn` accepts a consuming **`once () => T uses Io, ...E`** closure (`T extends Send`) whose environment captures must be either:
  1. First-class owned `U extends Send` bindings moved into the child fiber (such as moving an accepted `conn: Socket` into a connection handler fiber), or
  2. Shared `readonly V` borrows where `V extends Send` (including immutable `Ref<R, W>` where `W` contains no `Cell` or `RegionList`).
* **Cancellation and In-Flight Kernel Borrow Drain:** `Io.scope` waits for **all** fibers owned by `s` (both joined and detached) to finish before exiting. If any fiber in `s` raises an unhandled `Fail<E>`, `s` signals cancellation to all sibling fibers at their next `Io` suspension point: **for any sibling fiber with an in-flight kernel buffer (`Io.submitRead` / `Io.submitWrite`), the runtime issues an async kernel cancel (`IORING_OP_ASYNC_CANCEL`) and awaits the kernel `CQE` confirming DMA release of `buf` before unwinding the sibling fiber's stack (`defer` / `Drop`) and propagating `Fail<E>`**.

### 8.2 Data Parallelism (`par`, `parReduce`) and Recursive `comptime` `Soa<T>`
Multi-core data parallelism is provided by `std/par` over any mutable container implementing `ParSplit`:

```ts
// In "std/par":
export interface ParSplit {
  type ItemView; // May be a 2nd-class borrow (`mut T`) or a 2nd-class view record/struct!
  function parForEach(self: mut Self, body: (item: Self.ItemView, index: usize) => void): void;
}

export function par<C extends ParSplit>(
  container: mut C,
  body: (item: C.ItemView, index: usize) => void, // Shared closure with `uses []`!
): void {
  container.parForEach(body);
}

export function parReduce<C, View, Acc extends Send>(
  container: readonly C,
  identity: Acc,
  mapOne: (item: View, index: usize) => Acc, // Shared closure, `uses []`
  combine: (a: Acc, b: Acc) => Acc,          // Associative combiner, `uses []`
): Acc where readonly C extends ParRead<View>;
```
* **Recursive `comptime` `Soa<T>`:** `Soa<T>` uses `comptime` reflection (`Type.fieldsOf(T)`) to recursively flatten nested records and nominal structs into contiguous SIMD-aligned leaf scalar arrays, synthesizing a matching nested second-class `ItemView` record (`{ pos: { x: mut f32; y: mut f32 }; vel: { x: mut f32; y: mut f32 }; mass: mut f32 }`) for `ParSplit` and a `readonly` view record for `ParRead`.

### 8.3 Native (`x86_64`, `aarch64`) and WebAssembly (`wasm32`) Targets
* **Native:** `Io` is handled by the multi-threaded `io_uring` / `kqueue` stackful fiber scheduler; `extern "C"` calls switch from the fiber's 4 KB growable stacklet to the OS worker thread's native contiguous stack.
* **WebAssembly:** One-shot continuations (`Cont`, `Gen`, `Fiber`) and `Io` suspension compile to the **Wasm Stack Switching (`wasmfx` / JSPI)** mechanism, mapping `Io` operations directly to browser `fetch`/`ReadableStream`/DOM events or WASI Preview 2 async handles.

---

## 9. `comptime`, Modules, and Foreign Function Interface (FFI)

### 9.1 `comptime` Execution, Structural Derivation, and `Type` Reflection
Functions, parameters, and assertions marked `comptime` execute deterministically on the compiler's bytecode VM during Stage 2 before type/borrow checking. `Type` is a built-in `comptime`-only type supporting `Type.fieldsOf(T)`, `Type.variantsOf(T)`, `Type.structFromFields(fields)`, `Type.recordFromFields(fields)`, `Type.sizeOf(T)`, and `Type.alignOf(T)`:

```ts
comptime function FixedRingBuffer(comptime T: Type, comptime Capacity: usize): Type {
  comptime assert(Capacity > 0 && (Capacity & (Capacity - 1)) == 0, "Power of two required");
  return struct {
    buf: T[Capacity];
    head: usize;
    tail: usize;
  };
}

type ByteRing = FixedRingBuffer(u8, 1024);
```
The standard library uses `Type.fieldsOf(T)` and `Type.variantsOf(T)` to implement `Eq`, `Hash`, `Show`, and `Clone` structurally for all first-class records, tuples, variants, and nominal types.

### 9.2 Modules
Every `.fly` file is an ES module (`import { ... } from "...";`, `export`). Module import graphs must form a strict DAG; circular module dependencies are a compile-time error.

### 9.3 C ABI Interop (`extern "C"`, `@layout(c)`, Raw Pointers `T*`, `unsafe`)
* Functions declared `extern "C"` and structs marked `@layout(c)` or `@layout(packed)` follow the platform C ABI.
* Raw pointers (`T*`, `readonly T*`) are first-class `Copy` values (and `!Send`). There is no `*ptr` operator; reading, writing, or offsetting a raw pointer (`ptr.read()`, `ptr.write(val)`, `ptr.add(count)`) or calling an `extern "C"` function requires an explicit `unsafe { ... }` block.

---

## 10. Core Calculus ($\lambda_{\text{fly}}$ v1.5)

Surface Flyscript elaborates into $\lambda_{\text{fly}}$ judged under three contexts and one row kind (`Row`):

$$\Delta \;|\; \Theta \;|\; \Gamma \;\vdash\; e : \tau \;\!/\;\! \varepsilon \;\dashv\; \Theta_{\text{out}}$$

1. **Type, Region, and Unified Row Context ($\Delta$):**
   $$\Delta ::= \cdot \;\mid\; \Delta, \alpha : \{\text{Copy}, \text{Send}, \text{Drop}\} \;\mid\; \Delta, \rho : \text{region} \;\mid\; \Delta, r : \text{Row}_{\mathcal{L}}$$
   where $r : \text{Row}_{\mathcal{L}}$ is a sorted row variable lacking labels $\mathcal{L}$, used identically for structural record types $\Pi\langle r \rangle$, polymorphic variant types $\Sigma\langle r \rangle$, and effect rows $\varepsilon$.
2. **Universal Class Function ($\text{class}(\tau) \in \{1, 2\}$):**
   * $\text{class}(\text{readonly }\tau) = \text{class}(\text{mut }\tau) = \text{class}(\text{str}) = \text{class}(\tau[]) = 2$.
   * $\text{class}(\text{Cont}_{\Gamma_{\text{cap}}}\langle \tau_1, \tau_2, \varepsilon \rangle) = 2$ if $\Gamma_{\text{cap}} \neq \emptyset$, else $1$.
   * For any record, tuple, variant, or nominal `struct`/`enum` $F\langle \overline{\tau_i} \rangle$ with fields/payloads $\overline{\phi_j}$:
     $$\text{class}(F\langle \overline{\tau_i} \rangle) = \max\big(\{1\} \cup \{\text{class}(\tau_i)\} \cup \{\text{class}(\phi_j)\}\big)$$
   * Heap/region container type arguments (`Box<T>`, `Vec<T>`, `Arc<T>`, `Ref<R, T>`, `RegionList<T, R>`) and `Send`/`Copy`/`Drop` bounds require $\text{class}(T) = 1$.
3. **Affine First-Class Ownership ($\Theta$, $\text{class}(\tau) = 1$) & Second-Class View Ledger ($\Gamma$, $\text{class}(\tau) = 2$):**
   $$\Theta ::= \cdot \;\mid\; \Theta, x : \text{own}(\tau) \;\mid\; \Theta, x : \text{dead} \qquad \Gamma ::= \cdot \;\mid\; \Gamma, v : \text{view}(\{\pi_1 : m_1, \dots, \pi_k : m_k\}, \tau)$$
   * **Observational Purity Invariant:** No operation with $\varepsilon = []$ can mutate any path locked with $m_i = \text{ro}$ in $\Gamma$ or any `Ref<R, T>` value.
   * **Region Handler Rule (T-Region):**
     $$\frac{\Delta, \rho : \text{region} \;|\; \Theta \;|\; \Gamma \;\vdash\; e : \tau \;\!/\;\! \text{Region}\langle\rho\rangle, \varepsilon \;\dashv\; \Theta_{\text{out}} \qquad \rho \notin \text{ftv}(\tau) \cup \text{ftv}(\Theta_{\text{out}}) \cup \text{ftv}(\varepsilon)}{\Delta \;|\; \Theta \;|\; \Gamma \;\vdash\; \text{region}(\rho)\ \{ e \} : \tau \;\!/\;\! \varepsilon \;\dashv\; \Theta_{\text{out}}}$$
   * **Deep Handler & Continuation Forwarding Rule (T-Resume):** Resuming $k : \text{Cont}_{\Gamma_{\text{cap}}}\langle \tau_{\text{in}}, \tau_{\text{out}}, \varepsilon_k \rangle$ in context with ambient effect row $\varepsilon_{\text{caller}}$ requires $\varepsilon_k \subseteq \varepsilon_{\text{caller}}$, forwarding any unhandled operation in $\varepsilon_k$ to the handler environment of the resumer.

---

## 11. Standard Library Signatures & Validated HTTP / Simulation Examples

### 11.1 Standard Library Signatures (`prelude`, `std/net`)

```ts
// From prelude:
export enum Option<T> { #None, #Some(T) } // Propagates class(T) in {1, 2}!
export enum Result<T, E> { #Ok(T), #Err(E) }

export namespace Fail {
  export function raise<E>(err: E): never uses Fail<E>;
  export function capture<T, E, row Eff = []>(
    body: once () => T uses Fail<E>, ...Eff,
  ): Result<T, E> uses ...Eff;
}

// From "std/net" (`Fail<[ ... ]>` rows in signatures are implicitly open):
export type IoErr = [ #IoReset | #IoTimedOut | #IoBrokenPipe ];
export struct Profile { displayName: String; }
export struct QuotaStatus { allowed: bool; }

export struct Socket { fd: i32; }
impl Socket {
  export function read(self: mut Self, buf: mut u8[]): usize uses Io, Fail<IoErr>;
  export function writeStatus(self: mut Self, code: u16, body: str): void uses Io, Fail<IoErr>;
  export function close(self: mut Self): void uses Io;
}

export struct DbClient { poolId: u64; }
impl DbClient {
  export function fetchProfile(self: readonly Self, userId: str): Profile uses Io, Fail<IoErr>;
  export function checkTokenQuota(self: readonly Self, token: str): QuotaStatus uses Io, Fail<IoErr>;
}
```

### 11.2 Complete Validated HTTP Handler (`http_handler.fly`)
Uses single-region elision (`Ref<str>`, `Ref<ParsedReq>`), `Region.copyUtf8`, `Io.scope`, and abortive `Fail` handling:

```ts
import { Socket, DbClient } from "std/net";

// Single region parameter `R`: `Ref<str>` elides to `Ref<R, str>`!
struct ParsedReq<region R> {
  userId: Ref<str>;
  authToken: Ref<str>;
}

function parseHeader<region R>(
  raw: readonly u8[],
): Ref<ParsedReq> uses Region<R>, Fail<[ #MalformedRequest | #MalformedUtf8 ]> {
  if (raw.len < 16) {
    Fail.raise(#MalformedRequest);
  }
  Region.alloc({
    userId: Region.copyUtf8(raw[0..8]),
    authToken: Region.copyUtf8(raw[8..16]),
  })
}

export function handleConnection(
  conn: mut Socket,
  db: readonly DbClient,
): void uses Io {
  handle {
    region (R) {
      let rawBuf: u8[512] = repeat<512>(0);
      const n = conn.read(mut rawBuf);
      const req = parseHeader(rawBuf[0..n]);

      // `req` (`Ref<R, ParsedReq<R>>`) contains no `Cell` or `RegionList`, so it satisfies
      // `Send` within `R` and is shared safely across both fibers inside `Io.scope`:
      const pair = Io.scope((s) => {
        const fProfile = s.spawn(() => db.fetchProfile(req.userId.asStr()));
        const fQuota   = s.spawn(() => db.checkTokenQuota(req.authToken.asStr()));
        { profile: fProfile.join(), quota: fQuota.join() }
      });

      if (!pair.quota.allowed) {
        Fail.raise(#Unauthorized);
      }
      conn.writeStatus(200, pair.profile.displayName.asStr());
    } // <-- `R` bumped back in O(1); `pair.profile` (`String`) dropped
  } with Fail {
    // Abortive arm (`resumes` omitted): `R` is unwound and `conn` re-borrow has ended:
    raise(err) => {
      const code: u16 = match (err) {
        #MalformedRequest | #MalformedUtf8     => 400,
        #Unauthorized                          => 401,
        #IoReset | #IoTimedOut | #IoBrokenPipe => 502,
      };
      const _ = Fail.capture(() => conn.writeStatus(code, "error"));
    }
  }
}
```

### 11.3 Deterministic Simulation Test (`http_sim_test.fly`)

```ts
import { SimIo } from "std/testing";
import { handleConnection } from "./http_handler";

export function testConnectionUnderPacketLoss(): void {
  SimIo.run({ seed: 0x1234_5678, timeoutRate: 0.25 }, () => {
    let harness = SimIo.createMockPair();
    handleConnection(mut harness.socket, harness.db);
    assert(harness.statusWritten == 200 || harness.statusWritten == 502);
  });
}
```

---

## 12. Compiler Pipeline

1. **Stage 1 — Lexer & Recursive Descent Parser:** Parses `.fly` modules into an untyped CST, resolving `<TypeArgs>(` via speculative lookahead, expanding single-region elision (`Ref<T>` $\to$ `Ref<R, T>`), and validating DAG module imports.
2. **Stage 2 — `comptime` Bytecode Evaluator & Monomorphizer:** Evaluates `comptime` functions (`Soa<T>`, `FixedRingBuffer`, structural `Eq`/`Hash`/`Show`/`Clone` derivations) deterministically, canonicalizing structural record and variant layouts and monomorphizing row variables `<row R>` and generic types `<T>`.
3. **Stage 3 — Bidirectional Type, Class & Unified Row Checker:**
   * Computes $\text{class}(\tau) \in \{1, 2\}$ across all nominal and structural types, rejecting $\text{class} = 2$ types in heap containers and untied returns.
   * Performs call-wide unification before defaulting polymorphic numeric literals (`?Int` $\to$ `i32`, `?Float` $\to$ `f64`).
   * Solves whole-body region unification variables `?R`, infers effect rows for non-exported functions and closures, opens `Fail<[ ... ]>` variant rows in signatures, and unifies record, variant, and effect rows via a single Rémy row unifier.
4. **Stage 4 — Capability, Borrow & Region Pass (Mid-End SSA IR):**
   * Enforces affine move semantics ($\Theta$), second-class view borrow-ledger exclusivity ($\Gamma$), transparent borrow reads/writes, `defer`/`Drop` LIFO ordering, and abortive vs. resumptive handler borrow lifetimes.
   * Enforces the Two Region Laws (Rank-2 Non-Escape and Region-Storable No-External-Drop) for every `region (R)` handler of `Region<R>`.
   * Performs **Static Affine Reuse** (rewriting `Drop(Box<T>)` followed by `Box.new<U>` when `sizeof(T) == sizeof(U)` and `alignof(T) == alignof(U)` into in-place mutation).
   * Lowers **Evidence-Passing & Continuation Transformation** (tail-resumptive handlers like `Region<R>` and `for` loops over `Yield<T>` compile to direct inline/vtable calls; stored `Cont` values in `Gen<T>` and `Io` suspensions switch 4 KB stackful fiber segments on native or Wasm JSPI continuations).
5. **Stage 5 — Code Generation:**
   * **Debug:** Cranelift (or C11 / Wasm backend) for sub-second incremental compilation.
   * **Release:** LLVM IR (`x86_64`, `aarch64`, `wasm32`) with `noalias` and `readonly` attributes derived from `mut`, `readonly`, `Ref<R, T>`, and owned parameters.

---

## 13. Why Flyscript, Summary of Laws, Rejected Alternatives, and Open Question

### 13.1 Honest Comparison with Existing Languages

| Language | What Flyscript Does That It Cannot | What Flyscript Gives Up Compared to It |
| :--- | :--- | :--- |
| **Rust** | Zero `'a` lifetime annotations on types (second-class views propagate through `Option<mut T>` and `Scanner` automatically); cyclic graphs in `region (R)` via `Ref<T>` + `Cell<T>`; no `async`/`await` coloring or `Pin`; `#Tag` variant errors; deterministic `Io` simulation via handlers. | Cannot store borrows inside long-lived heap containers (uses owned values, regions, or `Handle<T>` indices), and uses stackful fiber segments rather than state-machine futures. |
| **TypeScript** | Compiles AOT to unboxed native code & Wasm with zero GC pauses, deterministic `defer`/`Drop`, real integers (`u64`, `i32`), recursive `Soa<T>` layout, and data-race-free multi-core parallelism (`par`). | No width subtyping without `<row R>`, no runtime reflection/`any`, and requires exported function signatures. |
| **Koka** | Zero reference-counting headers or atomic RC traffic on heap values (static affine ownership + regions instead of Perceus RC); explicit unboxed memory layout (`Soa<T>`); static data-race freedom (`Send`). | One-shot continuations only (no multi-shot backtracking) and second-class borrow discipline. |
| **Roc** | In-place mutation (`mut T`), cyclic region graphs (`region (R)`), first-class continuations (`Gen<T>`), low-level FFI, and user-definable effect handlers (Roc hardcodes effects into a single host "platform"). | Requires exported function type annotations rather than full-program HM inference. |
| **Hylo (Val)** | First-class lexical regions (`region (R)`) for cyclic graphs, algebraic effect handlers (`Io`, `Fail`, `Yield`, `Region`), first-class continuations (`Gen<T>`), and structural row polymorphism. | Uses explicit `mut` argument markers rather than implicit subscript projections. |
| **Zig** | Full memory safety and temporal/spatial borrow checking in safe code, algebraic data types with exhaustive `match`, closures, traits (`interface`), and algebraic effects (`Region<R>` instead of manual allocator threading). | Larger typechecker than Zig; C interop requires `extern "C"` declarations rather than Zig's `@cImport` C header translator. |
| **Mojo** | Unified row calculus (records, polymorphic variants, effects), swappable `Io` simulation handlers, TypeScript syntax, and lexical regions without lifetime parameter lists. | Does not target native GPU/TPU MLIR autotuning kernels in v1.5 (deferred to future work). |

### 13.2 Thesis and the Five Laws of Flyscript (Final Form)
**In one line:** *Affine values, one row calculus, handlers for everything, and `comptime`: Church on the outside, Turing on the inside.*

1. **Affine Ownership with Universal Second-Class View Propagation:** Values have one unique owner by default; transparent borrows (`readonly T`, `mut T`) propagate $\text{class} = 2$ through any `struct`, `enum`, record, or tuple (`Option<mut T>`, `Scanner`), preventing escape into heap containers without a single `'a` lifetime annotation.
2. **Effect-Gated Shared and Region Mutation (`uses Io`, `uses Region<R>`):** No operation with `uses []` can mutate state through `readonly T` or `Ref<R, T>`, making pure code 100% side-effect-free and allowing `Send` alone to guarantee thread-safe sharing.
3. **One Unified Row Calculus (`#Tag` and `{...}`):** A single sorted row unifier powers structural records `{ x: f64; ...R }`, implicitly open polymorphic variants `[ #Tag | ...R ]`, and algebraic effect rows `uses Io, ...E`, while nominal `struct`/`enum` provide generative identity, recursion, and `Drop`.
4. **One-Shot Algebraic Effect Handlers with Deep First-Class Continuations:** `Fail<E>` (errors), `Io` (async, locks & deterministic simulation), `Region<R>` (append-only arenas), and `Yield<T>` (push loops and pull `Gen<T>` iterators) are all ordinary one-shot effects over affine continuations.
5. **Compile-Time Execution as Ordinary Code:** `comptime` functions over `Type` values (`Soa<T>`, structural trait derivation) replace macro DSLs and bespoke compiler attributes.

### 13.3 Rejected Alternatives
* **Tracing Garbage Collection (Global or Actor-Local):** Rejected because global GC introduces tail-latency pauses and memory overhead, while actor-local GC requires write barriers and stack maps for cyclic state that `region (R)` and `Pool<T>` handle with flat cache layout.
* **Mutable Aliasable Region Pointers (`In<R, T>` in v1.3):** Rejected because allowing `Copy` region pointers to mutate fields or reallocate `Vec`s in place invalidates active borrows and violates observational purity; append-only `Ref<R, T>` + unborrowable `Cell<T extends Copy>` + chunked `RegionList<T, R>` under `uses Region<R>` is 100% alias-safe.
* **Effect-Free Interior Mutability (`Cell<T>`, `RefCell<T>`, un-effectful `Mutex`):** Rejected because allowing mutation behind `readonly T` without an effect (`uses Io` or `uses Region<R>`) destroys observational purity for `uses []` functions.
* **`iso` Capability and `recover` Blocks:** Rejected because affine ownership plus the ban on $\text{class} = 2$ borrows in $\text{class} = 1$ containers already guarantees every owned value is an isolated subgraph.
* **Width Subtyping on Structural Records:** Rejected because forgetting fields via subtyping requires dynamic field offset lookups or heap boxing, whereas row polymorphism (`<row R>`) monomorphizes to exact byte offsets.
* **Multi-Shot Continuations:** Rejected because resuming a continuation more than once duplicates affine resources (`Box<T>`, sockets) and invalidates active mutable borrows.
* **Global Hindley-Milner Type Inference:** Rejected because full-program HM unification produces non-local errors when combined with `comptime` type functions, rank-2 regions, and traits.
* **`async` / `await` Stackless Coroutines:** Rejected because they split the ecosystem into colored functions and prevent borrowing stack/region data naturally across suspension points without self-referential state-machine pinning (`Pin<&mut Self>`).
* **First-Class Lifetime Parameters (`'a`):** Rejected because infectious lifetime annotations on structs and types impose a severe ergonomic tax for patterns better served by universal second-class view propagation, lexical regions, or pool handles.

### 13.4 Open Question
1. **Target-Neutral SIMD Lane Permutation & Bitmask API (`Simd<T, comptime Lanes: usize>`):** While `Soa<T>` and `par` enable auto-vectorization for vertical arithmetic loops, algorithms such as vectorized UTF-8 validation, JSON scanning, and sorting networks require horizontal lane shuffles, saturating arithmetic, and lane-to-bitmask extraction (`movemask`), where ARM64 NEON/SVE and x86-64 AVX2/AVX-512 differ structurally. What is the minimal portable `Simd<T, Lanes>` intrinsic surface that lowers without emulation cliffs on both ARM64 and x8# Flyscript Language Specification (v1.5 — Part 2 of 3: §7–§13)

---


# Flyscript Language Specification (v1.5 — Part 3 of 3: Appendix of Eight Validated Programs)

Every program below typechecks against v1.5 and exercises the five v1.5 refinements: universal second-class propagation ($\text{class} = 2$ on `Scanner` and `Option<mut u64>`), transparent borrows (`slot += 1`), single-region elision (`Ref<T>`, `RegionList<T>`), `Scope`-owned fibers vs. `Gen`-owned continuations with deep effect forwarding, and call-wide polymorphic numeric literals (`0.0` in `parReduce`).

---

### Program 1: Recursive JSON Parser in a Region (`json_parser.fly`)
Exercises **single-region elision** (`Ref<str>`, `RegionList<Ref<Json>>` inside `enum Json<region R>`), **universal second-class propagation** (`Scanner` holds `src: readonly u8[]` and therefore has $\text{class} = 2$ without lifetime parameters), and whole-body region unification:

```ts
import { RegionList } from "std/region";

// Single `<region R>` in scope: `Ref<T>`, `RegionList<T>`, and `Json` elide `R` automatically!
export enum Json<region R> {
  #Null,
  #Bool(bool),
  #Num(f64),
  #Str(Ref<str>),
  #Arr(Ref<RegionList<Ref<Json>>>),
  #Obj(Ref<RegionList<{ key: Ref<str>; val: Ref<Json> }>>),
}

// `src: readonly u8[]` has class = 2, so `Scanner` automatically has class = 2
// (a stack-confined lexical view struct with zero `'a` lifetime annotations):
struct Scanner {
  src: readonly u8[];
  pos: usize;
}

function parseValue<region R>(
  sc: mut Scanner,
): Ref<Json> uses Region<R>, Fail<[ #UnexpectedEof | #InvalidJson | #MalformedUtf8 ]> {
  sc.skipWhitespace();
  if (sc.pos >= sc.src.len) { Fail.raise(#UnexpectedEof); }
  match (sc.src[sc.pos]) {
    b'n' => { sc.consumeLiteral("null"); Region.alloc(#Null) },
    b't' => { sc.consumeLiteral("true"); Region.alloc(#Bool(true)) },
    b'f' => { sc.consumeLiteral("false"); Region.alloc(#Bool(false)) },
    b'"' => {
      const rawSlice = sc.readQuotedBytes();
      const s = Region.copyUtf8(rawSlice);
      Region.alloc(#Str(s))
    },
    b'[' => {
      sc.pos += 1;
      const items = RegionList.new();
      while (!sc.tryConsumeByte(b']')) {
        RegionList.push(items, parseValue(mut sc));
        const _ = sc.tryConsumeByte(b',');
      }
      Region.alloc(#Arr(items))
    },
    _ => Fail.raise(#InvalidJson),
  }
}
```
* **Ergonomic note:** Single-region elision turned `#Arr(Ref<R, RegionList<Ref<R, Json<R>>, R>>)` into `#Arr(Ref<RegionList<Ref<Json>>>)`, and universal $\text{class} = 2$ propagation made `struct Scanner` completely legal without any special view keyword.

---

### Program 2: CLI Word Count with Transparent Borrows and `Option<mut u64>` (`word_count.fly`)
Exercises **universal second-class propagation** on `counts.getMut(word): Option<mut u64> from counts` and **transparent mutable borrows** (`slot += 1` without `*slot`):

```ts
import { File, Stdout } from "std/io";
import { HashMap } from "std/collections";

function wordsOf(line: str): void uses Yield<str> {
  for (const token of line.splitAsciiWhitespace()) {
    if (token.len > 0) { Yield.yield(token); }
  }
}

export function countWordsInFile(path: str): void uses Io, Fail<[ #FileOpenError | #IoReadError ]> {
  let file = File.open(path);
  defer file.close();

  let counts = HashMap.new<String, u64>();
  for (const line of file.lines()) {
    for (const word of wordsOf(line.asStr())) {
      // `getMut` returns `Option<mut u64> from counts` (a class = 2 enum!).
      // `slot: mut u64` is a transparent borrow: `slot += 1` writes in place!
      match (counts.getMut(word)) {
        #Some(slot) => { slot += 1; },
        #None       => { counts.insert(String.fromStr(word), 1); },
      }
    }
  }
  for (const entry of counts.entries()) {
    Stdout.println(`${entry.key}: ${entry.val}`);
  }
}
```
* **Ergonomic note:** Eliminating `*slot += 1` in favor of transparent borrows and allowing `Option<mut u64>` by universal $\text{class} = 2$ propagation makes in-place map updates read like idiomatic TypeScript.

---

### Program 3: Pull Generator Pipeline with Deep Effect Forwarding (`generators.fly`)
Exercises **first-class affine continuations (`Gen<T, E>`)**, **generator-owned drop cleanup on early `break`**, and **deep-handler effect forwarding** (where `streamA` or `streamB` can perform `Fail` or `Io`, forwarded out of `ga.next()`):

```ts
import { Gen, generate } from "std/iter";

export function zip<A, B, row E = []>(
  streamA: once () => void uses Yield<A>, ...E,
  streamB: once () => void uses Yield<B>, ...E,
): void uses Yield<[A, B]>, ...E {
  // `ga` and `gb` uniquely own their suspended continuations (and have class = 2
  // if `streamA`/`streamB` captured borrowed slices):
  let ga: Gen<A, E> = generate(streamA);
  let gb: Gen<B, E> = generate(streamB);
  while (true) {
    // Deep-handler forwarding: any effect in `...E` performed inside `streamA`
    // or `streamB` forwards directly out of `ga.next()` / `gb.next()`!
    match ([ga.next(), gb.next()]) {
      [#Some(a), #Some(b)] => Yield.yield([a, b]),
      _                    => break,
    }
  }
}

export function sumPositivePairs(
  xs: readonly i64[],
  ys: readonly i64[],
): i64 uses Fail<[ #NegativeValue ]> {
  let total: i64 = 0;
  for (const [x, y] of zip(() => xs.iter(), () => ys.iter())) {
    if (x < 0 || y < 0) {
      // Unwinds the `for` loop's Yield continuation, which drops `ga` and `gb` in `zip`,
      // which unwinds both inner slice iterators before raising `#NegativeValue`:
      Fail.raise(#NegativeValue);
    }
    total += x * y;
  }
  total
}
```
* **Ergonomic note:** Deep-handler effect forwarding means `zip` works seamlessly whether the input streams are pure slice iterators (`E = []`) or fallible network/file streams (`E = [Io, Fail<...>]`).

---

### Program 4: Particle Game Loop with Recursive `Soa<T>`, `par`, and `parReduce` (`particles.fly`)
Exercises **recursive `comptime` `Soa<T>` flattening**, **second-class nested view records**, and **call-wide polymorphic numeric literal inference** (`0.0` inferred as `f32` from the sibling closure without `0.0 as f32`):

```ts
import { par, parReduce } from "std/par";
import { Soa } from "std/layout";

struct Vec2 { x: f32; y: f32; }

struct Particle {
  pos: Vec2;
  vel: Vec2;
  mass: f32;
}

export function stepAndMeasureEnergy(
  particles: mut Soa<Particle>,
  dt: f32,
): f32 {
  // 1. Parallel in-place SIMD update via class = 2 nested view record:
  par(mut particles, (p, _i) => {
    p.pos.x += p.vel.x * dt;
    p.pos.y += p.vel.y * dt;
  });

  // 2. Call-wide literal inference: `0.0` unifies with `Acc = f32` from the closure return type!
  parReduce(
    particles.asReadonly(),
    0.0,
    (p, _i) => 0.5 * p.mass * (p.vel.x * p.vel.x + p.vel.y * p.vel.y),
    (e1, e2) => e1 + e2,
  )
}
```
* **Ergonomic note:** With call-wide numeric literal unification, both `0.0` and `0.5` infer as `f32` automatically with zero `as f32` casts.

---

### Program 5: Compiler Symbol Table in an Append-Only Region (`symbol_table.fly`)
Exercises **single-region elision (`Ref<T>`, `RegionList<T>`)**, **immutable `Ref<T>` sharing**, **unborrowable `Cell<T extends Copy>`**, and **append-only `RegionList<T>`** under `uses Region<R>`:

```ts
import { RegionList, Cell } from "std/region";

// Single `<region R>` parameter: `Ref<str>`, `Ref<Scope>`, `Ref<Decl>`, and `RegionList<...>`
// all elide `R` automatically!
export struct Decl<region R> {
  name: Ref<str>;
  typeId: Cell<u32>;
  visiting: Cell<bool>;
}

export struct Scope<region R> {
  parent: Option<Ref<Scope>>;
  bindings: Ref<RegionList<{ name: Ref<str>; decl: Ref<Decl> }>>;
}

impl<region R> Scope<R> {
  export function create(parent: Option<Ref<Scope>>): Ref<Scope> uses Region<R> {
    Region.alloc({ parent, bindings: RegionList.new() })
  }

  export function define(self: Ref<Self>, name: Ref<str>): Ref<Decl> uses Region<R> {
    const decl = Region.alloc(Decl {
      name,
      typeId: Cell.new(0 as u32),
      visiting: Cell.new(false),
    });
    RegionList.push(self.bindings, { name, decl });
    decl
  }

  // Pure lookup (`uses []`): reading immutable `Ref` fields and iterating a
  // `RegionList` snapshot performs zero effects and can never be invalidated by `push`!
  export function lookup(self: Ref<Self>, target: str): Option<Ref<Decl>> {
    for (const entry of self.bindings.iter()) {
      if (entry.name.asStr() == target) {
        return #Some(entry.decl);
      }
    }
    match (self.parent) {
      #Some(p) => p.lookup(target),
      #None    => #None,
    }
  }
}
```
* **Ergonomic note:** Region elision cut the type annotations in `Scope<R>` by more than half while preserving complete static region safety.

---

### Program 6: Key-Value Store Actor with Record-Payload Variant Tags (`kv_actor.fly`)
Exercises **variant tags with inline record payloads (`#Get { key: String; reply: ... }`)**, **`Borrow<str>` lookup on `HashMap<String, String>`**, and **$O(1)$ affine moves across channels**:

```ts
import { Channel, ReplyPort } from "std/sync";
import { HashMap } from "std/collections";

export type KvCommand = [
  | #Get { key: String; reply: ReplyPort<Option<String>> }
  | #Put { key: String; val: String }
  | #Shutdown
];

export function runKvActor(inbox: readonly Channel<KvCommand>): void uses Io {
  let store = HashMap.new<String, String>();
  while (true) {
    match (inbox.recv()) {
      #Get { key, reply } => {
        const res = match (store.get(key.asStr())) {
          #Some(v) => #Some(v.clone()),
          #None    => #None,
        };
        reply.send(res);
      },
      #Put { key, val } => {
        // `key` and `val` move into `store` in O(1) — zero string copies!
        store.insert(key, val);
      },
      #Shutdown => break,
    }
  }
}
```
* **Ergonomic note:** With `#Tag { field: Type }` in the grammar, structural variant commands read identically to TypeScript discriminated unions without needing a `"tag"` string field.

---

### Program 7: Concurrent Web Server Accept Loop (`http_server.fly`)
Exercises **`Scope`-owned fibers** (where `const _ = s.spawn(...)` detaches the `Fiber` join handle while `s` keeps owning and running the connection fiber) and **`once` closure moves into `s.spawn`**:

```ts
import { Listener, Socket, DbClient } from "std/net";
import { handleConnection } from "./http_handler";

export function serveForever(
  listener: mut Listener,
  db: readonly DbClient,
): void uses Io, Fail<[ #ListenerClosed ]> {
  Io.scope((s) => {
    for (let conn of listener.accept()) {
      // `s.spawn` takes a `once` closure: `conn: Socket` moves into the child fiber,
      // while `db: readonly DbClient` is shared.
      // Dropping the returned `Fiber<void>` handle with `const _ = ...` detaches the
      // handle WITHOUT cancelling the fiber; `s` owns the fiber until completion!
      const _ = s.spawn(() => {
        defer conn.close();
        handleConnection(mut conn, db);
      });
    }
  });
}
```
* **Ergonomic note:** Separating `Scope` fiber ownership from the detachable `Fiber<T>` join handle fixed the v1.4 drop-cancellation bug cleanly while preserving structured concurrency guarantees when `Io.scope` exits.

---

### Program 8: Browser Elm-Architecture UI on WebAssembly (`counter_ui.fly`)
Exercises **effect-driven `Region.fmt` (no region value parameter)**, **per-frame `region (R)` bump allocation**, and **algebraic `Dom<Msg>` rendering**:

```ts
export type Msg = [ #Increment | #Decrement | #Reset ];

export struct Model {
  count: i32;
  historyClicks: u32;
}

export effect Dom<M> {
  el(tag: str, attrs: readonly { key: str; val: str }[], children: () => void uses Dom<M>): void;
  onClick(msg: M): void;
  text(content: str): void;
}

export function update(model: mut Model, msg: Msg): void {
  model.historyClicks += 1;
  match (msg) {
    #Increment => { model.count += 1; },
    #Decrement => { model.count -= 1; },
    #Reset     => { model.count = 0; },
  }
}

export function view(model: readonly Model): void uses Dom<Msg> {
  region (R) {
    // `Region.fmt` performs `uses Region<R>`, handled by `region (R)` above!
    const label = Region.fmt(`Count: ${model.count} (clicks: ${model.historyClicks})`);
    Dom.el("div", [{ key: "class", val: "card" }], () => {
      Dom.el("h1", [], () => Dom.text(label.asStr()));
      Dom.el("button", [], () => { Dom.onClick(#Decrement); Dom.text("-"); });
      Dom.el("button", [], () => { Dom.onClick(#Increment); Dom.text("+"); });
      Dom.el("button", [], () => { Dom.onClick(#Reset);     Dom.text("Reset"); });
    });
  } // <-- `R` bumped back in 1 instruction after frame render!
}
```
* **Ergonomic note:** Computing `label` via `Region.fmt(...)` inside `region (R)` and borrowing `label.asStr()` inside the nested `Dom.el` shared closures requires zero heap allocation per frame and zero region value passing.

