# Flyscript Language Specification (v1.4 — Complete Consolidated Specification)

File extension: `.fly`

**Changelog (v0.1 $\to$ v1.4):** Evolved from an initial Rust-syntax sketch (v0.1) to a TypeScript-surface specification (v0.2–v1.0), unified around a four-pillar core of affine ownership, one row calculus, effect handlers, and `comptime` type functions (v1.1–v1.3), and finalized in v1.4 by making **regions append-only immutable arenas with `Cell<T>`/`RegionList<T, R>` gated by `uses Region<R>`**, promoting **one-shot continuations to first-class affine values** (unifying `Gen<T>` and `Fiber<T>`), merging `Shared` into `Io` (leaving **four standard effects: `Fail<E>`, `Io`, `Yield<T>`, `Region<R>`**), unifying nominal `struct`/`enum` with structural rows (`#Tag` everywhere, separate `impl` blocks), and replacing `return`/`finally` handler arms with lexical `defer`.

---

## 0. What Changed in v1.4, Independent Verification, and Concept Reduction

### 0.1 Independent Verification of the v1.4 Decisions (Plus One Crucial Safety Invariant)

Every one of the nine v1.4 decisions directly resolves a real soundness or expressiveness failure exposed by the eight test programs. There is **one subtle interaction in Decision 2 (First-Class Continuations)** that must be tightened into an explicit typing rule so that storing a continuation cannot smuggle a dangling lexical borrow out of scope:

* **The Subtlety in Decision 2 (`Gen<T>` Holding Lexical Borrows):**
  Suppose a user creates a generator `let g = generate(() => { for (const x of slice) { Yield.yield(x); } });` where `slice: readonly i32[]` is a second-class borrow of a local array `let arr = [1, 2, 3];`. When `generate` intercepts `Yield.yield`, it captures the one-shot continuation `k` and stores it inside `Gen<i32>` to return to the caller.
  * If `Gen<T>` were unconditionally a *first-class* struct, it could be returned from the function while its suspended stack frame still holds `slice` (a borrow of `arr`), causing a **use-after-free on `g.next()`**!
  * Conversely, our rule in §2.2 says *nominal `struct` fields cannot hold second-class values*—so how can `Gen<T>` store `k` when `k` captures `slice`?
  * **The Exact Resolution (Tied Continuation Views):** A captured continuation `k: Cont<In, Out, E>` is **first-class** when the handled closure captures only first-class owned/`Copy` values, and **second-class** (tied to the captured root path $\pi$ in $\Gamma$ via `from param`) when the closure captures a second-class borrow! Accordingly, `generate` has two natural signatures (or row-unified capture polymorphism): an escaping `Gen<T>` for owned inputs, and a second-class `Gen<T> from slice` for borrowed inputs—keeping `zip(sliceA.iter(), sliceB.iter())` 100% stack-safe while preventing a borrowed generator from escaping the stack frame it borrows from.

### 0.2 How v1.4 Fixes the Three Serious Problems from v1.3

1. **Fix for Problem A (Region Aliasing Unsoundness):**
   In v1.3, `In<R, T>` was both `Copy` (freely aliasable) and directly mutable (`b.names.push(x)` could reallocate a `Vec` while `a.names[0]` held a borrow into the old buffer, or overwrite an enum variant while its payload was borrowed).
   In v1.4:
   * **`Ref<R, T>` is `Copy` and points to immutable data.** Fields of `Ref<R, T>` can never be overwritten or reallocated in place, so `const first = a.names[0]` can never be invalidated by any operation on `b`.
   * Mutation inside a region occurs **only** through **`Cell<T>`** (where `T extends Copy`: `.get()` copies out by value and `.set(v)` writes in by value—**you can never borrow the interior of a `Cell<T>`**) and **`RegionList<T, R>`** (an append-only segmented/chunked list where `.push(v)` allocates a new chunk in `R` without ever moving or invalidating existing elements!).
   * Both `Cell.set` and `RegionList.push` perform `uses Region<R>`. Because effect handlers are **fiber-local**, a pure function (`uses []`) or a child fiber in `Io.scope` cannot perform `Region<R>`, restoring Law 2 (observational purity) automatically.

2. **Fix for Problem B (Pull Iteration & `zip`):**
   Because one-shot continuations `Cont<In, Out, E>` are now affine values that can be stored and returned, `Gen<T, row E = []>` is written in 20 lines of library code by storing the suspended continuation between `.next()` calls. `zip`, `merge`, `peekable`, and LL(k) parser lookahead work out of the box (see Appendix Program 3).

3. **Fix for Problem C (Concurrent Accept Loop):**
   `s.spawn` now accepts a **consuming `once () => T uses Io, ...E` closure** whose environment captures are either moved `Send` values (`let conn: Socket` moved into the child fiber) or shared `readonly U` borrows (`db: readonly DbClient` where `U extends Send`). The accept loop typechecks cleanly (see Appendix Program 7).

### 0.3 Concept-Count Reduction Table: v1.0 vs. v1.4

| Concept / Mechanism in v1.0 | Status in v1.4 | How v1.4 Unifies It |
| :--- | :--- | :--- |
| 1. Separate `struct`/`enum` syntax vs structural `{...}` and `[ #Tag ]` | **Unified into 1 Product & 1 Sum System** | `#Tag` syntax everywhere. `struct` is a nominal wrapper over a record row; `enum` is a nominal wrapper over a closed variant row. Data and methods are separated (`impl T`). |
| 2. Dual error model (`Result` + `Fail` + `From` + `try...else` + `@mustUse` `ignore`) | **Unified into `Fail<VariantRow>`** | Implicitly open `uses Fail<[ #Tag1 \| #Tag2 ]>` composes by automatic row union. `Result` is just `Fail.capture(...)`. |
| 3. Five effects (`Io`, `Fail`, `Alloc`, `Yield`, `Shared`) + `Async.scope` vs `Io.runScope` | **Reduced to 4 Standard Effects** | **`Fail<E>`**, **`Io`** (includes locks/channels/atomics & `Io.scope`), **`Yield<T>`**, and **`Region<R>`** (replaces `Alloc<R>`; heap allocation is unobservable). |
| 4. Three handler arm kinds (`resumes`, abortive, `return(v)`, `finally`) | **Reduced to 1 Arm Form + `defer`** | Handler arms are `op(args) [resumes k] => body`. `return(v)` and `finally` arms are deleted in favor of lexical `defer expr;`. |
| 5. Push-only `Yield<T>` vs Pull `Iterator` + separate `Fiber<T>` | **Unified by Affine `Cont<In, Out, E>`** | First-class one-shot continuations unify push generators (`Yield<T>`), pull iterators (`Gen<T>.next()`), and concurrent tasks (`Fiber<T>.join()`). |
| 6. Mutable `In<R, T>` + `Region<R>` value API + "frozen region in `scope`" rule | **Replaced by Append-Only `Ref<R, T>` + `Cell<T>` + `RegionList<T, R>`** | `Ref<R, T>` is immutable; only `Cell<T extends Copy>` and append-only `RegionList<T, R>` mutate via fiber-local `uses Region<R>`. |
| 7. Five Marker Traits (`Pod`, `Send`, `Sync`, `val`, `Drop`) | **Reduced to 3 (`Copy`, `Send`, `Drop`)** | With shared mutation gated by `uses Io` and region mutation gated by `uses Region<R>`, `readonly T` is 100% immutable in pure code; `Send` covers thread-sharing. |
| 8. `par for` keyword + `@layout(soa)` + `SoaSlice<T>` + integer refinement solver | **Replaced by library `par`/`parReduce` + `comptime` `Soa<T>`** | Propagating second-class view records + `comptime` recursive flattening express `Soa<T>` and parallel loops in library code. |

---

## 1. Goals and Non-Goals

### 1.1 Goals
1. **TypeScript surface, systems semantics:** Familiar syntax for developers who read TypeScript (`function`, `(x) => expr`, `const`/`let`, `<T extends U>`, `{ field: value }`, `#Tag`, `interface`, `impl`, `type`, ES modules) compiled ahead-of-time to native machine code and WebAssembly with unboxed layouts and deterministic destruction.
2. **One product system and one sum system over a unified row calculus:** Anonymous records `{ x: f64; y: f64 }` and polymorphic variants `[ #Ok(T) | #Err(E) ]` are structural and support row polymorphism (`<row R>`). Nominal `struct` and `enum` declarations wrap a record or variant row with a generative type identity for module privacy, iso-recursion, `@layout(c | packed)`, and `Drop`.
3. **Static affine ownership with propagating second-class views:** Every heap allocation (`Box<T>`, `Vec<T>`, `String`, `HashMap<K, V>`) has a single unique owner (`T`). Borrows (`readonly T`, `mut T`, `str`, `T[]`) and structural records/tuples/continuations containing them are **second-class views** restricted to parameters, locals, and tied returns (`from param`).
4. **Append-only immutable regions with effect-gated `Cell` and `RegionList`:** Lexical regions (`region (R) { ... }`) handle the fiber-local `Region<R>` effect. Region pointers `Ref<R, T>` are `Copy` and point to immutable data; intra-region mutation occurs exclusively through unborrowable `Cell<T extends Copy>` slots and append-only `RegionList<T, R>` collections via `uses Region<R>`.
5. **Four standard effects (`Fail<E>`, `Io`, `Yield<T>`, `Region<R>`) with first-class one-shot continuations:** Delimited continuations (`Cont<In, Out, E>`) are affine values, unifying push iteration (`Yield<T>`), pull generators (`Gen<T>`), and concurrent fibers (`Fiber<T>`), while enabling deterministic simulation testing by handling `Io`.
6. **Compile-time execution in the host language:** Generics, structural trait derivation (`Eq`, `Hash`, `Show`, `Clone`), and recursive `Soa<T>` layout flattening are ordinary Flyscript functions evaluated at `comptime`.

### 1.2 Non-Goals
1. **Width subtyping on structural records:** Handled statically via monomorphized row polymorphism (`<row R>`) so field offsets are always compile-time constants.
2. **Garbage collection:** No global or actor-local tracing garbage collector.
3. **Multi-shot continuations:** Continuations are strictly affine (resumed at most once; dropping unwinds the suspended frame).
4. **Equi-recursive structural types, integer refinement solvers, or automatic GPU lowering in v1:** Recursive types must go through nominal `struct` or `enum` declarations (iso-recursive).

---

## 2. Core Design Decisions and Rationales

1. **Pointer Taxonomy Organized by One Principle:**
   Every pointer/reference type in Flyscript occupies one cell in a $2 \times 2$ ownership grid:

   | Pointer / Handle | Scope & Lifetime | Aliasing | Mutability |
   | :--- | :--- | :--- | :--- |
   | **`Box<T>`** (`Vec<T>`, `String`) | Heap (unique owner) | Unique (affine move) | Mutable by owner (`let`) or `mut T` borrow |
   | **`Ref<R, T>`** | Lexical `region (R)` | `Copy` (freely shared in `R`) | **Immutable fields**; interior mutation only via `Cell<U>` / `RegionList<U, R>` (`uses Region<R>`) |
   | **`Arc<T>`** (`T extends Send`) | Heap (atomic RC across tasks) | Shared (`Arc.clone`) | **Immutable** (shared synchronization requires `Mutex<U>` / `Atomic*` via `uses Io`) |
   | **`readonly T` / `mut T`** | Second-class lexical borrow | Shared (`readonly`) or Unique (`mut`) | `readonly` is immutable; `mut` is exclusively mutable |

   Long-lived cyclic graphs outside a lexical region use library `Pool<T>` and `Handle<T>` (`{ index: u32; generation: u32 }`) built on `Vec<T>`.
   * *Rationale:* Eliminates overlapping smart pointers and guarantees that no aliasable pointer (`Ref<R, T>`, `Arc<T>`, `readonly T`) can ever invalidate a borrow into existing memory.

2. **Append-Only Regions (`Ref<R, T>`, `Cell<T>`, `RegionList<T, R>`) and the `Region<R>` Effect:**
   * Heap allocation (`Box.new`, `Vec.new`, `String.new`) is **not** an effect: it uses the global allocator and is observationally pure.
   * Region allocation and region mutation perform the **`Region<R>`** effect, handled lexically by `region (R) { ... }` on the current fiber's segmented bump arena (`FiberArena`):
     * `Region.alloc<R, T>(val: T): Ref<R, T> uses Region<R>` allocates `val` in `R` (requiring `T` to be a **Region-Storable Type**: `T` contains only `Copy` primitives, `Ref<R, U>`, `Cell<U>`, or `RegionList<U, R>`—never heap-owned `Box`/`Vec`/`String` or `Drop` types).
     * `Cell<T extends Copy>` may only be allocated inside a region (`Ref<R, Cell<T>>` or as a field of a struct inside `Ref<R, S>`). `cell.get(): T uses Region<R>` copies the `Copy` value out; `cell.set(val: T): void uses Region<R>` overwrites it in place. **Because `T extends Copy` and `Cell<T>` never yields a borrow (`readonly T` or `mut T`), `cell.set` can never invalidate any live reference.**
     * `RegionList<T, R>` is an append-only chunked list allocated in `R`. `list.push(val: T): void uses Region<R>` appends an element (allocating a new chunk in `R` when full without ever moving prior elements); `list.get(i: usize): readonly T` borrows an existing element safely because prior elements never move or deallocate until `region (R)` exits.
   * **Fiber-Locality and Sharing of `Ref<R, T>`:** Because effect handlers are **fiber-local**, a child fiber spawned via `Io.scope` cannot perform `Region<R>` for an enclosing fiber's region `R`. Furthermore, a `Ref<R, T>` satisfies `Send` (within the scope of `R`) and may be captured by child fibers in `Io.scope` or workers in `par` **if and only if `T` transitively contains no `Cell<_>` and no `RegionList<_, R>`** (making the subgraph reachable from `Ref<R, T>` 100% deeply immutable).
   * *Rationale:* Fixes Problem A completely. Borrowing a field or element from `Ref<R, T>` can never dangle after a subsequent `RegionList.push` or `Cell.set`, and pure functions (`uses []`) holding `Ref<R, T>` cannot mutate `Cell` or `RegionList` because they lack `uses Region<R>`.

3. **First-Class Affine Continuations (`Cont<In, Out, E>`) Unifying `Gen<T>` and `Fiber<T>`:**
   * In a resumptive handler arm `op(arg) resumes k => body`, `k` has the affine type `Cont<OpRet, BlockOut, HandledUses>`.
   * `k` is a real value: it can be moved into a variable, stored in a `struct`/`enum`, or returned from the `handle` block. Calling `k.resume(val)` consumes `k` by move. If `k` is dropped without being resumed (by going out of scope or `Drop`), `k`'s destructor unwinds the suspended fiber stack segment (running all pending `defer` statements and `Drop` destructors in LIFO order) and returns the stack segment to the fiber pool.
   * **Second-Class Propagation to Continuations:** If the handled block captures any second-class borrow from outside the `handle` block, `Cont<In, Out, E>` (and any wrapper holding it, such as `Gen<T>`) is classified as **second-class** tied to those borrows (`Gen<T> from slice`), preventing the suspended frame from outliving the stack variables it borrows.
   * *Rationale:* Fixes Problem B without adding a separate coroutine mechanism. Push streams (`Yield<T>`), pull iterators (`Gen<T>`), and concurrent tasks (`Fiber<T>`) are all the exact same runtime primitive.

4. **Four Standard Effects (`Fail<E>`, `Io`, `Yield<T>`, `Region<R>`):**
   * `Shared` is merged into **`Io`**: locks (`Mutex<T>`), channels (`Channel<T>`), and atomics (`AtomicU64`) perform `uses Io` because every synchronization operation is a concurrency scheduling boundary that `SimIo` must intercept for deterministic simulation testing.
   * `Async.scope` and `Io.runScope` are unified into **`Io.scope((s) => ...)`**.
   * *Rationale:* Every standard effect now has concrete operations and a clear semantic domain: failure (`Fail`), external world & concurrency scheduling (`Io`), stream production (`Yield`), and arena memory (`Region`).

5. **Unified Sums and Products (`#Tag` Everywhere) + Separate `impl` Blocks:**
   * Variant tags always start with `#` (`#Null`, `#Some(x)`), both in anonymous variant rows `[ #None | #Some(T) ]` and in nominal `enum` declarations `enum Option<T> { #None, #Some(T) }`.
   * `struct` and `enum` declarations contain **only data** (fields or `#Tag` variants). All inherent methods live in `impl Type { ... }` and all trait implementations live in `impl Trait for Type { ... }`.
   * **Iso-Recursive Rule:** Structural record and variant rows are strictly finite; any recursive type (`Json`, `Expr`, linked trees) must break the cycle through a nominal `struct` or `enum` declaration.
   * *Rationale:* Makes structural and nominal types 100% uniform in construction (`{ x, y }` and `#Tag(v)`) and pattern matching, while keeping the Rémy row unifier terminating and simple.

6. **Whole-Body Type-Directed Region Unification:**
   * A region parameter `<region R = Heap>` on a region-allocating call (`Region.alloc(v)`, `Region.copyStr(s)`, `RegionList.new()`) introduces a region unification variable `?R` solved across the enclosing function body via standard type unification (`?R` unifies with `R` when passed to a function expecting `Ref<R, _>`, stored in a struct `ParsedReq<R>`, or handled by an enclosing `region (R)` block). Any `?R` that remains unconstrained defaults to `Heap` (which is a compile error for `Region<R>`-only primitives, catching stray region calls immediately).
   * *Rationale:* Eliminates redundant `: Ref<R, str>` annotations on local variables inside a region block while remaining 100% type-directed (zero dependence on runtime escape paths).

---

## 3. Flyscript for TypeScript Developers

| Construct | In TypeScript | In Flyscript (`.fly`) |
| :--- | :--- | :--- |
| **Variables (`const` vs `let`)** | `const` prevents variable reassignment, but object properties remain mutable because objects are aliased references. | **Affine ownership unifies shallow & deep immutability:** Because an owned value has no other aliases, `const x = v` makes `x` and all its owned fields unmodifiable (`mut x` is rejected). `let x = v` allows field mutation and `mut x` borrowing. |
| **Numbers** | Single `number` (`f64`) and `bigint`. | Explicit machine scalars (`i32`, `u64`, `u8`, `usize`, `f32`, `f64`). Unadorned literals (`42`, `200`, `0.5`) infer their type from context; `x as u16` converts explicitly. |
| **Records & `struct`** | `{ x: 1, y: 2 }` and `type Point = { x: number; y: number }` are structural with width subtyping. | `{ x: 1.0, y: 2.0 }` is a structural record (extra fields accepted via `<row R>`). `struct Point { x: f64; y: f64; }` wraps a record row in a nominal type for methods (`impl Point`), privacy, or `Drop`. |
| **Variants (`#Tag`) & `enum`** | Discriminated unions `{ tag: "ok"; val: T } \| { tag: "err"; err: E }`. | **`#Tag` everywhere:** `[ #Ok(T) \| #Err(E) ]` is a structural variant row; `enum Option<T> { #None, #Some(T) }` is a nominal wrapper over a variant row. Matched exhaustively via `match (x) { #Some(v) => ... }`. |
| **`interface` & `impl`** | Structural shape contract; methods inside `class`. | **Nominal trait with associated types:** Implemented via `impl Trait for Type { ... }`. Inherent methods live in `impl Type { ... }`. Records and variants auto-derive `Eq`, `Hash`, `Show`, and `Clone`. |
| **Memory & Pointers** | Garbage collected; any reference can alias and mutate anything. | **Four pointer forms:** `Box<T>` (unique heap), `Ref<R, T>` (shared immutable in `region (R)`, with `Cell<T>`/`RegionList<T, R>` for `uses Region<R>` writes), `Arc<T>` (shared immutable across threads), and 2nd-class borrows `readonly T` / `mut T`. |
| **Cleanup (`defer` & `Drop`)** | `try { ... } finally { ... }` | **`defer expr;` + `Drop`:** `defer` schedules cleanup at block exit in LIFO order alongside RAII `Drop` destructors. |
| **Async, Generators & Errors** | `async`/`await`, `function*`, and untyped `throw`/`try`/`catch`. | **Four Algebraic Effects (`Fail<E>`, `Io`, `Yield<T>`, `Region<R>`):** Direct-style synchronous code on stackful fibers. First-class continuations unify `Yield<T>` push loops and `Gen<T>` pull iterators. |

---

## 4. Lexical Syntax and Complete Grammar (EBNF)

### 4.1 Lexical, Expression, and Disambiguation Rules
* **Expression-Oriented Blocks & Semicolons:** Blocks `{ stmt1; stmt2; finalExpr }`, `if`, `match`, `region`, and `handle` evaluate to their final operand expression. Inside `{ ... }`, a statement ending with `;` must have type `void` (non-`void` values are explicitly discarded with `const _ = expr;`). Omitting the trailing `;` on the last expression yields that expression as the block's value; ending the block with `;` yields `void`.
* **`defer expr;`:** Schedules `expr` (which must have type `void` and may perform effects in the enclosing function's `uses` row) to execute when the enclosing lexical block exits—whether by normal completion, `return`, `break`, or effect unwinding—interleaved in strict LIFO order with local variable `Drop` destructors.
* **Record and Struct Literals:** `{ field: value, ... }` constructs a nominal `struct` when the bidirectional expected type is that `struct` (or when prefixed as `StructName { field: value }`); otherwise it constructs a structural record `{ field: Type; ... }`. Field punning `{ x, y }` is equivalent to `{ x: x, y: y }`.
* **Variant Construction:** `#Tag` or `#Tag(expr)` constructs a variant value, typing as a nominal `enum` when expected by context (or prefixed `EnumName.#Tag(expr)`), and otherwise as an open structural variant `[ #Tag(Type) | ..._ ]`.

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
FieldType       = [ "mut" | "readonly" ] Type ;   (* 2nd-class allowed only in structural RecordType *)

EnumDecl        = [ Attr ] "enum" Ident [ TypeParams ]
                  "{" TagSpec { "," TagSpec } [ "," ] "}" ;

InterfaceDecl   = "interface" Ident [ TypeParams ] "{" { AssocTypeDecl | InterfaceSig } "}" ;
AssocTypeDecl   = "type" Ident [ "extends" ConstraintList ] ";" ;
InterfaceSig    = "function" Ident [ TypeParams ] "(" [ SelfParam [ "," ParamList ] | ParamList ] ")"
                  ":" ReturnType [ UsesClause ] ";" ;
SelfParam       = "self" ":" ( "Self" | "mut" "Self" | "readonly" "Self" ) ;

ImplDecl        = "impl" [ TypeParams ] TypeRef [ "for" TypeRef ]
                  "{" { AssocTypeDef | FunctionDecl } "}" ;
AssocTypeDef    = "type" Ident "=" ReturnType ";" ;
TypeAliasDecl   = "type" Ident [ TypeParams ] "=" Type ";" ;

EffectDecl      = "effect" Ident [ TypeParams ] "{" { OpSig ";" } "}" ;
OpSig           = Ident [ TypeParams ] "(" [ ParamList ] ")" ":" ReturnType [ UsesClause ] ;

FunctionDecl    = [ "comptime" ] "function" Ident [ TypeParams ]
                  "(" [ ParamList ] ")" ":" ReturnType [ UsesClause ] Block ;

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
TypeArg         = Type | Expr | "[" [ EffectRow ] "]" ;

Type            = PrimType
                | "dyn" TypeRef
                | "Ref" "<" Ident "," Type ">"
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
TagSpec         = "#" Ident [ "(" Type ")" ] ;
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

## 5. Types: Unified Rows, Nominal Wrappers, Strings, and Structural Derivation

### 5.1 Primitives, Strings, and Slices
* **Scalars (`Copy`, First-Class):** `i8`, `i16`, `i32`, `i64`, `isize`, `u8`, `u16`, `u32`, `u64`, `usize`, `f32`, `f64`, `bool`, `void`, `never`.
* **Strings:**
  * `str`: a second-class borrowed UTF-8 slice `(ptr: readonly u8*, len: usize)`. String literals `"hello"` have static type `str` in read-only binary data.
  * `String`: a first-class owned, growable UTF-8 heap buffer. Passing `s: String` to a `str` parameter borrows it automatically; `s.asStr(): str from s` borrows it explicitly.
  * `Ref<R, str>`: a first-class immutable UTF-8 string slice bump-allocated inside `region (R)`, implementing `Copy`, and freely borrowable as `str` (`refStr.asStr(): str from refStr`) while `R` is in scope.
* **Arrays, Slices, and Multi-Dimensional Grids:**
  * `T[N]`: inline fixed-size array of `N` first-class elements (`Copy` if `T extends Copy`).
  * `T[]`: second-class borrowed slice view (`readonly T[]` or `mut T[]`).
  * `Ref<R, T[]>`: a first-class immutable slice allocated in `region (R)`, implementing `Copy`.
  * `Grid2D<T>` and `Grid3D<T>`: second-class strided views indexed via `.get(row, col)`.

### 5.2 One Unified Row Calculus: Records, Variants, and Effects
Flyscript uses a single Rémy-style sorted row unifier across three type constructors:
1. **Structural Record Rows (`{ field: Type; ...R }`):** Anonymous records and `type` aliases of records are structural; physical layout is sorted by alignment descending then field name ascending.
2. **Polymorphic Variant Rows (`[ #Tag(Payload) | ...R ]`):** Tags prefixed with `#` (`#Null`, `#Num(f64)`) construct structural sum types without pre-declaration. In `uses Fail<[ #A | #B ]>` positions, variant rows are **implicitly open** (`[ #A | #B | ..._ ]`), so calling two functions with different failure tags automatically unifies their tag sets into the combined variant row.
3. **Effect Rows (`uses Io, Fail<E>, ...Eff`):** Unhandled algebraic effects form a row of effect labels.

### 5.3 Nominal `struct` and `enum`, Separate `impl`, and Associated Types
`struct` and `enum` wrap a record row or closed variant row in a generative nominal type:
```ts
struct Point { x: f64; y: f64; }

enum Json<region R> {
  #Null,
  #Bool(bool),
  #Num(f64),
  #Str(Ref<R, str>),
  #Arr(RegionList<Ref<R, Json<R>>, R>),
}
```
* **Separate `impl` Blocks:** Methods live in `impl Type { ... }`; interface implementations live in `impl Interface for Type { ... }`.
* **Associated Types on Interfaces:** Interfaces may declare associated types (`type Item;`), constrained at use sites via `I<Item = T>` or projected via `Self.Item`:
  ```ts
  export interface Borrow<Borrowed> {
    // `Borrowed` may be a 2nd-class type such as `str` or `readonly u8[]`
    function borrow(self: readonly Self): Borrowed from self;
  }
  ```

### 5.4 Automatic Structural Derivation (`Eq`, `Hash`, `Show`, `Clone`) and Borrowed Lookup
* **Auto-Derived Value Traits:** Using `comptime` reflection over record and variant rows, the standard library provides blanket implementations of **`Eq`**, **`Hash`**, **`Show`** (formatting records as `{ x: 1, y: 2 }` and variants as `#Tag(payload)`), and **`Clone`** for every structural record, tuple, and variant row whose components implement that trait, and automatically derives them for any nominal `struct` or `enum` whose fields are public or within the defining module.
* **Borrowed Lookup (`HashMap<K, V>.get`):** `String` implements `Borrow<str>` (and `Vec<T>` implements `Borrow<readonly T[]>`) with a law that `hash(k.borrow()) == hash(k)` and `eq(k1.borrow(), k2.borrow()) == eq(k1, k2)`. `HashMap<K, V>` defines:
  ```ts
  impl<K, V> HashMap<K, V> {
    function get<Q extends Hash & Eq>(
      self: readonly Self,
      key: Q,
    ): Option<readonly V> from self where K extends Borrow<Q>;
  }
  ```
  allowing `map.get("my_key")` on a `HashMap<String, Value>` with zero heap allocation.

---

## 6. Ownership, Propagating Second-Class Views, Closures, and Marker Traits

### 6.1 Three Marker Traits (`Copy`, `Send`, `Drop`)

| Form | Class | Meaning | Allowed in First-Class `struct`/`enum`? | Allowed in Structural Record/Tuple? |
| :--- | :--- | :--- | :--- | :--- |
| **`T`** (default) | 1st-class | Uniquely owned value; moves unless `T extends Copy` | Yes | Yes (record remains 1st-class) |
| **`Ref<R, T>`** | 1st-class | Unboxed immutable pointer in `region (R)`; is `Copy` | Yes (in `Struct<region R>`) | Yes (record remains 1st-class) |
| **`Arc<T>`** | 1st-class | Atomically refcounted `Heap` handle (`T extends Send`) | Yes | Yes (record remains 1st-class) |
| **`Cont<A, B, E>`** | 1st or 2nd | One-shot continuation (2nd-class iff frame holds borrows) | Only if 1st-class | Propagates class |
| **`readonly T`** | 2nd-class | Shared deeply immutable lexical borrow | **Never** | Yes (makes record **2nd-class**) |
| **`mut T`** | 2nd-class | Exclusive mutable lexical borrow (`mut x` at call) | **Never** | Yes (makes record **2nd-class**) |
| **2nd-class `{...}`** | 2nd-class | Record/tuple with $\ge 1$ second-class component | **Never** | Yes (makes outer record **2nd-class**) |

1. **`T extends Copy`:** Trivially copyable bits (scalars, `Ref<R, U>`, fixed arrays `U[N]`, and first-class composites whose fields are all `Copy` and do not implement `Drop`).
2. **`T extends Send`:** Safe to transfer across tasks or share as `readonly T` across worker threads. Satisfied by any first-class type whose fields are all `Send` and that contains **no `Cell<_>`**, **no `RegionList<_, R>`**, and **no raw pointers `U*`**. Note: a pure immutable `Ref<R, T>` (where `T` contains no `Cell` or `RegionList`) satisfies `Send` within lexical scopes nested inside `region (R)` (such as `Io.scope` or `par`), while the rank-2 non-escape rule on `region (R)` prevents `R` from escaping the region block!
3. **`T extends Drop`:** Implemented only by nominal `struct` and `enum` types (`impl Drop for MyType { function drop(self: mut Self): void { ... } }`).

### 6.2 Propagating Second-Class Views and Tied Returns (`from paramName`)
* **Second-Class Propagation Rule:** Any structural record `{ f1: T1; ... }`, tuple `[T1, ...]`, or continuation `Cont<...>` (and `Gen<T>`) that contains or captures one or more second-class components (`readonly U`, `mut U`, `str`, `U[]`, `Grid2D<U>`) is itself a **second-class view type**.
* **Where Second-Class Types May Appear:** Only as function parameters, local bindings, or function return types tied to an input parameter (`from paramName`, or tied automatically when there is a single second-class input parameter).

### 6.3 Closures (`once`, `mut`, and Shared)
* **Shared `(A) => B uses ...E`:** Captures outer bindings only by `readonly` borrow or `Copy`; callable multiple times concurrently.
* **Mutating `mut (A) => B uses ...E`:** Captures at least one outer binding by `mut` borrow; callable sequentially by a single holder.
* **Consuming `once (A) => B uses ...E`:** Moves at least one non-`Copy` owned binding out of its environment; callable at most once.

---

## 7. The Four Standard Effects and First-Class Continuations

### 7.1 The Four Standard Effects (`prelude`)
```ts
// 1. Recoverable Failure (implicitly open variant rows in signatures):
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
  cellGet<T extends Copy>(c: Ref<R, Cell<T>>): T;
  cellSet<T extends Copy>(c: Ref<R, Cell<T>>, val: T): void;
  listPush<T>(list: Ref<R, RegionList<T, R>>, val: T): void;
}

// 4. External World, Clocks, Locks, Channels & Structured Fiber Scheduling:
export effect Io {
  submitRead(fd: RawFd, buf: mut u8[]): usize uses Fail<IoErr>;
  submitWrite(fd: RawFd, buf: readonly u8[]): usize uses Fail<IoErr>;
  nowMonoNs(): u64;
  sleepNs(durationNs: u64): void;
  syncLock(lockId: u64): void;
  scope<T, row E = []>(body: once (s: mut Scope<E>) => T uses Io, ...E): T uses Io, ...E;
}
```

### 7.2 First-Class Affine Continuations (`Cont<In, Out, E>`) & Pull Generators (`Gen<T>`)
In a handler arm `op(x) resumes k => body`, `k` is an affine value of type `Cont<OpRet, HandleOut, HandledUses>`:
* **Resuming:** `k.resume(val)` consumes `k` by move and resumes the suspended computation up to the next unhandled operation of the handled effect (or completion of the `handle` block).
* **Dropping without Resuming:** If `k` goes out of scope or is dropped without `k.resume(...)` being called, `k`'s destructor immediately unwinds the suspended stack segment from its yield point outward—draining any in-flight kernel `Io` buffers and executing all pending `defer` statements and `Drop` destructors in LIFO order.
* **Pull Generators (`Gen<T, E>`) Implemented in Standard Library Code:**
  Because `k` can be stored inside an enum, `Gen<T, row E = []>` requires zero compiler magic:
  ```ts
  enum Step<T, row E = []> {
    #Done,
    #Yielded { item: T; nextCont: Cont<void, Step<T, E>, E>; },
  }

  export struct Gen<T, row E = []> {
    state: Option<Cont<void, Step<T, E>, E>>;
  }

  export function generate<T, row E = []>(
    producer: once () => void uses Yield<T>, ...E,
  ): Gen<T, E> { ... } // Wraps `producer` in a `handle ... with Yield<T>` returning `Step<T, E>`
  ```
  Calling `g.next(): Option<T> uses ...E` resumes `state`, stores the new continuation on `#Yielded`, and returns `Option.#Some(item)` or `Option.#None`. Dropping `g` early automatically drops `state`, unwinding the generator and running its `defer` / `Drop` cleanups!

### 7.3 Push Iteration (`for (const x of expr)`) and Loop Control
`for (const x of streamExpr) { loopBody }` is syntax sugar for handling `Yield<T>` around `streamExpr`:
* Normal end of `loopBody` or `continue;` calls `k.resume()` in tail position (compiled via evidence passing to a direct call with zero stack switching).
* `break;` drops `k` (synchronously unwinding `streamExpr` and running its `defer`/`Drop` cleanups) and exits the loop.
* `return val;` drops `k`, unwinds local scopes, and returns `val` from the enclosing function.

### 7.4 Structured Concurrency (`Io.scope` & `s.spawn` with `once` Closures)
```ts
export struct Scope<row E = []> {
  // Accepts a `once` closure: may move owned `Send` values (like `conn: Socket`)
  // into the child fiber AND capture shared `readonly U` borrows (`U extends Send`)!
  function spawn<T extends Send>(
    self: mut Self,
    task: once () => T uses Io, ...E,
  ): Fiber<T, E>;
}
```
* **In-Flight Kernel Borrow & Cancellation Drain:** If any child fiber in `Io.scope` fails with an unhandled `Fail<E>`, sibling fibers are cancelled at their next `Io` suspension point: the runtime issues an async kernel cancel (`IORING_OP_ASYNC_CANCEL`), **awaits kernel `CQE` confirmation that any in-flight `buf` borrow is released**, and unwinds the sibling fiber's stack (running `defer` and `Drop`).

---

## 8. Data Parallelism (`par`, `parReduce`) and Recursive `comptime` `Soa<T>`

### 8.1 Parallel Map and Associative Reduction (`std/par`)
```ts
export interface ParSplit {
  type ItemView; // May be `mut T`, `readonly T`, or a 2nd-class record of borrows
  function parForEach(self: mut Self, body: (item: Self.ItemView, index: usize) => void): void;
}

export function par<C extends ParSplit>(
  container: mut C,
  body: (item: C.ItemView, index: usize) => void, // Shared closure, `uses []`
): void {
  container.parForEach(body);
}

export function parReduce<T extends Send, Acc extends Send>(
  items: readonly T[],
  identity: Acc,
  mapOne: (item: readonly T, index: usize) => Acc, // `uses []`
  combine: (a: Acc, b: Acc) => Acc,                 // Associative combiner, `uses []`
): Acc;
```

### 8.2 Recursive Flattening in `comptime` `Soa<T>`
`Soa<T>` is a `comptime` function that **recursively flattens nested records and structs** into leaf scalar planes:
* Given `struct Vec2 { x: f32; y: f32; }` and `struct Particle { pos: Vec2; vel: Vec2; mass: f32; }`, `Soa<Particle>` synthesizes 5 contiguous SIMD-aligned scalar planes (`pos_x`, `pos_y`, `vel_x`, `vel_y`, `mass`) and a nested second-class view record for `ParSplit`:
  ```ts
  type ParticleView = {
    pos: { x: mut f32; y: mut f32; };
    vel: { x: mut f32; y: mut f32; };
    mass: mut f32;
  };
  ```
  so `p.pos.x += p.vel.x * dt` inside `par(mut particles, (p, _i) => ...)` accesses planar SIMD memory with natural nested field syntax!

---

## 9. Core Calculus ($\lambda_{\text{fly}}$ v1.4)

$$\Delta \;|\; \Theta \;|\; \Gamma \;\vdash\; e : \tau \;\!/\;\! \varepsilon \;\dashv\; \Theta_{\text{out}}$$

1. **$\Delta$ (Type, Region, and Unified Row Context):**
   $$\Delta ::= \cdot \;\mid\; \Delta, \alpha : \{\text{Copy}, \text{Send}, \text{Drop}\} \;\mid\; \Delta, \rho : \text{region} \;\mid\; \Delta, r : \text{Row}_{\mathcal{L}}$$
2. **Class Propagation ($\text{class}(\tau) \in \{1, 2\}$):**
   * $\text{class}(\text{readonly }\tau) = \text{class}(\text{mut }\tau) = \text{class}(\text{str}) = \text{class}(\tau[]) = 2$.
   * $\text{class}(\Pi\langle \ell_i : \tau_i \rangle) = \max_i \text{class}(\tau_i)$.
   * $\text{class}(\text{Cont}_{\Gamma_{\text{cap}}}\langle \tau_1, \tau_2, \varepsilon \rangle) = 2$ if $\Gamma_{\text{cap}} \neq \emptyset$, else $1$.
   * Nominal `struct`/`enum` fields and heap container parameters require $\text{class}(\tau) = 1$.
3. **$\Theta$ (Affine First-Class Ownership) & $\Gamma$ (Second-Class View Ledger):**
   * **Region Handler Rule (T-Region):**
     $$\frac{\Delta, \rho : \text{region} \;|\; \Theta \;|\; \Gamma \;\vdash\; e : \tau \;\!/\;\! \text{Region}\langle\rho\rangle, \varepsilon \;\dashv\; \Theta_{\text{out}} \qquad \rho \notin \text{ftv}(\tau) \cup \text{ftv}(\Theta_{\text{out}}) \cup \text{ftv}(\varepsilon)}{\Delta \;|\; \Theta \;|\; \Gamma \;\vdash\; \text{region}(\rho)\ \{ e \} : \tau \;\!/\;\! \varepsilon \;\dashv\; \Theta_{\text{out}}}$$
   * **Abortive vs. Resumptive Handler Borrow Rule (T-Handle):** In `op(x) => e_arm` (abortive), the inner block unwinds first (running `defer` and `Drop`), popping $\Gamma_{\text{body}}$ and restoring $\Gamma_0$ before $e_{\text{arm}}$ runs. In `op(x) resumes k => e_arm`, $\Gamma_{\text{body}}$ is transferred into the affine continuation token $k : \text{Cont}_{\Gamma_{\text{body}}}\langle \tau_{\text{in}}, \tau_{\text{out}}, \varepsilon \rangle$ and stays locked until $k$ is resumed and finishes or $k$ is dropped.

---

## 10. Why Flyscript, Summary of Laws, Rejected Alternatives, and Open Question

### 10.1 Honest Comparison with Existing Languages

| Language | What Flyscript Does That It Cannot | What Flyscript Gives Up Compared to It |
| :--- | :--- | :--- |
| **Rust** | Zero `'a` lifetime annotations; cyclic graphs in `region (R)` via `Ref<R, T>` + `Cell<T>`; no `async`/`await` coloring or `Pin`; structural records and `#Tag` variant errors; deterministic `Io` simulation via handlers. | Cannot store borrows inside long-lived nominal structs (uses owned values, regions, or `Handle<T>`), and uses stackful fiber segments rather than state-machine futures. |
| **TypeScript** | Compiles AOT to unboxed native code & Wasm with zero GC pauses, deterministic `defer`/`Drop`, real integers (`u64`, `i32`), recursive `Soa<T>` layout, and data-race-free multi-core parallelism (`par`). | No width subtyping without `<row R>`, no runtime reflection/`any`, and requires exported function signatures. |
| **Koka** | Zero reference-counting headers or atomic RC traffic on heap values (static affine ownership + regions instead of Perceus RC); explicit unboxed memory layout (`Soa<T>`); static data-race freedom (`Send`). | One-shot continuations only (no multi-shot backtracking) and second-class borrow discipline. |
| **Roc** | In-place mutation (`mut T`), cyclic region graphs (`region (R)`), first-class continuations (`Gen<T>`), low-level FFI, and user-definable effect handlers. | Requires exported function type annotations rather than full-program HM inference. |

### 10.2 Thesis and the Five Laws of Flyscript (Final Form)
**In one line:** *Affine values, one row calculus, handlers for everything, and `comptime`: Church on the outside, Turing on the inside.*

1. **Affine Ownership with Propagating Second-Class Views:** Values have one unique owner by default; borrows (`readonly T`, `mut T`) and structural records/tuples/continuations containing them are lexical views that never enter first-class nominal fields, giving $O(1)$ cross-thread moves and zero `'a` lifetime annotations.
2. **Effect-Gated Shared and Region Mutation (`uses Io`, `uses Region<R>`):** No operation with `uses []` can mutate state through `readonly T` or `Ref<R, T>`, making pure code 100% side-effect-free and allowing `Send` alone to guarantee thread-safe sharing.
3. **One Unified Row Calculus (`#Tag` and `{...}`):** A single sorted row unifier powers structural records `{ x: f64; ...R }`, implicitly open polymorphic variants `[ #Tag | ...R ]`, and algebraic effect rows `uses Io, ...E`, while nominal `struct`/`enum` provide generative identity, recursion, and `Drop`.
4. **One-Shot Algebraic Effect Handlers with First-Class Continuations:** `Fail<E>` (errors), `Io` (async, locks & deterministic simulation), `Region<R>` (append-only arenas), and `Yield<T>` (push loops and pull `Gen<T>` iterators) are all ordinary one-shot effects over affine continuations.
5. **Compile-Time Execution as Ordinary Code:** `comptime` functions over `Type` values (`Soa<T>`, structural trait derivation) replace macro DSLs and bespoke compiler attributes.

### 10.3 Open Question
1. **Target-Neutral SIMD Lane Permutation & Bitmask API (`Simd<T, comptime Lanes: usize>`):** What is the minimal portable `Simd<T, Lanes>` intrinsic surface for horizontal lane shuffles and bitmask extraction (`movemask`) that lowers without emulation cliffs on both ARM64 NEON/SVE and x86-64 AVX2/AVX-512?

---

## Appendix: The Eight Benchmark Programs in Flyscript v1.4

### Program 1: Recursive JSON Parser in a Region (`json_parser.fly`)
Uses nominal `enum Json<region R>` for iso-recursion, `Ref<R, str>` for zero-copy region strings, `RegionList<Ref<R, Json<R>>, R>` for region arrays, and whole-body region inference:

```ts
import { RegionList } from "std/region";

export enum Json<region R> {
  #Null,
  #Bool(bool),
  #Num(f64),
  #Str(Ref<R, str>),
  #Arr(Ref<R, RegionList<Ref<R, Json<R>>, R>>),
  #Obj(Ref<R, RegionList<{ key: Ref<R, str>; val: Ref<R, Json<R>> }, R>>),
}

struct Scanner {
  src: readonly u8[];
  pos: usize;
}

function parseValue<region R>(
  sc: mut Scanner,
): Ref<R, Json<R>> uses Region<R>, Fail<[ #UnexpectedEof | #InvalidJson | #MalformedUtf8 ]> {
  sc.skipWhitespace();
  if (sc.pos >= sc.src.len) { Fail.raise(#UnexpectedEof); }
  match (sc.src[sc.pos]) {
    b'n' => { sc.consumeLiteral("null"); Region.alloc(#Null) },
    b't' => { sc.consumeLiteral("true"); Region.alloc(#Bool(true)) },
    b'f' => { sc.consumeLiteral("false"); Region.alloc(#Bool(false)) },
    b'"' => {
      const rawSlice = sc.readQuotedBytes();
      const s = Region.copyUtf8(rawSlice); // `?R` unifies with `R` from `#Str(Ref<R, str>)`!
      Region.alloc(#Str(s))
    },
    b'[' => {
      sc.pos += 1;
      const items = RegionList.new(); // `?R` unifies with `R` from `#Arr(...)` return type!
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
* **Ergonomic note:** Whole-body region unification (§2.6) completely eliminated the `: Ref<R, str>` and `<Json<R>, R>` local type annotations that v1.3 required.

---

### Program 2: CLI Word Count with Borrowed `HashMap` Lookup (`word_count.fly`)
Uses `Yield<str>` for streaming lines/words, `Borrow<str>` on `HashMap<String, u64>` so looking up a `str` slice only allocates a `String` on first insertion, and `defer` for file cleanup:

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
      // `counts.getMut(word)` uses `String implements Borrow<str>` — zero heap alloc on hit!
      match (counts.getMut(word)) {
        #Some(slot) => { *slot += 1; },
        #None       => { counts.insert(String.fromStr(word), 1); },
      }
    }
  }
  for (const entry of counts.entries()) {
    Stdout.println(`${entry.key}: ${entry.val}`);
  }
}
```
* **Ergonomic note:** Having `let` and mutable references dereference via `slot` or field access is clean; for primitive scalar borrows `slot: mut u64` returned from `getMut`, we use `*slot += 1` (or `counts.updateOrInsert(word, 1, (n) => n + 1)`).

---

### Program 3: Pull Generator Pipeline (`zip` and `take` via First-Class `Cont`) (`generators.fly`)
Solves **Problem B** directly using `generate` and `Gen<T>` (backed by first-class affine continuations `Cont`):

```ts
import { Gen, generate } from "std/iter";

// `zip` turns two push streams into pull generators via `generate` and yields pairs!
// If either caller breaks early, `defer` / `Drop` unwinds both `ga` and `gb` automatically!
export function zip<A, B, row E = []>(
  streamA: once () => void uses Yield<A>, ...E,
  streamB: once () => void uses Yield<B>, ...E,
): void uses Yield<[A, B]>, ...E {
  let ga: Gen<A, E> = generate(streamA);
  let gb: Gen<B, E> = generate(streamB);
  while (true) {
    match ([ga.next(), gb.next()]) {
      [#Some(a), #Some(b)] => Yield.yield([a, b]),
      _                    => break,
    }
  }
}

export function sumPairProducts(xs: readonly i64[], ys: readonly i64[]): i64 {
  let total: i64 = 0;
  for (const [x, y] of zip(() => xs.iter(), () => ys.iter())) {
    if (x < 0 || y < 0) {
      break; // Drops the outer Yield continuation, which drops `ga` and `gb` cleanly!
    }
    total += x * y;
  }
  total
}
```
* **Ergonomic note:** Passing `() => xs.iter()` as a thunk to `zip` is slightly more characters than passing an iterator object, though `xs.iter` can itself be a method reference.

---

### Program 4: Particle Game Loop with Recursive `Soa<T>`, `par`, and `parReduce` (`particles.fly`)
Uses `Soa<Particle>` (recursively flattening `Vec2` fields into 4 contiguous SIMD planes), second-class view records in `par`, and `parReduce` for total kinetic energy:

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
  // 1. Parallel in-place SIMD update via 2nd-class nested view record:
  par(mut particles, (p, _i) => {
    p.pos.x += p.vel.x * dt;
    p.pos.y += p.vel.y * dt;
  });

  // 2. Parallel associative reduction (pure `uses []` closures):
  parReduce(
    particles.asReadonly(),
    0.0 as f32,
    (p, _i) => 0.5 * p.mass * (p.vel.x * p.vel.x + p.vel.y * p.vel.y),
    (e1, e2) => e1 + e2,
  )
}
```
* **Ergonomic note:** Zero awkwardness; recursive flattening of `p.pos.x` + `parReduce` is completely natural.

---

### Program 5: Compiler Symbol Table in an Append-Only Region (`symbol_table.fly`)
Solves **Problem A** using `Ref<R, Scope<R>>`, append-only `RegionList<..., R>`, and `Cell<bool>` for cycle/resolution marking under `uses Region<R>`:

```ts
import { RegionList, Cell } from "std/region";

export struct Decl<region R> {
  name: Ref<R, str>;
  typeId: Cell<u32>;     // Unborrowable `Copy` cell; mutated only via `uses Region<R>`
  visiting: Cell<bool>;  // Cycle-detection mark during type resolution
}

export struct Scope<region R> {
  parent: Option<Ref<R, Scope<R>>>;
  bindings: Ref<R, RegionList<{ name: Ref<R, str>; decl: Ref<R, Decl<R>> }, R>>;
}

impl<region R> Scope<R> {
  export function create(parent: Option<Ref<R, Scope<R>>>): Ref<R, Scope<R>> uses Region<R> {
    Region.alloc({ parent, bindings: RegionList.new() })
  }

  export function define(
    self: Ref<R, Self>,
    name: Ref<R, str>,
  ): Ref<R, Decl<R>> uses Region<R> {
    const decl = Region.alloc(Decl {
      name,
      typeId: Cell.new(0 as u32),
      visiting: Cell.new(false),
    });
    // `RegionList.push` never moves existing elements, so holding aliases to `self` is 100% sound!
    RegionList.push(self.bindings, { name, decl });
    decl
  }

  // Pure lookup (`uses []`!): reads immutable `Ref<R, ...>` and `RegionList` prefix without effects!
  export function lookup(self: Ref<R, Self>, target: str): Option<Ref<R, Decl<R>>> {
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
* **Ergonomic note:** Notice that `lookup` has `uses []` (it is 100% pure) even though `Scope<R>` has a growable `bindings` list, because reading the current snapshot of an append-only `RegionList` is effect-free while `define` requires `uses Region<R>`.

---

### Program 6: Key-Value Store Actor with Zero-Copy Channel Moves (`kv_actor.fly`)
Demonstrates affine ownership moving `String` keys/values and reply channels across tasks in $O(1)$ without `iso` or `recover`:

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
        // `key` and `val` (`String`) move into `store` in O(1) — zero string copies!
        store.insert(key, val);
      },
      #Shutdown => break,
    }
  }
}
```
* **Ergonomic note:** Structural variant rows with inline record payloads (`#Get { key: String; reply: ... }`) make actor message protocols exceptionally concise.

---

### Program 7: Concurrent Web Server Accept Loop (`http_server.fly`)
Solves **Problem C** (moving `conn: Socket` into `s.spawn` via a `once` closure while sharing `db: readonly DbClient` and region data):

```ts
import { Listener, Socket, DbClient } from "std/net";

struct ParsedReq<region R> {
  userId: Ref<R, str>;
  authToken: Ref<R, str>;
}

function parseHeader<region R>(
  raw: readonly u8[],
): Ref<R, ParsedReq<R>> uses Region<R>, Fail<[ #MalformedRequest | #MalformedUtf8 ]> {
  if (raw.len < 16) { Fail.raise(#MalformedRequest); }
  Region.alloc({
    userId: Region.copyUtf8(raw[0..8]),
    authToken: Region.copyUtf8(raw[8..16]),
  })
}

export function handleConnection(conn: mut Socket, db: readonly DbClient): void uses Io {
  handle {
    region (R) {
      let rawBuf: u8[512] = repeat<512>(0);
      const n = conn.read(mut rawBuf);
      const req = parseHeader(rawBuf[0..n]);

      // `req` (`Ref<R, ParsedReq<R>>`) contains no `Cell` or `RegionList`, so it is deeply
      // immutable (`Send`) and shared safely across both fibers inside `Io.scope`:
      const pair = Io.scope((s) => {
        const fProfile = s.spawn(() => db.fetchProfile(req.userId.asStr()));
        const fQuota   = s.spawn(() => db.checkTokenQuota(req.authToken.asStr()));
        { profile: fProfile.join(), quota: fQuota.join() }
      });

      if (!pair.quota.allowed) { Fail.raise(#Unauthorized); }
      conn.writeStatus(200, pair.profile.displayName.asStr());
    }
  } with Fail {
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

export function serveForever(listener: mut Listener, db: readonly DbClient): void uses Io {
  Io.scope((s) => {
    for (let conn of listener.accept()) {
      // `s.spawn` takes a `once` closure: `conn` (owned `Socket`) moves into the spawned
      // fiber in O(1), while `db` (`readonly DbClient`) is captured by shared borrow!
      const _ = s.spawn(() => {
        defer conn.close();
        handleConnection(mut conn, db);
      });
    }
  });
}
```
* **Ergonomic note:** `for (let conn of listener.accept())` + `s.spawn` moving `conn` and `defer conn.close()` is completely natural and 100% leak-free on fiber cancellation.

---

### Program 8: Browser Elm-Architecture UI on WebAssembly (`counter_ui.fly`)
Uses polymorphic variant messages, pure state transitions (`mut State`), and an effectful `Dom<Msg>` rendering tree built in a per-frame `region (R)`:

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
  region (frame) {
    Dom.el("div", [{ key: "class", val: "card" }], () => {
      const label = Region.fmt(frame, `Count: ${model.count} (clicks: ${model.historyClicks})`);
      Dom.el("h1", [], () => Dom.text(label.asStr()));
      Dom.el("button", [], () => { Dom.onClick(#Decrement); Dom.text("-"); });
      Dom.el("button", [], () => { Dom.onClick(#Increment); Dom.text("+"); });
      Dom.el("button", [], () => { Dom.onClick(#Reset);     Dom.text("Reset"); });
    });
  } // <-- Per-frame formatted strings freed in 1 instruction after DOM diffing!
}
```
* **Ergonomic note:** Making `Dom<Msg>` an algebraic effect means UI components don't even need to allocate intermediate virtual-DOM node trees on the heap—they stream element events directly to the host reconciler inside a per-frame region!