# Flyscript Language Specification (v1.0)

File extension: `.fly`

**Changelog (v0.1 $\to$ v1.0):** Evolved from an initial Rust-syntax sketch (v0.1) to a TypeScript-surface specification with affine ownership, second-class borrows, one-shot algebraic effects, and `Pod` fiber regions (v0.2–v0.3), simplified by replacing nominal-only records and `iso`/`recover` with row-polymorphic structural records and default affine isolation (v0.4), and finalized in v1.0 with `Sync` thread-safe sharing rules, user-handleable `Io` simulation semantics, and `io_uring` cancellation-drain safety.

---

## 1. Goals and Non-Goals

### 1.1 Goals
1. **TypeScript surface, systems semantics:** Familiar syntax for developers who read TypeScript (`function`, `(x) => expr`, `const`/`let`, `<T extends U>`, `{ field: value }`, `interface`, `implements`, `type`, ES modules) compiled ahead-of-time to native code with unboxed layouts and deterministic resource destruction.
2. **Structural records with row polymorphism, plus nominal datatypes for abstraction:** Anonymous records `{ x: f64; y: f64 }` and tuples `[T, U]` are structural and support row polymorphism (`<row R>`), while `struct` and `enum` declarations are nominal and generative—providing an abstraction boundary for invariants, custom physical layouts (`@layout`), and `Drop` destructors.
3. **Static affine ownership with second-class borrows:** Every heap allocation (`Box<T>`, `Vec<T>`, `String`, `Pool<T>`) has a single unique owner (`T`). Because there are no unsynchronized shared-mutable pointer types and borrows (`readonly T`, `mut T`) are strictly second-class lexical permissions that never appear inside data fields, every owned value is an isolated subgraph by construction and transfers across concurrent tasks in $O(1)$.
4. **Zero-GC cyclic data via fiber-local regions and typed index pools:** Short-lived cyclic or multi-parent graphs are built inside lexical bump-allocated arenas (`region (r) { ... }`); long-lived dynamic graphs use generational index pools (`Pool<T>` and `Handle<T>`).
5. **Typed algebraic effects with one-shot continuations and deterministic simulation:** Recoverable failure, I/O, clocks, and structured concurrency are tracked via row-polymorphic effect clauses (`uses Io, Fail<E>`) rather than `async`/`await` coloring or untyped exceptions. Because `Io` is an ordinary user-handleable effect, any network or concurrent system can be executed under a seeded in-memory simulation handler without changing application code.
6. **Compile-time execution in the host language:** Generics, type-level computation, and layout specialization are ordinary Flyscript functions evaluated at `comptime`.

### 1.2 Non-Goals
1. **Width subtyping on structural records:** Passing `{ x: f64; y: f64; z: f64 }` to a function expecting `{ x: f64; y: f64 }` without row polymorphism would require dynamic field offset dictionaries or boxing; Flyscript uses monomorphized row polymorphism instead.
2. **Garbage collection:** There is no global or actor-local tracing garbage collector in the language or runtime.
3. **Multi-shot continuations:** Effect handlers may resume a captured continuation at most once.
4. **Arbitrary dependent or non-linear refinement types:** Dependent type checking is decidable, but requires users to construct manual proof terms. Flyscript restricts value-indexed types to `comptime` constants and linear integer constraints (Quantifier-Free Presburger Arithmetic); multi-dimensional array views use `Grid2D<T>` / `Grid3D<T>` rather than non-linear multiplication proofs.
5. **Automatic GPU kernel compilation:** Lowering data-parallel loops to SPIR-V/PTX/Metal requires explicit shared-memory and warp-divergence modeling and is deferred to future work.

---

## 2. Core Design Decisions and Rationales

1. **Structural Records with Row Polymorphism + Nominal `struct` / `enum`:**
   * Record types `{ x: f64; y: f64 }` (including `type` aliases of records) and tuple types `[A, B]` are **structural**: two record types with the same field names and types are identical, and their physical fields are sorted canonically by alignment then lexicographical field name.
   * Functions over records may abstract over unknown trailing fields using a row variable `<row R>`: `function norm<row R>(p: readonly { x: f64; y: f64; ...R }): f64`.
   * `struct` and `enum` declarations are **nominal and generative** (the existential abstraction boundary, as in SML's split between structural records and nominal `datatype`s): only nominal `struct` and `enum` types may implement `Drop`, carry `@layout(soa | packed | c)`, or hide private fields behind module boundaries. Structural records and tuples cannot implement `Drop` directly (though their fields are dropped structurally if non-`Pod`).
   * *Rationale:* Width subtyping requires runtime offset lookups or boxing. Row polymorphism gives the flexibility of TypeScript records while monomorphizing every call site to static byte offsets.
2. **Affine Ownership + Static Reuse (No Perceus RC, No `iso`):**
   * Heap values (`Box<T>`, `Vec<T>`, `String`, `Pool<T>`) use static affine move semantics. There is no `iso` keyword or `recover` block: because borrows cannot be stored in data fields and there is no `Rc<RefCell<T>>`, every owned value is already a disjoint, isolated tree of allocations that moves across threads in $O(1)$.
   * When an owned `Box<T>` is consumed by move and a `Box<U>` is allocated in the same basic block where `sizeof(T) == sizeof(U)` and `alignof(T) == alignof(U)`, the compiler reuses the consumed allocation in place without calling the allocator or storing reference-count headers.
   * *Rationale:* Static uniqueness gives LLVM stronger alias guarantees (`noalias`) than reference counting and eliminates capability ceremony (`iso`/`recover`) that only exists in languages with unrestricted mutable graphs.
3. **`Sync` Thread-Safe Sharing, Synchronized Interior Mutability, and `val`:**
   * Flyscript provides **no unsynchronized interior mutability** (there is no `Cell<T>` or `RefCell<T>`). Interior mutability exists only through thread-safe synchronization primitives: hardware atomics (`AtomicU64`, `AtomicBool`, etc.), `Mutex<T extends Send>`, `RwLock<T extends Send & Sync>`, and runtime-synchronized I/O handles (such as `DbClient`'s connection pool).
   * **`T extends Sync`:** A built-in auto-trait satisfied when `readonly T` is safe to share concurrently across multiple worker threads (`T extends Sync` if and only if `readonly T` is `Send`). Because no unsynchronized interior mutability exists in safe code, every safe type free of raw pointers (`T*`) and `Region<R>` allocator handles satisfies `Sync` automatically.
   * **`T extends val`:** A stricter built-in auto-trait satisfied by any type transitively free of *all* interior mutability (including `Atomic*` and `Mutex<T>`) and raw pointers. Therefore, **`T extends val` strictly implies `T extends Sync`**. Calling `Arc.new<T extends val>(value: T): Arc<T>` moves a deeply immutable value into an atomically reference-counted allocation shareable across tasks in $O(1)$.
   * *Rationale:* Banning unsynchronized `Cell`/`RefCell` ensures that `readonly T` is genuinely thread-safe (`Sync`) across `Async.scope` fibers and `par for` workers while still permitting synchronized `readonly DbClient` handles (`Sync`, though not `val`) to be shared across concurrent fibers.
4. **Strict Ban on Borrows in Data Fields, and `In<R, T>` as `Pod`:**
   * Second-class borrows (`readonly T`, `mut T`, `str`, `T[]`) may never appear as fields of a record, tuple, `struct`, or `enum`.
   * Region pointers `In<R, T>`, region slices `In<R, T[]>`, and region strings `In<R, str>` are plain unboxed pointer/slice representations with no `Drop` destructor; therefore, **`In<R, _>` implements `Pod`** whenever `T extends Pod`.
   * *Rationale:* Banning borrows inside structs eliminates `'a` lifetime parameters on types. Making `In<R, _>` implement `Pod` allows cyclic and nested graphs inside `region (r)` while the rank-2 non-escape rule on `R` guarantees safety.
5. **Cutting Actor-Local Tracing GC in Favor of `Pool<T>` + `Handle<T>`:**
   * Long-lived cyclic state outside lexical regions uses standard-library generational arenas (`Pool<T>` indexed by `Handle<T>`, a 64-bit `{ index: u32; generation: u32 }` `Pod` token).
   * *Rationale:* `Pool<T>` is a single owned value (`Pool<T>`), stores nodes contiguously in cache, requires no write barriers or stack maps, and moves across tasks in $O(1)$.
6. **Fiber-Owned Segmented Regions:**
   * Each stackful fiber owns its own segmented bump-allocator chain (`FiberArena`). Entering `region (r) { ... }` records a watermark `(slabPtr, offset)` on the **current fiber’s** arena; suspending a fiber suspends its region stack with it. Child fibers spawned in `Async.scope` may read `In<R, T>` pointers from a parent region as `readonly` (provided `T extends Sync`), but cannot allocate into a parent fiber's `region (r)` (`Region<R>` is `!Send` and `!Sync`).
   * *Rationale:* Preserves strict LIFO arena teardown per fiber even when thousands of fibers interleave across `Io` suspension points on a worker thread.
7. **User-Handleable `Io` Effect and In-Flight Kernel Borrow Safety:**
   * `Io` is a concrete standard-library effect whose operations (`submitRead`, `submitWrite`, `nowMonoNs`, `sleepNs`, `runScope`) are handled by the runtime's native `io_uring`/`kqueue` scheduler in production, **and may be intercepted by user `handle { ... } with Io` blocks in tests**. `Async.scope` is a thin standard-library wrapper that invokes `Io.runScope`.
   * When an `Io` operation such as `Io.submitRead(fd, mut buf)` suspends a fiber after lending `mut buf` to the OS kernel (e.g. an `io_uring` submission queue entry), the fiber's `mut buf` borrow remains locked across the suspension until kernel completion. If the fiber is cancelled while the operation is in flight, the runtime's `Io` handler issues an asynchronous cancellation (`IORING_OP_ASYNC_CANCEL`) and **must await the kernel's completion queue event (`CQE`) confirming the kernel has released `buf` before unwinding the fiber's stack or dropping the frame/region that owns `buf`**.
   * *Rationale:* Prevents use-after-free kernel DMA writes into stack or region memory when a fiber is cancelled mid-I/O, while keeping `Io` virtualizable for deterministic simulation testing.
8. **Error Conversion (`try expr else ...` and `From<E>`) & `@mustUse` `Result`:**
   * `Result<T, E>` is marked `@mustUse`: an unused `Result` value is a compile-time error unless explicitly passed to `ignore(res)`.
   * `try expr` unwraps `Result<T, E>` (or intercepts `Fail<E>`) and raises `Fail<TargetE>` using `TargetE.from(err)` when `TargetE implements From<E>`. For ad-hoc mapping without a `From` impl, `try expr else (err) => TargetError` (or `try expr else TargetErrorValue` when the error payload is ignored) transforms and raises in one concise form.
   * *Rationale:* Eliminates repetitive `.mapErr((_) => ...)` noise while keeping error conversions explicit and zero-cost.
9. **Heap Allocation, Observational Purity, and Panics:**
   * Heap allocation (`Box`, `Vec`, `Region.alloc`) and deterministic `Drop` are **not** tracked in `uses`. An observationally pure function (`uses` nothing) may allocate temporary local memory and mutate `mut` parameters in place.
   * Out-of-memory, integer division by zero, arithmetic overflow in debug mode (wrapping arithmetic uses explicit `wrappingAdd`), and unrefined out-of-bounds indexing trigger an **unrecoverable fiber panic**, unwinding the fiber stack (running `Drop` destructors and `finally` blocks) and aborting the enclosing `Async.scope` or process. Panics cannot be caught by `handle`.
   * *Rationale:* Keeping allocation and hardware traps out of `uses` avoids polluting pure mathematical and data-parallel (`par for`) signatures.

---

## 3. Flyscript for TypeScript Developers

| Construct | In TypeScript | In Flyscript (`.fly`) |
| :--- | :--- | :--- |
| **Variables (`const` vs `let`)** | `const` prevents variable reassignment, but object properties remain mutable. | **Deep mutability control:** `const x = v` makes `x` and all its owned fields deeply immutable (`mut x` is rejected). `let x = v` allows field mutation and `mut x` borrowing. |
| **Numbers** | Single `number` (`f64`) and `bigint`. | Explicit machine scalars (`i32`, `u64`, `u8`, `usize`, `f32`, `f64`). Unadorned literals (`42`, `200`, `0.5`) infer their type from context; `x as u16` converts explicitly. |
| **Object Literals & `type`** | `{ x: 1, y: 2 }` and `type Point = { x: number; y: number }` are structural with width subtyping. | **Structural with row polymorphism (`<row R>`):** `{ x: 1.0, y: 2.0 }` has structural type `{ x: f64; y: f64 }`. Extra fields are accepted via `<row R>(p: { x: f64; ...R })`, compiled to static offsets with zero boxing. |
| **`struct` & `enum`** | `class` (reference type on GC heap) and numeric/string `enum`. | **Nominal, unboxed value types:** `struct` has inline memory layout, methods, and optional `Drop`. `enum` is a tagged union with payload variants (`Ok(T) \| Err(E)`), matched exhaustively via `match (x) { ... }`. |
| **`interface`** | Structural shape contract. | **Nominal trait (typeclass):** Implemented explicitly via `struct S implements I` or `impl I for S`. Zero-cost static dispatch via `<T extends I>`, or fat-pointer dynamic dispatch via `dyn I`. |
| **Nullability** | `T \| null \| undefined`. | **No `null` or `undefined`:** Use `Option<T>` (`Some(T)` or `None`). Niche optimization ensures `Option<Box<T>>` and `Option<In<R, T>>` are a single 64-bit pointer. |
| **Memory & Aliasing** | Garbage collected; any reference can alias and mutate anything. | **Affine ownership + second-class borrows:** Values move on assignment unless `Pod`. Functions borrow via `readonly T` or `mut T` (`fn(mut buf)` at call site). No GC pauses; no `'a` lifetime annotations on structs. |
| **Async & Exceptions** | `async`/`await` (Promise coloring) and untyped `throw`/`try`/`catch`. | **Typed Algebraic Effects (`uses Io, Fail<E>`):** Direct-style synchronous syntax on stackful fibers (`io_uring`/`kqueue`). Errors use `Result<T, E>` (unwrapped with `try expr` or `try expr else ErrVal`) or `uses Fail<E>`. |
| **Generics & Metaprogramming** | `<T extends U>` erased at runtime; conditional types `T extends U ? X : Y`. | `<T extends U & V>` monomorphized at compile time, plus `comptime` functions that compute `Type` values using ordinary `if`/`for` code. |

---

## 4. Lexical Syntax and Complete Grammar (EBNF)

### 4.1 Lexical & Disambiguation Rules
* **`const` vs. `let`:** `const x = expr` binds an immutable variable (`x` cannot be reassigned, its fields cannot be mutated, and `mut x` cannot be borrowed). `let x = expr` binds a mutable variable (`x` may be reassigned, its fields mutated, and `mut x` borrowed).
* **Numeric and Array Literals:** Numeric literals (`0`, `42`, `3.14159`) carry no type suffixes; their scalar type is inferred bidirectionally from context, defaulting to `i32` and `f64` when unconstrained. Fixed-size array initialization uses `[a, b, c]` or `repeat<N>(val)`.
* **Record and Struct Literals:** `{ field: value, ... }` constructs a nominal `struct` when the bidirectional expected type is that `struct` (or when prefixed as `StructName { field: value }`); otherwise it constructs a structural record `{ field: Type; ... }`. Shorthand `{ userId, authToken }` is equivalent to `{ userId: userId, authToken: authToken }`.
* **Generic Call `<` Disambiguation:** In expression position, `Ident<TypeArgs>(...)` and `Expr.Ident<TypeArgs>(...)` are parsed by speculative lookahead: if `<` is followed by a balanced `TypeArgList` and immediately followed by `(` or `{`, it is parsed as generic instantiation; otherwise `<` is the binary less-than operator.
* **Explicit Mutable Borrow Call-Site Markers:** Passing a mutable borrow requires `mut expr` at both the parameter declaration and the call site (`conn.read(mut rawBuf)`). Passing a shared `readonly` borrow requires no keyword at the call site (`parse(rawBuf)`).

### 4.2 EBNF Grammar

```ebnf
Module          = { ImportDecl | ExportDecl | TopDecl } ;
ImportDecl      = "import" "{" IdentList "}" "from" StringLit ";" ;
ExportDecl      = "export" TopDecl ;

TopDecl         = StructDecl | EnumDecl | InterfaceDecl | ImplDecl
                | TypeAliasDecl | EffectDecl | FunctionDecl | ExternDecl ;

Attr            = "@" Ident [ "(" AttrArgs ")" ] ;
StructDecl      = { Attr } "struct" Ident [ TypeParams ]
                  [ "implements" TypeList ] "{" { MemberDecl } "}" ;
MemberDecl      = FieldDecl | MethodDecl ;
FieldDecl       = Ident ":" Type ";" ;

MethodDecl      = "function" Ident [ TypeParams ] "(" [ SelfParam [ "," ParamList ] | ParamList ] ")"
                  ":" ReturnType [ UsesClause ] Block ;
SelfParam       = "self" ":" ( "Self" | "mut" "Self" | "readonly" "Self" ) ;

EnumDecl        = { Attr } "enum" Ident [ TypeParams ] [ "implements" TypeList ]
                  "{" VariantDecl { "," VariantDecl } [ "," ] "}" ;
VariantDecl     = Ident [ "(" TypeList ")" | "{" { FieldDecl } "}" ] ;

InterfaceDecl   = "interface" Ident [ TypeParams ] "{" { InterfaceSig ";" } "}" ;
InterfaceSig    = "function" Ident [ TypeParams ] "(" [ SelfParam [ "," ParamList ] | ParamList ] ")"
                  ":" ReturnType [ UsesClause ] ;

ImplDecl        = "impl" [ TypeParams ] TypeRef "for" TypeRef "{" { MethodDecl } "}" ;
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
EffectRow       = EffectRef { "," EffectRef } ;
EffectRef       = Ident [ TypeArgs ] ;

TypeParams      = "<" TypeParam { "," TypeParam } ">" ;
TypeParam       = "region" Ident
                | "row" Ident [ "=" RecordType ]
                | "effect" Ident [ "=" "[" [ EffectRow ] "]" ]
                | "comptime" Ident ":" Type
                | Ident [ "extends" ConstraintList ] ;
ConstraintList  = Constraint { "&" Constraint } ;
Constraint      = "Pod" | "Send" | "Sync" | "val" | "Drop" | TypeRef ;

TypeArgs        = "<" TypeArg { "," TypeArg } ">" ;
TypeArg         = Type | Expr | "[" [ EffectRow ] "]" ;

Type            = PrimType
                | "dyn" TypeRef
                | "Region" "<" Ident ">"
                | "In" "<" Ident "," Type ">"
                | RecordType
                | TupleType
                | TypeRef
                | Type "*"
                | Type "[" [ Expr ] "]"
                | [ "mut" | "once" ] "(" [ ClosureParamList ] ")" "=>" ReturnType [ UsesClause ]
                | PrimIntType "where" RefinementPred ;

RecordType      = "{" { FieldDecl } [ "..." Ident [ ";" ] ] "}" ;
TupleType       = "[" Type { "," Type } "]" ;

TypeRef         = Ident [ "." Ident ] [ TypeArgs ] ;
PrimIntType     = "i8" | "i16" | "i32" | "i64" | "isize" | "u8" | "u16" | "u32" | "u64" | "usize" ;
PrimType        = PrimIntType | "f32" | "f64" | "bool" | "str" | "void" | "never" | "Type" ;

Expr            = MatchExpr | RegionExpr | HandleExpr | TryExpr | UnsafeExpr | LambdaExpr | ... ;
MatchExpr       = "match" "(" Expr ")" "{" { MatchArm } "}" ;
MatchArm        = Pattern [ "if" Expr ] "=>" ( Expr "," | Block ) ;
RegionExpr      = "region" "(" Ident ")" Block ;
TryExpr         = "try" Expr [ "else" ( "(" Ident ")" "=>" Expr | Expr ) ] ;
UnsafeExpr      = "unsafe" Block ;

HandleExpr      = "handle" Block "with" EffectRef "{" { HandlerArm } [ ReturnArm ] [ FinallyArm ] "}" ;
HandlerArm      = Ident "(" [ HandlerParamList ] ")" [ "resumes" Ident ] "=>" Block ;
HandlerParamList= Ident [ ":" Type ] { "," Ident [ ":" Type ] } ;
ReturnArm       = "return" "(" Ident [ ":" Type ] ")" "=>" Block ;
FinallyArm      = "finally" "=>" Block ;
```

---

## 5. Types: Structural Records, Nominal Datatypes, Strings, and Refinements

### 5.1 Primitives, Strings, Slices, and Views
* **Scalars (`Pod`):** `i8`, `i16`, `i32`, `i64`, `isize`, `u8`, `u16`, `u32`, `u64`, `usize`, `f32`, `f64`, `bool`, `void`, `never`.
* **Strings:**
  * `str`: a second-class borrowed UTF-8 slice `(ptr: readonly u8*, len: usize)`. String literals `"hello"` have static type `str` in read-only binary data. `str` cannot be stored in a struct or record field.
  * `String`: an owned, growable UTF-8 heap buffer (`String`). Passing `s: String` to a `str` parameter borrows it automatically; `s.asStr(): str` borrows it explicitly.
  * `In<R, str>`: a UTF-8 string slice allocated inside lexical `region (r)`, valid for the lifetime of `R`, implementing `Pod`, and storable inside region structs/records.
* **Arrays, Slices, and Multi-Dimensional Grids:**
  * `T[N]`: inline fixed-size array of `N` elements (`Pod` if `T extends Pod`).
  * `T[]`: second-class borrowed slice view (`readonly T[]` or `mut T[]`).
  * `Grid2D<T>` and `Grid3D<T>`: second-class strided views indexed via `.get(row, col)` where `row: Index<Rows>` and `col: Index<Cols>`, avoiding non-linear `row * stride + col` proof obligations.

### 5.2 Structural Records, Tuples, and Row Polymorphism (`<row R>`)
Anonymous records `{ x: f64; y: f64 }` (and `type` aliases of records) and tuples `[A, B]` are structural: field order in physical memory is canonicalized by alignment descending, then field name ascending. Functions operate over open records via row variables `<row R>` using the same row-unification engine as effect rows:

```ts
type Point2D<row R = {}> = { x: f64; y: f64; ...R };

function distanceSq<row R>(p: readonly Point2D<R>): f64 {
  return p.x * p.x + p.y * p.y;
}
```

### 5.3 Nominal `struct`, `enum`, Methods, and `interface`
`struct` and `enum` declarations create distinct nominal types. Only nominal `struct` and `enum` types may implement `Drop` or carry `@layout(aos | soa | packed | c)`.
* **Methods:** Declared inside `struct` or `enum` with explicit `self: Self` (move), `self: mut Self` (exclusive borrow), or `self: readonly Self` (shared borrow).
* **Interfaces and Coherence:** Interfaces use `<T extends Bound1 & Bound2>` and carry an optional effect row parameter `<effect E = []>`:
  ```ts
  interface Hashable<effect E = []> {
    function hash(self: readonly Self): u64 uses E;
  }
  ```
  Implemented inline via `struct S implements Hashable` or externally via `impl Hashable for S`. **Orphan Rule:** An `impl I for T` declaration is legal only in the module defining `I` or the module defining `T`.

### 5.4 Linear Integer Refinements
Integer types may carry a linear inequality predicate (`where`) over in-scope `const` integers and slice lengths, decided via **Fourier-Motzkin variable elimination with Omega integer tightening over Quantifier-Free Presburger Arithmetic (QF_LIA)**:

```ts
type Index<comptime N: usize> = usize where self < N;

function dotProduct<comptime N: usize>(a: readonly f32[N], b: readonly f32[N]): f32 {
  let sum = 0.0;
  for (const i: Index<N> of 0..N) {
    sum += a[i] * b[i]; // Proven in-bounds statically; zero bounds check emitted
  }
  return sum;
}
```

### 5.5 Bidirectional Local Type Inference
Type checking runs **after** `comptime` specialization and uses bidirectional local inference:
1. **Required Annotations:** Every top-level or exported `function` and method must explicitly annotate parameter types, return type, and `uses` effects.
2. **Inferred Locally:** Inside function bodies, `const`/`let` variable types, numeric literal scalar types, struct literal nominal types (when expected by context), generic type and effect-row arguments at call sites (`Async.scope((s) => ...)`), and closure parameter/return/effect signatures are inferred automatically by propagating expected types inward and synthesized types outward.

---

## 6. Ownership, Second-Class Borrows, Closures, and Regions

### 6.1 Built-in Marker Traits (`Pod`, `Sync`, `val`, `Send`, `Drop`)

| Form | Category | Meaning | Allowed in Record/Struct Field? |
| :--- | :--- | :--- | :--- |
| **`T`** (default) | Owned value | Uniquely owned value; moves on assignment unless `T extends Pod` | Yes |
| **`readonly T`** | 2nd-class borrow | Shared immutable lexical borrow (`Send` across threads iff `T extends Sync`) | **Never** |
| **`mut T`** | 2nd-class borrow | Exclusive mutable lexical borrow (requires `mut x` at call site) | **Never** |
| **`In<R, T>`** | Region pointer | Unboxed pointer/slice into `region(r)`; implements `Pod` | Yes, inside `Struct<region R>` |
| **`Arc<T>`** | Shared heap handle | Atomically refcounted handle; requires `T extends val` | Yes |

Marker traits are derived structurally by the compiler for structural records, tuples, and nominal `struct`/`enum` types from their constituent fields:
* **`T extends Pod`:** Plain Old Data. Satisfied by scalars, `In<R, U>` (when `U extends Pod`), fixed arrays `U[N]`, structural records `{ f1: T1; ... }`, tuples `[T1, ...]`, and nominal `struct`/`enum` types **if and only if every field/variant payload satisfies `Pod` and the type does not implement `Drop`**. (For example, `{ count: u32; name: String }` is **not** `Pod` because `String` owns a heap buffer and implements `Drop`.) `Pod` values copy implicitly on assignment.
* **`T extends Sync`:** Safe to share concurrently across worker threads via `readonly T` borrow (`T extends Sync` if and only if `readonly T` is safe to pass across threads). Because Flyscript provides **no unsynchronized interior mutability** (no `Cell` or `RefCell`)—only thread-safe `Atomic*`, `Mutex<T extends Send>`, `RwLock<T extends Send & Sync>`, and synchronized runtime handles (`DbClient`)—a structural record, tuple, or nominal type satisfies `Sync` **if and only if every field satisfies `Sync` and it contains no raw pointers `U*` and no `Region<R>` allocator handles**. `In<R, T>` satisfies `Sync` whenever `T extends Sync` and region `R` is frozen as read-only (`ro`).
* **`T extends val`:** Deeply immutable when shared. Satisfied by a structural record, tuple, or nominal type **if and only if every field satisfies `val`** (contains no raw pointers `U*` and *no* interior mutability primitives, not even `Atomic*` or `Mutex<T>`). **`T extends val` strictly implies `T extends Sync`**. Required by `Arc<T>`.
* **`T extends Send`:** Safe to transfer ownership across tasks/threads. Satisfied by any owned structural record, tuple, or nominal type **if and only if every field satisfies `Send` and the type contains no region pointers `In<R, _>`, no `Region<R>` handles, and no raw pointers `U*`**.
* **`T extends Drop`:** May be implemented **only by nominal `struct` and `enum` types** (`impl Drop for MyType { function drop(self: mut Self): void { ... } }`). Structural records and tuples cannot implement `Drop` directly, though dropping a structural record or tuple automatically drops any non-`Pod` fields in reverse declaration order.

### 6.2 Second-Class Borrows and Tied Return Signatures (`from paramName`)
* `readonly T` and `mut T` (along with `str`, `T[]`, `Grid2D<T>`) are **second-class**: they may appear as parameter types, local bindings, and tied return types, **never** inside record, tuple, `struct`, or `enum` fields.
* If a function returns a borrow and takes **exactly one** borrowed parameter, the returned borrow ties to that parameter automatically. If it takes **two or more** borrowed parameters, the return type must name the source parameter via `from paramName`:
  ```ts
  function selectSlice(a: readonly u8[], b: readonly u8[], first: bool): readonly u8[] from a {
    return a[0..4];
  }
  ```

### 6.3 Closures and Capture Modes
The compiler infers both the calling mode and escapability of every lambda `(params) => body`:
1. **Calling Modes:**
   * **Shared (`(A) => B uses E`):** Captures outer bindings only by `readonly` borrow or `Pod` copy; callable concurrently multiple times.
   * **Mutating (`mut (A) => B uses E`):** Captures at least one outer binding by `mut` borrow; callable sequentially by a single holder.
   * **Consuming (`once (A) => B uses E`):** Moves at least one non-`Pod` owned binding out of its environment; callable at most once.
2. **Second-Class vs. Escaping Closures:** Any closure that captures a `readonly` or `mut` borrow (or an active `Region<R>` or `In<R, T>`) from an enclosing stack frame is **second-class**: it may be passed downward as a parameter (to `forEach`, `Async.scope`, `par for`, `Result.capture`), but **cannot** be returned from a function, stored in a data structure, or sent over a `Channel<T>`. Escaping closures must capture all environment values by owned move (`once` or shared over `Pod`/`Arc<T>`).

### 6.4 Fiber-Local Lexical Regions (`region (r)`)
Each stackful fiber owns a segmented bump-allocator (`FiberArena`). Entering `region (r) { ... }` pushes a watermark on the current fiber's arena and introduces a rigid region type `R` and allocator handle `r: Region<R>`:
* **Core `Region<R>` methods:**
  * `r.alloc<T extends Pod>(val: T): In<R, T>`
  * `r.allocSlice<T extends Pod>(len: usize, fill: T): In<R, T[]>`
  * `r.copySlice<T extends Pod>(src: readonly T[]): In<R, T[]>`
  * `r.copyStr(src: str): In<R, str>`
  * `r.copyUtf8(src: readonly u8[]): Result<In<R, str>, Utf8Error>`
  * `r.defer(cleanup: once () => void): void` (registers an explicit destructor outside the bump fast path).
* **Non-Escape Rule:** In `region (r) { body } : RetType`, the rigid region identifier `r` must not appear free in `RetType` or in the type of any outer binding mutated by `body`.

---

## 7. Effects, Handlers, Error Handling, and Deterministic Simulation

### 7.1 Effect Declarations, Rows, and Polymorphism
Functions declare unhandled algebraic effects in their `uses` clause. A function with no `uses` clause is observationally pure (`uses []`):

```ts
effect Fail<E> {
  raise(err: E): never;
}

function forEach<T, effect E = []>(
  items: readonly T[],
  visit: (item: readonly T) => void uses E,
): void uses E {
  for (const item of items) {
    visit(item);
  }
}
```

### 7.2 Standard `Io` Effect, In-Flight Borrow Safety, and Deterministic Simulation
Unlike opaque `async` keywords, `Io` is a concrete standard-library effect whose operations represent the boundary between a fiber and the operating system / scheduler. `Async.scope` is a standard-library wrapper that invokes `Io.runScope`:

```ts
// Defined in prelude / "std/io":
export effect Io {
  submitRead(fd: RawFd, buf: mut u8[]): Result<usize, IoError>;
  submitWrite(fd: RawFd, buf: readonly u8[]): Result<usize, IoError>;
  nowMonoNs(): u64;
  sleepNs(durationNs: u64): void;
  runScope<T, effect E = []>(body: once (s: mut Scope<E>) => T uses Io, E): T uses Io, E;
}
```
* **In-Flight Kernel Borrow & Cancellation Drain Rule:** When `Io.submitRead(fd, mut buf)` or `Io.submitWrite(fd, buf)` suspends a fiber after submitting a buffer address to the kernel (`io_uring`), the lexical borrow of `buf` remains active across the suspension point until the kernel operation completes. If the fiber is cancelled while an `Io` operation is in flight, the `Io` handler issues a kernel cancellation request and **waits for the kernel completion event confirming the kernel will no longer read or write `buf` before unwinding the fiber's stack frames or resetting any region owning `buf`**.
* **Production Handler:** At `main`, the runtime installs the native `io_uring` / `kqueue` stackful fiber scheduler handler for `Io`.
* **Deterministic Simulation Handler:** In tests, user code can wrap any subsystem in `handle { ... } with Io { ... }` using a seeded deterministic scheduler (`SimIo`) that intercepts `submitRead`, `submitWrite`, `nowMonoNs`, `sleepNs`, and `runScope`—virtualizing time, simulating packet drops, and interleaving fibers reproducibly on a single OS thread:

```ts
import { SimIo } from "std/testing";

function testTimeoutRecovery(): void {
  // Intercepts `Io`: 5 seconds of virtual sleep takes 0ms real time;
  // fiber scheduling and network faults are 100% reproducible from the seed.
  SimIo.runWithSeed(0xCAFE_BABE, { dropPacketRate: 0.15 }, () => {
    let server = MockServer.start();
    handleConnection(mut server.clientSocket, server.db);
    assert(server.lastStatusCode == 502 || server.lastStatusCode == 200);
  });
}
```

### 7.3 Handler Semantics: Resumptive, Abortive, `return`, and `finally`
1. **Resumptive Arm (`op(args) resumes k => armBody`):** The handled block remains suspended on its fiber stack; all lexical borrows (`mut` and `readonly`) active at the `op` call site remain locked and cannot be accessed by `armBody`. `k` is an affine one-shot continuation: calling `k(val)` resumes the block; if `armBody` exits without calling `k`, `k`'s destructor immediately unwinds the suspended block (waiting for any in-flight kernel `Io` cancellation drain, running `Drop` destructors, and exiting inner regions) before `armBody` returns.
2. **Abortive Arm (`op(args) => armBody`, no `resumes` keyword):** Before `armBody` begins executing, the runtime unwinds the handled block's stack frames back to the `handle` boundary, running all inner `Drop` destructors, resetting inner regions, and **releasing all inner lexical borrows**. Consequently, variables or borrowed parameters (`conn: mut Socket`) that were re-borrowed inside the `handle` block are restored to their pre-`handle` borrow state and may be freely borrowed again inside `armBody`.
3. **`return(v)` and `finally` Ordering:**
   * Normal exit: `body` returns `v` $\to$ optional `return(v)` arm produces `v'` $\to$ `finally` block runs $\to$ `handle` evaluates to `v'`.
   * Abortive exit or dropped continuation `k`: inner `body` unwinds $\to$ handler arm produces `v'` $\to$ `finally` block runs $\to$ `handle` evaluates to `v'`.
   * Unhandled effect or panic propagating out of `body` or a handler arm: inner `body` unwinds $\to$ `finally` block runs $\to$ unwind continues outward.

### 7.4 `Result<T, E>` vs. `Fail<E>` and `try ... else`
* **`Result<T, E>` (`@mustUse`):** Returned by low-level I/O and parsing primitives (`Socket.read`, `Region.copyUtf8`) where immediate caller inspection or error mapping is common. Ignoring a `Result` is a compile error; use `ignore(res)` to discard deliberately.
* **`Fail<E>`:** Used by application and domain pipelines.
* **Ergonomic Unwrapping (`try`):**
  * `try expr`: if `expr` is `Result<T, E>` in a function declaring `uses Fail<TargetE>` where `TargetE implements From<E>`, unwraps `Ok(v)` or calls `Fail.raise(TargetE.from(e))`.
  * `try expr else ErrVal` (or `try expr else (e) => makeErr(e)`): unwraps `Ok(v)` or raises `Fail.raise(ErrVal)` directly without requiring a `From<E>` implementation.
  * `Result.capture(() => body)`: intercepts `Fail<E>` inside `body` and returns `Result<T, E>`.

---

## 8. Concurrency and Parallelism

### 8.1 Structured Concurrency (`Async.scope`)
* **`Async.scope((s) => ...)`:** Invokes `Io.runScope` to spawn child fibers on a lexical nursery `s: mut Scope<E>`. Both the return type `T` and the child effect row `E` are inferred bidirectionally from the closure body.
* **Borrow, `Sync`, and Region Safety Across Fibers:** Because child fibers passed to `s.spawn(() => ...)` may execute in parallel on separate worker threads, they must be **shared closures** where **every outer binding captured by `readonly T` borrow satisfies `T extends Sync`** (or is copied as `Pod extends Send`, or cloned via `Arc<T>`). Any enclosing `region (r)` is frozen to read-only (`ro`) for the duration of `Async.scope`, allowing child fibers to capture `In<R, T>` pointers as `readonly` whenever `T extends Sync`.
* **Cancellation:** `Async.scope` waits for all child fibers to finish before exiting. If any child fiber raises an unhandled effect `Fail<E>`, sibling fibers are cancelled at their next `Io` suspension point: any in-flight kernel `Io` buffers are drained first, and their stacks unwind from the suspended `Io` frame outward (running all `Drop` destructors, resetting fiber regions, and running `finally` clauses of any active resumptive handlers) before `Fail.raise(e)` propagates out of `Async.scope`.

### 8.2 Long-Lived Actors and Channels
Long-lived concurrent state machines communicate over bounded `Channel<T>` where `T extends Send`. Because every owned value (`Vec<T>`, `Box<T>`, `Pool<T>`) is uniquely owned and free of borrows, sending an owned graph or a `Pool<T>` over a channel moves its root descriptor in $O(1)$ with zero copying.

### 8.3 Data Parallelism (`par for` and `@layout(soa)`)
```ts
@layout(soa)
struct Particle {
  posX: f32;
  posY: f32;
  velX: f32;
  velY: f32;
}

function stepPhysics(particles: mut SoaSlice<Particle>, dt: f32): void {
  par for (let p of particles) {
    p.posX += p.velX * dt;
    p.posY += p.velY * dt;
  }
}
```
* **Typing Rule for `par for`:** The loop body must have an **empty `uses` clause** (`uses []`), may capture outer bindings only by `readonly T` borrow **where `T extends Sync`** or by `Pod extends Send` copy, and binds the loop variable `let p` as an exclusive `mut` reference to a disjoint element index (requiring element type `Elem extends Send`). Local heap or `region` allocations inside the loop body use the worker thread's local arena and are permitted.

---

## 9. `comptime`, Modules, and Foreign Function Interface (FFI)

### 9.1 `comptime` Execution and `Type` Values
Functions, parameters, and assertions marked `comptime` execute deterministically on the compiler's bytecode VM during Stage 2 before type/borrow checking:

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

### 9.2 Modules
Every `.fly` file is an ES module (`import { ... } from "...";`, `export`). Module import graphs must form a strict DAG; circular module dependencies are a compile-time error.

### 9.3 C ABI Interop (`extern "C"`, `@layout(c)`, `unsafe`)
* Functions declared `extern "C"` and structs marked `@layout(c)` follow the platform C ABI.
* Calling an `extern "C"` function automatically switches from the current fiber's growable stacklet to the OS worker thread's native contiguous stack for the duration of the call.
* Raw pointers (`T*`, `readonly T*`) may be passed through safe code as `Pod` values (though `!Send` and `!Sync`), but dereferencing a raw pointer (`*ptr`) or calling an `extern "C"` function not wrapped in a safe abstraction requires an explicit `unsafe { ... }` block.

---

## 10. Core Calculus Sketch ($\lambda_{\text{fly}}$)

Surface Flyscript elaborates into a typed core calculus $\lambda_{\text{fly}}$ judged under four contexts:

$$\Delta \;|\; \Theta \;|\; \Gamma \;\vdash\; e : \tau \;\!/\;\! \varepsilon \;\dashv\; \Theta_{\text{out}}$$

1. **Type, Region, Row, and Effect Context ($\Delta$):**
   $$\Delta ::= \cdot \;\mid\; \Delta, \alpha : \text{Bounds} \;\mid\; \Delta, \rho : \text{region}\{\text{rw} \mid \text{ro}\} \;\mid\; \Delta, r : \text{row} \;\mid\; \Delta, \epsilon : \text{eff}$$
2. **Affine Ownership Context ($\Theta$):**
   $$\Theta ::= \cdot \;\mid\; \Theta, x : \text{own}(\tau) \;\mid\; \Theta, x : \text{dead}$$
   Moving a non-`Pod` variable $x$ transitions $x : \text{own}(\tau) \implies x : \text{dead}$. **$\Theta_{\text{out}}$ is the post-evaluation ownership context resulting from $e$**, recording which owned bindings were consumed and which outer mutable variables were updated.
3. **Second-Class Lexical Borrow Ledger ($\Gamma$):**
   $$\Gamma ::= \cdot \;\mid\; \Gamma, b : \text{borrow}(\pi, \text{mut} \mid \text{ro}, \tau)$$
   Maps each active borrow binding $b$ (including incoming borrowed function parameters such as `conn: mut Socket`, which enter the function body as $conn : \text{borrow}(\pi_{\text{caller}}, \text{mut}, \text{Socket}) \in \Gamma_0$) to the root path $\pi$ it locks. Re-borrowing a `mut` parameter `conn` for a sub-expression temporarily pushes a child lock $\text{borrow}(conn, \text{mut}, \text{Socket})$ onto $\Gamma$, suspending direct use of `conn` until that child borrow scope ends.
   * **Parallel & Fiber Capture Rule (T-Spawn / T-Par):** When typechecking a child closure body $e_{\text{child}}$ passed to `Scope.spawn` or `par for`, any outer binding borrowed from $\Theta$ or $\Gamma$ must enter $\Gamma_{\text{child}}$ as $\text{borrow}(\pi, \text{ro}, \tau)$ where $\Delta \vdash \tau : \text{Sync}$, and every active region $\rho \in \Delta$ transitions to $\rho : \text{region}\{\text{ro}\}$ in $\Delta_{\text{child}}$.
   * **Region Non-Escape Rule (T-Region):**
     $$\frac{\Delta, \rho : \text{region}\{\text{rw}\} \;|\; \Theta \;|\; \Gamma, r : \text{borrow}(\rho, \text{mut}, \text{Region}\langle\rho\rangle) \;\vdash\; e : \tau \;\!/\;\! \varepsilon \;\dashv\; \Theta_{\text{out}} \qquad \rho \notin \text{ftv}(\tau) \cup \text{ftv}(\Theta_{\text{out}}) \cup \text{ftv}(\varepsilon)}{\Delta \;|\; \Theta \;|\; \Gamma \;\vdash\; \text{region}(r)\ \{ e \} : \tau \;\!/\;\! \varepsilon \;\dashv\; \Theta_{\text{out}}}$$
   * **Handler Re-Borrow Rule (T-Handle):** Let $\Gamma_0$ be the lexical borrow context entering `handle { e_body } with Eff { ... }`. While `e_body` executes, it may take child re-borrows $\Gamma_{\text{body}}$ of bindings in $\Theta$ or $\Gamma_0$ (such as re-borrowing parameter `conn: mut Socket`).
     * In a **resumptive arm** (`op(x) resumes k => e_arm`), `e_body` is still suspended, so all paths locked in $\Gamma_{\text{body}}$ remain locked during $e_{\text{arm}}$.
     * In an **abortive arm** (`op(x) => e_arm`), `e_body` is unwound first, popping $\Gamma_{\text{body}}$ and restoring the borrow ledger to $\Gamma_0$; therefore, any incoming borrowed parameter `conn` in $\Gamma_0$ is unlocked and available to be re-borrowed inside $e_{\text{arm}}$.

---

## 11. Standard Library Signatures & Complete Validated Example

### 11.1 Standard Library Signatures (`prelude`, `std/net`, `std/async`)

```ts
// From prelude:
@mustUse
export enum Result<T, E> {
  Ok(T),
  Err(E),
}
export function ignore<T, E>(res: Result<T, E>): void {}

// From "std/net":
export enum IoError { ConnectionReset, TimedOut, BrokenPipe }
export struct Profile { displayName: String; }
export struct QuotaStatus { allowed: bool; }

export struct Socket {
  function read(self: mut Self, buf: mut u8[]): Result<usize, IoError> uses Io;
  function writeStatus(self: mut Self, code: u16, body: str): Result<void, IoError> uses Io;
}

// `DbClient` wraps an internally synchronized connection pool and implements `Sync`,
// so `readonly DbClient` may be shared safely across `Async.scope` fibers.
export struct DbClient implements Sync {
  function fetchProfile(self: readonly Self, userId: str): Result<Profile, IoError> uses Io;
  function checkTokenQuota(self: readonly Self, token: str): Result<QuotaStatus, IoError> uses Io;
}

// From "std/async":
export struct Fiber<T, effect E = []> {
  function join(self: Self): T uses Io, E;
}

export struct Scope<effect E = []> {
  function spawn<T extends Send>(self: mut Self, task: () => T uses Io, E): Fiber<T, E>;
}

export namespace Async {
  export function scope<T, effect E = []>(
    body: once (s: mut Scope<E>) => T uses Io, E,
  ): T uses Io, E {
    return Io.runScope(body);
  }
}
```

### 11.2 Complete Validated Example (`http_handler.fly`)

Every line of this program conforms to v1.0, using bidirectional inference for `Async.scope` and `s.spawn`, `Sync`-checked sharing of `readonly DbClient` and frozen `In<reqArena, str>` references, `try ... else` error conversion, shorthand record initialization, and `ignore(...)` for discarded `@mustUse` results:

```ts
import { Socket, DbClient, IoError } from "std/net";
import { Async } from "std/async";

export enum HttpError {
  MalformedRequest,
  Unauthorized,
  BackendError,
}

// Nominal Pod & Sync struct allocated inside lexical region R.
// Holds only `In<R, str>` (which implements Pod and Sync); zero outer borrows.
struct ParsedReq<region R> {
  userId: In<R, str>;
  authToken: In<R, str>;
}

function parseHeader<region R>(
  r: mut Region<R>,
  raw: readonly u8[],
): In<R, ParsedReq<R>> uses Fail<HttpError> {
  if (raw.len < 16) {
    Fail.raise(HttpError.MalformedRequest);
  }
  const userId = try r.copyUtf8(raw[0..8]) else HttpError.MalformedRequest;
  const authToken = try r.copyUtf8(raw[8..16]) else HttpError.MalformedRequest;
  return r.alloc({ userId, authToken });
}

export function handleConnection(
  conn: mut Socket,
  db: readonly DbClient,
): void uses Io {
  handle {
    region (reqArena) {
      let rawBuf: u8[512] = repeat<512>(0);
      const n = try conn.read(mut rawBuf) else HttpError.BackendError;
      const req = parseHeader(mut reqArena, rawBuf[0..n]);

      // Bidirectional inference deduces the return type `{ profile: Profile; quota: QuotaStatus }`
      // and the child effect row `[Fail<HttpError>]` directly from the closure body.
      // `reqArena` transitions to `ro` (`Sync`), and `DbClient` implements `Sync`.
      const pair = Async.scope((s) => {
        const fProfile = s.spawn(() => {
          return try db.fetchProfile(req.userId.asStr()) else HttpError.BackendError;
        });
        const fQuota = s.spawn(() => {
          return try db.checkTokenQuota(req.authToken.asStr()) else HttpError.BackendError;
        });
        return { profile: fProfile.join(), quota: fQuota.join() };
      });

      if (!pair.quota.allowed) {
        Fail.raise(HttpError.Unauthorized);
      }
      try conn.writeStatus(200, pair.profile.displayName.asStr()) else HttpError.BackendError;
    } // <-- `reqArena` fiber watermark reset in O(1); `pair.profile` (`String`) dropped
  } with Fail<HttpError> {
    // Abortive arm (`resumes` omitted): `reqArena` is already unwound and the inner
    // re-borrow of `conn` has ended, restoring `conn: mut Socket` in Gamma_0.
    raise(err) => {
      const code: u16 = match (err) {
        HttpError.MalformedRequest => 400,
        HttpError.Unauthorized     => 401,
        HttpError.BackendError     => 502,
      };
      ignore(conn.writeStatus(code, "error"));
    }
  };
}
```

---

## 12. Compiler Pipeline

1. **Stage 1 — Lexer & Recursive Descent Parser:** Parses `.fly` modules into an untyped CST, resolving `<TypeArgs>(` via speculative lookahead and validating DAG module imports.
2. **Stage 2 — `comptime` Bytecode Evaluator & Monomorphizer:** Evaluates `comptime` functions and constants deterministically, canonicalizing structural record layouts (`{ x: f64; y: f64 }`) and monomorphizing record row variables `<row R>` and generic types `<T>`.
3. **Stage 3 — Bidirectional Type, Effect & Refinement Checker:**
   * Checks structural records, nominal `struct`/`enum`/`interface` coherence, auto-traits (`Pod`, `Sync`, `val`, `Send`), closure capture modes (`once` / `mut` / shared), `@mustUse` results, and infers local bindings, literals, and closure signatures bidirectionally.
   * Unifies `uses` effect rows and defaults interface effect parameters (`effect E = []`).
   * Solves linear integer refinements (`where self < N`) via **Fourier-Motzkin elimination with Omega integer tightening** over QF_LIA.
4. **Stage 4 — Capability, Borrow & Region Pass (Mid-End SSA IR):**
   * Enforces affine move semantics ($\Theta$), lexical borrow exclusivity ($\Gamma$), `Sync` bounds on concurrent captures, tied return borrows (`from param`), and abortive vs. resumptive handler borrow lifetimes.
   * Enforces rank-2 non-escape for every `region (r)` variable and freezes active regions to read-only across `Async.scope`.
   * Performs **Static Affine Reuse** (rewriting `Drop(Box<T>)` followed by `Alloc(Box<U>)` when `sizeof(T) == sizeof(U)` and `alignof(T) == alignof(U)` into in-place mutation).
   * Lowers `@layout(soa)` projections and **Evidence-Passing Effect Transformation** (tail-resumptive handlers compile to direct vtable calls; suspending handlers switch fiber stacklets; `extern "C"` calls switch to the worker thread's native system stack).
5. **Stage 5 — Code Generation:**
   * **Debug:** Cranelift (or C11 backend) for fast incremental compilation.
   * **Release:** LLVM IR with `noalias` and `readonly` attributes derived from `mut`, `readonly`, and owned parameters.

---

## 13. Summary, Rejected Alternatives, and Open Questions

### 13.1 Thesis and the Five Laws of Flyscript
Flyscript combines TypeScript’s readable surface and structural records with a systems core where functional composition (Church) and hardware sympathy (Turing) reinforce rather than fight each other. Every design choice flows from **five invariants**:
1. **Affine Ownership with Second-Class, `Sync`-Checked Borrows:** Values have one unique owner by default; borrows (`readonly T`, `mut T`) are lexical permissions that never enter data fields, giving $O(1)$ cross-thread moves, zero `'a` lifetime annotations, and data-race-free concurrent sharing via `Sync`.
2. **Fiber-Local Regions and Generational Pools for Graphs:** Cyclic and multi-parent structures live in lexical bump regions (`region (r)`) or `Pool<T>` arenas rather than a garbage-collected heap.
3. **Structural Records via Row Polymorphism, Nominal Types for Invariants:** Records `{ x: f64; ...R }` give TypeScript ergonomics with static monomorphized offsets; nominal `struct` and `enum` provide layout control and `Drop`.
4. **One-Shot Algebraic Effects Over Function Coloring:** `Io` and `Fail<E>` replace `async`/`await` and exceptions, compiling to evidence passing or stackful fibers and enabling deterministic simulation testing out of the box.
5. **Compile-Time Execution as Ordinary Code:** `comptime` functions over `Type` values and linear integer refinements replace macro DSLs and runtime bounds checks.

### 13.2 Rejected Alternatives
* **Tracing Garbage Collection (Global or Actor-Local):** Rejected because global GC introduces tail-latency pauses and high memory multipliers, while actor-local GC requires write barriers and root maps for cyclic state that `region (r)` and `Pool<T>` handle with flat cache layout.
* **Unsynchronized Interior Mutability (`Cell<T>`, `RefCell<T>`):** Rejected because single-threaded interior mutability splits `readonly T` into thread-safe and thread-unsafe variants; keeping only synchronized interior mutability (`Atomic*`, `Mutex<T>`) allows almost all safe types to satisfy `Sync` automatically.
* **`iso` Capability and `recover` Blocks:** Rejected because affine ownership plus the ban on borrows in struct fields already guarantees every owned value is an isolated subgraph.
* **Width Subtyping on Structural Records:** Rejected because forgetting fields via subtyping requires dynamic field offset lookups or heap boxing, whereas row polymorphism (`<row R>`) monomorphizes to exact byte offsets.
* **Multi-Shot Continuations:** Rejected because resuming a continuation more than once duplicates affine resources (`Box<T>`, sockets) and invalidates active mutable borrows.
* **Global Hindley-Milner Type Inference:** Rejected because HM unification becomes undecidable or produces inscrutable errors when combined with `comptime` type functions, rank-2 regions, traits, and integer refinements.
* **`async` / `await` Stackless Coroutines:** Rejected because they split the ecosystem into colored functions and prevent borrowing stack/region data naturally across suspension points without self-referential state-machine pinning (`Pin<&mut Self>`).
* **First-Class Lifetime Parameters (`'a`):** Rejected because infectious lifetime annotations on structs and types impose a severe ergonomic tax for patterns better served by second-class borrows, lexical regions, or indices.

### 13.3 Open Question
1. **Target-Neutral SIMD Lane Permutation & Bitmask API (`Simd<T, comptime Lanes: usize>`):** While `@layout(soa)` and `par for` enable auto-vectorization for vertical arithmetic loops, algorithms such as vectorized UTF-8 validation, JSON scanning, and sorting networks require horizontal lane shuffles, saturating arithmetic, and lane-to-bitmask extraction (`movemask`), where ARM64 NEON/SVE and x86-64 AVX2/AVX-512 differ structurally. What is the minimal portable `Simd<T, Lanes>` intrinsic surface that lowers without emulation cliffs on both ARM64 and x86-64?