# Flyscript Language Specification (v1.3 — Final Consolidated Specification)

File extension: `.fly`

**Changelog (v0.1 $\to$ v1.3):** Evolved from an initial Rust-syntax sketch (v0.1) to a TypeScript-surface specification (v0.2–v1.0), unified around a four-pillar core of affine ownership, one row calculus, effect handlers, and `comptime` type functions (v1.1–v1.2), and finalized in v1.3 with **propagating second-class view records/tuples** (making `SoaItem<T>` and zipped slice views ordinary structural types without lifetime parameters) and **purely type-directed region inference** (`R` inferred from bidirectional expected type, otherwise defaulting to `Heap`).

---

## 0. What Changed in v1.3 & Concept-Count Reduction

### 0.1 What Changed in v1.3
1. **Second-Classness Propagates Across Structural Records and Tuples:** Replaced the ad-hoc `SoaItem<T>` special case and the flat "no borrows in fields" phrasing with a single compositional rule: **First-class types (`struct`, `enum`, heap containers, and all-first-class records/tuples) cannot contain second-class components; a structural record or tuple containing any second-class component (`readonly T`, `mut T`, `str`, `T[]`, or another second-class record/tuple) is itself a second-class view type.** Second-class records/tuples (`{ posX: mut f32; posY: mut f32 }`, `[readonly u8[], mut u8[]]`) may appear as function parameters, local bindings, and tied returns (`from param`), and are subject to the exact same lexical borrow-ledger tracking ($\Gamma$) as single borrows—with zero `'a` lifetime parameters.
2. **Purely Type-Directed Region Inference:** Removed escape-analysis-dependent region defaulting. A region type parameter `<region R = Heap>` on an allocation call (`alloc`, `copyUtf8`, `Vec.new`) is inferred strictly from the **bidirectional expected type** (such as a function return type `In<R, ParsedReq<R>>`, an annotated local binding `const s: In<R, str> = ...`, or an explicit type argument `Vec.new<u8, R>()`). When unconstrained by expected type, `R` deterministically defaults to `Heap`.
3. **One-Line Language Summary:** Added to §13.2.

### 0.2 Concept-Count Reduction Table: v1.0 vs. v1.3

| Concept / Mechanism in v1.0 | Status in v1.3 | How v1.3 Unifies It |
| :--- | :--- | :--- |
| 1. Record rows (`<row R>`) + Effect rows (`<effect E>`) + Nominal `enum` errors | **Unified into 1 Row Calculus** | One row kind (`Row`) powers **Records** `{ x: f64; ...R }`, **Polymorphic Variants** `[ #A \| #B(i32) \| ...R ]`, and **Effects** `uses Io, ...E`. |
| 2. Dual error model (`Result<T,E>` + `Fail<E>` + `From<E>` + `try...else` + `@mustUse` `ignore`) | **Unified into `Fail<VariantRow>`** | All fallible functions use implicitly open `uses Fail<[ #Tag1 \| #Tag2 ]>`. Errors compose by automatic row union. `Result` is just a library value from `Fail.capture(...)`. |
| 3. Separate `Region<R>` value API (`r.alloc`, `r.copyUtf8`) vs Heap allocation | **Unified into `Alloc<region R = Heap>` effect** | `region (R) { ... }` is a scoped handler for `Alloc<R>`. `Vec<T, R>`, `String<R>`, `Box<T, R>`, and `alloc(val)` work identically in `Heap` or `R`. |
| 4. Built-in `for (const x of slice)` + unresolved `Iterator` trait | **Unified into `Yield<T>` effect** | `for (const x of expr) { body }` is syntax sugar for handling `Yield<T>` with `continue` = resume and `break`/`return` = drop continuation. |
| 5. `par for` keyword + `@layout(soa)` + `SoaSlice<T>` | **Replaced by library `par` + `comptime` `Soa<T>` + 2nd-class records** | `ParSplit<View>` + `comptime` type reflection (`Type.fieldsOf(T)`) + second-class structural records `{ posX: mut f32; ... }` express `Soa<T>` and parallel loops in library code. |
| 6. Five Marker Traits (`Pod`, `Send`, `Sync`, `val`, `Drop`) + interior mutability | **Reduced to 3 (`Copy`, `Send`, `Drop`) + `uses Shared`** | Gating `Mutex`/`Atomic` behind `uses Shared` makes `readonly T` 100% immutable under `uses []`, so `Send` alone guarantees thread-safe sharing (`Sync`) and `Arc<T>`. |
| 7. Linear Integer Refinements (`where self < N` + Presburger solver) | **Removed from v1.3 (Future Work)** | `Yield<T>` iterators and `par` slice combinators eliminate bounds checks in standard loops without an integer solver in the compiler core. |

---

## 1. Goals and Non-Goals

### 1.1 Goals
1. **TypeScript surface, systems semantics:** Familiar syntax for developers who read TypeScript (`function`, `(x) => expr`, `const`/`let`, `<T extends U>`, `{ field: value }`, `interface`, `implements`, `type`, ES modules) compiled ahead-of-time to native machine code and WebAssembly with unboxed layouts and deterministic destruction.
2. **Structural records and variants with row polymorphism, plus nominal datatypes for abstraction:** Anonymous records `{ x: f64; y: f64 }`, tuples `[T, U]`, and polymorphic variants `[ #Ok(T) | #Err(E) ]` are structural and support row polymorphism (`<row R>`), while `struct` and `enum` declarations are nominal and generative—providing an abstraction boundary for module invariants, `@layout(c | packed)`, and `Drop` destructors.
3. **Static affine ownership with propagating second-class borrows:** Every heap allocation (`Box<T>`, `Vec<T>`, `String`, `Pool<T>`) is a first-class value with a single unique owner (`T`). Borrows (`readonly T`, `mut T`, `str`, `T[]`) and structural records/tuples containing them are **second-class views** restricted to parameters, locals, and tied returns—never stored in first-class data fields—so every owned `Send` value is an isolated subgraph that moves across tasks in $O(1)$ and shares across threads via `readonly T` with zero data races.
4. **Zero-GC cyclic data via effect-handled regions and typed index pools:** Short-lived cyclic or multi-parent graphs are built inside lexical bump-allocated arenas (`region (R) { ... }` handling `Alloc<R>`); long-lived dynamic graphs use generational index pools (`Pool<T>` and `Handle<T>`).
5. **Typed algebraic effects with one-shot continuations and deterministic simulation:** Recoverable failure (`Fail<E>`), I/O (`Io`), shared synchronization (`Shared`), arena allocation (`Alloc<R>`), and stream iteration (`Yield<T>`) are tracked as algebraic effects. Because `Io` and `Shared` are user-handleable effects, concurrent and network systems can be tested under a seeded deterministic simulation handler without changing application code.
6. **Compile-time execution in the host language:** Generics, type-level computation, and `Soa<T>` layout specialization are ordinary Flyscript functions evaluated at `comptime`.

### 1.2 Non-Goals
1. **Width subtyping on structural records:** Passing `{ x: f64; y: f64; z: f64 }` to a function expecting `{ x: f64; y: f64 }` without row polymorphism would require dynamic field offset lookup or boxing; Flyscript uses monomorphized row polymorphism instead.
2. **Garbage collection:** There is no global or actor-local tracing garbage collector in the language or runtime.
3. **Multi-shot continuations:** Effect handlers may resume a captured continuation at most once.
4. **Linear integer refinement solver or automatic GPU lowering in v1:** Moved to post-v1 future work.

---

## 2. Core Design Decisions and Rationales

1. **The Shared-Mutation Effect Law (`uses Shared`):**
   * Every operation that mutates or synchronizes shared state across aliases (`Mutex.lock`, `RwLock.write`, `AtomicU64.fetchAdd`, `Channel.send`) performs the built-in **`Shared`** effect (`uses Shared`), and OS/network handles (`DbClient`, `Socket`) perform **`Io`** (`uses Io`).
   * **Law:** In any computation with an empty effect row (`uses []`), **every `readonly T` reference is 100% transitively immutable**—no bytes reachable through `readonly T` can change, and no side channels can be observed.
   * *Rationale:* Makes `uses []` true mathematical observational purity (allowing `par` to share `readonly T` across cores without a separate `Sync` or `val` trait) while still letting concurrent fibers locking a `Mutex` or querying a `DbClient` share it as `readonly` when `Shared` or `Io` is in scope.
2. **First-Class vs. Second-Class Types (Compositional Borrow Propagation):**
   * Every type in Flyscript is classified as either **first-class** (may be owned, returned freely, stored in `struct`/`enum`/container fields, and captured by escaping closures) or **second-class** (a lexical borrow view restricted to function parameters, local bindings, and tied `from param` returns):
     * Base second-class types: `readonly T`, `mut T`, `str`, `T[]`, `Grid2D<T>`, `Grid3D<T>`, and closures capturing second-class bindings.
     * **Propagation Rule:** A structural record `{ f1: T1; ... }` or tuple `[T1, ...]` is **second-class if and only if at least one of its component types `Ti` is second-class**; otherwise it is first-class. Nominal `struct`, `enum`, and variant types `[ #Tag(T) ]`, as well as type arguments `T` to heap containers (`Vec<T>`, `Box<T>`, `Pool<T>`, `Arc<T>`), **must have exclusively first-class fields/payloads**.
   * *Rationale:* Allowing structural records and tuples to contain `mut T` and `readonly T` fields—by propagating second-class status to the enclosing record/tuple—makes multi-slice views, zipped iterators, and `Soa<T>` element proxies (`{ posX: mut f32; posY: mut f32; ... }`) completely ordinary structural records without introducing `'a` lifetime parameters on nominal data types.
3. **One Allocation Model (`Alloc<region R = Heap>`) with Purely Type-Directed Region Inference:**
   * All dynamic allocations (`Box<T, R>`, `Vec<T, R>`, `String<R>`, and region references `In<R, T>` created by `alloc<R, T>(val)` or `copyUtf8<R>(bytes)`) perform `uses Alloc<R>`, where the region parameter `R` defaults to the global `Heap`.
   * The global `Alloc<Heap>` effect is handled ambiently by the runtime entrypoint (`main`), so `Alloc<Heap>` never needs to be written in `uses` clauses.
   * Writing `region (R) { body }` introduces a fresh rigid region type `R` and handles `Alloc<R>` for `body` using the current fiber's segmented bump allocator (`FiberArena`).
   * **Type-Directed Region Inference Rule:** In any call to a region-parameterized function (`alloc(x)`, `copyUtf8(bytes)`, `Vec.new()`), `R` is unified from the **bidirectional expected type** (for example, a function's declared return type `In<R, ParsedReq<R>>`, an annotated local binding `const s: In<R, str> = copyUtf8(bytes)`, or an explicit type argument `Vec.new<u8, R>()`). If no expected type constrains `R`, `R` defaults deterministically to `Heap`.
   * **The Two Region Soundness Laws:**
     1. *Rank-2 Non-Escape Law:* The region type `R` must not appear free in the return type of `region (R) { body }`, in any outer variable mutated by `body`, or in any unhandled effect payload escaping `body`.
     2. *No-External-Drop Law:* Any type allocated inside a non-`Heap` region `R` (`In<R, T>`, `Vec<T, R>`, `String<R>`) must not transitively own `Heap` allocations or custom `Drop` types (`T` may contain `Copy` scalars, `In<R, U>`, `Vec<U, R>`, or `String<R>`). This guarantees `region (R)` can reset its bump pointer in $O(1)$ on exit without leaking heap memory or OS descriptors.
   * *Rationale:* Purely type-directed inference ensures `Vec.new()` always means `Vec<_, Heap>` unless explicitly typed or contextualized for region `R`, never changing meaning based on downstream escape analysis.
4. **Implicitly Open Polymorphic Variant Rows in `Fail<...>`:**
   * When a function signature declares `uses Fail<[ #Tag1 | #Tag2(T) ]>`, the compiler elaborates the variant row as **open** (`uses Fail<[ #Tag1 | #Tag2(T) | ..._e ]>`), quantifying over an anonymous row tail variable `_e`.
   * Consequently, a caller that can fail with `[ #Tag1 | #Tag2(T) | #Tag3 ]` may call the function directly: `_e` unifies with `#Tag3` by row subsumption. Closed variant rows are written explicitly only in `type` aliases or `match` exhaustiveness checks.
   * *Rationale:* Gives OCaml/Roc-style zero-boilerplate error composition without polluting function signatures with `<row E = []>`.
5. **Effect Inference Within Modules, Explicit `uses` at Module Boundaries:**
   * Exported functions (`export function`), `interface` method signatures, and `extern "C"` declarations must write their `uses` clause explicitly (omitting `uses` on an `export function` means `uses []`).
   * Non-exported module-private functions (`function helper(...)`) and closures (`(x) => ...`) may omit `uses`; the compiler infers their minimal polymorphic effect row from their body.
   * *Rationale:* Preserves fast per-module separate compilation and self-documenting public APIs while eliminating repetitive effect annotations on local helpers.
6. **Long-Lived Cyclic State via `Pool<T, R = Heap>` and `Handle<T>`:**
   * Outside lexical regions, long-lived graphs with cycles or dynamic node deletion use standard-library generational pools (`Pool<T, R = Heap>`) indexed by `Handle<T>` (a 64-bit `{ index: u32; generation: u32 }` `Copy` token).
   * *Rationale:* Avoids global or actor-local GC write barriers while keeping graph nodes contiguous in memory and $O(1)$ movable across tasks.

---

## 3. Flyscript for TypeScript Developers

| Construct | In TypeScript | In Flyscript (`.fly`) |
| :--- | :--- | :--- |
| **Variables (`const` vs `let`)** | `const` prevents variable reassignment, but object properties remain mutable. | **Deep mutability control:** `const x = v` makes `x` and all its owned fields deeply immutable (`mut x` is rejected). `let x = v` allows field mutation and `mut x` borrowing. |
| **Numbers** | Single `number` (`f64`) and `bigint`. | Explicit machine scalars (`i32`, `u64`, `u8`, `usize`, `f32`, `f64`). Unadorned literals (`42`, `200`, `0.5`) infer their type from context; `x as u16` converts explicitly. |
| **Object Literals & `type`** | `{ x: 1, y: 2 }` and `type Point = { x: number; y: number }` are structural with width subtyping. | **Structural with row polymorphism (`<row R>`):** `{ x: 1.0, y: 2.0 }` has structural type `{ x: f64; y: f64 }`. Extra fields are accepted via `<row R>(p: { x: f64; ...R })`, compiled to static offsets with zero boxing. |
| **Union Tags (`#Tag`)** | Discriminated unions `{ kind: "a"; v: number } \| { kind: "b" }`. | **Polymorphic Variant Rows:** `[ #A(i32) \| #B ]` constructed with `#A(42)` or `#B`. Unify automatically across functions and match exhaustively via `match (x) { ... }`. |
| **`struct` & `enum`** | `class` (reference type on GC heap) and numeric/string `enum`. | **Nominal, unboxed value types:** `struct` has inline memory layout, methods, and optional `Drop`. `enum` is a nominal tagged union when module encapsulation is desired. |
| **`interface`** | Structural shape contract. | **Nominal trait (typeclass):** Implemented explicitly via `struct S implements I` or `impl I for S`. Zero-cost static dispatch via `<T extends I>`, or fat-pointer dynamic dispatch via `dyn I`. |
| **Nullability** | `T \| null \| undefined`. | **No `null` or `undefined`:** Use `Option<T>` (`Some(T)` or `None`). Niche optimization ensures `Option<Box<T>>` and `Option<In<R, T>>` are a single 64-bit pointer. |
| **Memory & Aliasing** | Garbage collected; any reference can alias and mutate anything. | **Affine ownership + second-class borrows:** Values move on assignment unless `Copy`. Functions borrow via `readonly T` or `mut T` (`fn(mut buf)` at call site). No GC pauses; no `'a` lifetime annotations on structs. |
| **Async, Generators & Errors** | `async`/`await`, `function*`, and untyped `throw`/`try`/`catch`. | **Typed Algebraic Effects (`uses Io, Fail<E>, Yield<T>`):** Direct-style synchronous syntax on stackful fibers (`io_uring`/`kqueue`/Wasm JSPI). Generators use `Yield<T>`; errors use `Fail<[ #Tag ]>`. |
| **Generics & Metaprogramming** | `<T extends U>` erased at runtime; conditional types `T extends U ? X : Y`. | `<T extends U & V>` monomorphized at compile time, plus `comptime` functions that reflect on and construct `Type` values using ordinary `if`/`for` code. |

---

## 4. Lexical Syntax and Complete Grammar (EBNF)

### 4.1 Lexical, Expression, and Disambiguation Rules
* **Expression-Oriented Blocks & Semicolons:** Blocks `{ stmt1; stmt2; finalExpr }`, `if`, `match`, `region`, and `handle` evaluate to their final operand expression. Inside `{ ... }`, a statement ending with `;` must have type `void` (non-`void` values are explicitly discarded with `const _ = expr;`). Omitting the trailing `;` on the last expression yields that expression as the block's value; ending the block with `;` yields `void`. `return expr;` performs an early return from the enclosing function.
* **`const` vs. `let`:** `const x = expr` binds a deeply immutable variable (`x` cannot be reassigned, its fields cannot be mutated, and `mut x` cannot be borrowed). `let x = expr` binds a mutable variable (`x` may be reassigned, its fields mutated, and `mut x` borrowed).
* **Numeric and Array Literals:** Numeric literals (`0`, `42`, `3.14159`) carry no type suffixes; their scalar type is inferred bidirectionally from context, defaulting to `i32` and `f64` when unconstrained. Fixed-size array initialization uses `[a, b, c]` or `repeat<N>(val)`.
* **Record and Struct Literals:** `{ field: value, ... }` constructs a nominal `struct` when the bidirectional expected type is that `struct` (or when prefixed as `StructName { field: value }`); otherwise it constructs a structural record `{ field: Type; ... }`. Field punning `{ userId, authToken }` is equivalent to `{ userId: userId, authToken: authToken }`.
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
StructDecl      = [ Attr ] "struct" Ident [ TypeParams ]
                  [ "implements" TypeList ] "{" { MemberDecl } "}" ;
MemberDecl      = FieldDecl | MethodDecl ;
FieldDecl       = Ident ":" FieldType ";" ;
FieldType       = [ "mut" | "readonly" ] Type ;   (* 2nd-class allowed only in structural RecordType *)

MethodDecl      = "function" Ident [ TypeParams ] "(" [ SelfParam [ "," ParamList ] | ParamList ] ")"
                  ":" ReturnType [ UsesClause ] Block ;
SelfParam       = "self" ":" ( "Self" | "mut" "Self" | "readonly" "Self" ) ;

EnumDecl        = [ Attr ] "enum" Ident [ TypeParams ] [ "implements" TypeList ]
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
EffectRow       = ( EffectRef | "..." Ident ) { "," ( EffectRef | "..." Ident ) } ;
EffectRef       = Ident [ TypeArgs ] ;

TypeParams      = "<" TypeParam { "," TypeParam } ">" ;
TypeParam       = "region" Ident [ "=" TypeRef ]
                | "row" Ident [ "=" ( RecordType | VariantType | "[" [ EffectRow ] "]" ) ]
                | "comptime" Ident ":" Type
                | Ident [ "extends" ConstraintList ] [ "=" Type ] ;
ConstraintList  = Constraint { "&" Constraint } ;
Constraint      = "Copy" | "Send" | "Drop" | TypeRef ;

TypeArgs        = "<" TypeArg { "," TypeArg } ">" ;
TypeArg         = Type | Expr | "[" [ EffectRow ] "]" ;

Type            = PrimType
                | "dyn" TypeRef
                | "In" "<" Ident "," Type ">"
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

TypeRef         = Ident [ "." Ident ] [ TypeArgs ] ;
PrimIntType     = "i8" | "i16" | "i32" | "i64" | "isize" | "u8" | "u16" | "u32" | "u64" | "usize" ;
PrimType        = PrimIntType | "f32" | "f64" | "bool" | "str" | "void" | "never" | "Type" ;

Block           = "{" { Stmt ";" } [ Expr ] "}" ;
Stmt            = ConstDecl | LetDecl | AssignStmt | ReturnStmt | BreakStmt | ContinueStmt | Expr ;
Expr            = IfExpr | MatchExpr | RegionExpr | HandleExpr | ForExpr | UnsafeExpr | LambdaExpr | ... ;
IfExpr          = "if" "(" Expr ")" Block [ "else" ( IfExpr | Block ) ] ;
MatchExpr       = "match" "(" Expr ")" "{" { MatchArm } "}" ;
MatchArm        = Pattern [ "if" Expr ] "=>" ( Expr "," | Block ) ;
RegionExpr      = "region" "(" Ident ")" Block ;
ForExpr         = "for" "(" ( "const" | "let" ) Ident "of" Expr ")" Block ;
UnsafeExpr      = "unsafe" Block ;

HandleExpr      = "handle" Block "with" EffectRef "{" { HandlerArm } [ ReturnArm ] [ FinallyArm ] "}" ;
HandlerArm      = Ident "(" [ HandlerParamList ] ")" [ "resumes" Ident ] "=>" Block ;
HandlerParamList= Ident [ ":" Type ] { "," Ident [ ":" Type ] } ;
ReturnArm       = "return" "(" Ident [ ":" Type ] ")" "=>" Block ;
FinallyArm      = "finally" "=>" Block ;
```

---

## 5. Types: Unified Rows, Nominal Datatypes, and Strings

### 5.1 Primitives, Strings, and Slices
* **Scalars (`Copy`, First-Class):** `i8`, `i16`, `i32`, `i64`, `isize`, `u8`, `u16`, `u32`, `u64`, `usize`, `f32`, `f64`, `bool`, `void`, `never`.
* **Strings:**
  * `str`: a second-class borrowed UTF-8 slice `(ptr: readonly u8*, len: usize)`. String literals `"hello"` have static type `str` in read-only binary data.
  * `String<region R = Heap>`: a first-class owned, growable UTF-8 buffer allocated in region `R` (defaulting to `Heap`). Passing `s: String<R>` to a `str` parameter borrows it automatically; `s.asStr(): str from s` borrows it explicitly.
  * `In<R, str>`: a first-class immutable UTF-8 string slice bump-allocated inside `region (R)`, implementing `Copy`, and storable inside region-parameterized structs/records.
* **Arrays, Slices, and Multi-Dimensional Grids:**
  * `T[N]`: inline fixed-size array of `N` first-class elements (`Copy` if `T extends Copy`).
  * `T[]`: second-class borrowed slice view (`readonly T[]` or `mut T[]`).
  * `Grid2D<T>` and `Grid3D<T>`: second-class strided views indexed via `.get(row, col)`.

### 5.2 One Unified Row Calculus: Records, Variants, and Effects
Flyscript uses a single Rémy-style sorted row unifier across three type constructors:
1. **Structural Record Rows (`{ field: Type; ...R }`):** Anonymous records and `type` aliases of records are structural; physical layout is sorted by alignment descending then field name ascending:
   ```ts
   type Point2D<row R = {}> = { x: f64; y: f64; ...R };

   function distanceSq<row R>(p: readonly Point2D<R>): f64 {
     p.x * p.x + p.y * p.y
   }
   ```
2. **Polymorphic Variant Rows (`[ #Tag(Payload) | ...R ]`):** Tags prefixed with `#` (`#Malformed`, `#HttpStatus(u16)`) construct structural sum types without pre-declaration. In `uses Fail<[ #A | #B ]>` positions, variant rows are **implicitly open** (`[ #A | #B | ..._ ]`), so calling two functions with different failure tags automatically unifies their tag sets into the combined variant row.
3. **Effect Rows (`uses Io, Fail<E>, ...Eff`):** Unhandled algebraic effects form a row of effect labels.

### 5.3 Nominal `struct`, `enum`, Methods, and `interface`
`struct` and `enum` declarations create distinct first-class nominal types. Only nominal `struct` and `enum` types may implement `Drop` or carry `@layout(c | packed)`.
* **Methods:** Declared inside `struct` or `enum` with explicit `self: Self` (move), `self: mut Self` (exclusive borrow), or `self: readonly Self` (shared borrow).
* **Interfaces and Coherence:** Interfaces use `<T extends Bound1 & Bound2>` and carry an optional effect row parameter `<row E = []>`:
  ```ts
  interface Hashable<row E = []> {
    function hash(self: readonly Self): u64 uses ...E;
  }
  ```
  Implemented inline via `struct S implements Hashable` or externally via `impl Hashable for S`. **Orphan Rule:** An `impl I for T` declaration is legal only in the module defining `I` or the module defining `T`.

### 5.4 Bidirectional Local Type, Region & Effect Inference
Type checking runs **after** `comptime` specialization:
1. **Required Annotations:** Every `export function`, `interface` method signature, and `extern "C"` declaration must explicitly annotate its parameter types, return type, and `uses` clause (omitting `uses` on an `export function` means `uses []`).
2. **Inferred Locally:** Non-exported module-private `function` declarations may omit `uses` (their minimal polymorphic effect row is inferred). Inside function bodies, `const`/`let` variable types, numeric literal scalar types, struct literal nominal types (when expected by context), generic type and row arguments at call sites, and closure signatures are inferred bidirectionally.
3. **Purely Type-Directed Region Parameter Inference:** For any function or method parameterized by `<region R = Heap>` (such as `alloc`, `copyUtf8`, `Vec.new`), `R` is unified from the bidirectional expected type at the call site (e.g., an annotated binding `const s: In<R, str> = copyUtf8(bytes)`, a function return type `In<R, ParsedReq<R>>`, or an explicit type argument `copyUtf8<R>(bytes)`). When unconstrained by expected type, `R` defaults to `Heap`.

---

## 6. Ownership, Second-Class Views, Closures, and Marker Traits

### 6.1 Three Marker Traits (`Copy`, `Send`, `Drop`) and `Arc<T>`

| Form | Class | Meaning | Allowed in First-Class `struct`/`enum`? | Allowed in Structural Record/Tuple? |
| :--- | :--- | :--- | :--- | :--- |
| **`T`** (default) | 1st-class | Uniquely owned value; moves unless `T extends Copy` | Yes | Yes (record remains 1st-class) |
| **`In<R, T>`** | 1st-class | Unboxed pointer/slice into `region (R)`; is `Copy` | Yes (in `Struct<region R>`) | Yes (record remains 1st-class) |
| **`Arc<T>`** | 1st-class | Atomically refcounted `Heap` handle (`T extends Send`) | Yes | Yes (record remains 1st-class) |
| **`readonly T`** | 2nd-class | Shared deeply immutable lexical borrow | **Never** | Yes (makes record **2nd-class**) |
| **`mut T`** | 2nd-class | Exclusive mutable lexical borrow (`mut x` at call) | **Never** | Yes (makes record **2nd-class**) |
| **2nd-class `{...}`** | 2nd-class | Record/tuple with $\ge 1$ second-class component | **Never** | Yes (makes outer record **2nd-class**) |

Marker traits apply to **first-class types** and are derived structurally for first-class records, tuples, variants, and nominal types from their constituent fields:
1. **`T extends Copy`:** Trivially copyable bits (scalars, `In<R, U>` when `U extends Copy`, fixed arrays `U[N]`, and first-class composites whose fields are all `Copy` and do not implement `Drop`). Assigning a `Copy` value copies bits without invalidating the source binding.
2. **`T extends Send`:** Safe to transfer across tasks or share as `readonly T` across worker threads. Satisfied by any first-class type whose fields are all `Send` and that contains **no non-`Heap` region references (`In<R, _>`, `Vec<_, R>`, `String<R>` where `R != Heap`)** and **no raw pointers `U*`**. Because any mutation through a shared handle (`Mutex<T>`, `Atomic*`, `DbClient`) requires `uses Shared` or `uses Io`, **`T extends Send` guarantees both safe ownership transfer and safe concurrent `readonly T` sharing**, as well as safe wrapping in `Arc.new<T extends Send>(val: T): Arc<T>`.
3. **`T extends Drop`:** Implemented only by nominal `struct` and `enum` types (`impl Drop for MyType { function drop(self: mut Self): void { ... } }`). First-class structural records, tuples, and variants cannot implement `Drop` directly, though dropping them automatically drops any non-`Copy` fields in reverse declaration order.

### 6.2 Propagating Second-Class Views and Tied Returns (`from paramName`)
* **Second-Class Propagation Rule:** Any structural record `{ f1: T1; ... }` or tuple `[T1, ...]` that contains one or more second-class components (`readonly U`, `mut U`, `str`, `U[]`, `Grid2D<U>`, or a nested second-class record/tuple) is itself a **second-class view type**.
* **Where Second-Class Types May Appear:** A second-class type (whether a single borrow `mut T` or a composite view `{ posX: mut f32; posY: mut f32 }`) may appear **only** as a function parameter type, a local variable binding (`const` or `let`), or a function return type tied to an input parameter. It **cannot** be a field of a nominal `struct`, `enum`, or variant tag, cannot instantiate a container type parameter (`Vec<V>`, `Box<V>`, `Option<V>` where `V` must be first-class), and cannot be captured by an escaping closure.
* **Borrow Ledger Tracking for Second-Class Records:** Constructing a second-class record `{ a: mut x, b: mut y }` records independent borrow locks on root paths `x` and `y` in the lexical borrow ledger $\Gamma$ (rejecting overlapping mutable paths such as `{ a: mut x, b: mut x }`).
* **Tied Return Rule (`from paramName`):** If a function returns any second-class type and takes **exactly one** second-class parameter, the returned view ties to that parameter's borrow lock(s) automatically. If it takes **two or more** second-class parameters, the return type must name the source parameter via `from paramName`:
  ```ts
  function pairPrefix(
    a: { left: readonly u8[]; right: readonly u8[] },
    b: readonly u8[],
  ): { left: readonly u8[]; right: readonly u8[] } from a {
    { left: a.left[0..4], right: a.right[0..4] }
  }
  ```

### 6.3 Closures and Capture Modes
The compiler infers both the calling mode and escapability of every lambda `(params) => body`:
1. **Calling Modes:**
   * **Shared (`(A) => B uses ...E`):** Captures outer bindings only by `readonly` borrow (or second-class record of `readonly` borrows) or `Copy`; callable concurrently multiple times.
   * **Mutating (`mut (A) => B uses ...E`):** Captures at least one outer binding by `mut` borrow (or second-class record containing a `mut` component); callable sequentially by a single holder.
   * **Consuming (`once (A) => B uses ...E`):** Moves at least one non-`Copy` owned binding out of its environment; callable at most once.
2. **Second-Class vs. Escaping Closures:** Any closure that captures a second-class binding or a non-`Heap` region reference `In<R, _>` from an enclosing stack frame is **second-class**: it may be passed downward as a parameter (to `forEach`, `Async.scope`, `par`, `Fail.capture`), but **cannot** be returned from a function, stored in a data structure, or sent over a `Channel<T>`. Escaping closures must capture all environment values by first-class owned move (`once` or shared over `Copy`/`Arc<T>`).

---

## 7. Handlers for Everything: Errors, Allocation/Regions, Iteration, `Io`, and `Shared`

### 7.1 Standard Effects Overview (`prelude`)
```ts
export effect Fail<E> {
  raise(err: E): never;
}

export effect Alloc<region R = Heap> {
  allocBytes(size: usize, align: usize): In<R, u8[]>;
}

export effect Yield<T> {
  yield(item: T): void;
}

export effect Shared {
  // Performed by Mutex.lock, RwLock.read/write, Atomic*.fetchAdd/store/load, Channel.send/recv
  synchronize(): void;
}

export effect Io {
  submitRead(fd: RawFd, buf: mut u8[]): usize uses Fail<IoErr>;
  submitWrite(fd: RawFd, buf: readonly u8[]): usize uses Fail<IoErr>;
  nowMonoNs(): u64;
  sleepNs(durationNs: u64): void;
  runScope<T, row E = []>(body: once (s: mut Scope<E>) => T uses Io, ...E): T uses Io, ...E;
}
```

### 7.2 Error Handling (`Fail<E>` and `Fail.capture`)
All recoverable failures use `uses Fail<E>` where `E` is an implicitly open polymorphic variant row (`[ #MalformedRequest | #Unauthorized ]`).
* At FFI or secondary-cleanup boundaries where an error should be reified as data rather than propagated, `Fail.capture(() => expr)` handles `Fail<E>` and returns `Result<T, E>` (`enum Result<T, E> { Ok(T), Err(E) }`). Conversely, `Fail.unwrap(result)` raises `Fail.raise(err)` on `Err(err)`.

### 7.3 Allocation (`Alloc<R>`) and Fiber-Local Lexical Regions (`region (R)`)
Each stackful fiber owns a segmented bump-allocator (`FiberArena`). Entering `region (R) { body }` pushes a watermark on the current fiber's arena, introduces a rigid region type `R`, and installs a tail-resumptive handler for `Alloc<R>`:
* **Standard Region Allocation Primitives (in `prelude`, using `Alloc<R>`):**
  * `alloc<region R = Heap, T extends Copy>(val: T): In<R, T> uses Alloc<R>`
  * `allocSlice<region R = Heap, T extends Copy>(len: usize, fill: T): In<R, T[]> uses Alloc<R>`
  * `copySlice<region R = Heap, T extends Copy>(src: readonly T[]): In<R, T[]> uses Alloc<R>`
  * `copyStr<region R = Heap>(src: str): In<R, str> uses Alloc<R>`
  * `copyUtf8<region R = Heap>(src: readonly u8[]): In<R, str> uses Alloc<R>, Fail<[ #MalformedUtf8 ]>`
  * `Vec.new<T, region R = Heap>(): Vec<T, R> uses Alloc<R>`
  * `String.new<region R = Heap>(): String<R> uses Alloc<R>`
* **Purely Type-Directed Region Selection:** In any call to `alloc(...)`, `copyUtf8(...)`, or `Vec.new()`, `R` is unified strictly from the bidirectional expected type (such as a function return type `In<R, ParsedReq<R>>`, an annotated local binding `const s: In<R, str> = copyUtf8(bytes)`, or an explicit type argument `Vec.new<u8, R>()`). When unconstrained by expected type, `R` defaults to `Heap`.
* **Two Region Laws:** (1) *Rank-2 Non-Escape:* `R` cannot appear free in the return type of `region (R) { body }`, in any outer variable mutated by `body`, or in any unhandled effect payload escaping `body`. (2) *No-External-Drop:* Types allocated in `R != Heap` may only contain `Copy` types and `R`-allocated containers (`Vec<U, R>`, `String<R>`, `In<R, U>`), never `Heap`-owned types or `Drop` handles.

### 7.4 Iteration as `Yield<T>` (`for`, `continue`, `break`, `return`)
A stream or iterator is any expression performing `uses Yield<T>` (where `T` may be a first-class value or a second-class view). The loop:
```ts
for (const x of streamExpr) {
  loopBody
}
```
desugars to a handler of `Yield<T>` around `streamExpr`:
* **Normal step & `continue`:** Reaching the end of `loopBody` or executing `continue;` invokes the one-shot continuation `k()` in tail position (compiled via evidence passing to a direct call with zero stack switch).
* **`break;`:** Immediately **drops `k` without calling it** and exits the `handle` block. By the one-shot continuation drop rule (§7.5), dropping `k` synchronously unwinds the suspended `streamExpr` stack from its `Yield.yield` point outward—running all `Drop` destructors and `finally` blocks inside the generator before control continues past the `for` loop!
* **`return val;` inside `loopBody`:** Drops `k` (unwinding the generator and running all generator `Drop`/`finally` cleanups), unwinds any enclosing local scopes, and returns `val` from the enclosing function.

```ts
// Example: A database cursor generator automatically closes its cursor on `break`!
function queryUsers(db: readonly DbClient): void uses Io, Yield<User> {
  let cursor: DbCursor = db.openCursor("SELECT * FROM users"); // Implements `Drop`
  while (cursor.hasNext()) {
    Yield.yield(cursor.next());
  }
} // <-- `cursor.drop()` runs automatically even if the caller exits early with `break;`!
```

### 7.5 Handler Semantics: Resumptive, Abortive, `return`, and `finally`
1. **Resumptive Arm (`op(args) resumes k => armBody`):** The handled block remains suspended on its fiber stack; all lexical borrows (`mut` and `readonly`) active at the `op` call site remain locked and cannot be accessed by `armBody`. `k` is an affine one-shot continuation: calling `k(val)` resumes the block; if `armBody` exits without calling `k`, `k`'s destructor immediately unwinds the suspended block (waiting for any in-flight kernel `Io` cancellation drain, running `Drop` destructors, and exiting inner regions) before `armBody` returns.
2. **Abortive Arm (`op(args) => armBody`, no `resumes` keyword):** Before `armBody` begins executing, the runtime unwinds the handled block's stack frames back to the `handle` boundary, running all inner `Drop` destructors, resetting inner regions, and **releasing all inner lexical borrows**. Consequently, variables or borrowed parameters (`conn: mut Socket`) that were re-borrowed inside the `handle` block are restored to their pre-`handle` borrow state and may be freely borrowed again inside `armBody`.
3. **`return(v)` and `finally` Ordering:**
   * Normal exit: `body` returns `v` $\to$ optional `return(v)` arm produces `v'` $\to$ `finally` block runs $\to$ `handle` evaluates to `v'`.
   * Abortive exit or dropped continuation `k`: inner `body` unwinds $\to$ handler arm produces `v'` $\to$ `finally` block runs $\to$ `handle` evaluates to `v'`.
   * Unhandled effect or panic propagating out of `body` or a handler arm: inner `body` unwinds $\to$ `finally` block runs $\to$ unwind continues outward.

### 7.6 Panics and Observational Purity
* Out-of-memory on `Heap`, integer division by zero, arithmetic overflow in debug mode (wrapping arithmetic uses explicit `wrappingAdd`), and out-of-bounds slice indexing trigger an **unrecoverable fiber panic**, unwinding the fiber stack (running `Drop` destructors and `finally` blocks) and aborting the enclosing `Async.scope` or process. Panics cannot be caught by `handle`.
* Heap allocation (`Alloc<Heap>`) is ambient and not written in `uses`. A function with `uses []` is observationally pure: it may allocate local memory, open local `region (R)` arenas, and mutate `mut` parameters (or `mut` fields of a second-class view parameter) in place, but cannot perform `Io`, `Shared`, or `Fail`.

---

## 8. Concurrency, Parallelism, and Targets

### 8.1 Structured Concurrency (`Async.scope`) and In-Flight Borrow Drain
* **`Async.scope((s) => ...)`:** Invokes `Io.runScope` to spawn child fibers on a lexical nursery `s: mut Scope<E>`. Both the return type `T` and the child effect row `E` are inferred bidirectionally from the closure body.
* **Borrow & Region Sharing Across Fibers:** Child fibers passed to `s.spawn(() => ...)` must be **shared closures** where every captured `readonly T` binding satisfies `T extends Send` (or is a `readonly In<R, T>` where `T extends Send`). Any enclosing `region (R)` has its `Alloc<R>` handler suspended (preventing concurrent bump allocation into `R`) for the duration of `Async.scope`, while allowing child fibers to read `In<R, T>` pointers safely.
* **In-Flight Kernel Borrow & Cancellation Drain:** When `Io.submitRead(fd, mut buf)` or `Io.submitWrite(fd, buf)` suspends a fiber after submitting a buffer address to the kernel (`io_uring`), the lexical borrow of `buf` remains active across the suspension point. If any child fiber in `Async.scope` raises an unhandled `Fail<E>`, sibling fibers are cancelled at their next `Io` suspension point: **the runtime issues an async kernel cancel (`IORING_OP_ASYNC_CANCEL`) and awaits the kernel completion event (`CQE`) confirming `buf` is no longer accessed by DMA before unwinding the cancelled fiber's stack frames or resetting any region owning `buf`**.

### 8.2 Data Parallelism (`par` and `ParSplit`) and `comptime` `Soa<T>`
Multi-core data parallelism is a library function in `std/par`. Because **second-classness propagates across structural records (§2.2, §6.2)**, a container can yield either a single `mut Elem` borrow or a **second-class structural record of disjoint `mut` field borrows** (`{ posX: mut f32; posY: mut f32; ... }`) per index:

```ts
// In "std/par":
export interface ParSplit {
  // `ItemView` may be a 2nd-class borrow (`mut T`) or a 2nd-class structural record of `mut` borrows!
  type ItemView;
  function parForEach(self: mut Self, body: (item: Self.ItemView, index: usize) => void): void;
}

export function par<C extends ParSplit>(
  container: mut C,
  body: (item: C.ItemView, index: usize) => void, // Shared closure with `uses []`!
): void {
  container.parForEach(body);
}
```
* **How `Soa<T>` and `par` Work Together Soundly:**
  1. For a standard slice `T[]` (`T extends Send`), `T[]` implements `ParSplit` with `type ItemView = mut T`.
  2. For `Soa<T, R = Heap>`, the `comptime` type function `Soa<T>` reflects over `Type.fieldsOf(T)` (`{ posX: f32; posY: f32; velX: f32; velY: f32 }`) and synthesizes the **second-class structural record type**:
     ```ts
     type ParticleView = { posX: mut f32; posY: mut f32; velX: mut f32; velY: mut f32 };
     ```
     and implements `ParSplit` with `type ItemView = ParticleView`.
  3. Inside `par(mut particles, (p, _i) => { p.posX += p.velX * dt; })`, `p` has the second-class record type `ParticleView`. The closure captures only `dt: f32` by `Copy`, has an empty `uses []` effect row, and mutates the disjoint element references passed in `p`—100% sound under every rule of the type system with zero special cases!

```ts
import { par } from "std/par";
import { Soa } from "std/layout";

struct Particle { posX: f32; posY: f32; velX: f32; velY: f32; }

export function stepPhysics(particles: mut Soa<Particle>, dt: f32): void {
  par(mut particles, (p, _i) => {
    p.posX += p.velX * dt;
    p.posY += p.velY * dt;
  });
}
```

### 8.3 Native (`x86_64`, `aarch64`) and WebAssembly (`wasm32`) Targets
* **Native:** `Io` is handled by the multi-threaded `io_uring` / `kqueue` stackful fiber scheduler; `extern "C"` calls switch from the fiber's 4 KB growable stacklet to the OS worker thread's native contiguous stack.
* **WebAssembly:** One-shot continuations and `Io` suspension compile to the **Wasm Stack Switching (`wasmfx` / JSPI)** mechanism, mapping `Io` operations to browser `fetch`/`ReadableStream` Promises or WASI Preview 2 async handles.

---

## 9. `comptime`, Modules, and Foreign Function Interface (FFI)

### 9.1 `comptime` Execution and `Type` Reflection
Functions, parameters, and assertions marked `comptime` execute deterministically on the compiler's bytecode VM during Stage 2 before type/borrow checking. `Type` is a built-in `comptime`-only type supporting `Type.fieldsOf(T)`, `Type.structFromFields(fields)`, `Type.recordFromFields(fields)`, `Type.sizeOf(T)`, and `Type.alignOf(T)`:

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
* Functions declared `extern "C"` and structs marked `@layout(c)` or `@layout(packed)` follow the platform C ABI.
* Raw pointers (`T*`, `readonly T*`) are first-class `Copy` values (and `!Send`), but dereferencing a raw pointer (`*ptr`) or calling an `extern "C"` function requires an explicit `unsafe { ... }` block.

---

## 10. Core Calculus ($\lambda_{\text{fly}}$ v1.3)

Surface Flyscript elaborates into a typed core calculus $\lambda_{\text{fly}}$ judged under three contexts and one row kind (`Row`):

$$\Delta \;|\; \Theta \;|\; \Gamma \;\vdash\; e : \tau \;\!/\;\! \varepsilon \;\dashv\; \Theta_{\text{out}}$$

1. **Type, Region, and Unified Row Context ($\Delta$):**
   $$\Delta ::= \cdot \;\mid\; \Delta, \alpha : \{\text{Copy}, \text{Send}, \text{Drop}\} \;\mid\; \Delta, \rho : \text{region} \;\mid\; \Delta, r : \text{Row}_{\mathcal{L}}$$
   where $r : \text{Row}_{\mathcal{L}}$ is a sorted row variable lacking labels $\mathcal{L}$, used identically for structural record types $\Pi\langle r \rangle$, polymorphic variant types $\Sigma\langle r \rangle$, and effect rows $\varepsilon$.
2. **First-Class / Second-Class Kind Classification ($\text{class}(\tau) \in \{1, 2\}$):**
   * $\text{class}(\text{readonly }\tau) = \text{class}(\text{mut }\tau) = \text{class}(\text{str}) = \text{class}(\tau[]) = 2$.
   * For a structural record or tuple $\Pi\langle \ell_1 : \tau_1, \dots, \ell_k : \tau_k \rangle$, $\text{class}(\Pi\langle \dots \rangle) = \max_i \text{class}(\tau_i)$.
   * Nominal `struct`/`enum` fields and heap container type arguments require $\text{class}(\tau_i) = 1$.
3. **Affine Ownership Context ($\Theta$, First-Class Values Only):**
   $$\Theta ::= \cdot \;\mid\; \Theta, x : \text{own}(\tau) \;\mid\; \Theta, x : \text{dead} \qquad (\text{class}(\tau) = 1)$$
   Moving a non-`Copy` variable $x$ transitions $x : \text{own}(\tau) \implies x : \text{dead}$. $\Theta_{\text{out}}$ is the post-evaluation ownership context resulting from $e$.
4. **Second-Class Lexical Borrow Ledger ($\Gamma$, Single & Composite Views):**
   $$\Gamma ::= \cdot \;\mid\; \Gamma, b : \text{view}(\{\pi_1 : m_1, \dots, \pi_k : m_k\}, \tau) \qquad (\text{class}(\tau) = 2,\; m_i \in \{\text{mut}, \text{ro}\})$$
   Maps each active second-class binding $b$ (whether a single borrow `conn: mut Socket` locking $\{\pi_{\text{conn}} : \text{mut}\}$ or a second-class record `p: { x: mut f32; y: mut f32 }` locking $\{\pi_x : \text{mut}, \pi_y : \text{mut}\}$) to the multiset of disjoint root paths $\pi_i$ it locks.
   * **Shared-Mutation Purity Invariant:** No primitive operation with an empty effect row ($\varepsilon = []$) can mutate any memory location reachable through an $m_i = \text{ro}$ entry in $\Gamma$.
   * **Region Handler Rule (T-Region):**
     $$\frac{\Delta, \rho : \text{region} \;|\; \Theta \;|\; \Gamma \;\vdash\; e : \tau \;\!/\;\! \text{Alloc}\langle\rho\rangle, \varepsilon \;\dashv\; \Theta_{\text{out}} \qquad \rho \notin \text{ftv}(\tau) \cup \text{ftv}(\Theta_{\text{out}}) \cup \text{ftv}(\varepsilon)}{\Delta \;|\; \Theta \;|\; \Gamma \;\vdash\; \text{region}(\rho)\ \{ e \} : \tau \;\!/\;\! \varepsilon \;\dashv\; \Theta_{\text{out}}}$$
   * **Handler Re-Borrow Rule (T-Handle):** Let $\Gamma_0$ be the lexical borrow context entering `handle { e_body } with Eff { ... }`. In a **resumptive arm** (`op(x) resumes k => e_arm`), all paths locked in $\Gamma_{\text{body}}$ remain locked until $k$ is invoked or dropped. In an **abortive arm** (`op(x) => e_arm`), `e_body` is unwound first, popping $\Gamma_{\text{body}}$ and restoring $\Gamma_0$ so incoming borrowed parameters (`conn`) may be re-borrowed in $e_{\text{arm}}$.

---

## 11. Standard Library Signatures & Complete Validated Examples

### 11.1 Standard Library Signatures (`prelude`, `std/net`, `std/async`)

```ts
// From prelude:
export function alloc<region R = Heap, T extends Copy>(val: T): In<R, T> uses Alloc<R>;
export function copyUtf8<region R = Heap>(
  raw: readonly u8[],
): In<R, str> uses Alloc<R>, Fail<[ #MalformedUtf8 ]>;

export namespace Fail {
  export function raise<E>(err: E): never uses Fail<E>;
  export function capture<T, E, row Eff = []>(
    body: once () => T uses Fail<E>, ...Eff,
  ): Result<T, E> uses ...Eff;
}

// From "std/net" (Note: Fail<[ ... ]> rows in signatures are implicitly open!):
export type IoErr = [ #IoReset | #IoTimedOut | #IoBrokenPipe ];
export struct Profile { displayName: String; }
export struct QuotaStatus { allowed: bool; }

export struct Socket {
  function read(self: mut Self, buf: mut u8[]): usize uses Io, Fail<IoErr>;
  function writeStatus(self: mut Self, code: u16, body: str): void uses Io, Fail<IoErr>;
}

export struct DbClient {
  function fetchProfile(self: readonly Self, userId: str): Profile uses Io, Fail<IoErr>;
  function checkTokenQuota(self: readonly Self, token: str): QuotaStatus uses Io, Fail<IoErr>;
}

// From "std/async":
export struct Fiber<T, row E = []> {
  function join(self: Self): T uses Io, ...E;
}

export struct Scope<row E = []> {
  function spawn<T extends Send>(self: mut Self, task: () => T uses Io, ...E): Fiber<T, E>;
}

export namespace Async {
  export function scope<T, row E = []>(
    body: once (s: mut Scope<E>) => T uses Io, ...E,
  ): T uses Io, ...E {
    Io.runScope(body)
  }
}
```

### 11.2 Complete Validated HTTP Handler (`http_handler.fly`)

Every line conforms to v1.3:
* Inside `parseHeader<region R>`, the return type `In<R, ParsedReq<R>>` provides the bidirectional expected type `ParsedReq<R>` for `alloc({ userId, authToken })` (selecting region `R`), which in turn provides the expected field types `In<R, str>` for `userId` and `authToken`, so `copyUtf8(raw[0..8])` infers region `R` purely from expected types (§2.3, §5.4) without escape-analysis magic!
* `Fail<[ #MalformedRequest | #MalformedUtf8 ]>` is implicitly open (§2.4), unifying with `IoErr` and `#Unauthorized` inside `handleConnection`.

```ts
import { Socket, DbClient } from "std/net";
import { Async } from "std/async";

struct ParsedReq<region R> {
  userId: In<R, str>;
  authToken: In<R, str>;
}

// Module-private function: `R` in `copyUtf8` and `alloc` is inferred purely from
// the expected return type `In<R, ParsedReq<R>>` and its `In<R, str>` fields:
function parseHeader<region R>(
  raw: readonly u8[],
): In<R, ParsedReq<R>> uses Alloc<R>, Fail<[ #MalformedRequest | #MalformedUtf8 ]> {
  if (raw.len < 16) {
    Fail.raise(#MalformedRequest);
  }
  const userId: In<R, str> = copyUtf8(raw[0..8]);
  const authToken: In<R, str> = copyUtf8(raw[8..16]);
  alloc({ userId, authToken })
}

export function handleConnection(
  conn: mut Socket,
  db: readonly DbClient,
): void uses Io {
  handle {
    region (R) {
      let rawBuf: u8[512] = repeat<512>(0);
      const n = conn.read(mut rawBuf);
      const req: In<R, ParsedReq<R>> = parseHeader(rawBuf[0..n]);

      // `Async.scope` suspends `Alloc<R>` mutation on `R` and infers return type
      // `{ profile: Profile; quota: QuotaStatus }` and open `Fail` row automatically:
      const pair = Async.scope((s) => {
        const fProfile = s.spawn(() => db.fetchProfile(req.userId.asStr()));
        const fQuota   = s.spawn(() => db.checkTokenQuota(req.authToken.asStr()));
        { profile: fProfile.join(), quota: fQuota.join() }
      });

      if (!pair.quota.allowed) {
        Fail.raise(#Unauthorized);
      }
      conn.writeStatus(200, pair.profile.displayName.asStr());
    } // <-- `R` bumped back in O(1); `pair.profile` (`String<Heap>`) dropped
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

1. **Stage 1 — Lexer & Recursive Descent Parser:** Parses `.fly` modules into an untyped CST, resolving `<TypeArgs>(` via speculative lookahead and validating DAG module imports.
2. **Stage 2 — `comptime` Bytecode Evaluator & Monomorphizer:** Evaluates `comptime` functions (`Soa<T>`, `FixedRingBuffer`) deterministically, canonicalizing structural record and variant layouts and monomorphizing row variables `<row R>` and generic types `<T>`.
3. **Stage 3 — Bidirectional Type, Class & Unified Row Checker:**
   * Classifies types into first-class (`class = 1`) and propagating second-class views (`class = 2`), rejecting second-class types in nominal `struct`/`enum` fields and heap container parameters.
   * Checks structural records, polymorphic variants, nominal `struct`/`enum`/`interface` coherence, auto-traits (`Copy`, `Send`, `Drop`), and closure capture modes (`once` / `mut` / shared).
   * Infers effect rows for non-exported functions and closures, resolves `<region R = Heap>` parameters from bidirectional expected types, opens `Fail<[ ... ]>` variant rows in signatures, and unifies record, variant, and effect rows via a single Rémy row unifier.
4. **Stage 4 — Capability, Borrow & Region Pass (Mid-End SSA IR):**
   * Enforces affine move semantics ($\Theta$), single and composite second-class borrow ledger exclusivity ($\Gamma$), tied return views (`from param`), and abortive vs. resumptive handler borrow lifetimes.
   * Enforces the Two Region Laws (Rank-2 Non-Escape and No-External-Drop) for every `region (R)` handler of `Alloc<R>`.
   * Performs **Static Affine Reuse** (rewriting `Drop(Box<T>)` followed by `Alloc(Box<U>)` when `sizeof(T) == sizeof(U)` and `alignof(T) == alignof(U)` into in-place mutation).
   * Lowers **Evidence-Passing Effect Transformation** (tail-resumptive handlers like `Alloc<R>` and `Yield<T>` compile to direct inline/vtable calls; abortive `Fail<E>` handlers compile to two-register return/unwind; suspending `Io` handlers switch fiber stacklets on native or Wasm JSPI continuations).
5. **Stage 5 — Code Generation:**
   * **Debug:** Cranelift (or C11 / Wasm backend) for sub-second incremental compilation.
   * **Release:** LLVM IR (`x86_64`, `aarch64`, `wasm32`) with `noalias` and `readonly` attributes derived from `mut`, `readonly`, and owned parameters.

---

## 13. Why Flyscript, Summary of Laws, Rejected Alternatives, and Open Question

### 13.1 Honest Comparison with Existing Languages

| Language | What Flyscript Does That It Cannot | What Flyscript Gives Up Compared to It |
| :--- | :--- | :--- |
| **Rust** | Zero `'a` lifetime annotations on types; cyclic graphs in `region (R)` without `Rc<RefCell>`; no `async`/`await` coloring or `Pin<&mut Self>`; structural records and polymorphic variant errors; deterministic `Io` simulation via effect handlers. | Cannot store borrows inside long-lived nominal structs (must use owned values, regions, or `Handle<T>` indices), and uses 4 KB stackful fibers rather than packed state-machine futures. |
| **TypeScript** | Compiles AOT to unboxed native code & Wasm with zero GC pauses, deterministic `Drop`, real integers (`u64`, `i32`), `Soa<T>` SIMD layout, and data-race-free multi-core parallelism (`par`). | No width subtyping without `<row R>`, no dynamic `any`/reflection at runtime, and must annotate exported function types and `mut` borrows. |
| **Koka** | Zero reference-counting headers or atomic RC traffic on heap values (static affine ownership + regions instead of Perceus RC); explicit unboxed memory layout (`Soa<T>`, `@layout(c)`); static data-race freedom (`Send`). | Cannot resume effect continuations multiple times (one-shot only) and cannot freely alias mutable closures without borrow rules. |
| **Roc** | Supports in-place mutation (`mut T`), cyclic region graphs (`region (R)`), low-level systems/FFI control, and user-definable effect handlers (Roc hardcodes effects into a single host "platform"). | Does not have Roc's global Hindley-Milner full-program type inference (exported functions require signatures). |
| **Hylo (Val)** | Has first-class lexical regions (`region (R)`) for cyclic graphs, algebraic effect handlers (`Io`, `Fail`, `Yield`, `Alloc`), and structural row polymorphism. | Hylo's pure mutable value semantics (`inout` projections) allow subscript projections without region handles. |
| **Zig** | Full memory safety and temporal/spatial borrow checking in safe code, algebraic data types with exhaustive `match`, closures, traits (`interface`), and algebraic effects (`Alloc<R>` instead of manual allocator threading). | Larger typechecker than Zig; C interop requires `extern "C"` declarations rather than Zig's `@cImport` C header translator. |
| **Mojo** | Unified row calculus (records, polymorphic variants, effects), swappable `Io` simulation handlers, TypeScript syntax, and lexical regions without lifetime parameter lists. | Does not target native GPU/TPU MLIR autotuning kernels in v1.3 (deferred to future work). |

### 13.2 Thesis and the Five Laws of Flyscript (Final Form)
**In one line:** *Affine values, one row calculus, handlers for everything, and `comptime`: Church on the outside, Turing on the inside.*

Flyscript combines TypeScript’s readable surface and structural data with a four-pillar systems core where functional composition (Church) and hardware sympathy (Turing) reinforce each other. Every rule in the specification derives from **five laws**:
1. **Affine Ownership with Propagating Second-Class Views:** Values have one unique owner by default; borrows (`readonly T`, `mut T`) and structural records/tuples containing them are lexical views that never enter first-class data fields, giving $O(1)$ cross-thread moves and zero `'a` lifetime annotations.
2. **Effect-Gated Shared Mutation (`uses Shared`):** No operation with an empty effect row (`uses []`) can mutate state through a `readonly T` reference, making `readonly T` 100% immutable in pure/parallel code and allowing `Send` alone to guarantee thread-safe sharing.
3. **One Unified Row Calculus:** A single sorted row unifier powers structural records `{ x: f64; ...R }`, implicitly open polymorphic variants `[ #Tag | ...R ]`, and algebraic effect rows `uses Io, ...E`.
4. **One-Shot Algebraic Effect Handlers for Control, Memory, and Iteration:** `Fail<E>` (errors), `Io` (async & deterministic simulation), `Alloc<R>` (`region (R)` arenas), and `Yield<T>` (`for` loops and generators) are all ordinary one-shot algebraic effects.
5. **Compile-Time Execution as Ordinary Code:** `comptime` functions over `Type` values (`Soa<T>`) replace macro DSLs and bespoke layout attributes.

### 13.3 Rejected Alternatives
* **Tracing Garbage Collection (Global or Actor-Local):** Rejected because global GC introduces tail-latency pauses and memory overhead, while actor-local GC requires write barriers and stack maps for cyclic state that `region (R)` and `Pool<T>` handle with flat cache layout.
* **Effect-Free Interior Mutability (`Cell<T>`, `RefCell<T>`, un-effectful `Mutex`):** Rejected because allowing mutation behind `readonly T` without an effect (`uses Shared`) destroys observational purity for `uses []` functions and forces a split between `Send` and `Sync`.
* **`iso` Capability and `recover` Blocks:** Rejected because affine ownership plus the ban on borrows in first-class struct fields already guarantees every owned value is an isolated subgraph.
* **Width Subtyping on Structural Records:** Rejected because forgetting fields via subtyping requires dynamic field offset lookups or heap boxing, whereas row polymorphism (`<row R>`) monomorphizes to exact byte offsets.
* **Multi-Shot Continuations:** Rejected because resuming a continuation more than once duplicates affine resources (`Box<T>`, sockets) and invalidates active mutable borrows.
* **Global Hindley-Milner Type Inference:** Rejected because full-program HM unification produces non-local errors when combined with `comptime` type functions, rank-2 regions, and traits.
* **`async` / `await` Stackless Coroutines:** Rejected because they split the ecosystem into colored functions and prevent borrowing stack/region data naturally across suspension points without self-referential state-machine pinning (`Pin<&mut Self>`).
* **First-Class Lifetime Parameters (`'a`):** Rejected because infectious lifetime annotations on structs and types impose a severe ergonomic tax for patterns better served by propagating second-class views, lexical regions, or pool handles.

### 13.4 Open Question
1. **Target-Neutral SIMD Lane Permutation & Bitmask API (`Simd<T, comptime Lanes: usize>`):** While `Soa<T>` and `par` enable auto-vectorization for vertical arithmetic loops, algorithms such as vectorized UTF-8 validation, JSON scanning, and sorting networks require horizontal lane shuffles, saturating arithmetic, and lane-to-bitmask extraction (`movemask`), where ARM64 NEON/SVE and x86-64 AVX2/AVX-512 differ structurally. What is the minimal portable `Simd<T, Lanes>` intrinsic surface that lowers without emulation cliffs on both ARM64 and x86-64?