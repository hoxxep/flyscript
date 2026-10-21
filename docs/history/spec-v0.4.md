# Flyscript Language Specification (v0.4 — Release Candidate)

File extension: `.fly`

---

## 1. Goals and Non-Goals

### 1.1 Goals
1. **TypeScript surface, systems semantics:** Familiar syntax for developers who read TypeScript (`function`, `(x) => expr`, `const`/`let`, `<T extends U>`, `{ field: value }`, `interface`, `implements`, `type`, ES modules), compiled ahead-of-time to native code with unboxed layouts and deterministic resource destruction.
2. **Structural records with row polymorphism, plus nominal datatypes for abstraction:** Anonymous records `{ x: f64; y: f64 }` and tuples `[T, U]` are structural and support row polymorphism (`...R`), while `struct` and `enum` declarations are nominal and generative—providing encapsulation for invariants, custom layouts (`@layout`), and `Drop` destructors.
3. **Static affine ownership with second-class borrows:** Every heap allocation (`Box<T>`, `Vec<T>`, `String`, `Pool<T>`) has a single unique owner (`T`). Because there are no shared-mutable pointer types and borrows (`readonly T`, `mut T`) are strictly second-class lexical permissions that never appear inside data fields, every owned value is an isolated subgraph by construction and transfers across concurrent tasks in $O(1)$.
4. **Zero-GC cyclic data via fiber-local regions and typed index pools:** Short-lived graphs are built inside lexical bump-allocated arenas (`region (r) { ... }`); long-lived cyclic graphs use generational index pools (`Pool<T>` and `Handle<T>`).
5. **Typed algebraic effects with one-shot continuations:** Recoverable failure, I/O, and structured concurrency are tracked via row-polymorphic effect clauses (`uses Io, Fail<E>`) rather than `async`/`await` coloring or untyped exceptions.
6. **Compile-time execution in the host language:** Generics, type-level computation, and layout specialization are ordinary Flyscript functions evaluated at `comptime`.

### 1.2 Non-Goals (v0.4)
1. **Width subtyping on structural records:** Passing `{ x: f64; y: f64; z: f64 }` to a function expecting `{ x: f64; y: f64 }` without row polymorphism would require dynamic field offset lookup or boxing; Flyscript uses monomorphized row polymorphism instead.
2. **Garbage collection:** There is no global or actor-local tracing garbage collector in the language or runtime.
3. **Multi-shot continuations:** Effect handlers may resume a captured continuation at most once.
4. **Arbitrary dependent or non-linear refinement types:** Value-indexed types are restricted to `comptime` constants and linear integer constraints (Quantifier-Free Presburger Arithmetic); multi-dimensional array views use `Grid2D<T>` / `Grid3D<T>` rather than non-linear multiplication proofs.
5. **Automatic GPU kernel compilation:** Lowering data-parallel loops to SPIR-V/PTX/Metal requires explicit shared-memory and warp-divergence modeling and is deferred to future work.

---

## 2. Core Design Decisions and Rationales

1. **Structural Records with Row Polymorphism + Nominal `struct` / `enum`:**
   * Record types `{ x: f64; y: f64 }` (including `type` aliases of records) and tuple types `[A, B]` are **structural**: two record types with the same field names and types are identical, and their physical fields are sorted canonically by alignment then lexicographical field name.
   * Functions over records may abstract over unknown trailing fields using a row variable `<row R>`: `function norm<row R>(p: readonly { x: f64; y: f64; ...R }): f64`.
   * `struct` and `enum` declarations are **nominal and generative** (the existential abstraction boundary, as in SML's split between structural records and nominal `datatype`s): only nominal types may implement `Drop`, carry `@layout(soa | packed | c)`, or hide private fields behind module boundaries.
   * *Rationale:* Width subtyping requires passing hidden field-offset dictionaries or boxing records to find fields at unknown offsets. Row polymorphism provides the same ergonomics as TypeScript structural typing while monomorphizing every call site to exact static byte offsets.
2. **Elimination of `iso`, `recover`, and `IsoArena`:**
   * Flyscript has **no `iso` keyword, no `recover` block, and no `IsoArena`**. Because all owning pointers (`Box<T>`, `Vec<T>`, `String`, `Pool<T>`) are strictly affine (`own`), borrows (`readonly T`, `mut T`) are forbidden inside struct/record/enum fields, and there is no shared-mutable container (`Rc<RefCell<T>>`), **every owned value is already a disjoint, isolated tree of allocations**.
   * Moving an owned `T` across a channel or into a spawned task (`T extends Send`) is an $O(1)$ stack move of its root words with zero copying and zero aliasing risk.
   * *Rationale:* Pony and Verona need `iso` and `recover` only because their default reference capabilities (`ref`, `box`) permit arbitrary mutable aliasing within an actor heap. In an affine-by-default language with second-class borrows, uniqueness is the default invariant, making `iso` redundant.
3. **`val` as an Auto-Trait Constraint Only (`T extends val`):**
   * `val` is not a type prefix; it is a built-in auto-trait constraint (`T extends val`) satisfied by any type transitively free of raw pointers (`T*`), mutable borrows, and interior mutability (such as `AtomicU64` or OS handles). All `Pod` types, and owned containers (`Vec<T>`, `String`, `Box<T>`, `Pool<T>`, `Arc<T>`) whose element type satisfies `T extends val`, satisfy `val`.
   * Calling `Arc.new<T extends val>(value: T): Arc<T>` moves an owned value into an atomically reference-counted allocation shareable across tasks in $O(1)$. Borrowing `Arc<T>` yields `readonly T`.
   * *Rationale:* Unifying `val` as a trait bound eliminates the syntax ambiguity between a type constructor (`val T`), a borrow (`readonly T`), and a shared handle (`Arc<T>`).
4. **Static Affine Reuse (Size + Alignment Equal):**
   * When an owned `Box<T>` is consumed by move and a `Box<U>` is allocated in the same basic block where `sizeof(T) == sizeof(U)` and `alignof(T) == alignof(U)`, the mid-end compiler reuses the consumed allocation in place without calling the allocator or storing reference counts.
   * *Rationale:* Requiring both equal size and equal alignment preserves hardware alignment invariants and allocator size-class invariants statically.
5. **Strict Ban on Borrows in Data Fields, and `In<R, T>` as `Pod`:**
   * Second-class borrows (`readonly T`, `mut T`, `str`, `T[]`) may never appear as fields of a record, `struct`, or `enum`.
   * Region pointers `In<R, T>`, region slices `In<R, T[]>`, and region strings `In<R, str>` are plain unboxed pointer/slice representations with no `Drop` destructor; therefore, **`In<R, _>` implements `Pod`** whenever `T extends Pod`. Consequently, region-allocated structs (`struct ParsedReq<region R>`) may contain `In<R, _>` fields and themselves satisfy `Pod`.
   * *Rationale:* Making `In<R, _>` implement `Pod` allows arbitrarily nested graphs and slices to be bump-allocated inside `region (r)` while the rank-2 non-escape rule on `R` guarantees none of those `Pod` pointers outlive the region block.
6. **Tied Borrow Return Syntax (`from paramName`):**
   * Functions returning a borrowed view (`readonly T`, `mut T`, `str`, `T[]`) omit `from` when they take a single borrowed parameter (which the return borrow ties to automatically), and write `): ReturnType from paramName` when multiple borrowed parameters exist.
   * *Rationale:* Reads naturally in TypeScript signatures and avoids visual collision with arrow types `=>`.
7. **Deterministic Handler Ordering (`return`, Abortive Arms, Resumptive Drop, `finally`):**
   * Normal completion of `handle { body } with Eff { ... }`: `body` produces `v` $\to$ optional `return(v)` arm transforms `v` $\to$ `finally` block runs $\to$ result returned.
   * Abortive arm (`op(args) => armBody`, no `resumes` keyword): `body` stack unwinds to the `handle` boundary (running inner `Drop` destructors, exiting inner regions, and releasing all inner `mut`/`readonly` borrows) $\to$ `armBody` runs (may access variables previously borrowed by `body`) $\to$ `finally` block runs.
   * Resumptive arm (`op(args) resumes k => armBody`): `body` remains suspended on its fiber stack (its borrows stay locked). If `k(val)` is called, `body` resumes. If `armBody` drops `k` without calling it (on early return or branch), dropping `k` immediately unwinds the suspended `body` stack (running all pending inner `Drop` destructors and region exits) at the point `k` goes out of scope, before `armBody` finishes and before `finally` runs.
   * *Rationale:* Guarantees RAII destructor order is strictly LIFO even when a one-shot continuation is abandoned dynamically.
8. **Fiber Cancellation Across Resumptive Handlers:**
   * When a sibling fiber in `Async.scope` fails with an unhandled effect, other fibers in that scope are cancelled at their next `Io` suspension point. Cancellation unwinds the cancelled fiber’s stack from the innermost suspended `Io` frame outward—running all `Drop` destructors, resetting fiber-local regions, and executing `finally` blocks of any enclosing `handle` expressions, even if the fiber was mid-way inside a resumptive handler continuation.
   * *Rationale:* Treating cancellation as a forced unwind from the yield point ensures neither suspended continuations nor outer handler frames leak resources.
9. **Native Stack Switching for `extern "C"` Calls:**
   * Calling an `extern "C"` function switches the stack pointer from the current fiber’s growable stacklet to the OS worker thread’s contiguous native system stack for the duration of the C call (exactly as Go’s `cgo` runtime does).
   * *Rationale:* C compilers do not emit split-stack prologue checks and assume large contiguous stack frames; switching to the worker thread's system stack avoids allocating 1 MB virtual stacks per idle fiber.

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
| **Async & Exceptions** | `async`/`await` (Promise coloring) and untyped `throw`/`try`/`catch`. | **Typed Algebraic Effects (`uses Io, Fail<E>`):** Direct-style synchronous syntax on stackful fibers (`io_uring`/`kqueue`). Errors use `Result<T, E>` (unwrapped with `try expr`) or `uses Fail<E>` (caught with `handle { ... } with Fail<E>`). |
| **Generics & Metaprogramming** | `<T extends U>` erased at runtime; complex conditional types `T extends U ? X : Y`. | `<T extends U & V>` monomorphized at compile time, plus `comptime` functions that compute `Type` values using ordinary `if`/`for` code. |

---

## 4. Lexical Syntax and Complete Grammar (EBNF)

```ebnf
Module          = { ImportDecl | ExportDecl | TopDecl } ;
ImportDecl      = "import" "{" IdentList "}" "from" StringLit ";" ;
ExportDecl      = "export" TopDecl ;

TopDecl         = StructDecl | EnumDecl | InterfaceDecl | ImplDecl
                | TypeAliasDecl | EffectDecl | FunctionDecl ;

StructDecl      = [ LayoutAttr ] "struct" Ident [ TypeParams ]
                  [ "implements" TypeList ] "{" { MemberDecl } "}" ;
LayoutAttr      = "@layout" "(" ( "aos" | "soa" | "packed" | "c" ) ")" ;
MemberDecl      = FieldDecl | MethodDecl ;
FieldDecl       = Ident ":" Type ";" ;

MethodDecl      = "function" Ident [ TypeParams ] "(" [ SelfParam [ "," ParamList ] | ParamList ] ")"
                  ":" ReturnType [ UsesClause ] Block ;
SelfParam       = "self" ":" ( "Self" | "mut" "Self" | "readonly" "Self" ) ;

EnumDecl        = "enum" Ident [ TypeParams ] [ "implements" TypeList ]
                  "{" VariantDecl { "," VariantDecl } [ "," ] "}" ;
VariantDecl     = Ident [ "(" TypeList ")" | "{" { FieldDecl } "}" ] ;

InterfaceDecl   = "interface" Ident [ TypeParams ] "{" { InterfaceSig ";" } "}" ;
InterfaceSig    = "function" Ident [ TypeParams ] "(" [ SelfParam [ "," ParamList ] | ParamList ] ")"
                  ":" ReturnType [ UsesClause ] ;

ImplDecl        = "impl" [ TypeParams ] TypeRef "for" TypeRef "{" { MethodDecl } "}" ;
TypeAliasDecl   = "type" Ident [ TypeParams ] "=" Type ";" ;

EffectDecl      = "effect" Ident [ TypeParams ] "{" { OpSig ";" } "}" ;
OpSig           = Ident "(" [ ParamList ] ")" ":" Type ;

FunctionDecl    = [ "comptime" ] "function" Ident [ TypeParams ]
                  "(" [ ParamList ] ")" ":" ReturnType [ UsesClause ] Block ;

ReturnType      = [ "mut" | "readonly" ] Type [ "from" Ident ] ;

ParamList       = Param { "," Param } [ "," ] ;
Param           = [ "comptime" ] Ident ":" ParamType ;
ParamType       = [ "mut" | "readonly" ] Type ;

UsesClause      = "uses" EffectRow ;
EffectRow       = EffectRef { "," EffectRef } ;
EffectRef       = Ident [ TypeArgs ] ;

TypeParams      = "<" TypeParam { "," TypeParam } ">" ;
TypeParam       = "region" Ident
                | "row" Ident
                | "effect" Ident [ "=" "[" [ EffectRow ] "]" ]
                | "comptime" Ident ":" Type
                | Ident [ "extends" ConstraintList ] ;
ConstraintList  = Constraint { "&" Constraint } ;
Constraint      = "Pod" | "Send" | "val" | "Drop" | TypeRef ;

TypeArgs        = "<" TypeArg { "," TypeArg } ">" ;
TypeArg         = Type | Expr | "[" [ EffectRow ] "]" ;

Type            = PrimType
                | "dyn" TypeRef
                | "Region" "<" Ident ">"
                | "In" "<" Ident "," Type ">"
                | RecordType
                | TupleType
                | TypeRef
                | Type "[" [ Expr ] "]"
                | "(" [ ClosureParamList ] ")" "=>" ReturnType [ UsesClause ]
                | PrimIntType "where" RefinementPred ;

RecordType      = "{" { FieldDecl } [ "..." Ident [ ";" ] ] "}" ;
TupleType       = "[" Type { "," Type } "]" ;

TypeRef         = Ident [ "." Ident ] [ TypeArgs ] ;
PrimIntType     = "i8" | "i16" | "i32" | "i64" | "isize" | "u8" | "u16" | "u32" | "u64" | "usize" ;
PrimType        = PrimIntType | "f32" | "f64" | "bool" | "str" | "void" | "never" | "Type" ;

Expr            = MatchExpr | RegionExpr | HandleExpr | TryExpr | LambdaExpr | ... ;
MatchExpr       = "match" "(" Expr ")" "{" { MatchArm } "}" ;
MatchArm        = Pattern [ "if" Expr ] "=>" ( Expr "," | Block ) ;
RegionExpr      = "region" "(" Ident ")" Block ;
TryExpr         = "try" Expr ;

HandleExpr      = "handle" Block "with" EffectRef "{" { HandlerArm } [ ReturnArm ] [ FinallyArm ] "}" ;
HandlerArm      = Ident "(" [ HandlerParamList ] ")" [ "resumes" Ident ] "=>" Block ;
HandlerParamList= Ident [ ":" Type ] { "," Ident [ ":" Type ] } ;
ReturnArm       = "return" "(" Ident [ ":" Type ] ")" "=>" Block ;
FinallyArm      = "finally" "=>" Block ;
```

---

## 5. Types: Structural Records, Nominal Datatypes, and Refinements

### 5.1 Structural Records, Tuples, and Row Polymorphism (`<row R>`)
An anonymous record `{ x: f64; y: f64 }` or tuple `[i32, bool]` is structural. Record literals `{ x: 1.0, y: 2.0 }` construct structural records directly when no nominal `struct` type is expected from bidirectional context, or construct a nominal `struct` when expected (or when prefixed with the struct name `Vec2 { x: 1.0, y: 2.0 }`).

Functions that operate on any record containing a required subset of fields parameterize over a **row variable `<row R>`** using the same row-unification engine used for effect rows (`<effect E>`):

```ts
type Point2D<row R = {}> = { x: f64; y: f64; ...R };

function distanceSq<row R>(p: readonly Point2D<R>): f64 {
  return p.x * p.x + p.y * p.y;
}

function example(): f64 {
  const particle = { x: 3.0, y: 4.0, mass: 10.0, id: 7 as u32 };
  // `R` unifies with `{ mass: f64; id: u32 }`; monomorphizes to exact static field offsets.
  return distanceSq(particle);
}
```

### 5.2 Nominal `struct`, `enum`, and `interface`
`struct` and `enum` create distinct nominal types even if their fields are identical:
```ts
struct Meters { value: f64; }
struct Seconds { value: f64; } // Distinct nominal type from `Meters`
```
Interfaces use `<T extends Bound1 & Bound2>` and carry an optional effect row parameter when methods may perform effects:
```ts
interface Validator<T, effect E = []> {
  function validate(self: readonly Self, item: readonly T): bool uses E;
}
```

### 5.3 Linear Integer Refinements and Multi-Dimensional Views
Integer types may carry a linear inequality predicate (`where`) over in-scope `const` integers and slice lengths, decided via **Fourier-Motzkin variable elimination with Omega integer tightening over Quantifier-Free Presburger Arithmetic (QF_LIA)**:
```ts
type Index<comptime N: usize> = usize where self < N;
```
For 2D and 3D buffers (images, matrices), standard-library `Grid2D<T>` and `Grid3D<T>` provide bounds-checked or refinement-indexed `.get(row, col)` access without requiring non-linear `row * stride + col` multiplication proofs.

---

## 6. Ownership, Second-Class Borrows, and Regions

### 6.1 Built-in Marker Traits and Capabilities

| Form | Category | Meaning | Allowed in Record/Struct Field? |
| :--- | :--- | :--- | :--- |
| **`T`** (default) | Owned value | Uniquely owned value; moves on assignment unless `T extends Pod` | Yes |
| **`readonly T`** | 2nd-class borrow | Shared immutable lexical borrow | **Never** |
| **`mut T`** | 2nd-class borrow | Exclusive mutable lexical borrow (requires `mut x` at call site) | **Never** |
| **`In<R, T>`** | Region pointer | Unboxed pointer/slice into `region(r)`; implements `Pod` | Yes, inside `Struct<region R>` |
| **`Arc<T>`** | Shared heap handle | Atomically refcounted handle; requires `T extends val` | Yes |

#### Built-in Marker Traits (Compiler-Derived)
* **`T extends Pod`:** Plain Old Data (scalars, `In<R, U>`, fixed arrays `U[N]`, structural records/tuples, and nominal structs/enums whose fields are all `Pod` and that do not implement `Drop`). `Pod` values copy implicitly without invalidating the source binding.
* **`T extends val`:** Deeply immutable when shared (contains no raw pointers `U*` and no interior mutability primitives). Required by `Arc<T>`.
* **`T extends Send`:** Safe to transfer across tasks/threads. Satisfied by any owned type `T` whose fields are all `Send` and that contains **no region references `In<R, _>`** and **no `Region<R>` handles**.

### 6.2 Tied Borrow Return Signatures (`from paramName`)
Because borrows cannot be stored in structs, a returned borrow (`readonly T`, `mut T`, `str`, `T[]`) always projects from an input parameter borrow:
* If a function has **exactly one** borrowed parameter (including `self: readonly Self` or `self: mut Self`), any returned borrow ties to that parameter automatically.
* If a function has **two or more** borrowed parameters and returns a borrow, the return type must name the source parameter via `from paramName`:
  ```ts
  function choosePrefix(
    primary: str,
    fallback: str,
    usePrimary: bool,
  ): str from primary {
    return primary[0..4];
  }
  ```

### 6.3 Fiber-Local Lexical Regions (`region (r)`)
Each stackful fiber owns a segmented bump-allocator (`FiberArena`). Entering `region (r) { ... }` pushes a watermark on the current fiber's arena and introduces a rigid region type `R` and allocator handle `r: Region<R>`:
* **Core `Region<R>` methods:**
  * `r.alloc<T extends Pod>(val: T): In<R, T>`
  * `r.allocSlice<T extends Pod>(len: usize, fill: T): In<R, T[]>`
  * `r.copySlice<T extends Pod>(src: readonly T[]): In<R, T[]>`
  * `r.copyStr(src: str): In<R, str>`
  * `r.copyUtf8(src: readonly u8[]): Result<In<R, str>, Utf8Error>`
  * `r.defer(cleanup: once () => void): void` (allocates an explicit destructor node on the region's teardown list outside the fast bump path).
* **Projecting Views from Region References:**
  * Given `p: In<R, T>`, field access `p.field` reads or mutates the field in place while `R` is active and not frozen by `Async.scope`.
  * Given `s: In<R, str>`, `s.asStr(): str from s` returns a borrowed `str` tied to `s`.
  * Given `a: In<R, T[]>`, `a.asSlice(): readonly T[] from a` and `a.asMutSlice(): mut T[] from a` borrow the slice.

---

## 7. Core Calculus Sketch (Elaboration Target)

Every surface Flyscript function elaborates into a typed core calculus $\lambda_{\text{fly}}$ parameterized by four contexts:

$$\Delta \;|\; \Theta \;|\; \Gamma \;\vdash\; e : \tau \;\!/\;\! \varepsilon$$

1. **Type, Region, Row, and Effect Context ($\Delta$):**
   $$\Delta ::= \cdot \;\mid\; \Delta, \alpha : \text{Bounds} \;\mid\; \Delta, \rho : \text{region}\{\text{rw} \mid \text{ro}\} \;\mid\; \Delta, r : \text{row} \;\mid\; \Delta, \epsilon : \text{eff}$$
   Tracks rigid type variables $\alpha$, active lexical regions $\rho$ (with state $\text{rw}$ normally, or $\text{ro}$ when frozen inside `Async.scope`), record row variables $r$, and effect row variables $\epsilon$.
2. **Ownership and Capability Context ($\Theta$):**
   $$\Theta ::= \cdot \;\mid\; \Theta, x : \text{own}(\tau) \;\mid\; \Theta, x : \text{dead}$$
   Tracks affine owned bindings. Moving a non-`Pod` variable $x$ transitions $x : \text{own}(\tau) \implies x : \text{dead}$. At merge points of `if`/`match`, any variable $x$ that is $\text{dead}$ in one branch and $\text{own}(\tau)$ in another inserts an automatic `Drop(x)` at the end of the live branch.
3. **Second-Class Lexical Borrow Ledger ($\Gamma$):**
   $$\Gamma ::= \cdot \;\mid\; \Gamma, b : \text{borrow}(\pi, \text{mut} \mid \text{ro}, \tau)$$
   Maps each active borrow binding $b$ to the root owned path $\pi \in \Theta$ it locks:
   * **Exclusivity Invariant:** While $\text{borrow}(\pi, \text{mut}, \_) \in \Gamma$, path $\pi$ cannot be read, moved, or borrowed again. While $\text{borrow}(\pi, \text{ro}, \_) \in \Gamma$, path $\pi$ cannot be moved or mutably borrowed.
   * **Region Non-Escape Rule (T-Region):**
     $$\frac{\Delta, \rho : \text{region}\{\text{rw}\} \;|\; \Theta \;|\; \Gamma, r : \text{borrow}(\rho, \text{mut}, \text{Region}\langle\rho\rangle) \;\vdash\; e : \tau \;\!/\;\! \varepsilon \qquad \rho \notin \text{ftv}(\tau) \cup \text{ftv}(\Theta_{\text{out}}) \cup \text{ftv}(\varepsilon)}{\Delta \;|\; \Theta \;|\; \Gamma \;\vdash\; \text{region}(r)\ \{ e \} : \tau \;\!/\;\! \varepsilon}$$
   * **Handler Borrow Rule (T-Handle):**
     * In a **resumptive arm** (`op(x) resumes k => e_arm`), $e_{\text{arm}}$ is typechecked under $\Gamma_{\text{outer}}$ with all paths $\pi$ borrowed inside the handled block locked as inaccessible, and $k : \text{own}(\tau_{\text{in}} \xrightarrow{\varepsilon} \tau_{\text{body}})$ in $\Theta$.
     * In an **abortive arm** (`op(x) => e_arm`), the handled block's inner $\Gamma_{\text{body}}$ borrows are released first, so $e_{\text{arm}}$ is typechecked under the full unborrowed $\Theta_{\text{outer}}$.

---

## 8. Standard Library Signatures & Complete Validated Example

### 8.1 Standard Library Signatures Used in the Example (`std/net`, `std/async`)

To avoid unhandled effect mismatches, **`std/net` I/O operations return `Result<T, IoError> uses Io`** (performing the `Io` effect for suspension, and returning network failures as a `Result` value so callers can transform or `try`-propagate them into domain errors):

```ts
// From prelude:
export effect Io {}
export effect Fail<E> { raise(err: E): never; }

export enum Result<T, E> {
  Ok(T),
  Err(E),
  function mapErr<F, effect Eff = []>(
    self: Self,
    op: once (err: E) => F uses Eff,
  ): Result<T, F> uses Eff;
}

export namespace Result {
  export function capture<T, E, effect Eff = []>(
    body: once () => T uses Fail<E>, Eff,
  ): Result<T, E> uses Eff;
}

// From "std/net":
export enum IoError { ConnectionReset, TimedOut, BrokenPipe }
export struct Profile { displayName: String; }
export struct QuotaStatus { allowed: bool; }

export struct Socket {
  function read(self: mut Self, buf: mut u8[]): Result<usize, IoError> uses Io;
  function writeStatus(self: mut Self, code: u16, body: str): Result<void, IoError> uses Io;
}

export struct DbClient {
  function fetchProfile(self: readonly Self, userId: str): Result<Profile, IoError> uses Io;
  function checkTokenQuota(self: readonly Self, token: str): Result<QuotaStatus, IoError> uses Io;
}

// From "std/async":
export struct Fiber<T, effect E = []> {
  function join(self: Self): T uses Io, E;
}

export struct Scope<effect E = []> {
  function spawn<T>(
    self: mut Self,
    task: () => T uses Io, E,
  ): Fiber<T, E>;
}

export namespace Async {
  export function scope<T, effect E = []>(
    body: once (s: mut Scope<E>) => T uses Io, E,
  ): T uses Io, E;
}
```

### 8.2 Complete Validated Example (`http_handler.fly`)

Every expression, borrow, region reference, structural record, and effect row in this file typechecks against the v0.4 rules and the signatures in §8.1:

```ts
import { Socket, DbClient, IoError, Profile, QuotaStatus } from "std/net";
import { Async, Scope, Fiber } from "std/async";

export enum HttpError {
  MalformedRequest,
  Unauthorized,
  BackendError,
}

// Nominal Pod struct allocated inside lexical region R.
// Holds only `In<R, str>` (which implements Pod); zero outer borrows.
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
  const userId = try r.copyUtf8(raw[0..8]).mapErr((_) => HttpError.MalformedRequest);
  const authToken = try r.copyUtf8(raw[8..16]).mapErr((_) => HttpError.MalformedRequest);
  return r.alloc({ userId: userId, authToken: authToken });
}

export function handleConnection(
  conn: mut Socket,
  db: readonly DbClient,
): void uses Io {
  handle {
    region (reqArena) {
      let rawBuf: u8[512] = repeat<512>(0);
      const n = try conn.read(mut rawBuf).mapErr((_) => HttpError.BackendError);
      const req: In<reqArena, ParsedReq<reqArena>> = parseHeader(mut reqArena, rawBuf[0..n]);

      // Spawn two concurrent fibers in a structured nursery parameterized over `Fail<HttpError>`.
      // `reqArena` transitions to read-only (`ro`) during `Async.scope`; both child fibers
      // capture `db` and `req` by shared `readonly` borrow and return `T uses Io, Fail<HttpError>`.
      // The scope returns a structural record `{ profile: Profile; quota: QuotaStatus }`.
      const pair = Async.scope<
        { profile: Profile; quota: QuotaStatus },
        [Fail<HttpError>]
      >((s: mut Scope<[Fail<HttpError>]>) => {
        const fProfile: Fiber<Profile, [Fail<HttpError>]> = s.spawn(() => {
          return try db.fetchProfile(req.userId.asStr()).mapErr((_) => HttpError.BackendError);
        });
        const fQuota: Fiber<QuotaStatus, [Fail<HttpError>]> = s.spawn(() => {
          return try db.checkTokenQuota(req.authToken.asStr()).mapErr((_) => HttpError.BackendError);
        });
        return { profile: fProfile.join(), quota: fQuota.join() };
      });

      if (!pair.quota.allowed) {
        Fail.raise(HttpError.Unauthorized);
      }
      const _ = try conn.writeStatus(200, pair.profile.displayName.asStr())
        .mapErr((_) => HttpError.BackendError);
    } // <-- `reqArena` fiber watermark reset in O(1) here; `pair.profile` (`String`) dropped
  } with Fail<HttpError> {
    // Abortive arm (`resumes` omitted): `reqArena` is already unwound and the inner
    // `mut conn` borrow has ended before this block runs, so `mut conn` is legal here.
    raise(err) => {
      const code: u16 = match (err) {
        HttpError.MalformedRequest => 400,
        HttpError.Unauthorized     => 401,
        HttpError.BackendError     => 502,
      };
      const _ = conn.writeStatus(code, "error");
    }
  };
}
```

---

## 9. Compiler Pipeline and Implementation Notes

1. **Stage 1 — Lexer & Recursive Descent Parser:** Parses `.fly` modules into an untyped CST, disambiguating `<TypeArgs>(` via speculative lookahead and checking DAG module imports.
2. **Stage 2 — `comptime` Bytecode Evaluator & Monomorphizer:** Evaluates `comptime` functions and constants deterministically, canonicalizing structural record layouts (`{ x: f64; y: f64 }`) and monomorphizing record row variables `<row R>` and generic types `<T>`.
3. **Stage 3 — Bidirectional Type, Effect & Refinement Checker:**
   * Checks structural records, nominal `struct`/`enum`/`interface` coherence, closure capture modes (`once` / `mut` / shared), and infers local expression and unadorned numeric literal types bidirectionally.
   * Unifies `uses` effect rows and defaults interface effect parameters (`effect E = []`).
   * Solves linear integer refinements (`where self < N`) via **Fourier-Motzkin elimination with Omega integer tightening** over QF_LIA.
4. **Stage 4 — Capability, Borrow & Region Pass (Mid-End SSA IR):**
   * Enforces affine move semantics ($\Theta$), lexical borrow exclusivity ($\Gamma$), tied return borrows (`from param`), and abortive vs. resumptive handler borrow lifetimes.
   * Enforces rank-2 non-escape for every `region (r)` variable and freezes active regions to read-only across `Async.scope`.
   * Performs **Static Affine Reuse** (rewriting `Drop(Box<T>)` followed by `Alloc(Box<U>)` when `sizeof(T) == sizeof(U)` and `alignof(T) == alignof(U)` into in-place mutation).
   * Lowers `@layout(soa)` field projections and **Evidence-Passing Effect Transformation** (tail-resumptive handlers compile to direct vtable calls; suspending handlers switch fiber stacklets; `extern "C"` calls switch to the worker thread's native system stack).
5. **Stage 5 — Code Generation:**
   * **Debug:** Cranelift (or C11 backend) for incremental builds.
   * **Release:** LLVM IR with `noalias` and `readonly` parameter attributes emitted from `mut`, `readonly`, and owned parameters.

---

## 10. Genuine Open Question

1. **Target-Neutral SIMD Lane Permutation & Bitmask API (`Simd<T, Lanes>`):** While `@layout(soa)` and `par for` enable auto-vectorization for vertical arithmetic loops, algorithms such as vectorized UTF-8 validation, JSON scanning, and sorting networks require horizontal lane shuffles, saturating arithmetic, and lane-to-bitmask extraction (`movemask`), where ARM64 NEON/SVE and x86-64 AVX2/AVX-512 differ structurally. What is the minimal portable `Simd<T, comptime Lanes: usize>` intrinsic surface that lowers without emulation cliffs on both ARM64 and x86-64?