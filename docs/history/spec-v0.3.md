# Flyscript Language Specification (v0.3)

File extension: `.fly`

---

## 1. Goals and Non-Goals

### 1.1 Goals
1. **TypeScript surface, systems semantics:** Idiomatic TypeScript syntax (`function`, `(x) => expr`, `const`/`let`, `struct`, `interface`, `implements`, `type`, `<T>`, ES modules) compiled ahead-of-time to native code with unboxed layouts and deterministic destruction.
2. **Static affine ownership with second-class borrows:** Every heap allocation has a single owner by default (`Box<T>`, `Vec<T>`, `String`). Borrows (`readonly T`, `mut T`) are strictly second-class lexical permissions on parameters, local bindings, and tied return values—never stored inside struct fields or enum variants—eliminating Rust-style `'a` lifetime annotations on data types.
3. **Zero-GC cyclic data via lexical regions and typed index pools:** Short-lived cyclic or multi-parent graphs use fiber-local bump-allocated lexical regions (`region R`); long-lived dynamic graphs use generation-checked typed index pools (`Pool<T>` and `Handle<T>`).
4. **Typed algebraic effects with one-shot continuations:** Recoverable failure, I/O, and structured concurrency are tracked as effect rows (`uses Io, Fail<E>`) rather than `async`/`await` function coloring or untyped exceptions.
5. **Compile-time execution in the host language:** Generics, type-level computation, and layout specialization are ordinary Flyscript functions evaluated at `comptime`.

### 1.2 Non-Goals (v0.3)
1. **Structural typing:** All `struct`, `enum`, and `interface` definitions are nominal.
2. **Garbage collection:** There is no global or actor-local tracing garbage collector in the language or runtime.
3. **Multi-shot continuations:** Effect handlers may resume a captured continuation at most once.
4. **Arbitrary dependent or non-linear refinement types:** Dependent type checking is decidable, but requires users to construct manual proof terms. Flyscript restricts value-indexed types to `comptime` constants and linear integer constraints (Quantifier-Free Presburger Arithmetic); multi-dimensional indexing uses dedicated strided view types (`Grid2D<T>`, `Grid3D<T>`) rather than non-linear multiplication proofs.
5. **Automatic GPU kernel compilation:** Lowering data-parallel loops to SPIR-V/PTX/Metal requires explicit shared-memory and warp-divergence modeling and is deferred to future work.

---

## 2. Core Design Decisions and Rationales

1. **Affine Ownership + Static Reuse (No Perceus RC):** Heap values (`Box<T>`, `Vec<T>`, `String`) use static affine move semantics. The compiler performs compile-time reuse analysis (reusing storage of a consumed `Box<T>` when constructing a same-sized `Box<U>` in the same scope) with zero runtime reference counts. Cross-thread shared immutable data uses explicit `Arc<T>`.
   * *Rationale:* Static uniqueness gives LLVM stronger alias guarantees (`noalias`) than reference counting and avoids atomic traffic or header overhead on small allocations.
2. **Strict Ban on Borrows in Structs (Including Regions):** Neither `readonly T` nor `mut T` (including `str` and `T[]`) may appear as a field of any `struct` or `enum`, even inside a `region R`. Region structs may only contain `Pod` scalars, inline `Pod` structs/enums, intra-region pointers `In<R, T>`, and intra-region slices `In<R, T[]>`.
   * *Rationale:* Allowing outer borrows inside region structs reintroduces covariance/outlives checking between region variables and unnamed borrow lifetimes. Copying external data into the region via `r.copySlice(...)` or `r.copyStr(...)` keeps region safety purely rank-2 over `R`.
3. **Cutting Actor-Local Tracing GC in Favor of `Pool<T>` + `Handle<T>`:** Long-lived cyclic state (state machines, entity graphs, DOMs, caches) uses standard-library generational arenas (`Pool<T>` indexed by `Handle<T>`, a 64-bit `(index: u32, generation: u32)` Pod token) rather than an actor-local tracing GC.
   * *Rationale:* A `Pool<T>` is a single owned value (`own Pool<T>` or `iso Pool<T>`), stores nodes contiguously in cache, requires zero write barriers or root-scanning tables in the compiler backend, and can be sent across actors in $O(1)$ inside an `iso` envelope.
4. **Exact Definition of `iso T`, `val T`, and `Arc<T>`:**
   * `iso T` is an **owned isolated pointer** to a heap subgraph allocated inside a dedicated isolation arena (`IsoArena`) that has zero pointers entering from or exiting to mutable external state.
   * `val T` is a **capability qualifier on `T`** meaning "transitively immutable (contains no interior mutability and no mutable borrows)." Any `Pod` type is trivially `val`.
   * `Arc<T>` requires `T: val` and is an **owned atomically reference-counted handle** to a frozen heap allocation or frozen `IsoArena` segment. Borrowing an `Arc<T>` yields `readonly T` with zero refcount traffic. No `mprotect` syscalls are used; deep immutability is enforced statically by the typechecker.
   * *Rationale:* Separating the ownership wrapper (`Arc<T>`) from the deep-immutability constraint (`val`) removes ambiguity between borrowed views (`readonly T`) and owned shared handles (`Arc<T>`).
5. **Creating `iso T` via `recover { ... }`:** An `iso T` value is created by a `recover { ... }` expression, which opens a fresh `IsoArena`, executes the block, and returns its result as `iso T`. Capture rule: every free variable referenced inside `recover { ... }` must be either consumed as `iso`, or accessed as `val` / `Pod` by copy or `Arc<T>`. Local `mut` and `readonly` borrows from the enclosing scope cannot enter a `recover` block.
   * *Rationale:* Follows Pony’s capability recovery: if nothing mutable enters the block from outside, the returned subgraph cannot be aliased by the outside world.
6. **Fiber-Owned Segmented Regions:** Each stackful fiber owns its own segmented bump-allocator chain (`FiberArena`). Entering `region R` records a watermark `(slabPtr, offset)` on the **current fiber’s** arena; suspending a fiber suspends its region stack with it. Child fibers spawned in `Async.scope` may **read** `In<R, T>` pointers from a parent region as `readonly`, but **cannot allocate** into a parent fiber's `region R` (the `Region<R>` allocator handle is `!Send` and `!Sync`).
   * *Rationale:* Thread-local region stacks corrupt LIFO ordering the moment two fibers interleave across an `Io` suspension point; fiber-local watermark stacks preserve strict LIFO order per fiber with zero synchronization.
7. **Handlers $\times$ Borrows (Abortive vs. Resumptive Arms):** A handler arm that **never mentions `resume`** (an *abortive arm*, such as `Fail.raise(err) => { ... }`) executes **after** the handled block's stack frames, regions, and active lexical borrows (`mut` and `readonly`) have been unwound and released. Therefore, an abortive arm may freely access variables (`conn`) that were mutably borrowed inside the `handle` block. A handler arm that **binds `resume`** executes *while* the handled block is still suspended on the stack, so any borrows held by the suspended block remain locked and inaccessible to that handler arm.
   * *Rationale:* Matches traditional `try / catch` ergonomics for abortive errors while preserving strict aliasing exclusivity when a continuation is still live.
8. **Heap Allocation, Purity, and Panics:**
   * Heap allocation (`Box`, `Vec`, `Region.alloc`) and deterministic cleanups (`Drop`) are **not** effects in `uses`; an observationally pure function (`uses` nothing) and a `par for` body may allocate and free local heap/region memory using the fiber/thread-local allocator.
   * OOM, integer division by zero, arithmetic overflow in debug mode (wrapping functions `wrappingAdd` are explicit), and unrefined out-of-bounds slice indexing trigger an **unrecoverable fiber/task panic**, which unwinds the fiber stack running `Drop` destructors and aborts the enclosing `Async.scope` (or terminates the process if on the root task). Panics cannot be caught by `handle`.
   * *Rationale:* Treating allocation or arithmetic traps as tracked `uses` effects pollutes every function signature in the language and prevents pure data-parallel code from using temporary buffers.
9. **Refinement Decision Procedure:** Linear integer refinements are checked using **Quantifier-Free Presburger Arithmetic over integers (QF_LIA)** decided by **Fourier-Motzkin variable elimination with Omega test integer tightening**, restricted to at most 16 variables per verification condition.
   * *Rationale:* Complete, fast ($<1\text{ms}$ per function), and deterministic without shipping an external SMT solver.

---

## 3. Lexical Syntax and Complete Grammar (EBNF)

### 3.1 Disambiguation and Lexical Rules
* **`const` vs. `let`:** `const x = expr` binds an immutable variable: `x` cannot be reassigned, and `mut x` borrows cannot be taken from it. `let x = expr` binds a mutable variable: `x` may be reassigned and borrowed via `mut x`.
* **Numeric and Array Literals:** Numeric literals (`0`, `42`, `3.14159`) have no type suffixes; their concrete scalar type (`i32`, `u16`, `f32`, `usize`) is inferred bidirectionally from the expected type, defaulting to `i32` for integers and `f64` for floats when unconstrained. Explicit conversion uses `expr as ScalarType`. Fixed-size array repetition uses `Array.fill<T, N>(val)` or `[val; N]` is replaced by `repeat<N>(val)`.
* **Struct Literals:** Written `{ field: value, ... }` when the target nominal `struct` type is known from bidirectional context, or prefixed with the type name `StructName { field: value, ... }` when unconstrained.
* **Generic Call `<` Disambiguation:** In expression position, `Ident<TypeArgs>(...)` and `Expr.Ident<TypeArgs>(...)` are parsed by speculative lookahead: if `<` is followed by a balanced `TypeArgList` and immediately followed by `(` or `{`, it is parsed as generic instantiation; otherwise `<` is the binary less-than operator.
* **Explicit Borrow Call-Site Markers:** Passing a mutable borrow requires `mut expr` at both the signature and the call site (`conn.read(mut rawBuf)`). Passing a shared `readonly` borrow requires no keyword at the call site (`parse(rawBuf)`).

### 3.2 EBNF Grammar

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
                  [ "->" ParamIdent ] ":" Type [ UsesClause ] Block ;
SelfParam       = "self" ":" ( "Self" | "mut" "Self" | "readonly" "Self" ) ;

EnumDecl        = "enum" Ident [ TypeParams ] [ "implements" TypeList ]
                  "{" VariantDecl { "," VariantDecl } [ "," ] "}" ;
VariantDecl     = Ident [ "(" TypeList ")" | "{" { FieldDecl } "}" ] ;

InterfaceDecl   = "interface" Ident [ TypeParams ] "{" { InterfaceSig ";" } "}" ;
InterfaceSig    = "function" Ident [ TypeParams ] "(" [ SelfParam [ "," ParamList ] | ParamList ] ")"
                  [ "->" ParamIdent ] ":" Type [ UsesClause ] ;

ImplDecl        = "impl" [ TypeParams ] TypeRef "for" TypeRef "{" { MethodDecl } "}" ;
TypeAliasDecl   = "type" Ident [ TypeParams ] "=" Type ";" ;

EffectDecl      = "effect" Ident [ TypeParams ] "{" { OpSig ";" } "}" ;
OpSig           = Ident "(" [ ParamList ] ")" ":" Type ;

FunctionDecl    = [ "comptime" ] "function" Ident [ TypeParams ]
                  "(" [ ParamList ] ")" [ "->" ParamIdent ] ":" Type [ UsesClause ] Block ;

ParamList       = Param { "," Param } [ "," ] ;
Param           = [ "comptime" ] Ident ":" ParamType ;
ParamType       = [ "mut" | "readonly" ] Type ;

UsesClause      = "uses" EffectRow ;
EffectRow       = EffectRef { "," EffectRef } ;
EffectRef       = Ident [ TypeArgs ] ;

TypeParams      = "<" TypeParam { "," TypeParam } ">" ;
TypeParam       = "region" Ident
                | "effect" Ident [ "=" "[" [ EffectRow ] "]" ]
                | "comptime" Ident ":" Type
                | Ident [ ":" ConstraintList ] ;
ConstraintList  = Constraint { "+" Constraint } ;
Constraint      = "Pod" | "Send" | "val" | TypeRef ;

TypeArgs        = "<" TypeArg { "," TypeArg } ">" ;
TypeArg         = Type | Expr | "[" [ EffectRow ] "]" ;

Type            = PrimType
                | "iso" Type
                | "val" Type
                | "dyn" TypeRef
                | "Region" "<" Ident ">"
                | "In" "<" Ident "," Type ">"
                | TypeRef
                | Type "[" [ Expr ] "]"
                | "(" [ ClosureParamList ] ")" [ "->" ParamIdent ] "=>" Type [ UsesClause ]
                | PrimIntType "where" RefinementPred ;

TypeRef         = Ident [ "." Ident ] [ TypeArgs ] ;
PrimIntType     = "i8" | "i16" | "i32" | "i64" | "isize" | "u8" | "u16" | "u32" | "u64" | "usize" ;
PrimType        = PrimIntType | "f32" | "f64" | "bool" | "str" | "void" | "never" | "Type" ;

Expr            = MatchExpr | RegionExpr | RecoverExpr | HandleExpr | TryExpr | ... ;
MatchExpr       = "match" "(" Expr ")" "{" { MatchArm } "}" ;
MatchArm        = Pattern [ "if" Expr ] "=>" ( Expr "," | Block ) ;
RegionExpr      = "region" "(" Ident ")" Block ;
RecoverExpr     = "recover" Block ;
TryExpr         = "try" Expr ;

HandleExpr      = "handle" Block "with" EffectRef "{" { HandlerArm } [ ReturnArm ] [ FinallyArm ] "}" ;
HandlerArm      = Ident "(" [ HandlerParamList ] ")" [ "resumes" Ident ] "=>" Block ;
HandlerParamList= Ident [ ":" Type ] { "," Ident [ ":" Type ] } ;
ReturnArm       = "return" "(" Ident [ ":" Type ] ")" "=>" Block ;
FinallyArm      = "finally" "=>" Block ;
```

---

## 4. Types, Strings, Methods, and Interfaces

### 4.1 Primitives, Strings, and Views
* **Scalars (`Pod`):** `i8`, `i16`, `i32`, `i64`, `isize`, `u8`, `u16`, `u32`, `u64`, `usize`, `f32`, `f64`, `bool`, `void`, `never`.
* **Strings:**
  * `str`: a borrowed, UTF-8 validated slice `(ptr: readonly u8*, len: usize)`. `str` is always a second-class borrowed view (equivalent to `readonly str`) and cannot be stored in a struct field. String literals `"hello"` have static type `str` (allocated in read-only binary `.rodata`, valid for the entire program).
  * `String`: an owned, growable UTF-8 heap buffer (`own String`). Borrowing `s: String` coerces to `str`.
  * `In<R, str>`: a UTF-8 string slice allocated inside lexical `region(r)`, valid for the lifetime of `R` and storable inside region structs.
* **Slices and Grids:**
  * `T[N]`: inline fixed-size array of `N` elements (`Pod` if `T: Pod`). Initialized via `[a, b, c]` or `repeat<N>(val)`.
  * `T[]`: second-class borrowed slice view (`readonly T[]` or `mut T[]`).
  * `Grid2D<T>`: second-class strided 2D view (`readonly Grid2D<T>` or `mut Grid2D<T>`) indexed via `grid.get(row, col)` where `row: Index<Rows>` and `col: Index<Cols>`, avoiding non-linear `row * stride + col` proof obligations.

### 4.2 Tied Borrow Return Signatures (`-> paramName`)
Because borrows have no named lifetime parameters (`'a`), any function returning a borrowed view (`readonly T`, `mut T`, `str`, `T[]`) must either take exactly one borrowed input parameter (which it ties to automatically) or specify the source parameter via `-> paramName`:

```ts
function subslice(
  buf: readonly u8[],
  fallback: readonly u8[],
  useFirst: bool,
) -> buf: readonly u8[] {
  // Error if `fallback` is returned; return borrow is tied strictly to `buf`
  return buf[0..4];
}
```
The caller's borrow of `buf` remains active for as long as the returned view is live.

### 4.3 Methods, `implements`, and External `impl`
Methods are declared directly inside `struct` or `enum` blocks with an explicit `self` parameter (`self: Self` for consuming by move, `self: mut Self` for exclusive mutation, `self: readonly Self` for shared read):

```ts
interface Hashable<effect E = []> {
  function hash(self: readonly Self): u64 uses E;
}

struct UserId implements Hashable {
  raw: u64;

  function hash(self: readonly Self): u64 {
    return self.raw ^ (self.raw >> 32);
  }
}
```
To implement an interface defined in the current module for a type imported from another module, use `impl Interface for Type { ... }`. **Orphan Rule:** Every `implements` or `impl` must appear in the module defining the interface or the module defining the target type.

---

## 5. Ownership, Capabilities, Closures, and Regions

### 5.1 Capabilities and `recover` Blocks

| Type / Modifier | Category | Meaning | Storable in Struct Field? | `Send` Across Tasks? |
| :--- | :--- | :--- | :--- | :--- |
| **`T`** (default) | Ownership | Uniquely owned value (`own`) | Yes | Yes (if fields are `Send`) |
| **`iso T`** | Ownership | Isolated heap subgraph in its own `IsoArena` | Yes | **Yes ($O(1)$ pointer move)** |
| **`Arc<T>`** (`T: val`) | Ownership | Atomically reference-counted frozen subgraph | Yes | **Yes ($O(1)$ refcount clone)** |
| **`val T`** | Qualifier | Type `T` contains no interior mutability or borrows | Yes (as `T`) | Yes |
| **`mut T`** | Borrow (2nd-class) | Exclusive lexical borrow of `T` | **Never** | Scoped `par for` only |
| **`readonly T`** | Borrow (2nd-class) | Shared lexical borrow of `T` | **Never** | Scoped `Async.scope` / `par for` |
| **`In<R, T>`** (`T: Pod`) | Region Ref | Pointer into lexical `region(r)` | Only inside `Struct<region R>` | Read-only in `Async.scope` |

#### Constructing, Mutating, and Freezing `iso T`
1. **Creation (`recover`):**
   ```ts
   const packet: iso Packet = recover {
     let p = Packet.create();
     p.appendPayload(bytes); // `bytes` must be Pod/val or moved `iso`
     p
   };
   ```
   Inside `recover { ... }`, heap allocations (`Vec`, `Box`, `String`, `Pool`) are routed into a fresh `IsoArena`. No `mut` or `readonly` borrows from the enclosing scope may be read unless copied as `Pod`.
2. **Scoped Mutation:** If `let x: iso T` is owned locally, passing `mut x` to a function whose other parameters are all `val` or `Pod` temporarily borrows the isolated subgraph as `mut T` without breaking isolation on return.
3. **Freezing (`freeze`):** Calling `freeze(x: iso T): Arc<T>` consumes `x`, seals its `IsoArena` against further allocation, initializes its segment reference count to 1, and returns `Arc<T>` (where `T` is now `val T`).

### 5.2 Closures and Capture Inference
Because borrows are second-class, Flyscript distinguishes **non-escaping (second-class) closures** from **escaping (`Send`) closures**:
1. **Inferred Calling Mode:** The compiler infers whether a closure is:
   * **Shared (`(Args) => Ret`):** Captures outer variables only by `readonly` borrow or `val` copy; callable multiple times concurrently.
   * **Mutating (`mut (Args) => Ret`):** Captures at least one outer variable by `mut` borrow; callable sequentially by a single owner.
   * **Consuming (`once (Args) => Ret`):** Moves an owned (`T` or `iso T`) variable out of its environment; callable at most once.
2. **Second-Class Closure Rule:** Any closure that captures a `readonly` or `mut` borrow from its enclosing frame is **second-class**: it may be passed downward as a function parameter (to `forEach`, `Async.scope`, `par for`), but **cannot** be returned from a function, stored in a struct/enum field, or sent over a `Channel<T>`.

### 5.3 Fiber-Local Lexical Regions (`region(r)`)
```ts
region (r) {
  // `r` has type `Region<R>` where `R` is a fresh rigid region type variable
  const slice: In<R, u8[]> = r.copySlice(inputBytes);
}
```
* **Region API on `r: Region<R>`:**
  * `r.alloc<T: Pod>(val: T): In<R, T>`
  * `r.allocSlice<T: Pod>(len: usize, fill: T): In<R, T[]>`
  * `r.copySlice<T: Pod>(src: readonly T[]): In<R, T[]>`
  * `r.copyStr(src: str): In<R, str>`
* **Dereferencing and Indexing:** Given `p: In<R, T>`, reading or mutating `p.field` is valid whenever `R` is in lexical scope and not concurrently shared across `Async.scope` fibers. Given `s: In<R, T[]>`, `s.asReadonly(): readonly T[]` and `s.asMut(): mut T[]` borrow the region slice for functions expecting standard slices.
* **Non-Escape Rule:** In `region (r) { body } : RetType`, the region type parameter `R` must not appear in `RetType` or in any outer variable mutated by `body`.

---

## 6. Effects, Handlers, and Error Handling

### 6.1 Standard Effects (`std/effects`)
Flyscript defines two built-in core effects in the prelude:
1. **`Fail<E>`:** Short-circuiting typed failure:
   ```ts
   effect Fail<E> {
     raise(err: E): never;
   }
   ```
2. **`Io`:** Performing operating-system I/O, timers, or fiber suspension (scheduled on the runtime's `io_uring` / `kqueue` event loop). Structured concurrency (`Async.scope`) is a standard library API requiring `uses Io`.

### 6.2 `Result<T, E>` vs. `Fail<E>` and Conversion
* Use **`Fail<E>`** on functions that execute a pipeline of fallible steps where callers normally propagate or handle errors at a boundary.
* Use **`Result<T, E>`** when failure is an expected per-item data outcome stored in collections or returned across C FFI.
* **Bridging (`try` and `Result.capture`):**
  * `try resultExpr`: unwraps `Ok(v)` to `v`, or calls `Fail.raise(err)` on `Err(err)` (requires `uses Fail<E>`).
  * `Result.capture(() => expr)`: handles `Fail<E>` around `expr` and returns `Result<T, E>` with `Fail<E>` removed from the `uses` row.

### 6.3 Handler Semantics: Resumptive vs. Abortive Arms
```ts
const value = handle {
  work(mut conn)
} with MyEffect {
  // 1. RESUMPTIVE ARM (`resumes k` present):
  // `work` is still suspended on its fiber stack; `conn` is STILL mutably borrowed by `work`
  // and CANNOT be accessed here. `k` is an affine one-shot continuation.
  askConfig(key) resumes k => {
    return k(lookup(key));
  }
  // 2. ABORTIVE ARM (`resumes` omitted):
  // Immediately unwinds `work`'s stack frames, runs all `Drop` destructors, exits inner
  // regions, and RELEASES the `mut conn` borrow before executing the arm body!
  abortWith(code) => {
    conn.reset(code); // Legal: `work`'s borrow of `conn` has already ended!
    return defaultResult();
  }
  return(v) => {
    return transform(v);
  }
  finally => {
    cleanup(); // Runs on normal return, abortive arm, or unhandled unwind
  }
};
```

---

## 7. Concurrency and Parallelism

### 7.1 Structured Concurrency (`Async.scope`)
```ts
// Defined in `std/async`:
// function scope<T, effect E>(
//   body: (s: mut Scope) => T uses Io, E
// ): T uses Io, E;
```
* **`s.spawn(fn)`:** Accepts a **shared closure** `() => R uses Io, Fail<Err>` that may capture outer variables only as `readonly` borrows, `val` copies, `Arc<T>`, or read-only `In<R, T>` pointers. While an `Async.scope` is active, any `region(r)` in the enclosing function is frozen as read-only (`r: Region<R>` cannot be mutated or passed to `alloc` until `Async.scope` returns).
* **Deterministic Join & Error Propagation:** `Async.scope` waits for all spawned fibers before returning. If any child fiber raises an unhandled `Fail<E>` (and `E` is in the scope's effect row), sibling fibers are cancelled at their next `Io` suspension point, their stacks are unwound cleanly, and `Fail.raise(e)` propagates out of `Async.scope`.

### 7.2 Data Parallelism (`par for` and `@layout(soa)`)
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
* **Purity and Disjointness Rule:** The body of `par for` must have an **empty `uses` clause**, may capture outer variables only as `readonly` or `val`, and binds `let p` as an exclusive `mut` reference to a single disjoint element index. Heap/region allocation inside the loop body uses thread-local arenas and is permitted.

---

## 8. Complete Validated Example (`http_handler.fly`)

Every line of this program conforms to the v0.3 grammar, borrow rules, region non-escape rules, and abortive handler rules:

```ts
import { Socket, DbClient, Async, Scope } from "std/net";

export enum HttpError {
  MalformedRequest,
  Unauthorized,
  BackendTimeout,
}

// Pod struct living inside region R; holds only intra-region `In<R, str>` views (no outer borrows)
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
  // Copy slices into region R as validated UTF-8 strings; freed in O(1) on region exit
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
      const n = try conn.read(mut rawBuf);
      const req: In<reqArena, ParsedReq<reqArena>> = parseHeader(mut reqArena, rawBuf[0..n]);

      // Spawn two concurrent fibers in a structured nursery.
      // `reqArena` is frozen as read-only during `Async.scope`; both fibers read `req` safely.
      const pair = Async.scope((s: mut Scope) => {
        const fProfile = s.spawn(() => db.fetchProfile(req.userId.asStr()));
        const fQuota   = s.spawn(() => db.checkTokenQuota(req.authToken.asStr()));
        return { profile: fProfile.join(), quota: fQuota.join() };
      });

      if (!pair.quota.allowed) {
        Fail.raise(HttpError.Unauthorized);
      }
      try conn.writeStatus(200, pair.profile.displayName.asStr());
    } // <-- `reqArena` fiber watermark reset in 1 instruction here
  } with Fail<HttpError> {
    // Abortive arm (no `resumes` keyword): `reqArena` is already torn down and the
    // inner `mut conn` borrow is released before this block runs, so `conn` is usable here.
    raise(err) => {
      const code: u16 = match (err) {
        HttpError.MalformedRequest => 400,
        HttpError.Unauthorized     => 401,
        HttpError.BackendTimeout   => 504,
      };
      let _ = Result.capture(() => conn.writeStatus(code, "error"));
    }
  };
}
```

---

## 9. Compiler Pipeline

1. **Stage 1 — Lexer & Recursive Descent Parser:** Parses `.fly` files into an untyped CST, resolving `<TypeArgs>(` via bounded speculative lookahead and checking DAG module imports.
2. **Stage 2 — `comptime` Bytecode Evaluator & Monomorphizer:** Evaluates `comptime` functions and constants deterministically, erasing `Type` parameters and generating specialized monomorphic HIR definitions.
3. **Stage 3 — Bidirectional Type, Effect & Refinement Checker:**
   * Checks nominal types, `implements`/`impl` coherence, closure capture modes (`once` / `mut` / shared), and infers local expression and literal types bidirectionally.
   * Verifies `uses` effect rows and defaults interface effect parameters (`effect E = []`).
   * Solves linear integer refinements (`where self < N`) via **Fourier-Motzkin elimination + Omega integer tightening** over QF_LIA ($\le 16$ variables per obligation).
4. **Stage 4 — Capability, Borrow & Region Pass (Mid-End SSA IR):**
   * Enforces affine move semantics (`own`), `recover` block capture isolation (`iso`), lexical borrow exclusivity (`mut` XOR `readonly`), and abortive vs. resumptive handler borrow lifetimes.
   * Verifies rank-2 non-escape for every `region(r)` variable and freezes active regions across `Async.scope`.
   * Performs **Static Affine Reuse** (rewriting `Drop(Box<T>)` followed by same-size `Alloc(Box<U>)` into in-place mutation).
   * Lowers `@layout(soa)` field projections and **Evidence-Passing Effect Transformation**.
5. **Stage 5 — Code Generation:**
   * **Debug:** Cranelift (or C11 backend) for fast incremental turnaround.
   * **Release:** LLVM IR with `noalias` and `readonly` attributes emitted on every `mut`, `readonly`, `iso`, and `val` parameter.

---

## 10. Genuine Open Questions

1. **Stacklet Growth vs. C FFI Stack Frames:** Fiber stacks start at 4 KB and grow dynamically by allocating segmented stacklets at Flyscript function prologues. However, calling an `extern "C"` function requires at least 64 KB of contiguous native stack because C compilers do not emit segmented-stack prologues. Should `extern "C"` calls switch to the OS worker thread's native system stack on entry (as Go’s `cgo` does), or allocate virtual-memory guard-paged 1 MB stacks for fibers that perform FFI?
2. **SIMD Portable Vector Intrinsics vs. Auto-Vectorization:** While `@layout(soa)` and `par for` guarantee LLVM auto-vectorization for map/reduce loops, algorithms like SIMD string parsing (`simdjson`-style shuffle/bitmask operations) require explicit horizontal lane operations. What is the minimal target-neutral `Simd<T, Lanes>` API that maps cleanly to both ARM64 NEON/SVE and x86-64 AVX2/AVX-512 without leaking architecture-specific intrinsics into safe code?