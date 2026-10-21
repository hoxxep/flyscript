# Flyscript Language Specification (v0.2)

File extension: `.fly`

---

## 1. Goals and Non-Goals

### 1.1 Goals
1. **TypeScript surface, systems semantics:** Familiar syntax for developers who read TypeScript (`function`, `const`/`let`, `interface`, `type`, `<T>`, ES modules), compiled ahead-of-time to native machine code with deterministic resource management and unboxed data layouts.
2. **Static affine ownership without lifetime parameters on types:** Values have a single owner by default; borrows are second-class lexical permissions on function parameters and local bindings, never type parameters (`'a`) on data definitions.
3. **Lexical regions and actor-isolated heaps for graphs:** Cyclic and multi-parent data structures are built inside explicit lexical regions (`region R`) freed in bulk, or inside task-isolated heaps (`iso`) collected locally without global stop-the-world pauses.
4. **Typed algebraic effects with one-shot continuations:** Side effects, structured concurrency, and recoverable failures are tracked as effect rows (`uses Io, Fail<E>`) rather than `async`/`await` coloring or untyped exceptions.
5. **Compile-time execution in the host language:** Type-level computation and code generation use ordinary Flyscript functions evaluated at `comptime`.

### 1.2 Non-Goals (v0.2)
1. **Structural typing:** All `struct`, `enum`, and `interface` definitions are nominal.
2. **Multi-shot continuations:** Effect handlers may resume a captured continuation at most once; backtracking/nondeterminism via multi-shot resumption is excluded to preserve affine resource safety.
3. **Full dependent types:** Dependent type checking is decidable, but requires users to construct manual proof terms for arbitrary predicates. Flyscript restricts value-indexed types to `comptime` constants and linear integer refinements discharged automatically by a built-in Presburger arithmetic solver.
4. **Automatic GPU kernel compilation:** Lowering pure data-parallel loops to SPIR-V/PTX/Metal requires hardware-specific memory hierarchy mapping (shared memory tiling, warp divergence constraints) and is deferred to future work.
5. **Unrestricted pointers Inside Regions:** Region-allocated values cannot directly own non-trivially destructible external resources without explicit registration (see Section 5.4).

---

## 2. Decisions Resolving v0.1 Ambiguities

1. **Ownership vs. Perceus:** Flyscript uses **static affine ownership with moves** as its sole default model for heap allocations (`Box<T>`, `Vec<T>`, `String`). There is no implicit reference counting. **Static reuse optimization** (reusing the memory allocation of a consumed `Box<T>` or enum variant in the same basic block when sizes match) is performed purely at compile time via linear dataflow analysis, requiring zero reference-count headers or runtime checks. Explicit reference counting exists only in the standard library as `Arc<val T>` for cross-task shared immutable roots.
2. **Type Inference:** Flyscript uses **bidirectional local type inference** executed *after* `comptime` evaluation. Every top-level and exported `function` must explicitly annotate its parameter types, return type, and `uses` effect clause. Inside function bodies, `const`/`let` bindings, generic type arguments at call sites, and closure parameter/return/effect types are inferred locally from outward context or initializer expressions.
3. **Effects $\times$ Affinity:** All delimited continuations captured by effect handlers are **affinely one-shot** (`Continuation<In, Out, Uses>`). Invoking `resume(v)` consumes the continuation linearly; failure to resume a suspended continuation automatically unwinds its suspended stack frame and runs all pending lexical destructors (`Drop`) from innermost to outermost scope. Tail-resumptive handlers (`resume` in tail position) compile via **evidence passing** to direct function calls with zero stack switching; non-tail suspending handlers switch a pooled stackful fiber segment.
4. **Regions $\times$ Destructors:** A lexical `region R` is a pure bump-allocated arena freed in $O(1)$ by resetting a single pointer on exit. Therefore, only types implementing the marker trait **`Pod` (Plain Old Data / no `Drop` destructor)** may be allocated inside a `region R`. A region-allocated struct may contain scalars, inline structs/enums of `Pod` types, and intra-region pointers ` In<R, T>`, as well as borrowed references (`readonly T`) that outlive `R`. It **cannot** own a `Box<T>`, `Arc<val T>`, `iso T`, or file descriptor. If a region computation needs to register cleanup actions, it must allocate an explicit destructor list outside the fast bump path via `R.defer(() => ...)`.
5. **Reclaiming `val`:** Deeply immutable graphs (`val T`) shared across actors/threads are reclaimed via **deferred atomic reference counting (`Arc<val T>`) on the root allocation only**. When an `iso` subgraph is frozen into a `val` subgraph (`freeze(graph)`), the entire isolated heap segment is sealed as a single read-only arena header with one atomic reference count for the segment as a whole. Traversing internal pointers inside a `val` graph touches zero reference counts; when the last `Arc<val T>` handle across actors drops, the sealed segment is freed as a unit.
6. **Naming & Purity Rules:**
   * Capability `ref T` is replaced by TypeScript’s **`readonly T`** (immutable borrow) and **`mut T`** (exclusive mutable borrow). Region pointers are named **`In<R, T>`** ("a pointer to `T` living in region `R`").
   * **Observational Purity Rule:** A function with no `uses` clause (empty effect row) is **observationally pure**: it may allocate temporary regions, mutate local `let` variables, and mutate caller-supplied `mut T` parameters in place, because `mut T` is exclusively owned by the caller and the mutation is isomorphic to returning an updated value `(T, Return)`. It may not perform I/O, read mutable globals, or observe wall-clock time.
7. **Capability System:** Reduced to **four orthogonal capabilities** (`own`, `mut`, `readonly`, `iso`) plus one deep-immutability qualifier (`val`). See Section 5.1 for the complete conversion and subtyping lattice.

---

## 3. Lexical Syntax and Grammar Sketch (EBNF)

```ebnf
Module          = { ImportDecl | ExportDecl | TopDecl } ;
ImportDecl      = "import" "{" IdentList "}" "from" StringLit ";" ;
ExportDecl      = "export" TopDecl ;

TopDecl         = StructDecl | EnumDecl | InterfaceDecl | TypeAliasDecl
                | EffectDecl | FunctionDecl ;

StructDecl      = [ LayoutAttr ] "struct" Ident [ TypeParams ] "{" { FieldDecl } "}" ;
FieldDecl       = Ident ":" Type ( ";" | "," ) ;
LayoutAttr      = "@layout" "(" ( "aos" | "soa" | "packed" | "c" ) ")" ;

EnumDecl        = "enum" Ident [ TypeParams ] "{" VariantDecl { "," VariantDecl } [ "," ] "}" ;
VariantDecl     = Ident [ "(" TypeList ")" | "{" { FieldDecl } "}" ] ;

InterfaceDecl   = "interface" Ident [ TypeParams ] "{" { MethodSig ";" } "}" ;
TypeAliasDecl   = "type" Ident [ TypeParams ] "=" Type ";" ;

EffectDecl      = "effect" Ident [ TypeParams ] "{" { OpSig ";" } "}" ;
OpSig           = Ident "(" [ ParamList ] ")" ":" Type ;

FunctionDecl    = [ "comptime" ] "function" Ident [ TypeParams ]
                  "(" [ ParamList ] ")" ":" Type [ UsesClause ] Block ;

ParamList       = Param { "," Param } [ "," ] ;
Param           = [ "comptime" ] Ident ":" ParamType ;
ParamType       = [ "mut" | "readonly" | "iso" | "val" ] Type ;

UsesClause      = "uses" EffectRow ;
EffectRow       = EffectRef { "," EffectRef } ;
EffectRef       = Ident [ TypeArgs ] ;   (* Ident may be a concrete effect or effect variable E *)

TypeParams      = "<" TypeParam { "," TypeParam } ">" ;
TypeParam       = "region" Ident
                | "effect" Ident
                | "comptime" Ident ":" Type
                | Ident [ ":" ConstraintList ] ;

Type            = PrimType
                | CapabilityMod Type
                | Ident [ TypeArgs ]
                | Type "[" [ RefinementExpr ] "]"     (* Slices & fixed arrays *)
                | "(" [ ParamTypeList ] ")" "=>" Type [ UsesClause ]
                | IntegerType "where" RefinementPred ;

CapabilityMod   = "iso" | "val" ;
PrimType        = "i8" | "i16" | "i32" | "i64" | "isize"
                | "u8" | "u16" | "u32" | "u64" | "usize"
                | "f32" | "f64" | "bool" | "void" | "never" | "Type" ;

Expr            = MatchExpr | RegionExpr | HandleExpr | LambdaExpr | BinaryExpr | CallExpr | ... ;

MatchExpr       = "match" "(" Expr ")" "{" { MatchArm } "}" ;
MatchArm        = Pattern [ "if" Expr ] "=>" ( Expr "," | Block ) ;

RegionExpr      = "region" Ident Block ;

HandleExpr      = "handle" Block "with" Ident "{" { HandlerArm } "}" ;
HandlerArm      = Ident "(" [ ParamList ] "," "resume" ")" "=>" Block ;
```

---

## 4. Types

### 4.1 Primitives and Containers
* **Scalars:** `i8`, `i16`, `i32`, `i64`, `isize`, `u8`, `u16`, `u32`, `u64`, `usize`, `f32`, `f64`, `bool`, `void`, `never`.
* **Built-inSlices & Arrays:**
  * `T[N]` (where `N: usize` is a `comptime` value): inline fixed-size array of `N` elements.
  * `T[]`: borrowed view (pointer + length) into contiguous `T` elements; always paired with `readonly T[]` or `mut T[]`.
  * `SoaSlice<T>`: borrowed planar view over a `@layout(soa)` struct buffer.
* **Standard Library Heap Types:** `Box<T>` (single affine heap allocation), `Vec<T>` (growable owned buffer), `String` (UTF-8 buffer), `Option<T>` (`Some(T) | None`), `Result<T, E>` (`Ok(T) | Err(E)`).

### 4.2 Nominal Structs, Enums, and Pattern Matching
Structs are constructed with TypeScript object-literal syntax `{ field: value }`, annotated or inferred from context:

```ts
struct Point {
  x: f32;
  y: f32;
}

enum Shape {
  Circle(f32),
  Rect { width: f32; height: f32 },
  Empty,
}

function area(s: readonly Shape): f32 {
  return match (s) {
    Shape.Circle(r) => 3.14159265f32 * r * r,
    Shape.Rect { width, height } => width * height,
    Shape.Empty => 0.0f32,
  };
}
```

### 4.3 Interfaces and Coherence
`interface` defines a trait (typeclass), implemented for a nominal type via `impl Interface for Type`.
* **Static dispatch (default):** `function sort<T: Ord>(items: mut T[]): void` monomorphizes per concrete type `T`.
* **Dynamic dispatch (opt-in):** `dyn Reader` is an explicit 16-byte fat pointer `(dataPtr, vtablePtr)`.
* **Orphan rule:** An `impl I for T` declaration may appear only in the module defining `I` or the module defining `T`.

### 4.4 Linear Integer Refinements
An integer type may carry a linear arithmetic refinement predicate over in-scope `const` integers and slice lengths:

```ts
type Index<comptime N: usize> = usize where self < N;

function dotProduct<comptime N: usize>(a: readonly f32[N], b: readonly f32[N]): f32 {
  let sum: f32 = 0.0f32;
  for (const i: Index<N> of 0..N) {
    // Compiler proves `i < N` via Presburger solver; emits zero bounds checks.
    sum += a[i] * b[i];
  }
  return sum;
}
```
If the solver cannot discharge a refinement obligation from control-flow guards (`if (i < buf.len)`), compilation fails with a diagnostic pointing to the unproven bound.

---

## 5. Ownership, Capabilities, and Regions

### 5.1 The Capability Lattice
Flyscript distinguishes **how a value is passed** (value vs. lexical borrow) from **heap isolation qualifiers** (`iso`, `val`):

| Syntax | Meaning | Aliasing | Mutability | Thread/Actor Transfer |
| :--- | :--- | :--- | :--- | :--- |
| **`T`** (default `own`) | Uniquely owned value | None | Mutable if bound with `let` | Move semantics |
| **`mut T`** | Second-class exclusive borrow | None (locks owner for scope) | Mutable | Scoped `par` blocks only |
| **`readonly T`** | Second-class shared borrow | Arbitrary local aliases | Immutable | Scoped `par` blocks only |
| **`iso T`** | Isolated heap subgraph root | Zero pointers into subgraph from outside | Mutable by owner | **Zero-copy $O(1)$ move** |
| **`val T`** | Deeply immutable subgraph | Arbitrary aliases (via `Arc<val T>`) | **Deeply immutable** | **Zero-copy $O(1)$ share** |

#### Conversion and Subtyping Lattice
$$\text{iso } T \;\xrightarrow{\text{freeze(x)}}\; \text{val } T \;\xrightarrow{\text{borrow}}\; \text{readonly } T$$
$$\text{iso } T \;\xrightarrow{\text{open}}\; T \text{ (own)} \;\xrightarrow{\text{mut borrow}}\; \text{mut } T \;\xrightarrow{\text{reborrow}}\; \text{readonly } T$$

1. **Borrowing (`T` $\to$ `mut T` / `readonly T`):** Passing an owned `let x: T` to a parameter `p: mut T` temporarily suspends access to `x` for the duration of the call. During that scope, either one `mut T` or any number of `readonly T` borrows may exist, never both.
2. **Second-Class Borrow Restriction:** `mut T` and `readonly T` (and slices `readonly U[]`, `mut U[]`) may appear **only** as function parameter types, local variable bindings, and return types whose source parameter is deterministically tied to a single input borrow. **Struct fields and enum variants cannot contain `mut T` or `readonly T`** (they must own `T`, hold `In<R, T>` in a region, or hold `Arc<val T>`). This eliminates Rust-style `'a` struct lifetime virus completely.
3. **Isolation & Freezing (`iso T` $\to$ `val T`):** An `iso T` subgraph is allocated in an independent heap page group. Within an `iso` block, only `iso` and `val` values may enter from outside (ensuring no external mutable alias into the subgraph exists). Calling `freeze(x: iso T): Arc<val T>` consumes `x`, marks its heap pages read-only, attaches a single atomic refcount to the segment header, and returns a shareable `Arc<val T>`.

### 5.2 Static Affine Reuse (Compile-Time Perceus)
When a function consumes an owned heap value (e.g., `node: Box<TreeNode>`) and constructs a new `Box<TreeNode>` of identical size and alignment before `node`'s storage dies, the mid-end compiler rewrites `free(node); malloc(sizeof(TreeNode))` into an in-place write to `node`'s address. Unlike Koka’s Perceus, this requires **no runtime reference count check** because `Box<T>` is statically unique (`own`).

### 5.3 Lexical Regions (`region R`)
A `region R { ... }` expression creates a lexical bump-allocation arena on the current thread’s region stack.

```ts
struct AstNode<region R> {
  kind: u8;
  span: u32;
  children: In<R, AstNode<R>>[]; // Slice allocated inside region R
}
```

#### Typing Rules for Regions
1. **Allocation:** Inside `region R { ... }`, `R.alloc(value)` allocates `value: T` in `R` and returns `In<R, T>`, provided `T: Pod`. `R.allocSlice(len, init)` returns `In<R, T[]>`.
2. **Non-Escape Rule (Rank-2 Region Safety):** For a block `region R { body } : ResultType`, the region type variable `R` **must not appear free in `ResultType`** or in the type of any outer mutable variable written by `body`.
3. **Mutating Inside a Region:** Dereferencing `p: In<R, T>` is legal only when `R` is in lexical scope. Because `T: Pod` cannot contain owned heap pointers that get reallocated/dropped (leaving dangling interior pointers), fields of `In<R, T>` may be read and mutated freely in place while `R` is active, including cyclic graphs (`nodeA.next = Some(nodeB); nodeB.prev = Some(nodeA)`).
4. **Teardown:** Exiting `region R` resets the thread’s region bump cursor to its entry mark in a single instruction.

---

## 6. Effects and Handlers

### 6.1 Effect Declarations and Rows
Effects declare typed operations that a function may perform:

```ts
effect Fail<E> {
  raise(error: E): never;
}

effect Log {
  info(msg: readonly u8[]): void;
}
```
A function signature lists its required capabilities in its `uses` clause:
```ts
function parsePort(raw: readonly u8[]): u16 uses Fail<ParseError>, Log { ... }
```
* **Pure functions:** A function with no `uses` clause has an empty effect row and cannot call any function with non-empty unhandled effects.
* **Effect polymorphism:** Higher-order functions parameterize over an effect row variable `<effect E>`:
  ```ts
  function forEach<T, effect E>(
    items: readonly T[],
    visit: (item: readonly T) => void uses E,
  ): void uses E {
    for (const item of items) {
      visit(item);
    }
  }
  ```

### 6.2 Effect Handlers and One-Shot Continuations
A `handle { ... } with EffectName { ... }` block intercepts an effect and removes it from the enclosing function’s `uses` row:

```ts
function parsePortOrDefault(raw: readonly u8[], fallback: u16): u16 uses Log {
  return handle {
    parsePort(raw)
  } with Fail<ParseError> {
    raise(err, resume) => {
      // We do NOT call `resume`; the suspended computation inside `handle`
      // is unwound deterministically (running all Drop destructors) and returns `fallback`.
      Log.info("using fallback port");
      return fallback;
    }
  };
}
```
* **Affine One-Shot Rule:** The `resume` parameter in a handler arm has affine type `Continuation<Arg, BlockResult, EnclosingUses>`. The typechecker enforces that `resume` is called **at most once** along any control-flow path and cannot be captured in a closure or stored in a struct that outlives the handler arm.
* **Compilation Strategy:**
  1. **Tail-Resumptive Fast Path:** If every arm of a handler ends with `return resume(expr)` (such as `Log`, `Reader<Env>`, `State<S>`, or custom allocators), the compiler compiles the handler via **evidence passing** (passing a hidden vtable pointer down the call stack). Operations compile to direct indirect function calls with **zero stack switching and zero heap allocation**.
  2. **Abortive Fast Path (`Fail<E>`):** If an arm never touches `resume` and its operation returns `never`, it compiles to zero-cost table-driven unwinding (or two-register return Value/Tag return for immediate callers).
  3. **Suspending Path (`AsyncIo`, generators):** When a handler stores or suspends before calling `resume`, the runtime executes the `handle` block on a **4 KB growable stacklet fiber**, switching stack pointers in user space when the operation yields.

---

## 7. Concurrency and Parallelism

### 7.1 Structured Concurrency (`AsyncIo` + Lexical Scopes)
There are no detached `go` statements or `tokio::spawn` background tasks. Concurrent I/O tasks are spawned inside a lexical `Async.scope((s) => ...)` block:

```ts
effect Async {
  sleepMs(ms: u64): void;
  // Built-in structured concurrency nursery
}
```
* **Lexical Lifetime Guarantee:** `Async.scope` blocks until all fibers spawned on `s` have completed or been cancelled. Because no child fiber can outlive `Async.scope`, child fibers may safely capture **`readonly T` borrows** and **`In<R, T>` region pointers** from the parent frame (provided no concurrent mutation of `R` occurs).
* **Cancellation:** If any child fiber raises an unhandled `Fail<E>`, the scope signals cancellation to all sibling fibers at their next effect operation (`AsyncIo`), unwinds their stacks cleanly, and propagates `Fail<E>`.

### 7.2 Actor Message Passing (`iso` and `val`)
For long-lived stateful services (connection pools, state engines), tasks communicate over typed `Channel<T>` where `T` must be **`Send`**, defined strictly as:
* `Pod` scalars/structs,
* `own T` containing no region pointers,
* `iso T` (mutable isolated subgraph — transferred in $O(1)$ by moving the pointer),
* `Arc<val T>` (immutable frozen subgraph — shared in $O(1)$ by incrementing one segment header refcount).

Each long-lived actor owns its own `IsoHeap`. If an actor allocates cyclic state inside its `IsoHeap` rather than a short-lived `region R`, its `IsoHeap` runs a local mark-compact pass between message-processing turns, completely independent of every other thread.

### 7.3 Data Parallelism (`par` and `@layout(soa)`)
For CPU multi-core and SIMD workloads, Flyscript provides:
1. **`@layout(soa)` Structs:**
   ```ts
   @layout(soa)
   struct Particle {
     posX: f32;
     posY: f32;
     velX: f32;
     velY: f32;
   }
   ```
   A `Vec<Particle>` allocates a single contiguous block partitioned into planar arrays `[posX_0..posX_n | posY_0..posY_n | velX_0..velX_n | velY_0..velY_n]` padded to 64-byte cache lines. Indexing `particles[i].posX` lowers automatically to planar pointer arithmetic.
2. **Structured Parallel Loops (`par for`):**
   ```ts
   function integrate(particles: mut SoaSlice<Particle>, dt: f32): void {
     par for (let p of particles) {
       p.posX += p.velX * dt;
       p.posY += p.velY * dt;
     }
   }
   ```
   **Typing rule for `par for`:** The loop body must have an **empty effect row (`uses` nothing)**, may capture outer variables only as `readonly` or `val`, and receives an exclusive `mut` element reference for its disjoint index `i`. Work is partitioned across the runtime work-stealing thread pool and vectorizes cleanly via LLVM `llvm.loop.parallel_accesses`.

---

## 8. `comptime` Metaprogramming

Any parameter, variable, or function marked `comptime` is evaluated by the compiler's bytecode interpreter during typechecking. `Type` is a built-in `comptime`-only primitive type.

```ts
comptime function FixedRingBuffer(comptime T: Type, comptime Capacity: usize): Type {
  comptime assert(Capacity > 0 && (Capacity & (Capacity - 1)) == 0, "Capacity must be a power of two");
  return struct {
    buf: T[Capacity];
    head: usize;
    tail: usize;
  };
}

type ByteRing = FixedRingBuffer(u8, 1024);
```
* **Phase separation:** `comptime` evaluation is strictly pure and deterministic (no `AsyncIo`, no wall-clock time, no network access, bounded step counter by default). Once `comptime` specialization completes, `Type` values are erased and the resulting monomorphic AST proceeds to bidirectional type/effect/capability checking.

---

## 9. Modules and Foreign Function Interface (FFI)

* **ES Module Syntax:** Every `.fly` file is a module. Declarations are private unless prefixed with `export`. Circular module imports are rejected at compile time (forming a strict DAG for parallel per-module compilation).
* **Zero-Cost C ABI Interop:** Functions marked `extern "C"` and structs marked `@layout(c)` use the platform C ABI with zero marshaling wrappers:
  ```ts
  @layout(c)
  export struct IoVec {
    base: readonly u8*;
    len: usize;
  }
  extern "C" function writev(fd: i32, iov: readonly IoVec*, iovcnt: i32): isize uses Io;
  ```
  Raw pointers (`T*`) may only be dereferenced inside an explicit `unsafe { ... }` block.

---

## 10. Complete Example Program (`http_handler.fly`)

This ~45-line program demonstrates a request handler that parses an HTTP header inside a zero-GC lexical `region`, uses `Fail<HttpError>` and `AsyncIo`, and spawns two concurrent backend fetches inside a structured `Async.scope` sharing region-allocated slices safely:

```ts
import { Socket, Async, AsyncIo, DbClient } from "std/net";

export enum HttpError {
  MalformedRequest,
  Unauthorized,
  BackendTimeout,
}

export effect Fail<E> {
  raise(err: E): never;
}

// Pod struct allocated inside lexical region R; holds slices pointing into R
struct ParsedReq<region R> {
  userId: In<R, u8[]>;
  authToken: In<R, u8[]>;
}

function parseHeader<region R>(
  r: region R,
  raw: readonly u8[],
): In<R, ParsedReq<R>> uses Fail<HttpError> {
  if (raw.len < 16) {
    Fail.raise(HttpError.MalformedRequest);
  }
  // Bump-allocate copies/slices inside region R (freed in O(1) when R exits)
  const userId = r.allocSlice(raw[0..8]);
  const authToken = r.allocSlice(raw[8..16]);
  return r.alloc(ParsedReq { userId, authToken });
}

export function handleConnection(
  conn: mut Socket,
  db: readonly DbClient,
): void uses AsyncIo, Async {
  handle {
    region reqArena {
      let rawBuf: u8[512] = [0u8; 512];
      const n = conn.read(mut rawBuf);
      const req = parseHeader(reqArena, rawBuf[0..n]);

      // Spawn two concurrent fibers in a structured nursery.
      // Both fibers safely borrow `req` (in `reqArena`) as `readonly` because
      // `Async.scope` guarantees both fibers finish before `reqArena` exits.
      const [profile, quota] = Async.scope((s) => {
        const fProfile = s.spawn(() => db.fetchProfile(req.userId));
        const fQuota   = s.spawn(() => db.checkTokenQuota(req.authToken));
        return [fProfile.join(), fQuota.join()];
      });

      if (!quota.allowed) {
        Fail.raise(HttpError.Unauthorized);
      }
      conn.writeStatus(200, profile.displayName);
    } // <-- `reqArena` bump pointer reset in 1 instruction here
  } with Fail<HttpError> {
    raise(err, _resume) => {
      // Unwinds suspended scope/region cleanly and writes HTTP error response
      const code: u16 = match (err) {
        HttpError.MalformedRequest => 400u16,
        HttpError.Unauthorized     => 401u16,
        HttpError.BackendTimeout   => 504u16,
      };
      conn.writeStatus(code, "error");
    }
  };
}
```

---

## 11. Compiler Pipeline Architecture

1. **Stage 1 — Lexer & Recursive Descent Parser:** Parses `.fly` source into an untyped Concrete Syntax Tree (CST) and validates DAG module imports.
2. **Stage 2 — `comptime` Evaluator & Monomorphizer:** Evaluates `comptime` functions and type generators on a register-based bytecode VM, producing a fully concrete High-Level IR (HIR) with all `Type` values resolved.
3. **Stage 3 — Bidirectional Type, Effect & Refinement Checker:**
   * Checks nominal types, trait implementations, and infers local expressions and closure signatures.
   * Verifies `uses` effect rows and substitutes handled effects.
   * Discharges linear integer refinements (`where i < N`) via a built-in Fourier-Motzkin / Simplex integer solver.
4. **Stage 4 — Capability, Borrow & Region Escape Pass (Mid-End SSA IR):**
   * Enforces affine move semantics (`own`), lexical exclusivity (`mut` XOR `readonly`), and `iso` boundary isolation.
   * Verifies rank-2 non-escape for every `region R` variable.
   * Runs **Static Affine Reuse Analysis**, pairing `Drop(Box<T>)` with subsequent `Alloc(Box<T>)` of matching size/alignment.
   * Lowers `@layout(soa)` indexing and **Evidence-Passing Effect Transformation** (compiling tail-resumptive handlers to direct vtable calls).
5. **Stage 5 — Code Generation:**
   * **Debug target:** Cranelift (or C11 backend) for sub-second incremental builds.
   * **Release target:** LLVM IR emitting `noalias` and `readonly` parameter attributes derived directly from `mut`, `readonly`, `iso`, and `val` capabilities.

---

## 12. Genuine Open Questions

1. **Mutually Recursive Regions vs. Dynamic Arena Growth:** When a lexical `region R` exhausts its initial thread-local slab and links an overflow slab, `O(1)` exit becomes `O(k)` over the `k` linked overflow slabs. Should `region R` take an optional capacity hint `region R(64 * 1024)` to guarantee single-slab $O(1)$ teardown in real-time code?
2. **Effect Tunneling in Generic Interfaces:** When a standard interface method like `Iterator.next(self: mut Self): Option<T>` is defined without effects, how should an implementation that performs `AsyncIo` or `Fail<E>` integrate—via an associated effect type `effect Uses` on every core interface (`interface Iterator<T, effect E = []>`), or via effect-polymorphic interface defaults?
3. **Refinement Solver Completeness Boundary:** Presburger arithmetic handles linear inequalities (`i + offset < buf.len`), but 2D matrix/image indexing requires non-linear multiplication (`row * stride + col < buf.len`). What is the exact canonical rewrite rule set for stride multiplication so array indexing stays predictable without embedding an unbounded SMT solver like Z3?