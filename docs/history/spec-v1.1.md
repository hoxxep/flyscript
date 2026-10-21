# Flyscript Language Specification (v1.1)

File extension: `.fly`

**Changelog (v0.1 $\to$ v1.1):** Consolidated from a 15-mechanism systems synthesis (v1.0) into a four-pillar core (v1.1): **(1) Affine ownership with second-class borrows**, **(2) One unified row calculus for records, polymorphic variants, and algebraic effects**, **(3) Effect handlers as the single control, allocation, and iteration abstraction**, and **(4) `comptime` type reflection for data layout**.

---

## 0. Critique of v1.0, Pushbacks, and Concept Reduction

### 0.1 Five Concrete Objections to v1.0

#### Objection 1: Context-Dependent `Sync` on `In<R, T>` Is Unsound Under Separate Compilation
In v1.0 §6.1, `In<R, T>` satisfies `T extends Sync` *"whenever `T extends Sync` and region `R` is frozen as read-only (`ro`)."* That makes trait satisfaction depend on **program position** ($\Delta$), violating basic substitution in generic functions:
```ts
// v1.0 broken program:
function assertSync<T extends Sync>(x: readonly T): void {}

function bad<region R>(r: mut Region<R>, p: In<R, i32>): void {
  // Here `R` is `rw` (mutable!). If `In<R, i32>` is unconditionally `Sync`,
  // then a generic helper holding `readonly In<R, i32>` can read `*p` on another
  // thread while `r` is still mutating the arena. If `In<R, i32>` is NOT `Sync`
  // until `Async.scope` freezes `R`, then `s.spawn` cannot typecheck through a helper!
  assertSync(p);
}
```
* **v1.1 Fix:** Traits are 100% context-independent. `In<R, T>` is replaced by region-indexed values and slices whose concurrent access is governed purely by lexical borrow capabilities (`readonly` vs `mut`) on the region handle itself.

#### Objection 2: Two Competing Error Worlds (`Result<T, E>` + `Fail<E>`) Force Boilerplate on Every Line
In v1.0’s HTTP example, `Socket.read` returns `Result<usize, IoError> uses Io`, which must then be converted via `try ... else HttpError.BackendError` into `Fail<HttpError>`. Composing two functions that fail with `DbError` and `ParseError` requires inventing a nominal wrapper `enum AppError` and writing mapping glue at every call site:
```ts
// v1.0 unergonomic error glue:
const n = try conn.read(mut rawBuf) else HttpError.BackendError;
const userId = try r.copyUtf8(rawBuf[0..8]) else HttpError.MalformedRequest;
```
* **v1.1 Fix:** One error mechanism (`Fail<E>`) backed by **structural variant rows** (`#MalformedRequest | #IoFailed(IoError) | ...R`). Calling a function with `uses Fail<#MalformedRequest>` and a function with `uses Fail<#Unauthorized>` automatically unifies their effect rows to `uses Fail<#MalformedRequest | #Unauthorized>` with zero `try`, zero `From`, and zero `else` mapping.

#### Objection 3: `Pod`-Only Regions Cannot Hold `Vec`, `String`, or Hash Maps
In v1.0, `r.alloc(val)` requires `T extends Pod`, and `String` / `Vec<T>` are hardcoded to the global `malloc` heap. You **cannot** write a JSON parser or HTTP header map that parses into dynamic `Vec` or `Map` containers inside `region (r)`:
```ts
// Impossible in v1.0: `Vec` is not `Pod` and always uses the global heap!
region (scratch) {
  let headers = Vec.new(); // Allocates on global heap, NOT in `scratch`!
  headers.push(parseLine(raw));
}
```
* **v1.1 Fix:** Standard collections (`Vec<T, R = Heap>`, `String<R = Heap>`, `Box<T, R = Heap>`) are parameterized by a region/allocator phantom tag `R` (defaulting to `Heap`) and allocate through an `Alloc<R>` effect handler.

#### Objection 4: `for (const x of xs)` Cannot Express Generators, Laziness, or Effectful Streams
In v1.0, iteration is only defined for slices and ranges (`0..N`), and Open Question 2 in v0.3 showed that an `Iterator` trait fights with effects (`Io`, `Fail`). You cannot write a streaming database cursor or tree traversal without allocating an intermediate `Vec`:
```ts
// Impossible in v1.0 without allocating a temporary Vec or writing manual state machines:
function walkTree(node: readonly Tree): void uses Yield<i32> { ... }
```
* **v1.1 Fix:** Iteration **is** the `Yield<T>` algebraic effect. `for (const x of stream()) { ... }` is syntax sugar for handling `Yield<T>` around `stream()`. Any effect (`Io`, `Fail`) performed by `stream()` flows through naturally.

#### Objection 5: `SoaSlice<T>` Cannot Express Partial Field Projections or Nested AoS/SoA
In v1.0, `@layout(soa)` is a magical compiler attribute on `struct` accompanied by a special built-in type `SoaSlice<T>`. If you pass `&mut particles[i]` to a normal function expecting `mut Particle`, it is **impossible** because the fields `posX`, `posY` are miles apart in memory (there is no contiguous `Particle` address to point to!):
```ts
// Unsound in v1.0:
function resetOne(p: mut Particle): void { p.posX = 0.0; }
// Inside `par for (let p of soaParticles)`: `p` is NOT a contiguous `Particle` in RAM!
// Passing `mut p` to `resetOne` requires a contiguous pointer that does not exist!
```
* **v1.1 Fix:** Delete `@layout(soa)` and `SoaSlice<T>`. `Soa<T>` is a pure `comptime` type function (using `Type.fieldsOf(T)`) that generates a struct of parallel slices (`{ posX: f32[]; posY: f32[]; ... }`) and synthesized proxy accessors, making the physical separation of planes explicit and sound.

---

### 0.2 Two Explicit Pushbacks on the v1.1 Prompt

1. **Pushback on "Pure Effect-Only `Alloc` Without a Region Tag on Containers":**
   If `Alloc` is an unindexed effect (`uses Alloc`) and `Vec<T>` has no region parameter, then inside `region (r) { ... }` (which handles `Alloc` by bump-allocating in `r`), a user can create `let outer = Vec.new<i32>()` *outside* the region, or return a `Vec<i32>` allocated *inside* the region:
   ```ts
   function leak(): Vec<i32> {
     return region (r) {
       Vec.new<i32>() // Allocated in `r`, returned as plain `Vec<i32>` -> USE-AFTER-FREE!
     };
   }
   ```
   **Why we must keep a defaulted region parameter `R = Heap`:** To prevent `leak()` at compile time while keeping 95% of signatures free of region noise, `Alloc<region R = Heap>` and containers `Vec<T, region R = Heap>` carry a region parameter **that defaults to the global `Heap`**. When you write `Vec<i32>` in a normal signature, it means `Vec<i32, Heap>`. Inside `region (r) { ... }`, `r` provides `Alloc<r>`, producing `Vec<i32, r>` (or `In<r, T>`), which the existing rank-2 non-escape rule (`r` cannot appear in the return type of `region (r)`) statically prevents from escaping! Furthermore, because `region (r)` is an O(1) bump arena, **any value allocated in `r` must still be `Pod` (or recursively own only `r`-allocated memory, never `Heap` memory or OS file descriptors)**—otherwise resetting `r`'s bump pointer in O(1) would leak `Heap` allocations or sockets owned by items inside `r`.

2. **Pushback on Combining `Pod`, `Send`, `Sync`, `val`, and `Drop` Too Aggressively:**
   We *can* reduce the five marker traits from v1.0 down to **three** (`Copy`, `Send`, `Drop`), eliminating `Sync` and `val` as separate traits! How?
   * Rename `Pod` to the standard **`Copy`** (trivially copyable bits, no `Drop`).
   * **Eliminate `Sync` and `val` by banning all interior mutability from ordinary types:** In v1.1, `readonly T` means **100% transitively immutable** (what `val` meant!). Synchronized shared state (`Mutex<T>`, `AtomicU64`, `Channel<T>`, or an OS handle pool like `DbPool`) is an **effect or a `Copy` handle to runtime-managed state**, never hidden interior mutability inside a normal struct.
   * Result: If `readonly T` has zero interior mutability anywhere in the language, then **for every `T extends Send`, `readonly T` is automatically thread-safe (`Sync`) and `Arc<T>` is automatically valid!** That deletes both `Sync` and `val` from the language completely.

---

### 0.3 Concept-Count Reduction Table: v1.0 vs. v1.1

| Concept / Mechanism in v1.0 | Status in v1.1 | How v1.1 Unifies It |
| :--- | :--- | :--- |
| 1. Record rows (`<row R>`) + Effect rows (`<effect E>`) + Nominal `enum` errors | **Unified into 1 Row Calculus** | One row kind (`Row`) powers **Records** `{ x: f64; ...R }`, **Polymorphic Variants** `[ #A \| #B(i32) \| ...R ]`, and **Effects** `uses Io, ...E`. |
| 2. Dual error model (`Result<T,E>` + `Fail<E>` + `From<E>` + `try...else` + `@mustUse` `ignore`) | **Unified into `Fail<VariantRow>`** | All fallible functions use `uses Fail<[ #Tag \| ...R ]>`. Errors compose by automatic row union. `Result` is just a library value from `Fail.capture(...)`. |
| 3. Separate `Region<R>` API (`r.alloc`, `r.copySlice`, `r.copyUtf8`) vs Heap allocation | **Unified into `Alloc<region R = Heap>` effect** | `region (r) { ... }` is just the scoped handler for `Alloc<r>`. `Vec<T, r>`, `String<r>`, and `Box<T, r>` work uniformly in `Heap` or `r`. |
| 4. Built-in `for (const x of slice)` + unresolved `Iterator` trait | **Unified into `Yield<T>` effect** | `for (const x of expr) { body }` is syntax sugar for `handle { expr } with Yield<T> { yield(x) resumes k => { body; k(); } }`. |
| 5. `par for` keyword | **Replaced by library `par(slice, fn)`** | Enabled by disjoint mutable slice splitting and `uses []` pure closure types. |
| 6. `@layout(soa)` compiler attribute + `SoaSlice<T>` built-in type | **Replaced by `comptime` `Soa<T>`** | `comptime` reflection (`Type.fieldsOf(T)`) builds `Soa<T>` in library code. Only `@layout(c)` and `@layout(packed)` remain for FFI. |
| 7. Five Marker Traits (`Pod`, `Send`, `Sync`, `val`, `Drop`) | **Reduced to 3 (`Copy`, `Send`, `Drop`)** | Banning unsynchronized & arbitrary interior mutability makes every `Send` type deeply immutable behind `readonly`, deleting `Sync` and `val`. |
| 8. Linear Integer Refinements (`where self < N` + Presburger solver) | **Removed from v1.1 (Future Work)** | `Yield<T>` iterators and slice combinators eliminate bounds checks in hot loops without an integer solver in the compiler core. |

---

## 1. The Four Pillars of Flyscript v1.1

1. **Affine Ownership with Second-Class Borrows:** Every value has a single owner by default; borrows (`readonly T`, `mut T`) are strictly second-class lexical permissions on parameters, locals, and tied returns (`from param`). Because borrows cannot be stored in structs/records and `readonly T` is transitively immutable, every owned `Send` value is an isolated subgraph and every `readonly T` (`T extends Send`) is thread-safe (`Sync`) by construction.
2. **One Unified Row System (Records, Variants, Effects):** A single row-polymorphic unification engine (Rémy-style sorted label rows) types structural records `{ x: f64; ...R }`, structural sum types (polymorphic variants `[ #NotFound | #Io(IoError) | ...R ]`), and algebraic effect rows `uses Io, Fail<E>, ...Eff`.
3. **Algebraic Effect Handlers for Control, Memory, and Iteration:** Exceptions (`Fail<E>`), asynchronous I/O and structured concurrency (`Io`), arena memory allocation (`Alloc<R>`), and stream iteration (`Yield<T>`) are all ordinary one-shot algebraic effects intercepted with `handle { ... } with Effect`.
4. **`comptime` Type Reflection as the Metalanguage:** Generics, conditional compilation, and Struct-of-Arrays (`Soa<T>`) layout transformations are written as ordinary Flyscript functions operating on `Type` values at compile time.

---

## 2. Expression-Oriented Syntax and Complete Grammar (EBNF)

### 2.1 Expression and Semicolon Rule
Flyscript is **expression-oriented**:
* Blocks `{ stmt1; stmt2; finalExpr }`, `if (cond) { a } else { b }`, `match (x) { ... }`, `region (r) { ... }`, and `handle { ... } with E { ... }` are all expressions that evaluate to the value of their final operand expression.
* Inside a block `{ ... }`, expressions terminated by `;` discard their value (which must be `void`; non-`void` values must be bound via `const _ = expr;`) and evaluate the next item. If the final expression in a block has **no trailing semicolon**, its value is the value of the block; if it ends with `;`, the block evaluates to `void`. `return expr;` remains valid for early return.

### 2.2 EBNF Grammar

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
FieldDecl       = Ident ":" Type ";" ;

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
TupleType       = "[" Type { "," Type } "]" ;

TypeRef         = Ident [ "." Ident ] [ TypeArgs ] ;
PrimIntType     = "i8" | "i16" | "i32" | "i64" | "isize" | "u8" | "u16" | "u32" | "u64" | "usize" ;
PrimType        = PrimIntType | "f32" | "f64" | "bool" | "str" | "void" | "never" | "Type" ;

Block           = "{" { Stmt ";" } [ Expr ] "}" ;
Expr            = IfExpr | MatchExpr | RegionExpr | HandleExpr | ForExpr | LambdaExpr | ... ;
IfExpr          = "if" "(" Expr ")" Block [ "else" ( IfExpr | Block ) ] ;
MatchExpr       = "match" "(" Expr ")" "{" { MatchArm } "}" ;
MatchArm        = Pattern [ "if" Expr ] "=>" ( Expr "," | Block ) ;
RegionExpr      = "region" "(" Ident ")" Block ;
ForExpr         = "for" "(" ( "const" | "let" ) Ident "of" Expr ")" Block ;

HandleExpr      = "handle" Block "with" EffectRef "{" { HandlerArm } [ ReturnArm ] [ FinallyArm ] "}" ;
HandlerArm      = Ident "(" [ HandlerParamList ] ")" [ "resumes" Ident ] "=>" Block ;
HandlerParamList= Ident [ ":" Type ] { "," Ident [ ":" Type ] } ;
ReturnArm       = "return" "(" Ident [ ":" Type ] ")" "=>" Block ;
FinallyArm      = "finally" "=>" Block ;
```

---

## 3. Unified Row System: Records, Polymorphic Variants, and Effects

Flyscript uses **one row calculus** across products (records), sums (variants), and effects (`uses`). A row is a finite mapping from labels to payloads $\langle \ell_1 : \tau_1, \dots, \ell_k : \tau_k \mid \rho \rangle$, extensible by a row variable `<row R>`.

### 3.1 Structural Record Rows (`{ field: Type; ...R }`)
Record literals `{ x: 1.0, y: 2.0 }` and `type` aliases of records are structural, laid out canonically by alignment descending then field name ascending:
```ts
function normSq<row R>(p: readonly { x: f64; y: f64; ...R }): f64 {
  return p.x * p.x + p.y * p.y;
}
```

### 3.2 Structural Variant Rows (`[ #Tag(Payload) | ...R ]`)
Tags prefixed with `#` (`#NotFound`, `#Unauthorized`, `#HttpStatus(u16)`) construct **polymorphic variants** (structural sum types). Unlike nominal `enum` declarations, variant tags require no pre-declaration and automatically unify into open or closed sum rows:

```ts
function parseHeader(raw: readonly u8[]): u32 uses Fail<[ #MalformedHeader | #EmptyInput ]> {
  if (raw.len == 0) { Fail.raise(#EmptyInput); }
  if (raw.len < 4)  { Fail.raise(#MalformedHeader); }
  return 42;
}

function checkAuth(id: u32): void uses Fail<[ #Unauthorized ]> {
  if (id == 0) { Fail.raise(#Unauthorized); }
}

// Calling both functions automatically unifies their `Fail` variant rows!
// Zero `From` impls, zero `mapErr`, zero `try ... else` glue:
function authenticate(raw: readonly u8[]): u32
  uses Fail<[ #MalformedHeader | #EmptyInput | #Unauthorized ]>
{
  const id = parseHeader(raw);
  checkAuth(id);
  return id;
}
```
Nominal `struct` and `enum` declarations remain for types that need module-private invariants, recursive definitions, custom `@layout(c | packed)`, or `Drop` destructors.

### 3.3 Effect Rows (`uses Effect1, ...E`)
Function `uses` clauses are rows of effect labels. Higher-order functions parameterize over open effect rows with `<row E = []>`:
```ts
function mapSlice<T, U, row E = []>(
  items: readonly T[],
  f: (item: readonly T) => U uses ...E,
): Vec<U> uses ...E { ... }
```

---

## 4. Ownership, Second-Class Borrows, and Marker Traits

### 4.1 Three Marker Traits (`Copy`, `Send`, `Drop`)
By prohibiting unsynchronized interior mutability (`Cell`/`RefCell`) and restricting OS/concurrency synchronization primitives (`Mutex<T>`, `Channel<T>`, `AtomicU64`) to opaque runtime handles that are `Copy` or `Send`, Flyscript requires only **three** marker traits, derived structurally for records, tuples, variants, and nominal types:
1. **`T extends Copy`:** Trivially copyable bits (scalars, `In<R, U>` when `U extends Copy`, fixed arrays `U[N]`, and composites whose fields are all `Copy` and do not implement `Drop`). Assigning a `Copy` value copies bits without invalidating the source binding.
2. **`T extends Send`:** Safe to transfer across tasks or share as `readonly T` across worker threads. Satisfied by any type whose fields are all `Send` and that contains **no region references `In<R, _>`** and **no raw pointers `U*`**. Because `readonly T` permits zero mutation anywhere in the type system, **`T extends Send` guarantees both safe ownership transfer (`Send`) and safe concurrent `readonly T` sharing (`Sync`)**, as well as safe wrapping in `Arc.new<T extends Send>(val: T): Arc<T>`.
3. **`T extends Drop`:** Implemented only by nominal `struct` and `enum` types for deterministic resource cleanup.

### 4.2 Second-Class Borrows and Tied Returns (`from paramName`)
* `readonly T` and `mut T` (and views `str`, `T[]`, `Grid2D<T>`) are **second-class**: they appear only on parameters, local bindings, and tied return types, **never** inside record, tuple, variant, `struct`, or `enum` fields.
* Returning a borrow ties automatically to the sole borrowed input parameter, or explicitly via `from paramName` when multiple borrowed inputs exist.

### 4.3 Closures (`once`, `mut`, and Shared)
* **Shared `(A) => B`:** Captures outer variables only by `readonly` borrow or `Copy`.
* **Mutating `mut (A) => B`:** Captures at least one outer variable by `mut` borrow.
* **Consuming `once (A) => B`:** Moves at least one non-`Copy` owned value out of its environment.
* Any closure capturing a `readonly` or `mut` borrow or a region reference `In<R, _>` is **second-class** (may be passed downward to callees, never returned or stored in a data structure).

---

## 5. Handlers for Everything: Errors, Allocation/Regions, Iteration, and `Io`

### 5.1 One Error Mechanism (`Fail<E>`)
```ts
export effect Fail<E> {
  raise(err: E): never;
}
```
All recoverable errors use `uses Fail<E>` (where `E` is typically a structural variant row `[ #Tag1 | #Tag2(Info) ]`). `Result<T, E>` is simply a standard-library data type produced at boundaries via `Fail.capture(() => expr)` (which intercepts `Fail<E>` and returns `Result<T, E>`) and reflected back via `Fail.unwrap(result)`.

### 5.2 Allocation as an Effect (`Alloc<region R = Heap>`) and Regions as Handlers
Memory allocation is an algebraic effect indexed by a region phantom tag `R` that **defaults to the global `Heap`**:

```ts
// Global `Heap` is the default region tag installed at `main`:
export effect Alloc<region R = Heap> {
  allocBytes(size: usize, align: usize): In<R, u8[]>;
}
```
* **Standard Collections Work Inside Regions:** `Box<T, region R = Heap>`, `Vec<T, region R = Heap>`, and `String<region R = Heap>` allocate their backing buffers through `Alloc<R>`.
  * In normal signatures, writing `Vec<i32>` or `String` uses the default `R = Heap` and `uses Alloc<Heap>` (which is satisfied by the ambient root handler without needing to be written in `uses`).
  * Inside `region (r) { ... }`, the `region (r)` construct is a **rank-2 lexical handler for `Alloc<r>`** backed by the current fiber's segmented bump arena (`FiberArena`):
    ```ts
    region (r) {
      // `Vec.newIn(r)` or `r.alloc(val)` allocates inside region `r` (`Vec<u8, r>`, `In<r, T>`).
      let buf: Vec<u8, r> = Vec.newIn(r);
      buf.push(1);
    } // <-- Entire region `r` bumped back in O(1)!
    ```
* **How Escape and Resource Leaks Are Prevented (The Two Region Laws):**
  1. **Rank-2 Non-Escape Law:** In `region (r) { body } : RetType`, the rigid region tag `r` **must not appear free in `RetType`** or in any outer variable mutated by `body`. Thus a `Vec<u8, r>`, `String<r>`, or `In<r, T>` can never escape `region (r)`! Copying a result out to the heap before exit is explicit (`strInR.toString()` allocates a `String<Heap>`).
  2. **No-Heap-Drop Law Inside `r`:** Because `region (r)` frees all its allocations in $O(1)$ by resetting a bump pointer without running element destructors, the element type `T` of `In<r, T>` or `Vec<T, r>` **must not own `Heap`-allocated resources or OS handles (`T` may contain `Copy` types and other `r`-allocated containers `Vec<U, r>`, `String<r>`, `In<r, U>`, never `String<Heap>` or `Socket`)**.

### 5.3 Iteration as the `Yield<T>` Effect
There is no special `Iterator` trait hierarchy. Streams and iterators are functions that perform `Yield<T>`:

```ts
export effect Yield<T> {
  yield(item: T): void;
}

// A generator over a binary tree is just a normal recursive function:
function valuesInOrder(node: readonly Option<Box<TreeNode>>): void uses Yield<i32> {
  match (node) {
    Option.Some(n) => {
      valuesInOrder(n.left);
      Yield.yield(n.value);
      valuesInOrder(n.right);
    },
    Option.None => {},
  }
}
```
The loop `for (const x of streamExpr) { body }` is direct syntax sugar for a tail-resumptive handler of `Yield<T>`:
```ts
handle {
  streamExpr
} with Yield<T> {
  yield(x) resumes k => {
    body;
    return k(); // Tail-resumptive: compiles via evidence passing to a direct loop/call!
  }
}
```
Because `Yield.yield` is tail-resumptive, `for (const x of slice.iter())` compiles to a direct pointer loop with zero stack switching and zero bounds checks, while `for (const row of db.streamRows())` naturally propagates `uses Io, Fail<...>`.

### 5.4 `Io`, Structured Concurrency (`Async.scope`), and Native/Wasm Targets
```ts
export effect Io {
  submitRead(fd: RawFd, buf: mut u8[]): usize uses Fail<[ #IoReset | #IoTimedOut | #IoBrokenPipe ]>;
  submitWrite(fd: RawFd, buf: readonly u8[]): usize uses Fail<[ #IoReset | #IoTimedOut | #IoBrokenPipe ]>;
  nowMonoNs(): u64;
  sleepNs(durationNs: u64): void;
  runScope<T, row E = []>(body: once (s: mut Scope<E>) => T uses Io, ...E): T uses Io, ...E;
}
```
* **In-Flight Borrow & Cancellation Drain:** When `submitRead`/`submitWrite` suspends a fiber, the borrow of `buf` remains locked until completion. On fiber cancellation, the `Io` handler cancels the kernel operation and **awaits kernel completion (`CQE`) before unwinding the fiber stack or resetting any region owning `buf`**.
* **Borrow & Region Sharing in `Async.scope`:** `s.spawn(closure)` requires a shared closure where every captured `readonly T` binding satisfies `T extends Send` (or is a `readonly In<R, T>` where `T extends Send` and the enclosing `region (R)` is locked against mutation for the duration of `runScope`).
* **First-Class WebAssembly Target (`wasm32-wasi` / Browser Host):**
  * On **Native (`x86_64`, `aarch64`)**: `Io` is handled by the runtime's multi-threaded `io_uring` / `kqueue` stackful fiber scheduler; `extern "C"` switches to the OS worker thread's native stack.
  * On **WebAssembly (`wasm32`)**: One-shot continuations and `Io` suspension compile directly to the **Wasm Stack Switching (`wasmfx` / JSPI — JavaScript Promise Integration)** proposal (or segmented shadow stacks on legacy Wasm engines), mapping `Io` operations directly to browser `fetch`/`ReadableStream` Promises or WASI Preview 2 async handles without changing a single line of `.fly` code.

---

## 6. Library Parallelism (`par`) and `comptime` Layout (`Soa<T>`)

### 6.1 Parallelism as a Library Function (`par`)
There is no `par for` keyword. Multi-core data parallelism is a standard-library function in `std/par`:

```ts
export function par<T extends Send>(
  items: mut T[],
  body: (item: mut T, index: usize) => void, // Empty `uses` clause = observationally pure!
): void;
```
**Why the type system makes `par` 100% safe as a library function:**
1. `items: mut T[]` guarantees the caller holds exclusive mutable access to the slice, and `T extends Send` guarantees elements can be mutated on worker threads.
2. `body` is a **shared closure** `(item: mut T, index: usize) => void` with an **empty `uses` row**:
   * Because `body` is a shared closure (not `mut (...) => void` or `once (...) => void`), it can only capture outer variables by `readonly U` borrow (which is deeply immutable!) or `Copy`.
   * Because `body` has an empty `uses` row, it cannot perform `Io` or shared side effects (though it may use thread-local `region (r)` scratch memory).
   * `par` partitions `items` into disjoint sub-slices across the work-stealing thread pool and invokes `body` on disjoint elements in parallel.

### 6.2 `Soa<T>` as a `comptime` Type Function
Instead of a magical `@layout(soa)` attribute, `Soa<T>` is written in 20 lines of `comptime` library code using `Type.fieldsOf(T)` and `Type.structFromFields(...)`:

```ts
// In "std/layout":
export comptime function Soa(comptime T: Type, region R = Heap): Type {
  // Reflects over fields `{ f_i: FieldType_i }` of `T` and synthesizes a struct
  // containing a single aligned allocation partitioned into planar slices `FieldType_i[]`
  // plus a `.slices()` view yielding `{ f_i: mut FieldType_i[] }` for SIMD loops.
  ...
}
```
```ts
struct Particle { posX: f32; posY: f32; velX: f32; velY: f32; }

function stepPhysics(particles: mut Soa<Particle>, dt: f32): void {
  const planes = particles.planesMut();
  par(planes.indices(), (i) => {
    planes.posX[i] += planes.velX[i] * dt;
    planes.posY[i] += planes.velY[i] * dt;
  });
}
```

---

## 7. Core Calculus ($\lambda_{\text{fly}}$ v1.1)

Every surface Flyscript module elaborates into $\lambda_{\text{fly}}$ with a single row kind (`Row`) and three contexts:

$$\Delta \;|\; \Theta \;|\; \Gamma \;\vdash\; e : \tau \;\!/\;\! \varepsilon \;\dashv\; \Theta_{\text{out}}$$

* **$\Delta$ (Type, Region, and Unified Row Context):**
  $$\Delta ::= \cdot \;\mid\; \Delta, \alpha : \{\text{Copy}, \text{Send}, \text{Drop}\} \;\mid\; \Delta, \rho : \text{region} \;\mid\; \Delta, r : \text{Row}_{\mathcal{L}}$$
  where $r : \text{Row}_{\mathcal{L}}$ is a row variable lacking labels $\mathcal{L}$, used identically for record types $\Pi\langle r \rangle$, variant types $\Sigma\langle r \rangle$, and effect rows $\varepsilon$.
* **$\Theta$ (Affine Ownership Context):** Maps owned variables $x : \text{own}(\tau)$ to $x : \text{dead}$ on move when $\tau \not\in \text{Copy}$.
* **$\Gamma$ (Second-Class Borrow Ledger):** Maps active lexical borrows $b : \text{borrow}(\pi, \text{mut} \mid \text{ro}, \tau)$ to the root path $\pi$ they lock (including `region (r)`, which enters $\Gamma$ as an owned region root $\rho$ borrowed via `mut` for allocation or `ro` across `Async.scope` child fibers).
  * **Abortive vs. Resumptive Handler Rule:** An abortive handler arm (`op(x) => e_arm`, no `resumes`) unwinds the inner block first, popping all inner borrows $\Gamma_{\text{body}}$ and restoring $\Gamma_0$ before evaluating $e_{\text{arm}}$. A resumptive arm (`op(x) resumes k => e_arm`) keeps $\Gamma_{\text{body}}$ locked until the one-shot continuation $k$ is either invoked or dropped (which unwinds the suspended frame at $k$'s drop point).

---

## 8. Complete Validated Examples in v1.1

### 8.1 Standard Library Signatures (`std/net`, `std/async`)

```ts
// From "std/net":
export type IoErr = [ #IoReset | #IoTimedOut | #IoBrokenPipe ];
export struct Profile { displayName: String; }
export struct QuotaStatus { allowed: bool; }

export struct Socket {
  function read< row E = [] >(
    self: mut Self,
    buf: mut u8[],
  ): usize uses Io, Fail<[ ...IoErr | ...E ]>;

  function writeStatus< row E = [] >(
    self: mut Self,
    code: u16,
    body: str,
  ): void uses Io, Fail<[ ...IoErr | ...E ]>;
}

export struct DbClient {
  function fetchProfile< row E = [] >(
    self: readonly Self,
    userId: str,
  ): Profile uses Io, Fail<[ ...IoErr | ...E ]>;

  function checkTokenQuota< row E = [] >(
    self: readonly Self,
    token: str,
  ): QuotaStatus uses Io, Fail<[ ...IoErr | ...E ]>;
}
```

### 8.2 HTTP Handler (`http_handler.fly`)

Look how clean this is compared to v1.0: **zero `try ... else` error-mapping noise**, **automatic variant-row union** across `parseHeader`, `Socket`, and `DbClient`, and `String<r>` / `In<r, str>` working seamlessly inside `region (reqArena)`:

```ts
import { Socket, DbClient, IoErr } from "std/net";
import { Async } from "std/async";

type AppErr = [ #MalformedRequest | #Unauthorized | ...IoErr ];

struct ParsedReq<region R> {
  userId: In<R, str>;
  authToken: In<R, str>;
}

function parseHeader<region R, row E = []>(
  r: mut Region<R>,
  raw: readonly u8[],
): In<R, ParsedReq<R>> uses Fail<[ #MalformedRequest | ...E ]> {
  if (raw.len < 16) {
    Fail.raise(#MalformedRequest);
  }
  // `r.copyUtf8` raises `#MalformedUtf8`; we map or let row union compose:
  const userId = r.copyUtf8(raw[0..8]);
  const authToken = r.copyUtf8(raw[8..16]);
  return r.alloc({ userId, authToken });
}

export function handleConnection(
  conn: mut Socket,
  db: readonly DbClient,
): void uses Io {
  handle {
    region (reqArena) {
      let rawBuf: u8[512] = repeat<512>(0);
      const n = conn.read(mut rawBuf);
      const req = parseHeader(mut reqArena, rawBuf[0..n]);

      // `Async.scope` infers return type `{ profile: Profile; quota: QuotaStatus }`
      // and unified effect row `Fail<AppErr>` directly from the two spawned closures:
      const pair = Async.scope((s) => {
        const fProfile = s.spawn(() => db.fetchProfile(req.userId.asStr()));
        const fQuota   = s.spawn(() => db.checkTokenQuota(req.authToken.asStr()));
        return { profile: fProfile.join(), quota: fQuota.join() };
      });

      if (!pair.quota.allowed) {
        Fail.raise(#Unauthorized);
      }
      conn.writeStatus(200, pair.profile.displayName.asStr());
    } // <-- `reqArena` bumped back in O(1); `pair.profile` (`String<Heap>`) dropped
  } with Fail {
    // Abortive arm handles the unified polymorphic variant row:
    raise(err) => {
      const code: u16 = match (err) {
        #MalformedRequest | #MalformedUtf8 => 400,
        #Unauthorized                      => 401,
        #IoReset | #IoTimedOut | #IoBrokenPipe => 502,
      };
      // Ignore any secondary write error when sending the error response:
      const _ = Fail.capture(() => conn.writeStatus(code, "error"));
    }
  };
}
```

### 8.3 Deterministic Simulation Test (`http_sim_test.fly`)

```ts
import { SimIo } from "std/testing";
import { handleConnection } from "./http_handler";

export function testConnectionUnderPacketLoss(): void {
  // Intercepts the `Io` effect with a seeded single-threaded virtual scheduler:
  SimIo.run({ seed: 0x1234_5678, timeoutRate: 0.25 }, () => {
    let harness = SimIo.createMockPair();
    handleConnection(mut harness.socket, harness.db);
    assert(harness.statusWritten == 200 || harness.statusWritten == 502);
  });
}
```

---

## 9. Why Flyscript: Honest Comparison with Existing Languages

| Language | What Flyscript Does That It Cannot | What Flyscript Gives Up Compared to It |
| :--- | :--- | :--- |
| **Rust** | Zero `'a` lifetime annotations on types; cyclic graphs in `region (r)` without `Rc<RefCell>`; no `async`/`await` coloring or `Pin<&mut Self>`; structural records and polymorphic variant errors; deterministic `Io` simulation via effect handlers. | Cannot store borrows inside long-lived structs (must use owned values, regions, or `Handle<T>` indices), and no zero-cost state-machine packing across suspension points (uses 4 KB stackful fibers). |
| **TypeScript** | Compiles AOT to unboxed machine code & Wasm with zero GC pauses, deterministic `Drop`, real integers (`u64`, `i32`), `Soa<T>` SIMD layout, and data-race-free multi-core parallelism (`par`). | No width subtyping without `<row R>`, no dynamic `any`/reflection at runtime, and must annotate top-level function types and `mut` borrows. |
| **Koka** | Zero reference-counting headers or atomic RC traffic on heap values (static affine ownership + regions instead of Perceus RC); explicit unboxed memory layout (`Soa<T>`, `@layout(c)`); static data-race freedom (`Send`). | Cannot resume effect continuations multiple times (one-shot only) and cannot freely alias mutable closures without borrow rules. |
| **Roc** | Supports in-place mutation (`mut T`), cyclic region graphs (`region (r)`), low-level systems/FFI control, and user-definable effect handlers (Roc hardcodes effects into a single host "platform"). | Does not have Roc's global Hindley-Milner full-program type inference (Flyscript requires top-level function signatures). |
| **Hylo (Val)** | Has first-class lexical regions (`region (r)`) for cyclic graphs, algebraic effect handlers (`Io`, `Fail`, `Yield`), and structural row polymorphism. | Hylo's pure mutable value semantics (`inout` projections) allow slightly more implicit subscript projections without region handles. |
| **Zig** | Full memory safety and temporal/spatial borrow checking in safe code, algebraic data types with exhaustive `match`, closures, traits (`interface`), and algebraic effects. | Significantly larger typechecker than Zig; C interop requires `extern "C"` declarations rather than Zig's direct `@cImport` C header parser. |
| **Mojo** | Algebraic effects (no `async` coloring, swappable `Io` simulation), row-polymorphic records/variants, TypeScript syntax, and lexical regions without lifetime parameter lists. | Does not target native GPU/TPU MLIR autotuning kernels in v1.1 (deferred to future work). |

---

## 10. Removed in v1.1 and Open Question

### 10.1 Removed in v1.1 (Compared to v1.0)
1. **Linear Integer Refinements (`where self < N`) and the Presburger/Fourier-Motzkin Solver:** Moved to post-v1.0 future work; `Yield<T>` iterators and `par` slice combinators remove bounds checks in standard loops without a solver in the compiler core.
2. **`@layout(soa)` and `SoaSlice<T>`:** Replaced by the `comptime` `Soa<T>` library type constructor.
3. **`par for` Keyword:** Replaced by the standard-library `par(slice, fn)` function.
4. **`Sync` and `val` Marker Traits:** Merged into `Send` by eliminating unsynchronized interior mutability and making `readonly T` strictly deeply immutable.
5. **`try ... else` and `From<E>` Error Boilerplate:** Replaced by structural variant rows (`Fail<[ #Tag | ...R ]>`) that compose automatically by row union.

### 10.2 Open Question
1. **Target-Neutral SIMD Lane Permutation & Bitmask API (`Simd<T, comptime Lanes: usize>`):** While `Soa<T>` and `par` enable auto-vectorization for vertical arithmetic loops, algorithms such as vectorized UTF-8 validation, JSON scanning, and sorting networks require horizontal lane shuffles, saturating arithmetic, and lane-to-bitmask extraction (`movemask`), where ARM64 NEON/SVE and x86-64 AVX2/AVX-512 differ structurally. What is the minimal portable `Simd<T, Lanes>` intrinsic surface that lowers without emulation cliffs on both ARM64 and x86-64?