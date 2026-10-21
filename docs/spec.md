# Flyscript

**Language specification, version 1.6**

*Affine values, one row calculus, handlers for everything, and `comptime`: Church on the outside, Turing on the inside.*

---

## 0. Overview

Flyscript is an ahead-of-time compiled systems language with TypeScript's surface. It compiles to native code and to WebAssembly, has no garbage collector, and is memory- and data-race-safe without lifetime annotations.

The whole language rests on five laws. Every rule in this document is a consequence of one of them.

1. **One owner.** Every value has exactly one owner. A borrow (`readonly T`, `mut T`) is a *second-class* value: it may be passed down and returned to the caller it came from, but never stored where it could outlive its owner. Second-classness propagates: any type containing a borrow is itself second-class.
2. **Effects are visible.** Everything a function does besides computing its result — failing, performing I/O, synchronizing with other tasks, producing a stream, writing to a region — is an *effect*, listed in its type. A function with no effects is pure, and a `readonly` borrow seen from pure code is immutable.
3. **One row calculus.** Records (`{ x: f64; ...R }`), tag unions (`#Ok(T) | #Err(E) | ...R`) and effect lists (`uses Io, ...E`) are all *rows*, checked by one unifier.
4. **Handlers for everything.** Errors, I/O, iteration and region memory are ordinary effects with ordinary handlers. A handler may hold the rest of a computation as a one-shot continuation value; generators and tasks are both built from that one primitive.
5. **`comptime` is the metalanguage.** Generics, reflection, layout transformation and derived interfaces are ordinary Flyscript code run by the compiler.

### 0.1 Changes from 1.5

1.6 is a pass for simplicity and for TypeScript fidelity. Nothing below adds a concept; each item removes one or replaces it with something a TypeScript programmer already knows.

| Change | Replaces |
| :--- | :--- |
| Tag unions are written without brackets: `#A \| #B(T)` | `[ #A \| #B(T) ]`, which collided with tuple syntax |
| `Option` and `Result` are type aliases of tag unions | nominal `enum Option` / `enum Result` |
| `throw`, `try`/`catch` are syntax for the `Fail` effect | `Fail.raise`, and `handle … with Fail` for the common case |
| `yield e` is syntax for the `Yield` effect | `Yield.yield(e)` |
| A child failure cancels its scope and is rethrown from `Io.scope` (nursery semantics); a task that cannot fail is one whose type says so | ad-hoc cancellation rules and supervision questions |
| Expression statements may discard any value | `const _ = e;` |
| Region operations are methods: `list.push(x)`, `cell.set(v)` | `RegionList.push(list, x)`, `Region.cellSet(c, v)` |
| Field and parameter types flow into literals: `Cell.new(0)` | `Cell.new(0 as u32)` |

---

## 1. Goals and non-goals

**Goals**

1. TypeScript's surface: a TypeScript programmer can read Flyscript on day one.
2. Predictable performance: unboxed values, static dispatch by default, no hidden allocation, no collector, deterministic destruction.
3. Safety without annotation burden: no lifetime parameters, no `async` colouring, no checked-exception boilerplate.
4. Testability by construction: because I/O is an effect, any program can run under a deterministic simulator.
5. A small core: features are library code over the core wherever possible.

**Non-goals**

1. Width subtyping of records (row polymorphism replaces it).
2. Garbage collection of any kind.
3. Multi-shot continuations (backtracking via re-resumption).
4. Equi-recursive structural types (recursion goes through a nominal declaration).
5. Refinement types and automatic GPU lowering, in version 1.

---

## 2. Syntax

### 2.1 Flyscript for TypeScript programmers

| TypeScript | Flyscript | Note |
| :--- | :--- | :--- |
| `const x = e` / `let x = e` | same | `const` forbids mutation as well as reassignment. With one owner there is no aliasing, so "shallow" and "deep" immutability coincide. |
| `number`, `bigint` | `i8 … i64`, `u8 … u64`, `isize`, `usize`, `f32`, `f64` | Literals take their type from context; `as` converts. |
| `{ x: 1, y: 2 }` | same | A structural record. Functions accept extra fields through a row variable, not by subtyping. |
| `{ kind: "a", … } \| { kind: "b", … }` | `#A(…) \| #B { … }` | Tag unions are first-class; no discriminant field. |
| `[A, B]` | same | Tuples. |
| `interface` + `class … implements` | `interface` + `struct` + `impl` | Data and behaviour are declared separately. Interfaces are nominal. |
| `T \| null \| undefined` | `Option<T>` = `#Some(T) \| #None` | There is no null. |
| `throw` / `try` / `catch` | same | Typed: a function's failures are part of its type. |
| `function*` / `yield` / `for…of` | `yield` / `for…of` | A generator is any function that uses `Yield<T>`. |
| `async` / `await` | (nothing) | I/O is an effect; every function is "direct style". |
| `import` / `export` | same | ES modules; the import graph must be acyclic. |
| `<T extends U>` | same | Monomorphized. Bounds compose with `&`. |

### 2.2 Lexical rules

- **Statements and blocks.** Flyscript is expression-oriented. A block `{ s1; s2; e }` evaluates to its final expression `e` when that expression has no trailing semicolon, and to `void` otherwise. `if`, `match`, `try`, `region` and `handle` are expressions. An expression statement `e;` discards its value. `return e;` returns early.
- **Literals.** Numeric literals have no suffix; their type is solved together with the whole enclosing call or initializer from the expected type, defaulting to `i32` and `f64` only if still unconstrained. Byte literals are `b'n'`; strings are `"…"` and templates `` `…${e}…` ``.
- **Record literals.** `{ f: e, … }` builds the nominal struct named by the expected type, if there is one, and a structural record otherwise. `Point { … }` names the struct explicitly. `{ x, y }` puns field names.
- **Generic calls.** In expression position, `f<…>(` and `x.f<…>(` are parsed as type application when the `<…>` is a balanced type-argument list followed immediately by `(`; otherwise `<` is less-than. This is TypeScript's rule.
- **Mutable borrows are visible at the call site.** `read(mut buf)` lends `buf` mutably; `parse(buf)` lends it read-only. The one exception is a method's receiver, which is lent in whatever mode the method declares: `conn.read(mut buf)` borrows `conn` mutably.
- **Parameters bind like `let`.** An owned parameter may be mutated and lent `mut` by its function.

### 2.3 Grammar

```ebnf
Module      = { Import | ["export"] Decl } ;
Import      = "import" "{" Ident { "," Ident } "}" "from" String ";" ;

Decl        = Struct | Enum | Interface | Impl | TypeAlias | Effect | Function | Extern ;
Struct      = [ Layout ] "struct" Ident [ TypeParams ] "{" { Ident ":" Type ";" } "}" ;
Enum        = "enum" Ident [ TypeParams ] "{" Tag { "," Tag } [ "," ] "}" ;
Layout      = "@layout" "(" ( "c" | "packed" ) ")" ;
Interface   = "interface" Ident [ TypeParams ] "{" { ( Sig | "type" Ident [ "extends" Bounds ] ) ";" } "}" ;
Impl        = "impl" [ TypeParams ] Type [ "for" Type ] "{" { ["export"] Function } "}" ;
TypeAlias   = "type" Ident [ TypeParams ] "=" Type ";" ;
Effect      = "effect" Ident [ TypeParams ] "{" { Op ";" } "}" ;
Op          = Name [ TypeParams ] "(" [ Params ] ")" ":" Return [ Uses ] ;
Name        = Ident | Keyword ;                     (* member names may be reserved words *)
Function    = Sig Block ;
Extern      = "extern" "\"C\"" Sig ";" ;
Sig         = [ "comptime" ] "function" Ident [ TypeParams ] "(" [ Params ] ")" ":" Return [ Uses ] ;
Params      = Param { "," Param } [ "," ] ;
Param       = [ "comptime" ] Ident ":" [ "mut" | "readonly" ] Type ;
Return      = [ "mut" | "readonly" ] Type [ "from" Ident ] ;
Uses        = "uses" Row ;

TypeParams  = "<" TypeParam { "," TypeParam } ">" ;
TypeParam   = "region" Ident | "row" Ident [ "=" Type ] | "comptime" Ident ":" Type
            | Ident [ "extends" Bounds ] [ "=" Type ] ;
Bounds      = Type { "&" Type } ;

Type        = Prim | Path [ TypeArgs ] | Path "(" Expr { "," Expr } ")" | Record | Union | Tuple | Fn
            | Type "[" [ Expr ] "]" | "mut" Type | "readonly" Type | Type "*" | "dyn" Path | "[" "]" ;
Record      = "{" { Ident ":" Type ";" } [ "..." Ident ] "}" ;
Union       = Tag { "|" Tag } [ "|" "..." Ident ] ;
Tag         = "#" Ident [ "(" Type { "," Type } ")" | Record ] ;
Tuple       = "[" Type { "," Type } "]" ;
Fn          = [ "mut" | "once" ] "(" [ Params ] ")" "=>" Return [ Uses ] ;
Row         = RowItem { "," RowItem } ;               (* effect rows *)
RowItem     = Path [ TypeArgs ] | "..." Ident ;
Prim        = "i8" | "i16" | "i32" | "i64" | "isize" | "u8" | "u16" | "u32" | "u64" | "usize"
            | "f32" | "f64" | "bool" | "str" | "void" | "never" | "Type" ;

Block       = "{" { Stmt } [ Expr ] "}" ;
Stmt        = ( "const" | "let" ) Pattern [ ":" Type ] "=" Expr ";" | "defer" Expr ";"
            | "return" [ Expr ] ";" | "break" ";" | "continue" ";" | Expr ";" | BlockLike ;
BlockLike   = If | While | For | Match | Try | Region | Handle | Unsafe | Block ;
Expr        = … | BlockLike | Throw | Yield | Lambda | RecordLit | "struct" "{" { Ident ":" Type ";" } "}" ;
RecordLit   = [ Path ] "{" [ Name [ ":" Expr ] { "," Name [ ":" Expr ] } ] "}" ;
Match       = "match" "(" Expr ")" "{" { Pattern [ "if" Expr ] "=>" ( Expr "," | Block ) } "}" ;
For         = "for" "(" ( "const" | "let" ) Pattern "of" Expr ")" Block ;
Try         = "try" Block "catch" "(" Pattern ")" Block ;
Throw       = "throw" Expr ;
Yield       = "yield" Expr ;
Region      = "region" "(" Ident ")" Block ;
Handle      = "handle" Block "with" Path [ TypeArgs ] "{" { Arm } "}" ;
Arm         = Name "(" [ Ident { "," Ident } ] ")" [ "resumes" Ident ] "=>" Block ;
Lambda      = "(" [ Params ] ")" "=>" ( Expr | Block ) ;
```

Three rules settle the grammar's ambiguities, all borrowed from TypeScript:

- **Braces.** A `{` in expression position begins a record literal. A block appears only as the body of a block-like construct, after `=>` in a lambda or match arm, or at the start of a statement.
- **Block-like statements.** A block-like expression at the start of a statement needs no `;` and is not continued by operators: `if (c) { … } [a, b]` is two statements. As the last item of a block it is the block's value.
- **Contextual words.** `from`, `of`, `with`, `resumes` and `row` are keywords only where the grammar expects them, and any reserved word may be used as a member name (`Yield.yield`, `{ default: 1 }`).

---

## 3. Types

### 3.1 Primitives, strings, arrays

- Scalars: `i8`–`i64`, `isize`, `u8`–`u64`, `usize`, `f32`, `f64`, `bool`, `void`, `never`. All are `Copy`.
- `str` is a borrowed UTF-8 slice; string literals are `str` with static storage. `String` is an owned, growable UTF-8 buffer; wherever a `str` is expected, a `String` lends itself.
- `T[N]` is an inline array (`Copy` if `T` is); `[a, b, c]` and `repeat(v)` build one, with `N` from context. `T[]` is a borrowed slice, always `readonly T[]` or `mut T[]`.
- `Vec<T>`, `Box<T>`, `HashMap<K, V>` and the other owning containers are library types.

### 3.2 One row calculus

A *row* is a finite map from labels to types, optionally ending in a row variable. Flyscript has three kinds of row, all solved by one Rémy-style unifier over label-sorted rows:

- **Records**: `{ x: f64; y: f64; ...R }`. Physical layout is canonical (by alignment, then name), so equal record types have equal layouts.
- **Tag unions**: `#Some(T) | #None`, `#Get { key: String } | #Put { key: String; val: String } | ...R`. Payloads are a tuple `(…)` or a record `{…}`. Tags need no declaration.
- **Effect rows**: `uses Io, Fail<E>, ...R`.

Row variables are declared `<row R>`. A function generic in a row is monomorphized per instantiation, so field offsets and tag numbers are always constants: row polymorphism gives TypeScript's flexibility at C's cost.

```ts
function norm<row R>(p: readonly { x: f64; y: f64; ...R }): f64 {
  sqrt(p.x * p.x + p.y * p.y)
}
norm({ x: 3, y: 4, label: "a" })   // R = { label: str }
```

**Open failure rows.** A tag union written as the argument of `Fail` in a signature is implicitly open: `uses Fail<#Eof | #Bad>` means `uses Fail<#Eof | #Bad | ...ρ>` for a fresh `ρ`. A caller that may fail in more ways simply unifies its larger row with the callee's; error sets compose by union with no conversion code.

**Standard aliases.**
```ts
type Option<T>    = #Some(T) | #None;
type Result<T, E> = #Ok(T) | #Err(E);
```

### 3.3 Nominal types

`struct` names a record and `enum` names a closed tag union. A nominal type is a *new* type: it has identity (a `Meters` is not a `Seconds`), may keep its fields private to its module, may implement `Drop`, may carry `@layout(c)` or `@layout(packed)`, and may be recursive. Construction and matching are identical to the structural forms.

```ts
struct Point { x: f64; y: f64; }
enum Expr { #Num(f64), #Add(Box<Expr>, Box<Expr>), #Neg(Box<Expr>) }
```

**Recursion is iso-recursive**: a recursive type must pass through a nominal declaration. Structural rows are always finite, which keeps unification simple and terminating.

### 3.4 Interfaces and `impl`

Interfaces are nominal, may declare associated types, and may be generic in an effect row:

```ts
interface Hash<row E = []> {
  function hash(self: readonly Self, h: mut Hasher): void uses ...E;
}
interface Collection {
  type Item;
  function len(self: readonly Self): usize;
}
```

Declarations hold data only. Behaviour lives in `impl T { … }` (inherent methods) and `impl I for T { … }` (interface implementations). An `impl I for T` must appear in the module that declares `I` or the module that declares `T`. Calls dispatch statically through `<T extends I>`; `dyn I` is an explicit fat pointer for dynamic dispatch.

### 3.5 Derived interfaces

`Eq`, `Hash`, `Show` and `Clone` are derived for every record, tuple and tag union, and for any nominal type that requests them, by `comptime` reflection over its fields (§7). An error union therefore prints, compares and hashes with no code.

### 3.6 Inference

Type checking happens after `comptime` evaluation and uses bidirectional local inference.

- Exported functions, interface methods and `extern` declarations state their parameter types, return type and effects. An exported function with no `uses` clause is pure.
- Everything inside a body is inferred: local types, closure signatures, generic and row arguments, literal types, region arguments, and the effects of non-exported functions.
- Region arguments are unification variables solved over the whole body; one left unconstrained defaults to the heap.
- There is no global Hindley–Milner inference: errors stay local, and `comptime`, regions and interfaces stay decidable.

---

## 4. Ownership

### 4.1 Values, moves and borrows

A value has one owner. Assignment and argument passing *move* a value unless its type is `Copy`; a moved-from binding is dead. At the end of its scope a live owner is dropped.

A **borrow** lends a value without moving it:

- `readonly T`: shared and immutable. Any number may coexist.
- `mut T`: exclusive and mutable. While it exists, the owner is inaccessible.

Borrows are **transparent**: a borrow binding reads and writes as the value it refers to, and cannot be re-pointed. There is no dereference operator.

A borrow lasts until its last use, not to the end of its scope. In the example below, the `#None` arm holds no borrow of `counts`, so it may insert.

**Lending.** Wherever a borrow of `U` is expected, an owner that *lends* `U` may be passed: `String` lends `str`, `Vec<T>` lends `T[]`, `Box<T>` lends `T`, and `Ref<R, T>` lends `readonly T`. Lending is the only implicit conversion. Lookups in `HashMap<K, V>` accept any `Q` that `K` lends, so a `HashMap<String, V>` is searched with a `str` without allocating.

```ts
match (counts.getMut(word)) {
  #Some(n) => { n += 1; },               // n: mut u64, written in place
  #None    => { counts.insert(word.toString(), 1); },
}
```

### 4.2 Second-class values

Every type has a *class*, 1 or 2.

- `readonly T`, `mut T`, `str` and `T[]` are class 2.
- Every other type takes the maximum class of its components: fields, payloads and type arguments, structural or nominal alike. `Option<mut u64>` is class 2; so is `struct Scanner { src: readonly u8[]; pos: usize; }`.

A class-2 value may be a parameter, a local, or a return value tied to a parameter. It may not be stored in a class-1 value, captured by an escaping closure, sent to another task, or returned untied. That is the only restriction, and it is what replaces lifetime parameters.

**Tied returns.** A function that returns a class-2 value and takes exactly one class-2 parameter returns a view of that parameter. With several, the return names its source:

```ts
function longer(a: str, b: str, preferA: bool): str from a { … }
```

### 4.3 Closures

The compiler infers each closure's mode from what it captures:

| Type | Captures | Callable |
| :--- | :--- | :--- |
| `(A) => B` | `Copy` values and `readonly` borrows | any number of times, concurrently |
| `mut (A) => B` | at least one `mut` borrow | many times, one caller at a time |
| `once (A) => B` | at least one moved value | at most once |

A closure that captures any class-2 value is itself class 2: it can be passed down but not returned or stored. An escaping closure captures only by move.

### 4.4 Marker interfaces

The compiler derives three marker interfaces from structure:

- **`Copy`**: bitwise copyable; no field owns a resource and the type has no `Drop`.
- **`Send`**: may move to another task, and `readonly T` may be shared with other tasks. `T` is `Send` when it is class 1, owns no raw pointer, and contains no region data with a mutable slot (§4.6). Law 2 is what makes one marker enough: since every mutation through a shared reference is an effect, a `readonly` value seen by pure parallel code cannot change.
- **`Drop`**: user-implemented on nominal types; destructors run in reverse order of construction.

### 4.5 Pointers

| Pointer | Where | Sharing | Mutation |
| :--- | :--- | :--- | :--- |
| `Box<T>` | heap | unique | by its owner |
| `Ref<R, T>` | region `R` | `Copy` | none, except through `Cell` and `RegionList` |
| `Arc<T>` (`T extends Send`) | heap | atomic count | none; shared state goes through `Mutex`, `Atomic` and `Channel`, which are `Io` |
| `readonly T` / `mut T` | anywhere | second-class | `mut` only |

Long-lived cyclic structures outside a region use the library's `Pool<T>` with generation-checked `Handle<T>` indices.

### 4.6 Regions

A region is a fiber-local bump arena with lexical extent. `region (R) { … }` introduces a region type `R` and handles the `Region<R>` effect for its body; when the block exits, the arena is released at once.

A region is **append-only and immutable**:

- `alloc(v)` places `v` in the region and returns a `Ref<R, T>`. Reading through a `Ref` is pure, and data reached through it may be borrowed `readonly`.
- The only mutable slots are `Cell<T>` with `T extends Copy`, whose `get` copies out and `set` copies in (a `Cell` is never borrowed), and `RegionList<T>`, an append-only chunked list whose elements never move.
- `alloc`, `Cell.set`, `Cell.get` and `RegionList.push` perform `Region<R>`.

Two rules make this sound:

1. **No escape.** `R` may not occur in the type of the region expression, in any variable assigned from outside the block, or in an unhandled effect.
2. **No owned resources.** Region data contains only `Copy` values, `Ref`s, `Cell`s and `RegionList`s of the same region. Nothing in a region needs a destructor, so releasing the arena is constant-time.

Because nothing in a region moves or is freed before the region ends, and the only mutation is copy-in to a `Cell` or append to a list, no borrow into region data can be invalidated. Because handlers are fiber-local, no other task can perform `Region<R>`; a `Ref<R, T>` whose referent contains no `Cell` or `RegionList` is deeply immutable and may be shared with child tasks.

**Region elision.** In a declaration or block with exactly one region in scope, `Ref<T>`, `RegionList<T>` and region-generic type names take that region implicitly:

```ts
enum Json<region R> {
  #Null, #Bool(bool), #Num(f64), #Str(Ref<str>),
  #Arr(Ref<RegionList<Ref<Json>>>),
  #Obj(Ref<RegionList<{ key: Ref<str>; val: Ref<Json> }>>),
}
```
---

## 5. Effects

### 5.1 Effects and rows

An effect is a named set of operations:

```ts
effect Fail<E>        { raise(err: E): never; }
effect Yield<T>       { yield(item: T): void; }
effect Region<region R> { /* alloc, cell get/set, list push; used through library methods */ }
effect Io {
  read(fd: Fd, buf: mut u8[]): usize uses Fail<IoErr>;
  write(fd: Fd, buf: readonly u8[]): usize uses Fail<IoErr>;
  now(): Instant;
  sleep(d: Duration): void;
  park(on: WaitKey): void;                       // the primitive under locks, channels, atomics and join
  scope<T, row E>(body: once (s: mut Scope<E>) => T uses Io, ...E): T uses Io, ...E;
}
type IoErr = #Reset | #TimedOut | #BrokenPipe | #NotFound | #PermissionDenied;
```

These four are the standard effects. They are ordinary declarations; what makes them standard is only that the runtime installs root handlers for `Io` (and for the heap, which is not an effect).

A function's `uses` clause is a row of effects. A function with no `uses` clause is **pure**: it may allocate on the heap, open and use its own regions, and mutate its `mut` parameters, but it observes nothing and affects nothing outside its arguments and result. Higher-order functions are polymorphic in their callbacks' effects:

```ts
function map<T, U, row E>(xs: readonly T[], f: (x: readonly T) => U uses ...E): Vec<U> uses ...E
```

### 5.2 Handlers

`handle { body } with Eff { arms }` runs `body` and intercepts its `Eff` operations. Each arm has one of two forms:

- **Abortive** — `op(x) => armBody`. The body's frames are unwound first (running its `defer`s and destructors and releasing its borrows), then `armBody` runs and its value becomes the value of the `handle` expression. Because the body's borrows are released, the arm may use anything the body had borrowed.
- **Resumptive** — `op(x) resumes k => armBody`. The body stays suspended, holding its borrows, and `k` is the rest of the body as a value of type `Cont<A, B, E>`, where `A` is the operation's result type, `B` the `handle` expression's type and `E` the body's other effects.

The `handle` expression evaluates to the body's value if the body completes without performing `Eff`, and otherwise to the value of the arm that handled the operation. A resumptive arm usually produces that value by resuming: `k.resume(a)` itself evaluates to the `handle` expression's eventual value.

### 5.3 Continuations

A `Cont<A, B, E>` is an affine value. It may be stored, moved and returned like any other.

- `k.resume(a)` consumes `k` and runs the suspended computation until it next performs the handled effect (when the arm runs again) or finishes. Its value is the `handle` expression's value from that point.
- Dropping `k` unwinds the suspended computation in place: its `defer`s and destructors run in reverse order, in-flight I/O is cancelled and drained (§6.3), and its stack segment is released.
- Handlers are **deep**: the handler stays installed beneath the suspended computation. Operations of other effects performed while `k` runs go to the handlers around the `resume` call, which is why `E` appears in `resume`'s type.
- A `Cont` is class 2 when the suspended computation holds a class-2 value, so a continuation can never outlive a borrow it holds.
- Continuations are one-shot. Resuming twice would duplicate owned values and live `mut` borrows.

### 5.4 Errors: `throw`, `try`, `catch`

`throw e` performs `Fail.raise(e)`. `try { body } catch (p) { handler }` is an abortive handler of `Fail`: it evaluates to the body's value, or binds the failure to `p` and evaluates to the handler's value. Since the error type is a tag union, `catch` is usually a `match`:

```ts
const port = try { parsePort(raw) } catch (e) {
  match (e) { #Empty => 80, #NotANumber | #OutOfRange(_) => throw #BadConfig }
};
```

To keep a failure as data, `Fail.capture(() => body)` returns `Result<T, E>`; `r.unwrap()` turns it back into a failure. There is no separate error-conversion machinery: failure rows compose by union (§3.2).

### 5.5 Iteration: `yield` and `for…of`

`yield e` performs `Yield.yield(e)`. A generator is any computation that uses `Yield<T>`; nothing else marks it.

`for (const x of gen) { body }` handles `Yield` around `gen`, running `body` for each item:

- reaching the end of `body`, or `continue`, resumes the generator;
- `break` drops the continuation, so the generator unwinds and its cleanup runs, then the loop exits;
- `return` and an uncaught `throw` drop it in the same way before leaving.

```ts
function rows(db: readonly Db, sql: str): void uses Io, Fail<DbErr>, Yield<Row> {
  let cursor = db.open(sql);            // Drop closes the cursor
  while (cursor.hasNext()) { yield cursor.next(); }
}
```

Pull iteration is library code. `generate(f)` runs `f` under a `Yield` handler whose resumptive arm stores the continuation, and returns a `Gen<T, E>` whose `next()` resumes it:

```ts
export struct Gen<T, row E> { state: Option<Cont<void, Step<T, E>, E>>; }
type Step<T, row E> = #Done | #Item { item: T; rest: Cont<void, Step<T, E>, E> };

impl<T, row E> Gen<T, E> {
  export function next(self: mut Self): Option<T> uses ...E {
    match (self.state.take()) {
      #None    => #None,
      #Some(k) => match (k.resume()) {
        #Done => #None,
        #Item { item, rest } => { self.state = #Some(rest); #Some(item) },
      },
    }
  }
}
```

A `Gen` owns its continuation, so dropping it runs the generator's cleanup; if the generator throws, `next()` throws.

### 5.6 Cleanup: `defer` and `Drop`

`defer e;` schedules `e` to run when the enclosing block exits. `defer`s and the destructors of the block's owned locals share one stack and run in reverse order of the points at which they were registered, whether the block exits normally, by `return`, `break`, `throw`, an abortive handler, a dropped continuation, or cancellation.

### 5.7 Panics

Integer division by zero, overflow in checked builds (`wrappingAdd` and friends are explicit), an out-of-bounds index and heap exhaustion *panic*. A panic is not an effect and cannot be caught by a handler: it unwinds the current task, running cleanup, and fails the task's scope (§6.1); an unscoped panic terminates the process. Panics are for bugs; anticipated failure is `Fail`.

---

## 6. Concurrency and parallelism

### 6.1 Tasks and scopes

Concurrency is structured. `Io.scope((s) => body)` opens a scope; `s.spawn(task)` starts a task in it and returns a `Fiber<T, E>`; `f.join()` waits for the result.

```ts
interface Scope<row E> {
  function spawn<T extends Send>(self: mut Self, task: once () => T uses Io, ...E): Fiber<T, E>;
}
interface Fiber<T, row E> {
  function join(self: Self): T uses Io, ...E;
}
```

The rules:

1. **A scope owns its tasks.** `Io.scope` returns only when every task spawned in it has finished. A `Fiber` is a handle to the result, not to the task: dropping it (`s.spawn(t);` as a statement) leaves the task running.
2. **Failure cancels the scope.** If a task fails, or panics, the scope is cancelled: the body and every other task stop at their next `Io` operation and unwind. Once all have finished, the first failure is rethrown from `Io.scope` (or the panic continues). Joining a failed task rethrows its failure at the `join`.
3. **Captures.** A task is a `once` closure. It may move in owned `Send` values and capture `readonly` borrows of `Send` values from outside the scope; the scope outlives every task, so the borrows are safe.
4. **Isolation is a type.** A task whose effects are only `Io` cannot fail. A server that must survive a bad connection spawns tasks that handle their own errors, and the type checker proves it:

```ts
Io.scope((s) => {
  for (let conn of listener.accept()) {
    s.spawn(() => serveOne(conn, db));   // serveOne: (…) => void uses Io — cannot fail the scope
  }
});
```

### 6.2 Shared state

`Mutex<T>`, `Atomic*` and `Channel<T>` are library types whose operations perform `Io` (through `Io.park`). Every synchronization is therefore visible in the type, pure code cannot observe shared mutable state, and the deterministic simulator (§6.4) controls every interleaving.

### 6.3 Cancellation and in-flight I/O

When an `Io.read` or `Io.write` suspends, the buffer stays borrowed until the operation completes. If the task is cancelled while the operation is in flight, the runtime cancels it in the kernel and waits for the kernel to confirm it has released the buffer before unwinding the frame or region that owns the buffer. The same holds when a continuation holding such an operation is dropped.

### 6.4 Deterministic simulation

`Io` is an ordinary effect, so a test can handle it. The standard `SimIo` handler runs every task on one thread with a seeded scheduler, a virtual clock and fault injection; with the same seed, a run is reproducible exactly.

```ts
test("handler degrades under packet loss", () => {
  SimIo.run({ seed: 0x5eed, loss: 0.25 }, () => {
    let net = SimIo.pair();
    serveOne(net.server, net.db);
    assert(net.client.status() == 200 || net.client.status() == 502);
  });
});
```

### 6.5 Data parallelism

Parallel loops are library functions over pure closures:

```ts
interface ParSplit {
  type View;        // a mutable view of one element
  type ReadView;    // a read-only view of one element
  function len(self: readonly Self): usize;
  function split(self: mut Self, at: usize): [mut Self, mut Self] from self;
  function viewAt(self: mut Self, i: usize): Self.View from self;
  function readAt(self: readonly Self, i: usize): Self.ReadView from self;
}
function par<C extends ParSplit>(c: mut C, f: (v: C.View, i: usize) => void): void;
function parReduce<C extends ParSplit, A extends Send>(
  c: readonly C, zero: A, one: (v: C.ReadView, i: usize) => A, both: (a: A, b: A) => A,
): A;
```

`f` has no effects and receives a disjoint `mut` view of one element as an argument, so it cannot race; `par` divides the work with `split`, which the borrow rules already prove disjoint. `both` must be associative. For a slice, `View = mut T` and `ReadView = readonly T`; for a struct-of-arrays container they are records of field views (§7.2).

---

## 7. `comptime`

### 7.1 The metalanguage

Any function, parameter or expression marked `comptime` runs in the compiler before type checking, on a deterministic interpreter with a step budget and no effects. `Type` is a `comptime`-only type; types are values that `comptime` code inspects (`Type.fields(T)`, `Type.size(T)`, `Type.align(T)`) and builds (`Type.struct(fields)`). Generic types that need computation are written as functions:

```ts
comptime function Ring(comptime T: Type, comptime N: usize): Type {
  comptime assert(N > 0 && (N & (N - 1)) == 0, "capacity must be a power of two");
  struct { buf: T[N]; head: usize; tail: usize; }
}
type ByteRing = Ring(u8, 1024);
```

Derived interfaces (§3.5) are `comptime` functions in the standard library; user code can define its own derivations the same way.

### 7.2 Layout as a library: `Soa<T>`

`Soa<T>` is a `comptime` function that flattens `T`'s fields recursively into one contiguous, aligned allocation of planes and implements `ParSplit` with a nested view record:

```ts
struct Vec2 { x: f32; y: f32; }
struct Particle { pos: Vec2; vel: Vec2; mass: f32; }
// Soa<Particle> stores planes pos.x, pos.y, vel.x, vel.y, mass and has
// View = { pos: { x: mut f32; y: mut f32 }; vel: { x: mut f32; y: mut f32 }; mass: mut f32 }

function step(ps: mut Soa<Particle>, dt: f32): void {
  par(mut ps, (p, _) => { p.pos.x += p.vel.x * dt; p.pos.y += p.vel.y * dt; });
}
```

The view is an ordinary class-2 record (§4.2); no part of this is built into the compiler.

---

## 8. Modules, foreign code and targets

### 8.1 Modules

Each `.fly` file is an ES module. Declarations are private unless exported. The import graph must be acyclic, so modules compile in parallel in dependency order.

### 8.2 Foreign code

`extern "C"` declares a C function; `@layout(c)` gives a struct C layout. `T*` is a raw pointer: `Copy`, not `Send`, and readable or writable only inside `unsafe { … }` via `p.read()`, `p.write(v)` and `p.add(n)`. Calling an `extern "C"` function is `unsafe`; the usual pattern is a safe wrapper that states the function's real effects.

A foreign call runs on the worker thread's native stack, not on the task's growable segment.

### 8.3 Targets

- **Native** (x86-64, AArch64): tasks are stackful fibers scheduled by the runtime over `io_uring` or `kqueue`.
- **WebAssembly**: continuations lower to the stack-switching proposal (or JSPI on hosts without it); the root `Io` handler maps to the host's promises or WASI. Without threads, `par` runs sequentially with the same semantics.

---

## 9. Core calculus

Surface Flyscript elaborates into a small calculus, λ-fly, with judgments

> Δ | Θ | Γ ⊢ e : τ / ε ⊣ Θ′

- **Δ** binds type variables (with their bounds), region variables, and row variables. One kind of row variable serves records, tag unions and effects.
- **Θ** is the ownership context: each owned binding is live or moved. Θ′ is the context after `e`. Where branches disagree, the live branch drops the value.
- **Γ** is the borrow ledger: each live borrow, its mode (`ro` or `mut`) and the path it locks. A `mut` entry locks its path against all use; a `ro` entry locks it against moves and `mut` borrows.
- **ε** is the effect row of `e`.

The rules that carry the design:

- **Class.** class(`readonly τ`) = class(`mut τ`) = class(`str`) = class(`τ[]`) = 2. For every other type former, class is the maximum over components. A continuation's class is 2 if the frame it captures holds a class-2 value. Stores into class-1 places, escaping captures, `Send`, and untied returns require class 1.
- **Purity.** No primitive with ε = ∅ writes memory reachable through a `ro` entry of Γ. Writes through shared references exist only as operations of `Io` or `Region`.
- **Region.**
  > Δ, ρ | Θ | Γ ⊢ e : τ / Region⟨ρ⟩, ε ⊣ Θ′ &nbsp;&nbsp; ρ ∉ ftv(τ, Θ′, ε)
  > ─────────────────────────────────────────
  > Δ | Θ | Γ ⊢ region(ρ) { e } : τ / ε ⊣ Θ′
- **Handle.** An abortive arm is checked under the Γ of the `handle` expression, the body's borrows having been released. In a resumptive arm, the body's borrows move into `k`, whose type records them; they are released when `k` is resumed to completion or dropped.
- **Scope.** A task's captures must be class 1 and `Send`, or `ro` borrows of `Send` values whose paths are not under `mut` in Γ.
---

## 10. A worked example

### 10.1 Library signatures used

```ts
// std/net
export struct Socket { … }
impl Socket {
  export function read(self: mut Self, buf: mut u8[]): usize uses Io, Fail<IoErr>;
  export function writeStatus(self: mut Self, code: u16, body: str): void uses Io, Fail<IoErr>;
}
export struct Db { … }
impl Db {
  export function fetchProfile(self: readonly Self, user: str): Profile uses Io, Fail<IoErr>;
  export function checkQuota(self: readonly Self, token: str): Quota uses Io, Fail<IoErr>;
}
export type Profile = { displayName: String };
export type Quota = { allowed: bool };

// prelude, region operations (R inferred, §3.6)
function alloc<region R, T>(v: T): Ref<R, T> uses Region<R>;
function copyUtf8<region R>(bytes: readonly u8[]): Ref<R, str> uses Region<R>, Fail<#MalformedUtf8>;
```

### 10.2 An HTTP request handler

```ts
import { Socket, Db } from "std/net";

struct Request<region R> { user: Ref<str>; token: Ref<str>; }

function parse<region R>(raw: readonly u8[]): Ref<Request> uses Region<R>, Fail<#Malformed | #MalformedUtf8> {
  if (raw.len < 16) { throw #Malformed; }
  alloc({ user: copyUtf8(raw[0..8]), token: copyUtf8(raw[8..16]) })
}

export function serveOne(conn: Socket, db: readonly Db): void uses Io {
  try {
    region (R) {
      let buf: u8[512] = repeat(0);
      const n = conn.read(mut buf);
      const req = parse(buf[0..n]);

      // Two concurrent lookups. `req` is immutable region data and `db` a shared
      // borrow, so both tasks may read them; a failure in either cancels the other.
      const [profile, quota] = Io.scope((s) => {
        const p = s.spawn(() => db.fetchProfile(req.user));
        const q = s.spawn(() => db.checkQuota(req.token));
        [p.join(), q.join()]
      });

      if (!quota.allowed) { throw #Unauthorized; }
      conn.writeStatus(200, profile.displayName);
    }
  } catch (e) {
    const code: u16 = match (e) {
      #Malformed | #MalformedUtf8 => 400,
      #Unauthorized               => 401,
      _                           => 502,
    };
    try { conn.writeStatus(code, "error"); } catch (_) {}
  }
}
```

Everything here follows from the rules above: the failure row of the `try` body is the union of `parse`'s, `read`'s, the tasks', `writeStatus`'s and `#Unauthorized`; the `catch` arm may use `conn` because the body's borrow of it was released when the body unwound; and `serveOne` itself is `uses Io` only, so a server can spawn it without risking the scope (§6.1).

---

## 11. Implementation

1. **Parse** each module into a syntax tree; check that imports are acyclic.
2. **Evaluate `comptime`** on a bytecode interpreter: compute types, derive interfaces, instantiate generics and row variables, canonicalize record and tag layouts.
3. **Check types and effects** bidirectionally with one row unifier; infer local effects, region variables and literal types.
4. **Check ownership** on a mid-level SSA form: moves (Θ), the borrow ledger (Γ), class, tied returns, handler borrow transfer, region non-escape.
5. **Lower effects** by evidence passing: tail-resumptive handlers (most `Yield`, all `Region`) become direct calls; abortive `Fail` handlers become two-register returns; handlers that store or delay `k` switch stack segments.
6. **Generate code** with Cranelift for fast debug builds and LLVM for release, emitting `noalias` and `readonly` from `mut` and `readonly`. A struct-of-arrays view lowers to plane arithmetic; an affine value consumed and rebuilt at the same size reuses its allocation.

---

## 12. Design notes

### 12.1 Compared with

| Language | Flyscript adds | Flyscript gives up |
| :--- | :--- | :--- |
| Rust | No lifetime parameters; no `async` colouring or `Pin`; cyclic data in regions without `Rc<RefCell>`; structural records and tag unions; error sets by union; deterministic simulation | Borrows can't live in long-lived structs; stackful tasks instead of compiler-built state machines |
| TypeScript | Native and Wasm code with no collector; real integer types; typed failures; data-race freedom | Width subtyping, `any`, runtime reflection |
| Koka | Ownership instead of reference counting; unboxed layout control; data-race freedom | Multi-shot continuations |
| OCaml 5 | Ownership; typed effects (OCaml 5's are untyped); row-polymorphic records | A garbage collector's convenience |
| Roc | Mutation, regions, user-defined handlers, FFI | Whole-program inference |
| Hylo | Effects, regions, structural rows | Hylo's subscript projections |
| Zig | Memory safety; ADTs and `match`; interfaces; effects | Zig's tiny checker and `@cImport` |
| Mojo | Effects, rows, TypeScript syntax, no lifetime lists | MLIR-native accelerator targets, for now |

### 12.2 Rejected alternatives

- **Garbage collection**, global or per-actor: pauses, memory overhead and barriers, for a problem that ownership, regions and pools already cover.
- **Lifetime parameters**: they spread through every type that holds a borrow. Second-class borrows plus tied returns cover the same programs that matter, without annotations.
- **`async`/`await`**: function colouring, and self-referential futures that cannot borrow across suspension without `Pin`.
- **`iso` and `recover`** (Pony): redundant once ownership is affine and borrows cannot be stored.
- **Interior mutability without an effect** (`Cell`/`RefCell` as in Rust): it breaks Law 2 and would need a `Sync` marker to repair.
- **Width subtyping**: needs runtime field lookup or boxing; rows are free.
- **Multi-shot continuations**: they duplicate owned values and `mut` borrows.
- **Global Hindley–Milner inference**: non-local errors, and undecidable alongside `comptime` and regions.
- **A separate `Result` world with conversion traits**: one failure effect with union rows does the same job with no code.

### 12.3 Open questions

1. **Portable SIMD.** `Soa` and `par` cover vertical arithmetic. Horizontal operations (shuffles, mask extraction) need a `Simd<T, N>` surface that lowers well to both NEON/SVE and AVX2/AVX-512.
2. **Supervision beyond scopes.** Nursery semantics plus "a task that cannot fail says so" cover servers. Whether long-lived actor trees want restart strategies as a library is open.

---

## Appendix: eight programs

These were written to test the design, not to show it off; each ends with what still feels awkward.

### A.1 JSON parser in a region

```ts
import { RegionList } from "std/region";

export enum Json<region R> {
  #Null, #Bool(bool), #Num(f64), #Str(Ref<str>),
  #Arr(Ref<RegionList<Ref<Json>>>),
  #Obj(Ref<RegionList<{ key: Ref<str>; val: Ref<Json> }>>),
}

struct Scanner { src: readonly u8[]; pos: usize; }      // class 2: holds a borrow

type JsonErr = #Eof | #Unexpected(usize) | #MalformedUtf8;

function value<region R>(sc: mut Scanner): Ref<Json> uses Region<R>, Fail<JsonErr> {
  sc.skipSpace();
  if (sc.pos >= sc.src.len) { throw #Eof; }
  match (sc.src[sc.pos]) {
    b'n' => { sc.expect("null"); alloc(#Null) },
    b't' => { sc.expect("true"); alloc(#Bool(true)) },
    b'"' => alloc(#Str(copyUtf8(sc.quoted()))),
    b'[' => {
      sc.pos += 1;
      const items = RegionList.new();
      while (!sc.eat(b']')) { items.push(value(mut sc)); sc.eat(b','); }
      alloc(#Arr(items))
    },
    _ => throw #Unexpected(sc.pos),
  }
}
```
*Awkward:* nothing serious. `Ref<…>` around every node is the honest cost of region allocation.

### A.2 Word count

```ts
import { File, stdout } from "std/io";
import { HashMap } from "std/collections";

function words(line: str): void uses Yield<str> {
  for (const w of line.splitWhitespace()) { yield w; }
}

export function main(args: readonly String[]): void uses Io {
  let counts = HashMap.new<String, u64>();
  for (const path of args) {
    try {
      let f = File.open(path);
      for (const line of f.lines()) {
        for (const w of words(line)) {
          match (counts.getMut(w)) {
            #Some(n) => { n += 1; },
            #None    => { counts.insert(w.toString(), 1); },
          }
        }
      }
    } catch (e) { stdout.println(`${path}: ${e}`); }
  }
  for (const [w, n] of counts.sortedByValue()) { stdout.println(`${n} ${w}`); }
}
```
*Awkward:* none. `${e}` works because tag unions derive `Show`.

### A.3 Generators: `zip`

```ts
import { generate } from "std/iter";

export function zip<A, B, row E>(
  a: once () => void uses Yield<A>, ...E,
  b: once () => void uses Yield<B>, ...E,
): void uses Yield<[A, B]>, ...E {
  let ga = generate(a);
  let gb = generate(b);
  while (true) {
    match ([ga.next(), gb.next()]) {
      [#Some(x), #Some(y)] => yield [x, y],
      _ => break,
    }
  }
}

export function dot(xs: readonly f64[], ys: readonly f64[]): f64 {
  let total = 0.0;
  for (const [x, y] of zip(() => xs.each(), () => ys.each())) { total += x * y; }
  total
}
```
*Awkward:* passing streams as thunks (`() => xs.each()`) rather than as values. That is the price of streams being computations; `Gen` is the value form when one is wanted.

### A.4 Particles

```ts
import { par, parReduce } from "std/par";
import { Soa } from "std/layout";

struct Vec2 { x: f32; y: f32; }
struct Particle { pos: Vec2; vel: Vec2; mass: f32; }

export function step(ps: mut Soa<Particle>, dt: f32): f32 {
  par(mut ps, (p, _) => {
    p.pos.x += p.vel.x * dt;
    p.pos.y += p.vel.y * dt;
  });
  parReduce(ps, 0.0,
    (p, _) => 0.5 * p.mass * (p.vel.x * p.vel.x + p.vel.y * p.vel.y),
    (a, b) => a + b)
}
```
*Awkward:* none.

### A.5 A symbol table with cycles

```ts
import { RegionList, Cell } from "std/region";

export struct Decl<region R> { name: Ref<str>; ty: Cell<u32>; visiting: Cell<bool>; }
export struct Scope<region R> {
  parent: Option<Ref<Scope>>;
  names: Ref<RegionList<{ name: Ref<str>; decl: Ref<Decl> }>>;
}

impl<region R> Scope<R> {
  export function new(parent: Option<Ref<Scope>>): Ref<Scope> uses Region<R> {
    alloc({ parent, names: RegionList.new() })
  }
  export function define(self: Ref<Self>, name: Ref<str>): Ref<Decl> uses Region<R> {
    const d = alloc(Decl { name, ty: Cell.new(0), visiting: Cell.new(false) });
    self.names.push({ name, decl: d });
    d
  }
  export function lookup(self: Ref<Self>, name: str): Option<Ref<Decl>> {   // pure
    for (const b of self.names.each()) { if (b.name == name) { return #Some(b.decl); } }
    match (self.parent) { #Some(p) => p.lookup(name), #None => #None }
  }
}
```
*Awkward:* none. `lookup` is pure because reading `Ref`s and the current contents of an append-only list cannot observe mutation.

### A.6 A key–value actor

```ts
import { Receiver, Reply } from "std/sync";
import { HashMap } from "std/collections";

export type Command =
  | #Get { key: String; reply: Reply<Option<String>> }
  | #Put { key: String; val: String }
  | #Stop;

export function kv(inbox: readonly Receiver<Command>): void uses Io {
  let store = HashMap.new<String, String>();
  for (const cmd of inbox.each()) {
    match (cmd) {
      #Get { key, reply } => reply.send(store.get(key).cloned()),
      #Put { key, val }   => store.insert(key, val),
      #Stop               => break,
    }
  }
}
```
*Awkward:* none.

### A.7 A server

```ts
import { Listener, Db } from "std/net";
import { serveOne } from "./handler";

export function serve(listener: mut Listener, db: readonly Db): void uses Io, Fail<IoErr> {
  Io.scope((s) => {
    for (const conn of listener.accept()) {
      s.spawn(() => serveOne(conn, db));
    }
  });
}
```
*Awkward:* none. `serveOne` is `uses Io` only, so a failing connection cannot cancel the server; if it could, this would not type-check without a `try`.

### A.8 A browser UI

```ts
export type Msg = #Inc | #Dec | #Reset;
export type Model = { count: i32; clicks: u32 };

export effect Dom<M> {
  el(tag: str, attrs: readonly { key: str; val: str }[], children: () => void uses Dom<M>): void;
  text(s: str): void;
  onClick(m: M): void;
}

export function update(m: mut Model, msg: Msg): void {
  m.clicks += 1;
  match (msg) { #Inc => m.count += 1, #Dec => m.count -= 1, #Reset => m.count = 0 }
}

export function view(m: readonly Model): void uses Dom<Msg> {
  region (R) {
    const label = fmt(`Count: ${m.count} (${m.clicks} clicks)`);
    Dom.el("div", [{ key: "class", val: "card" }], () => {
      Dom.el("h1", [], () => Dom.text(label));
      Dom.el("button", [], () => { Dom.onClick(#Dec); Dom.text("−"); });
      Dom.el("button", [], () => { Dom.onClick(#Inc); Dom.text("+"); });
    });
  }
}
```
*Awkward:* none. The view streams into the host's reconciler through an effect, so no virtual-DOM tree is allocated; per-frame strings live in a region released after the frame.
