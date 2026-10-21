# Flyscript

**Language specification, version 0.25**

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

### 0.1 Changes from 0.24

0.25 closes four soundness gaps a holistic review found at the edges of 0.24's new features (docs/reviews/2026-10-21-holistic-review-of-0-24.md), and removes the appendix's last awkward note.

| Change | Why |
| :--- | :--- |
| A function is called through a borrow only as its mode allows: shared through any, `mut` through `mut`, `once` never (§4.3) | a `once` closure called twice through a `readonly` borrow moved its captures out twice |
| Associated types may hide a borrow until their base is known (§4.2) | `Vec<C.Slice>` in generic code could keep a `mut f32[]` past its loan |
| Each instance of a template struct is checked as the struct it is (§7.1) | a non-`view` `Partial<{ name: str }>` held a borrow |
| `ParSplit` impls require `Send` elements; `Soa<T>` requires a field (§6.5, §7.4) | `par` would hand non-`Send` elements to other workers |
| `if (let pat = e)` binds mutable names; the pattern grammar is written out (§2.3) | `let` was refused where `for (let …)` was accepted |
| Expected types are stated to flow into blocks, branches and lambda bodies (§3.6) | the rule was implemented but specified only for calls |
| A.9 decodes with `try`/`catch` and `const s: Signup = parse(body)` | no type argument to spell, and no awkward note left in the appendix |

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
5. Refinement types and automatic GPU lowering, before 1.0.

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
| `interface` + `class … implements` | `interface` + `struct` + `impl` | Data and behaviour are declared separately. Interfaces are nominal and may extend others. Fields are public unless `private`. |
| `T \| null \| undefined` | `Option<T>` = `#Some(T) \| #None` | There is no null. |
| `throw` / `try` / `catch` | same | Typed: a function's failures are part of its type. |
| `function*` / `yield` / `for…of` | `yield` / `for…of` | A generator is any function that uses `Yield<T>`; `for…of` also accepts any `Iterable<T>`. |
| `xs.map(f).filter(p)` | `xs.iter().map(f).filter(p)` | Iteration chains are lazy generators (§5.5). |
| `.d.ts` declaration files | `.d.fly` declaration files | Signatures without bodies, used for the standard library. |
| `async` / `await` | (nothing) | I/O is an effect; every function is "direct style". |
| `import` / `export` | same | ES modules; the import graph must be acyclic. |
| `<T extends U>` | same | Monomorphized. Bounds compose with `&`. |

### 2.2 Lexical rules

- **Statements and blocks.** Flyscript is expression-oriented. A block `{ s1; s2; e }` evaluates to its final expression `e` when that expression has no trailing semicolon, and to `void` otherwise. `if`, `match`, `try`, `region` and `handle` are expressions. An expression statement `e;` discards its value. `return e;` returns early.
- **Literals.** Numeric literals have no suffix; their type is solved together with the whole enclosing call or initializer from the expected type, defaulting to `i32` and `f64` only if still unconstrained. Byte literals are `b'n'`; strings are `"…"` (type `str`) and templates `` `…${e}…` ``, which build a `String` from the `Show` of each interpolated value.
- **Record literals.** `{ f: e, … }` builds the nominal struct named by the expected type, if there is one, and a structural record otherwise. `Point { … }` names the struct explicitly. `{ x, y }` puns field names.
- **Generic calls.** In expression position, `f<…>(` and `x.f<…>(` are parsed as type application when the `<…>` is a balanced type-argument list followed immediately by `(`; otherwise `<` is less-than. This is TypeScript's rule.
- **Mutable borrows are visible at the call site.** `read(mut buf)` lends `buf` mutably; `parse(buf)` lends it read-only. The one exception is a method's receiver, which is lent in whatever mode the method declares: `conn.read(mut buf)` borrows `conn` mutably.
- **Parameters bind like `let`.** An owned parameter may be mutated and lent `mut` by its function.

### 2.3 Grammar

```ebnf
Module      = { Import | ["export"] Decl } ;
Import      = "import" "{" ImportName { "," ImportName } "}" "from" String ";" ;
ImportName  = Ident [ "as" Ident ] ;

Decl        = Struct | Enum | Interface | Impl | TypeAlias | Effect | Function | Extern | Const ;
Struct      = [ Layout ] [ "view" ] "struct" Ident [ TypeParams ] "{" { [ "private" ] Field | "comptime" Expr ";" } "}" ;
Enum        = [ "view" ] "enum" Ident [ TypeParams ] "{" Tag { "," Tag } [ "," ] "}" ;
Layout      = "@layout" "(" ( "c" | "packed" ) ")" ;
Const       = "const" Ident [ ":" Type ] "=" Expr ";" ;      (* evaluated at comptime *)
Interface   = "interface" Ident [ TypeParams ] [ "extends" Bounds ] "{" { ( Sig | "type" Ident [ "extends" Bounds ] ) ";" } "}" ;
Impl        = "impl" [ TypeParams ] Type [ "for" Type ] "{" { ["export"] Function | "type" Ident "=" Type ";" } "}"
            | "impl" Type "for" Type ";" ;                (* asks for the derivation, §7.3 *)
TypeAlias   = "type" Ident [ TypeParams ] "=" Type ";" ;
Effect      = "effect" Ident [ TypeParams ] "{" { Op ";" } "}" ;
Op          = Name [ TypeParams ] "(" [ Params ] ")" ":" Return ;   (* operations have no effects *)
Name        = Ident | Keyword ;                     (* member names may be reserved words *)
Function    = Sig Block ;
Extern      = "extern" "\"C\"" Sig ";" ;
Sig         = [ "comptime" ] "function" Ident [ TypeParams ] "(" [ Params ] ")" ":" Return [ Uses ] ;
Params      = Param { "," Param } [ "," ] ;
Param       = [ "comptime" ] Ident ":" [ "mut" | "readonly" ] Type ;
Return      = [ "mut" | "readonly" ] Type [ "from" Ident { "," Ident } ] ;
Uses        = "uses" Row ;

TypeParams  = "<" TypeParam { "," TypeParam } ">" ;
TypeParam   = "region" Ident | "row" Ident [ "=" Type ] | "comptime" Ident ":" Type
            | Ident [ "extends" Bounds ] [ "=" Type ] ;
Bounds      = Type { "&" Type } ;

Type        = Prim | Path [ TypeArgs ] | Record | Union | Tuple | Fn
            | Type "[" [ Expr ] "]" | "mut" Type | "readonly" Type | Type "*" | "dyn" Path | "[" "]" ;
Record      = "{" { Field } [ "..." Ident ] "}" ;
Field       = FieldName ":" Type ";" | Generate(Field) ;
FieldName   = Ident | "[" Expr "]" ;                       (* computed by comptime code, §7.2 *)
Generate(X) = "comptime" "for" "(" "const" Pattern "of" Expr ")" "{" { X } "}"
            | "comptime" "if" "(" Expr ")" "{" { X } "}" [ "else" "{" { X } "}" ]
            | "comptime" "match" "(" Expr ")" "{" { Pattern "=>" "{" { X } "}" [ "," ] } "}" ;
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
BlockLike   = If | IfConst | While | For | Match | Try | Region | Handle | Unsafe | Block | "comptime" ( If | Match | For ) ;
Expr        = … | BlockLike | Throw | Yield | Lambda | RecordLit | ListLit | "comptime" Unary
            | Expr "." "[" Expr "]" | "#" "[" Expr "]" [ TagArgs ] ;
RecordLit   = [ Path ] "{" [ Entry { "," Entry } ] "}" ;
Entry       = FieldName [ ":" Expr ] | Generate(Entry) ;
ListLit     = "[" [ Item { "," Item } ] "]" ;
Item        = Expr | "comptime" ( For | If ) ;          (* one item per iteration, §7.2 *)
Match       = "match" "(" Expr ")" "{" { MatchArm } "}" ;
IfConst     = "if" "(" ( "const" | "let" ) Pattern "=" Expr ")" Block [ "else" ( If | IfConst | Block ) ] ;  (* a two-armed match *)
MatchArm    = Pattern [ "if" Expr ] "=>" ( Expr "," | Block ) | Generate(MatchArm) ;
Pattern     = PatAtom { "|" PatAtom } ;
PatAtom     = "_" | Literal | "comptime" Unary | Ident
            | ( "#" Ident | "#" "[" Expr "]" ) [ "(" [ Pattern { "," Pattern } ] ")" | PatRecord ]
            | [ Path ] PatRecord | "[" [ Pattern { "," Pattern } ] "]" ;
PatRecord   = "{" [ Ident [ ":" Pattern ] { "," Ident [ ":" Pattern ] } ] "}" ;
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

- **Braces.** A `{` in expression position begins a record literal. A block appears only as the body of a block-like construct, after `=>` in a lambda or match arm, or at the start of a statement — unless the brace opens an entry (`{ a: 1 }`, `{ [k]: v }`, or a `comptime for` over entries): Flyscript has no labeled statements, so that is always a record.
- **Block-like statements.** A block-like expression at the start of a statement needs no `;` and is not continued by operators: `if (c) { … } [a, b]` is two statements. As the last item of a block it is the block's value.
- **Contextual words.** `from`, `of`, `with`, `resumes`, `row`, `view` and `private` are keywords only where the grammar expects them, and any reserved word may be used as a member name (`Yield.yield`, `{ default: 1 }`).

---

## 3. Types

### 3.1 Primitives, strings, arrays

- Scalars: `i8`–`i64`, `isize`, `u8`–`u64`, `usize`, `f32`, `f64`, `bool`, `void`, `never`. All are `Copy`.
- `str` is a borrowed UTF-8 slice; string literals are `str` with static storage. `String` is an owned, growable UTF-8 buffer; wherever a `str` is expected, a `String` lends itself.
- `T[N]` is an inline array (`Copy` if `T` is); `[a, b, c]` and `repeat(v)` build one, with `N` from context. `T[]` is a borrowed slice, always `readonly T[]` or `mut T[]`.
- `Vec<T>`, `Box<T>`, `HashMap<K, V>` and the other owning containers are library types.

A tuple `[A, B]` is built with a list literal checked against a tuple type, taken apart with a pattern (`const [a, b] = t`), and indexed by a constant, as in TypeScript: `t[0]` is a place of its own, like a field.

Indexing an array, a slice or a `Vec` (`xs[i]`) is a place of the element type, checked against the length at run time (a panic out of bounds); assigning to it writes in place, and while it is borrowed the whole collection is. Slicing (`xs[a..b]`, either bound optional) lends `readonly T[]`, or `mut T[]` where a `mut` slice is expected; `s[a..b]` on a `str` lends a `str`, and panics unless both bounds fall on character boundaries.

### 3.2 One row calculus

A *row* is a finite map from labels to types, optionally ending in a row variable. Flyscript has three kinds of row, all solved by one Rémy-style unifier over label-sorted rows. They differ only in what a label is and in what happens when a label appears twice:

- **Records**: `{ x: f64; y: f64; ...R }`. A label is a field name and appears at most once; extending a row requires that its tail lack the label. Physical layout is canonical (by alignment, then name), so equal record types have equal layouts.
- **Tag unions**: `#Some(T) | #None`, `#Get { key: String } | #Put { key: String; val: String } | ...R`. A label is a tag; payloads are a tuple `(…)` or a record `{…}`. Tags need no declaration. Two unions are joined by merging their tags, unifying the payloads of a tag present in both. Whatever its shape, `#A(x)` builds or binds a payload whole: `#Add(pair)` where `pair: [Expr, Expr]`, `#Get(req)` where `req: { key: String }`. Code that is generated per tag (§7.2) relies on it.
- **Effect rows**: `uses Io, Fail<E>, Region<R>, ...R`. A label is an effect name together with its **region arguments**: `Region<R1>` and `Region<R2>` are different labels and may share a row. An effect's other type arguments are **determined by its label**, so a row holds one `Fail` and one `Yield`, and wherever two rows meet, their `Fail` payloads unify. Effect rows are sets: extending a row with a label it already contains is the identity, so `uses Io, ...E` is well formed whether or not `E` contains `Io`.

Determined arguments are what make error sets compose. A block that calls `conn.read` (`Fail<IoErr | ...ρ1>`) and `parse` (`Fail<#Malformed | ...ρ2>`) has one `Fail` whose payload is the merged union `IoErr | #Malformed | ...ρ3`; no conversion code is involved.

Row variables are declared `<row R>`. A function generic in a row is monomorphized per instantiation, so field offsets and tag numbers are always constants: row polymorphism gives TypeScript's flexibility at C's cost.

```ts
function norm<row R>(p: readonly { x: f64; y: f64; ...R }): f64 {
  sqrt(p.x * p.x + p.y * p.y)
}
norm({ x: 3, y: 4, label: "a" })   // R = { label: str }
```

**Open and closed unions.** A tag union written in a type alias or a signature is closed. Two exceptions make tag unions pleasant to use:

- A *construction* is open: `#Some(x)` has type `#Some(T) | ...ρ`, so it fits any union that has a `#Some`.
- The argument of `Fail` in a signature is open, after expanding aliases: `uses Fail<IoErr>` means `uses Fail<IoErr | ...ρ>` for a fresh `ρ`. A caller that may fail in more ways unifies its larger row with the callee's.

Handling `Fail` closes the row again (§5.4), so the value caught is exactly the union the body can throw. Exhaustiveness is checked once a function's types are final, over nested patterns — tags, tuples, records, structs and `bool` — and an incomplete `match` names a value it misses: `does not handle '#Err(#Unknown(_))'`. A union whose tail is still open at that point was built only from the tags the function saw, so it is closed rather than requiring a `_` arm; a union with a row-parameter tail always needs one.

**Standard aliases.**
```ts
type Option<T>    = #Some(T) | #None;
type Result<T, E> = #Ok(T) | #Err(E);
```

### 3.3 Nominal types

`struct` names a record and `enum` names a closed tag union. A nominal type is a *new* type: it has identity (a `Meters` is not a `Seconds`), may implement `Drop`, may carry `@layout(c)` or `@layout(packed)`, and may be recursive. Construction and matching are identical to the structural forms. Fields are public, as in TypeScript, unless marked `private`, which limits them to the declaring module: outside it, a struct with private fields cannot be built with a literal or taken apart with a pattern, only through the functions its module exports. That is what lets a type keep an invariant (`NonZero`).

A struct or enum that holds a borrow (§4.2) must say so: `view struct Scanner { src: readonly u8[]; pos: usize; }`. A view is a temporary lens on someone else's data; it can be a local or a parameter but never stored or returned untied. Without `view`, a borrow field is an error that suggests the owned alternative (`String` for `str`, `Vec<T>` for `T[]`), so the choice is made where the type is declared, not discovered where it is first stored.

```ts
struct Point { x: f64; y: f64; }
enum Expr { #Num(f64), #Add(Box<Expr>, Box<Expr>), #Neg(Box<Expr>) }
```

**Recursion is iso-recursive**: a recursive type must pass through a nominal declaration. Structural rows are always finite, which keeps unification simple and terminating.

### 3.4 Interfaces and `impl`

Interfaces are nominal, may extend other interfaces (`interface Ord extends Eq`), may declare associated types, and may be generic in an effect row:

```ts
interface Hash<row E = []> {
  function hash(self: readonly Self, h: mut Hasher): void uses ...E;
}
interface Collection {
  type Item;
  function len(self: readonly Self): usize;
}
```

Declarations hold data only. Behaviour lives in `impl T { … }` (inherent methods) and `impl I for T { … }` (interface implementations). An `impl I for T` must appear in the module that declares `I` or the module that declares `T`. Structural and built-in types (records, tag unions, slices, `str`) belong to no module, so only the standard library gives them inherent methods (`Option.cloned`, `str.splitWhitespace`); other code extends them through interfaces. Calls dispatch statically through `<T extends I>`: a method through a value (`x.encode(out)`) and a function without `self` through the type (`T.decode(p)`, `User.decode(p)`). Each call states the bounds its type arguments must meet, checked where the types are known. `dyn I` is an explicit fat pointer for dynamic dispatch.

An interface's associated types are given by each impl (`type View = mut T;`), and `C.View` for a known `C` is whatever `C`'s impl says.

The impl for a type is the first whose head matches it, after expanding aliases; specific impls come before an interface's derivation (§7.3). An impl of `I` for `T` requires `T` to satisfy every interface `I` extends: `interface FromJson extends Send` means nothing that borrows is decoded, derivation or not.

A method's receiver is a first parameter named `self`: `self: Self` (by move), `self: readonly Self` or `self: mut Self`. A function in an `impl` without `self` is called on the type: `RegionList.new()`.

### 3.5 Derived interfaces

An interface can come with a *derivation*: an impl, written in Flyscript with `comptime` reflection, that works for any type whose shape it can see (§7.3). Records, tuples and tag unions get it whenever they have no impl of their own; a struct or enum asks for it with `impl Eq for Point;`. `Eq`, `Hash`, `Show` and `Clone` are derived this way in the prelude, so an error union prints, compares and hashes with no code, and so are `ToJson` and `FromJson` in the standard library.

`Ord extends Eq` is derived too, ordering by fields and then by tags, in declaration order; `type Ordering = #Less | #Equal | #Greater`.

The derivations settle three things a derived interface must get right. On floats, `Eq`, `Ord` and `Hash` are total, so a record with a float field is a sound `HashMap` key and sorts consistently: `NaN` equals itself and orders after every number, and `-0.0` equals and hashes as `0.0` (the primitive operators on floats stay IEEE 754). `Clone` copies a `readonly` borrow and never duplicates a `mut` one. `Box<T>` and `Arc<T>` compare, order, hash and show as what they hold; cloning a `Box` clones its contents, cloning an `Arc` shares them again.

The operators use them. `==` and `!=` are built in for primitives and call `Eq.eq` on anything else, and `<`, `<=`, `>` and `>=` likewise call `Ord.cmp`; an owner compared with the type it lends is compared at that type (`name == "ada"` for a `String`, `b.name == name` for a `Ref<R, str>`); `` `${e}` `` writes a primitive or a string as it is and anything else with `Show`, which writes a value as Flyscript would (`Point { x: 1, y: 2 }`, `#Some("a")`). A struct is a new type, so it is compared or printed only if it asks: `impl Eq for Point;`.

### 3.6 Inference

Type checking happens after `comptime` evaluation and uses bidirectional local inference.

- Exported functions, interface methods and `extern` declarations state their parameter types, return type and effects. An exported function with no `uses` clause is pure.
- Everything inside a body is inferred: local types, closure signatures, generic and row arguments, literal types, region arguments, and the effects of non-exported functions.
- Region arguments are unification variables solved over the whole body. An allocation whose region the types leave undetermined goes to the **innermost enclosing region it does not escape from**: when a `region` block ends, each such allocation is placed in it unless that would let the data outlive the block (through the block's value or a variable declared outside it), in which case it is offered to the next enclosing region. A region argument left unconstrained outside every region defaults to the heap, where region allocation is an error, so a stray `alloc` is caught.
- **Recursion.** A function that is called again while its effects are being inferred — itself, or through others — is assumed pure there; if its body then performs an effect, it must state its effects with `uses`.
- **Expected types flow inward**: into blocks and their last expression, into the branches of `if`, `match`, `try`, `region` and `handle`, into a lambda's body from the function type expected of it, and into calls. A call checked against an expected type unifies the callee's instantiated return type with it *before* checking the arguments. This is how `alloc({ user, token })` in a function returning `Ref<Request>` builds a `Request` rather than an anonymous record.
- `break`, `continue`, `return` and `throw` have type `never`, which fits any expected type.
- There is no global Hindley–Milner inference: errors stay local, and `comptime`, regions and interfaces stay decidable.

---

## 4. Ownership

### 4.1 Values, moves and borrows

A value has one owner. Assignment and argument passing *move* a value unless its type is `Copy`; a moved-from binding is dead until it is assigned again. Moves are tracked through branches and loops: a binding moved on any path is moved where the paths meet, and a binding used at the top of a loop must still be live at the end of the loop body. At the end of its scope a live owner is dropped. Moving a field out of a value moves only that field, unless the value's type implements `Drop`, from which no field may be moved.

A **borrow** lends a value without moving it:

- `readonly T`: shared and immutable. Any number may coexist.
- `mut T`: exclusive and mutable. While it exists, the owner is inaccessible.

Borrows are **transparent**: a borrow binding reads and writes as the value it refers to, and cannot be re-pointed. There is no dereference operator.

`readonly T` is `Copy`; `mut T` is not. Passing a binding of type `mut T` where a `mut` borrow is expected **reborrows** it: the binding is locked until the new borrow ends, and usable again afterwards, so `value(mut sc); sc.eat(b',')` is legal. Read where an owned value is expected, a borrow gives a copy of what it refers to, which must be `Copy`; and a `mut T` field read through a `readonly` borrow is `readonly T`.

A value that is borrowed without having a place — a call's result, a template string, a literal lent as `str` — is stored in an anonymous local of the enclosing block, dropped when the block ends. So ``stringify(#Rejected { reason: `missing ${field}` })`` lends the string for the call, and ``const r = #Rejected { reason: `…` };`` holds a borrow of it while `r` is used; returning `r` is the usual error, a borrow of a local.

A borrow lasts until the last use of any value that holds it, not to the end of its scope. Every value carries the set of borrows it holds: a borrow taken for an argument is held by the call's result if the result can hold it (§4.2); a value bound by a pattern or assigned to a binding passes its borrows on; a binding assigned on several paths holds the union. In the example below, the `#None` arm holds no borrow of `counts`, so it may insert, while in the `#Some` arm `n` holds `counts` mutably until its last use.

A method call borrows its receiver in two phases: the receiver is borrowed `readonly` while the arguments are evaluated and `mut` only for the call itself, so `v.push(v.len())` is legal and `v.push({ v.clear(); 1 })` is not.

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
- Every other type takes the maximum class of its components: fields, payloads and type arguments, structural or nominal alike. `Option<mut u64>` is class 2; so is `view struct Scanner { src: readonly u8[]; pos: usize; }`. A region reference `Ref<R, T>` is class 1 whatever it points to: what it points at lives in the region, not on loan.

Some types can hold a borrow without showing it: closures, continuations (`Cont`, §5.3), anything built from them (`Gen`), type parameters, and associated types until their base is known (`C.Slice`). A value of such a type is class 2 when it actually holds a borrow, so a closure capturing a `readonly` slice, or a generator iterating one, is class 2 although its type's arguments are all class 1.

A class-2 value may be a parameter, a local, or a return value tied to a parameter. It may not be stored in a class-1 value, captured by an escaping closure, sent to another task, or returned untied. That is the only restriction, and it is what replaces lifetime parameters. Two consequences are worth stating:

- **Containers hold first-class values.** A nominal type's type parameters range over class-1 types unless the type is a `view`: `Vec<String>` and `HashMap<String, u64>` are fine, `Vec<str>` is an error that suggests `Vec<String>`. Structural types (`Option`, `Result`, tuples, records) and views (`Gen`, `Scanner`) may hold borrows.
- **No borrow is stored through a borrow.** A `mut` borrow of a view may change its class-1 parts (`sc.pos += 1`) but cannot have a class-2 value written into it: a function that wrote its argument's borrow into a caller's `mut Option<mut T>` would keep that borrow alive after the call had released it. A local binding may still be reassigned (`s = b`), since its borrows are tracked where it lives.

**Results carry their sources' borrows.** A call's result can hold the borrows of its *sources*: the parameters named in its `from` clause; without one, the receiver for a method and every borrowed argument for a free function. Arguments whose types can hide a borrow — closures, generators, type parameters — are always sources. A result whose type cannot hold a borrow at all (class 1, with no closure, continuation or type parameter once instantiated) holds nothing. So `v.len()` holds nothing; `counts.getMut(key)` holds the borrow of `counts` but not of `key`; and `generate(() => v.each())` holds the borrow of `v` for as long as the generator lives.

```ts
function longer(a: str, b: str): str { if (a.len() >= b.len()) { a } else { b } }   // borrows a and b
function prefix(s: str, sep: str): str from s { … }                               // borrows only s
```

The body is checked against the same rule: everything the returned value borrows must come from a source, never from a local. Inside the body, a parameter whose type can hide a borrow carries a loan of its own, so a `from` that leaves out a type-parameter or closure argument the result actually contains is rejected there. A type parameter bounded by `Send`, directly or through an interface that extends it (`interface FromJson extends Send`), ranges over class-1 types and hides nothing: `parse<T extends FromJson>(text: str): T` returns a value its own parser decoded.

### 4.3 Closures

A closure captures each binding as its body needs it, by reference: a read takes a `readonly` borrow, a change a `mut` borrow. Passing a closure as an argument is lending it: in `xs.iter().filter((x) => x > min)` the closure borrows `min`, and the resulting generator carries that borrow (§4.2), so `min` may change again once the chain is collected. A closure that *escapes* — returned, or stored in a record, tag or list by the function that creates it — instead takes ownership of what it captures, by move, so it holds no borrows; it may own only `Send` values, so every first-class closure is `Send`. Function values are affine, like any owned value: moving one moves its captures, and dropping it drops them. Its mode follows from what its body does when called:

| Type | Body | Callable |
| :--- | :--- | :--- |
| `(A) => B` | only reads its captures | any number of times, concurrently |
| `mut (A) => B` | changes a capture, or calls a captured `mut` closure | many times, one caller at a time |
| `once (A) => B` | consumes a capture (moves it out), or calls a captured `once` closure | at most once |

So ``(path) => `${prefix}/${path}` `` returned from a function owns `prefix` and is an ordinary `(str) => String`. A closure that holds a borrow is class 2: it can be passed down but not returned or stored.

A function value is called through a borrow of it as well as directly, so a helper that passes its callback on lends it: `f: readonly (x: T) => void` may be given to two calls. The borrow must fit the mode: a shared function is called through any borrow, a `mut` one only through a `mut` borrow, and a `once` one only by moving it.

The mode is checked wherever a closure meets a function type — an argument, a binding, a returned value: a `mut` closure cannot go where a shared one is wanted (`par` would run it on many tasks at once), and a `once` closure only where `once` is. Library functions that call their closure from one place in sequence take `mut` closures (`Gen.map`, `Gen.filter`), so `xs.iter().map((x) => { total += x; x * 2 })` may count as it goes; `par` and `parReduce` take shared ones.

### 4.4 Marker interfaces

The compiler derives three marker interfaces from structure:

- **`Copy`**: bitwise copyable; no field owns a resource and the type has no `Drop`.
- **`Send`**: may move to another task, and `readonly T` may be shared with other tasks. `T` is `Send` when it is class 1 and owns no raw pointer or runtime handle (`Gen`, `Fiber`, `Scope`); a type parameter is `Send` when declared `extends Send`. Every function value is `Send`, since an escaping closure owns only `Send` values (§4.3); a closure that holds a borrow carries it as a loan, which a task cannot take (§6.1). Law 2 is what makes one marker enough: every mutation through a shared reference is an effect, and while tasks run no fiber may perform the effect that writes to an outer region (§6.1), so whatever a task can see through a `readonly` value or a `Ref` cannot change.
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

- `alloc(v)` places `v` in the region and returns a `Ref<R, T>`. A `Ref<R, T>` is used exactly as a `readonly T`: field access and method calls go through it, and reading is pure.
- The only mutable slots are `Cell<R, T>` with `T extends Copy`, whose `get` copies out and `set` copies in (a `Cell` is never borrowed), and `RegionList<R, T>`, an append-only chunked list whose elements never move. Both are handles into their region — `Copy`, like a `Ref` — and their writes are operations of `Region<R>`: mutation by effect, not by ownership. That is why `const items = RegionList.new(); items.push(x)` is legal.
- `alloc`, `Cell.get`, `Cell.set` and `RegionList.push` perform `Region<R>`. Reading a `RegionList`'s existing elements does not: they never change.

```ts
// std/region.d.fly
export struct Cell<region R, T extends Copy>;
export struct RegionList<region R, T>;
impl<region R, T extends Copy> Cell<R, T> {
  export function new(v: T): Cell<R, T> uses Region<R>;
  export function get(self: Self): T uses Region<R>;
  export function set(self: Self, v: T): void uses Region<R>;
}
impl<region R, T> RegionList<R, T> {
  export function new(): RegionList<R, T> uses Region<R>;
  export function push(self: Self, v: T): void uses Region<R>;
  export function len(self: Self): usize;
}
impl<region R, T> Iterable<readonly T> for RegionList<R, T> { … }
```

Two rules make this sound:

1. **No escape.** `R` may not occur in the type of the region expression, in any variable assigned from outside the block, or in an unhandled effect.
2. **No owned resources.** Region data contains only `Copy` values, `Ref`s, `Cell`s and `RegionList`s of the same region; this is checked wherever a value is placed in a region (`alloc`, `RegionList.push`). Nothing in a region needs a destructor, so releasing the arena is constant-time.

Because nothing in a region moves or is freed before the region ends, and the only mutation is copy-in to a `Cell` or append to a list, no borrow into region data can be invalidated. Because handlers are fiber-local, no task can perform another fiber's `Region<R>`, and while a scope's tasks run, neither can the scope's own body (§6.1): an outer region is frozen while it is shared, so every `Ref<R, T>` is `Send`.

**Region elision.** In a declaration or block with exactly one region in scope, every region-generic type written without its region argument takes that region: `Ref<T>`, `Cell<T>`, `RegionList<T>`, and user types such as `Json`. The rule applies recursively through type arguments.

```ts
enum Json<region R> {
  #Null, #Bool(bool), #Num(f64), #Str(Ref<str>),
  #Arr(RegionList<Ref<Json>>),
  #Obj(RegionList<{ key: Ref<str>; val: Ref<Json> }>),
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
  read(fd: Fd, buf: mut u8[]): Result<usize, IoErr>;
  write(fd: Fd, buf: readonly u8[]): Result<usize, IoErr>;
  now(): Instant;
  sleep(d: Duration): void;
  park(on: WaitKey): void;                       // the primitive under locks, channels, atomics and join
}
type IoErr = #Reset | #TimedOut | #BrokenPipe | #NotFound | #PermissionDenied;
```

These four are the standard effects. They are ordinary declarations; what makes them standard is only that the runtime installs root handlers for `Io` (and for the heap, which is not an effect).

**Operations have no effects of their own.** An operation's handler runs where the effect is handled, not where it was performed, so an operation cannot fail at its call site by itself; one that can fail returns a `Result`, and library code turns that into a `throw` where it is called (`Socket.read` is `Io.read(…).unwrap()`). Everything richer — scopes, channels, locks — is library code over these few operations and the runtime's scheduler, whose primitive for starting a task is internal to the standard library: a task can be started only through a scope.

A function's `uses` clause is a row of effects. A function with no `uses` clause is **pure**: it may allocate on the heap, open and use its own regions, and mutate its `mut` parameters, but it observes nothing and affects nothing outside its arguments and result. Higher-order functions are polymorphic in their callbacks' effects:

```ts
function map<T, U, row E>(xs: readonly T[], f: (x: readonly T) => U uses ...E): Vec<U> uses ...E
```

### 5.2 Handlers

`handle { body } with Eff { arms }` runs `body` and intercepts its `Eff` operations. Each arm has one of two forms:

- **Abortive** — `op(x) => armBody`. The body's frames are unwound first (running its `defer`s and destructors and releasing its borrows), then `armBody` runs and its value becomes the value of the `handle` expression. Because the body's borrows are released, the arm may use anything the body had borrowed.
- **Resumptive** — `op(x) resumes k => armBody`. The body stays suspended, holding its borrows, and `k` is the rest of the body as a value of type `Cont<A, B, E>`, where `A` is the operation's result type, `B` the `handle` expression's type and `E` the body's other effects.

The `handle` expression evaluates to the body's value if the body completes without performing `Eff`, and otherwise to the value of the arm that handled the operation. A resumptive arm usually produces that value by resuming: `k.resume(a)` itself evaluates to the `handle` expression's eventual value.

An arm runs in the context of the `handle` expression: its effects are those of the code around the `handle`. If the body's row is `Eff, ...E`, the `handle` expression's row is `...E` together with the arms' own effects.

### 5.3 Continuations

A `Cont<A, B, E>` is an affine value. It may be stored, moved and returned like any other.

- `k.resume(a)` consumes `k` and runs the suspended computation until it next performs the handled effect (when the arm runs again) or finishes. Its value is the `handle` expression's value from that point.
- Dropping `k` unwinds the suspended computation in place: its `defer`s and destructors run in reverse order, in-flight I/O is cancelled and drained (§6.3), and its stack segment is released.
- Handlers are **deep**: the handler stays installed beneath the suspended computation. Operations of other effects performed while `k` runs go to the handlers around the `resume` call, which is why `E` appears in `resume`'s type.
- A `Cont` holds every borrow its suspended computation holds: in a resumptive arm, `k` holds the borrows the body had taken when it performed the operation. A `Cont` holding a borrow is class 2 (§4.2), so a continuation can never outlive a borrow it holds, and the borrowed places stay locked while it lives.
- Continuations are one-shot. Resuming twice would duplicate owned values and live `mut` borrows.
- **Resuming re-enters.** `k.resume(a)` runs the rest of the body, which may perform the same operation again and re-enter an arm of the same handler. So, for ownership, `k.resume(a)` uses every binding from outside the `handle` that the body or any of its arms uses, in the strongest mode any of them does: an arm cannot hold a borrow of such a binding across `resume`.

### 5.4 Errors: `throw`, `try`, `catch`

`throw e` performs `Fail.raise(e)`. `try { body } catch (p) { handler }` is an abortive handler of `Fail`: it evaluates to the body's value, or binds the failure to `p` and evaluates to the handler's value.

Handling `Fail` **closes** its row: any open tail left in the body's failure union is set to empty, so `p` has exactly the type of what the body can throw, and a `match` on it can be checked for exhaustiveness. Since the error type is a tag union, `catch` is usually a `match`:

```ts
const port = try { parsePort(raw) } catch (e) {
  match (e) { #Empty => 80, #NotANumber | #OutOfRange(_) => throw #BadConfig }
};
```

To keep a failure as data, `Fail.capture(() => body)` returns `Result<T, E>`; `r.unwrap()` turns it back into a failure. There is no separate error-conversion machinery: failure rows compose by union (§3.2). Because they do, a tag means the same thing wherever it comes from: two libraries that both throw `#Unknown(String)` throw one tag. A library names its failures for what failed — `std/json` throws `#MissingField`, `#UnknownTag`, `#BadJson` — so that a caller's own `#Unknown` stays its own.

Tags are structural, so two libraries can use the same tag for different things (`#TimedOut(u32)` and `#TimedOut`) — and then a block calling both does not type-check, because one tag cannot carry two payloads. `Fail.map` wraps one call's failures, which both resolves the collision and records where an error came from:

```ts
const user = Fail.map(() => fetchUser(id), (e) => #Http(e));      // fails with #Http(HttpErr)
const row  = Fail.map(() => queryDb(sql), (e) => #Db(e));         // fails with #Db(DbErr)
```

It is library code: `try { f() } catch (e) { throw wrap(e) }`.

### 5.5 Iteration: `yield` and `for…of`

`yield e` performs `Yield.yield(e)`. A generator is any computation that uses `Yield<T>`; nothing else marks it.

`for (const x of e) { body }` handles `Yield` around a generator, running `body` for each item. If `e` is a generator call, it is the generator. Otherwise `e`'s type must implement `Iterable`, TypeScript's iteration protocol in Flyscript form, and the generator is `e.each()`:

```ts
interface Iterable<T, row E = []> {
  function each(self: readonly Self): void uses Yield<T>, ...E;
}
```

Slices, arrays, `Vec`, `String`'s lines, `HashMap`, `RegionList` and channels' receivers are all `Iterable`, so `for (const path of args)` needs no ceremony. Inside the loop:

- reaching the end of `body`, or `continue`, resumes the generator;
- `break` drops the continuation, so the generator unwinds and its cleanup runs, then the loop exits;
- `return` and an uncaught `throw` drop it in the same way before leaving.

```ts
function rows(db: readonly Db, sql: str): void uses Io, Fail<DbErr>, Yield<Row> {
  let cursor = db.open(sql);            // Drop closes the cursor
  while (cursor.hasNext()) { yield cursor.next(); }
}
```

**Iteration chains.** `xs.iter()` turns any `Iterable` into a `Gen`, and a `Gen` is itself `Iterable` and has the familiar lazy adaptors — `map`, `filter`, `take`, `zip`, `enumerate` — and `collect()`. Because a generator carries the borrows of its sources (§4.2), a chain over borrowed data needs no annotations:

```ts
for (const [x, y] of xs.iter().zip(ys.iter())) { total += x * y; }
const firstEvens = xs.iter().filter((x) => x % 2 == 0).take(10).collect();
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

`for…of` reads: it lends the collection `readonly` and yields `readonly` elements (copies, for `Copy` types). To update elements in place, iterate `xs.iterMut()`, which lends `xs` `mut` and yields `mut T` elements: `for (const x of xs.iterMut()) { x += 1; }`. The collection is locked while the loop holds its elements.

### 5.6 Cleanup: `defer` and `Drop`

`defer e;` schedules `e` to run when the enclosing block exits. `defer`s and the destructors of the block's owned locals share one stack and run in reverse order of the points at which they were registered, whether the block exits normally, by `return`, `break`, `throw`, an abortive handler, a dropped continuation, or cancellation.

Because a `defer` runs at the block's exit, it holds the borrows it needs from the point it is registered to the end of the block, including past a `return`: after `defer v.clear();`, `v` cannot be lent `readonly` or moved, so `return v[0..1]` is rejected. A `defer` may not move a binding declared outside its block. A destructor reads its whole value, which is why no field may be moved out of a type that implements `Drop` (§4.1).

### 5.7 Panics

Integer division by zero, overflow in checked builds (`wrappingAdd` and friends are explicit), an out-of-bounds index and heap exhaustion *panic*. A panic is not an effect and cannot be caught by a handler: it unwinds the current task, running cleanup, and fails the task's scope (§6.1); an unscoped panic terminates the process. Panics are for bugs; anticipated failure is `Fail`.

---

## 6. Concurrency and parallelism

### 6.1 Tasks and scopes

Concurrency is structured. `Io.scope((s) => body)` opens a scope, and a scope starts tasks in two ways:

```ts
function scope<T, X>(body: once (s: mut Scope<X>) => T uses Io, Fail<X>): T uses Io, Fail<X>;
interface Scope<X> {
  // Fire and forget: the task cannot fail, so it cannot cancel the scope.
  function spawn(self: mut Self, task: once () => void uses Io): void;
  // Work whose result or failure the scope waits for; its failures `X` are rethrown by the scope.
  function fork<T extends Send>(self: mut Self, task: once () => T uses Io, Fail<X>): Fiber<T>;
}
interface Fiber<T> {
  function join(self: Self): T uses Io;
}
```

The rules:

1. **A scope owns its tasks.** `Io.scope` returns only when every task started in it has finished. A `Fiber` is a handle to a forked task's result, not to the task: dropping it leaves the task running.
2. **Isolation is a type.** `spawn` accepts only a task whose effects are `Io`, which cannot fail. A server that must survive a bad connection spawns its connections, and the type checker proves they cannot take the scope down: a connection handler that let an error escape would not be accepted by `spawn`.
3. **Failure cancels the scope.** A forked task's failures `X` are rethrown by `Io.scope`. If a forked task fails, or any task panics, the scope is cancelled: the body and every other task stop at their next `Io` operation and unwind, and once all have finished the first failure is rethrown from `Io.scope` (or the panic continues). `join` therefore never fails by itself: it returns the result, or the joiner is cancelled along with the rest of the scope.
4. **A task performs only what its fiber can handle.** A task runs on a new fiber, where the only handlers are the runtime's `Io` and the scope's capture of failures, so its effects are `Io` and `Fail` and nothing else. It cannot allocate in its parent's region or perform an effect whose handler lives in the parent fiber.
5. **Outer regions are frozen while tasks run.** The body of a scope runs on the parent's fiber, but like its tasks it performs only `Io` and failures: it cannot write to a region outside the scope while tasks may be reading it, nor suspend to an outer handler that could. A task or the body may still open and use regions of its own, and anything else is done before or after the scope.
6. **Captures.** A task is a `once` closure. It may move in owned `Send` values and capture `readonly` borrows of `Send` values from outside the scope; the scope outlives every task, so the borrows are safe.

`scope`, `spawn`, `fork` and `join` are library code over the runtime's scheduler and `Io.park`; nursery semantics are not built into the language.

```ts
Io.scope((s) => {
  for (const conn of listener.accept()) {
    s.spawn(() => serveOne(conn, db));   // serveOne: (…) => void uses Io, so it cannot fail the scope
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

Parallel loops are library functions over pure closures (`std/par`):

```ts
interface ParSplit {
  type Slice;       // a splittable mutable view of a run of elements
  type View;        // a mutable view of one element
  type ReadView;    // a read-only view of one element
  function len(self: readonly Self): usize;
  function slice(self: mut Self): Self.Slice from self;
  function split(s: Self.Slice, at: usize): [Self.Slice, Self.Slice] from s;
  function viewAt(s: Self.Slice, i: usize): Self.View from s;
  function readAt(self: readonly Self, i: usize): Self.ReadView from self;
}
function par<C extends ParSplit>(c: mut C, f: (v: C.View, i: usize) => void): void;
function parReduce<C extends ParSplit, A extends Send>(
  c: readonly C, zero: A, one: (v: C.ReadView, i: usize) => A, both: (a: A, b: A) => A,
): A;
```

`par` borrows its container once into a `Slice` and divides it with `split`, which consumes a slice and returns two disjoint ones — the borrow rules prove them disjoint, so the halves can go to different workers — down to single elements, each lent to `f` by `viewAt`. `f` is shared, so it cannot change anything it captures, and has no effects: it cannot race. `parReduce` only reads, so its workers share the container `readonly` and read elements with `readAt`; `both` must be associative. Slices, arrays and `Vec`s split as `mut T[]`, with `View = mut T` and `ReadView = readonly T`; `Soa<T>` splits all its planes at once (§7.4). The elements go to different workers, so every impl requires them to be `Send`. The prototype runs the halves in order.

---

## 7. `comptime`

`comptime` is the metalanguage, and it is Flyscript: the compiler runs ordinary code, on a deterministic interpreter with a step budget and no effects, to compute types, choose code and repeat it. What users call stays typed and parametric; the computing happens inside.

### 7.1 Two kinds of type parameter

A type parameter is one of two kinds, and callers cannot tell them apart:

- **`<T>` is parametric.** The body is checked once, against `T`'s bounds, and works for every `T` that meets them. Almost all generic code is written this way.
- **`<comptime T: Type>` is a template parameter.** The function or impl is *specialized* for each type it is used at: its `comptime` code runs with `T` known, and the code that results is checked as if written by hand. `T` is inferred from the arguments like any other.

A template states its whole signature, effects included (none means pure), because its body is checked only per specialization. An error in a specialization points into the template and names the specialization: `no method 'toJson' on 'bool' (in 'toJson' for 'Flag')`. Specializations are memoized by template and types, and registered before their bodies are expanded, so a derivation over a recursive type refers to itself.

A `comptime function` runs only in the compiler: it is called from `comptime` code, never at run time. Module constants (`const SLOTS: usize = 64;`) are evaluated the same way. `Type` is a comptime-only type whose values are types.

A struct is a template too when it has a `comptime` type parameter or `comptime` code among its fields: its fields are computed for each instance, `comptime` statements in its body check its arguments, and two uses with the same arguments are the same type. Each instance is checked as the struct it is, so a template not declared `view` cannot hold a borrow in any instance:

```ts
struct Ring<T, comptime N: usize> {
  comptime assert(N > 0 && (N & (N - 1)) == 0, "capacity must be a power of two");
  buf: T[N];
  head: usize;
  tail: usize;
}
type ByteRing = Ring<u8, 1024>;

struct Partial<comptime T: Type> {                       // every field of T, made optional
  comptime for (const f of fieldsOf(T)) { [f.name]: Option<f.type>; }
}
```

### 7.2 Reflection and generated code

**Reflection.** `Type.info(T)` describes a type, and `Type.name(T)` names it; everything else is library code over these two. The prelude declares what `Type.info` returns:

```ts
type Field   = { name: str; type: Type };
type TagInfo = { name: str; payload: Option<Type> };   // the one type of #A(T), or the tuple or record
type TypeInfo =
  | #Int { signed: bool; bits: u8 } | #Float(u8) | #Bool | #Str | #Void | #Fn
  | #Record(Field[]) | #Tuple(Type[]) | #Union(TagInfo[])
  | #Struct { name: str; fields: Field[] } | #Enum { name: str; tags: TagInfo[] }
  | #Array { item: Type; len: usize } | #Slice(Type) | #Borrow { mutable: bool; type: Type }
  | #Opaque { name: str; args: Type[] };
```

A struct's private fields are visible to reflection only from its own module, or in a derivation it asked for (§7.3); elsewhere the struct is `#Opaque`.

**Generating code.** `comptime` before a construct runs it in the compiler and leaves code behind:

- `comptime if (c) { … } else { … }` and `comptime match (e) { … }` keep the branch the value selects. The others are never checked, so they may mention fields the type lacks.
- `comptime for (const x of xs) { … }` repeats its body once per element of a `comptime` list, with `x` a constant in each copy.
- `comptime e`, for any other expression, computes `e` and leaves its value: `comptime fields.len()`, `comptime panic("…")`, `comptime assert(…)`. `comptime` is a prefix operator, binding like TypeScript's `await`: `n > comptime (1 << bits) - 1`.

The same `comptime for`, `comptime if` and `comptime match` generate the items of a sequence: the fields of a record type, the entries of a record literal, the arms of a `match`, the items of a list literal (one per iteration). A `comptime` value used at run time becomes a literal, and a `Type` value can stand wherever a type does: `Option<f.type>`, `f.type.fromJson(p)`.

**Computed names.** `[e]` names something by a `comptime` string, as in TypeScript's computed keys: `v.[f.name]` reads a field, `{ [f.name]: x }` and `{ [f.name]: T; }` build records and record types, and `#[t.name](x)` builds or matches a tag. In a pattern, `comptime e` matches the value of `e`.

```ts
function sum<comptime T: Type>(v: readonly T): f64 {
  let total = 0.0;
  comptime for (const f of fieldsOf(T)) { total += v.[f.name]; }
  total
}
```

### 7.3 Derivation

A *derivation* is an impl with a template parameter. It lives with its interface, so the orphan rule is unchanged, and a type asks for it with an empty impl in its own module:

```ts
impl<comptime T: Type> Show for T { … }   // in Show's module: how to show anything visible
impl Show for Point;                       // in Point's module: Point asks for it
```

Types that belong to no module — primitives, records, tuples and tag unions — get a derivation directly whenever they have no impl of their own; the JSON derivation's `#Int { signed, bits }` arm decodes every integer width and checks its range, computed at compile time. The impl for a type is chosen in one step: specific impls first, by matching their heads against the type after expanding aliases, then the derivation. A specific impl whose head matches is the answer even if its bounds fail: `Option<T>` has its own JSON impl (the value or `null`), and an `Option` of something that cannot be encoded is an error, never quietly encoded as the union `{"Some": …}`.

A derivation requested by a struct may read and build its private fields: the author asked for it, where the type is declared. A type that keeps an invariant in a private field writes its impl by hand instead, calling its own constructor.

### 7.4 Layout as a library: `Soa<T>`

`Soa<T>` (`std/layout`) is a template struct that lays out a `T` with at least one field as planes — a `Vec` per scalar field, a nested `Soa` per struct field — with three template views: `SoaSlice<T>`, a `mut` slice of each plane; `SoaView<T>`, one element as a borrow of each field; and `SoaRead<T>`, its `readonly` counterpart:

```ts
export struct Soa<comptime T: Type> {
  comptime for (const f of fieldsOf(T)) {
    comptime if (nested(f.type)) { [f.name]: Soa<f.type>; } else { [f.name]: Vec<f.type>; }
  }
}

impl<comptime T: Type> ParSplit for Soa<T> {
  type Slice = SoaSlice<T>;
  type View = SoaView<T>;
  type ReadView = SoaRead<T>;
  function slice(self: mut Self): SoaSlice<T> from self {
    { comptime for (const f of fieldsOf(T)) { [f.name]: self.[f.name].slice(), } }
  }
  function split(s: SoaSlice<T>, at: usize): [SoaSlice<T>, SoaSlice<T>] from s { s.splitAt(at) }
  …
}
```

So `Soa<Particle>` stores planes `pos.x`, `pos.y`, `vel.x`, `vel.y` and `mass`, and in `par(mut ps, (p, _) => { p.pos.x += p.vel.x * dt; })` the closure's `p` is a `SoaView<Particle>` whose `p.pos.x` is a `mut f32` into its plane. No part of this needs `unsafe` or is known to the compiler.

### 7.5 A worked derivation: JSON

`std/json` is a JSON codec written in Flyscript. Encoding and decoding are two interfaces, so a value that borrows (`{ status: "ok", user: req.user }`) can be encoded without being decodable:

```ts
export interface ToJson { function toJson(self: readonly Self, out: mut String): void; }
export interface FromJson extends Send { function fromJson(p: mut JsonParser): Self uses Fail<JsonError>; }
export function stringify<T extends ToJson>(v: readonly T): String;
export function parse<T extends FromJson>(text: str): T uses Fail<JsonError>;
```

`String`, `Vec<T>` and `Option<T>` have impls written by hand. Everything else is one derivation per interface; this is the whole of the decoder for records and structs:

```ts
impl<comptime T: Type> FromJson for T {
  function fromJson(p: mut JsonParser): T uses Fail<JsonError> {
    comptime match (Type.info(T)) {
      #Record(fields) | #Struct { fields } => {
        let slots: { comptime for (const f of fields) { [f.name]: Option<f.type>; } } =
          { comptime for (const f of fields) { [f.name]: #None, } };
        p.beginObject();
        while (p.nextKey()) {
          const key = p.key();
          match (key.asStr()) {
            comptime for (const f of fields) {
              comptime f.name => { slots.[f.name] = #Some(f.type.fromJson(mut p)); },
            }
            _ => p.skip(),
          }
        }
        {
          comptime for (const f of fields) {
            [f.name]: match (slots.[f.name]) {
              #Some(v) => v,
              #None => comptime if (isOption(f.type)) { #None } else { throw #MissingField(String.fromStr(f.name)) },
            },
          }
        }
      }
      // … tuples, and tag unions as "Name" or { "Name": payload }
      _ => comptime panic(`${Type.name(T)} cannot be decoded from JSON`),
    }
  }
}
```

Keys may come in any order, unknown keys are skipped, and an `Option` field may be left out — decided per field at compile time by `isOption`, a four-line `comptime function`. Appendix A.9 uses it.

---

## 8. Modules, foreign code and targets

### 8.1 Modules

Each `.fly` file is an ES module. Declarations are private unless exported. A module-level `const` is evaluated at compile time (`const MAX_BUF: usize = 512;`). The import graph must be acyclic, so modules compile in parallel in dependency order.

A **declaration file**, `.d.fly`, states a module's interface without its implementation, as a TypeScript `.d.ts` file does. In a declaration file, a function or method ends with `;` instead of a body, and `struct Name<…>;` declares a type whose fields are hidden. The standard library is written this way; its bodies are the runtime's.

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
- **Scope.** A task's captures must be class 1 and `Send`, or `ro` borrows of `Send` values whose paths are not under `mut` in Γ. A spawned task's row is exactly `Io`; a forked task's row, and the scope body's, is `Io` and `Fail<X>`, where `X` is rethrown by the scope.
- **Effect rows.** Rows are label-sorted maps with an optional tail. For records a label occurs once and extension requires the tail to lack it; for tag unions labels merge and their payloads unify; for effects a label is an effect name with its region arguments, its other arguments are functions of the label, and extension by a present label is the identity. Handling `Fail` sets the open tail of its payload to the empty row.
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
  if (raw.len() < 16) { throw #Malformed; }
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
        const p = s.fork(() => db.fetchProfile(req.user));
        const q = s.fork(() => db.checkQuota(req.token));
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

Everything here follows from the rules above: the failure row of the `try` body is the union of `parse`'s, `read`'s, the forked tasks', `writeStatus`'s and `#Unauthorized`; `catch` closes that row, so `e`'s type is exactly that union; the `catch` arm may use `conn` because the body's borrow of it was released when the body unwound; and `serveOne` itself is `uses Io` only, so a server can `spawn` it (§6.1).

---

## 11. Implementation

The prototype compiler, `flyc`, implements this specification except code generation.

1. **Parse** each module into a syntax tree. Standard-library modules are declaration files and Flyscript modules (the prelude's derivations, `std/json`); either may leave out a body that the runtime provides.
2. **Expand** `comptime` code: a template is specialized when a call or a bound needs it, its body expanded with fresh positions in source order (each repeated copy is distinct code to the later passes) that map back to the template for diagnostics.
3. **Check types and effects** bidirectionally with one row unifier for records and tag unions; effect rows are checked by subsumption into the effects allowed at each point, with region arguments as part of an effect's label and `Fail` payloads compared by union inclusion. Region arguments are solved over the body, and an undetermined allocation goes to the innermost region it does not escape from.
4. **Check ownership** after typing: every value carries the loans it holds, loans flow through call results, patterns, assignments and captures, and a loan is live while any binding holding it may still be used, judged by reachability over the program's structure.
5. **Evaluate** directly, carrying each frame's type arguments so a call through a bound runs the impl for the type it stands for: abortive handlers unwind and tail-resumptive ones run where the effect is performed, so `for…of` over a generator captures no stack; a `Gen` pulled with `next()` runs on its own thread. `Io` is handled by a deterministic world (files, sockets, a database, a seeded fault schedule), which is what makes §6.4's simulation testing concrete.

A native compiler would add: **lower effects** by evidence passing (tail-resumptive handlers to direct calls, abortive `Fail` to two-register returns, stored continuations to stack switching), and **generate code** with Cranelift for debug builds and LLVM for release, emitting `noalias` and `readonly` from `mut` and `readonly`.

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

## Appendix: ten programs

These were written to test the design, not to show it off; each ends with what still feels awkward.

### A.1 JSON parser in a region

```ts
import { RegionList } from "std/region";

export enum Json<region R> {
  #Null, #Bool(bool), #Num(f64), #Str(Ref<str>),
  #Arr(RegionList<Ref<Json>>),
  #Obj(RegionList<{ key: Ref<str>; val: Ref<Json> }>),
}

view struct Scanner { src: readonly u8[]; pos: usize; }      // a view: it borrows the source

type JsonErr = #Eof | #Unexpected(usize) | #MalformedUtf8;

function isSpace(b: u8): bool { b == b' ' || b == b'\n' || b == b'\t' || b == b'\r' }

impl Scanner {
  function skipSpace(self: mut Self): void {
    while (self.pos < self.src.len() && isSpace(self.src[self.pos])) { self.pos += 1; }
  }
  function eat(self: mut Self, b: u8): bool {
    if (self.pos < self.src.len() && self.src[self.pos] == b) { self.pos += 1; true } else { false }
  }
  function expect(self: mut Self, word: str): void uses Fail<JsonErr> {
    for (const b of word.bytes()) { if (!self.eat(b)) { throw #Unexpected(self.pos); } }
  }
  function quoted(self: mut Self): readonly u8[] from self uses Fail<JsonErr> {
    self.pos += 1;
    const start = self.pos;
    while (self.pos < self.src.len() && self.src[self.pos] != b'"') { self.pos += 1; }
    if (self.pos >= self.src.len()) { throw #Eof; }
    self.pos += 1;
    self.src[start..self.pos - 1]
  }
}

function value<region R>(sc: mut Scanner): Ref<Json> uses Region<R>, Fail<JsonErr> {
  sc.skipSpace();
  if (sc.pos >= sc.src.len()) { throw #Eof; }
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

export function parseJson<region R>(text: str): Ref<Json> uses Region<R>, Fail<JsonErr> {
  let sc = Scanner { src: text.asBytes(), pos: 0 };
  value(mut sc)
}
```
*Awkward:* nothing serious. `Ref<…>` around each recursive node is the honest cost of region allocation; lists and slots are handles and need none.

### A.2 Word count

```ts
import { File, println } from "std/io";
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
    } catch (e) { println(`${path}: ${e}`); }
  }
  for (const [w, n] of counts.sortedByValue()) { println(`${n} ${w}`); }
}
```
*Awkward:* none. `${e}` works because tag unions derive `Show`.

### A.3 Generators and iteration chains

```ts
// A generator is any function that yields.
function runningSums(xs: readonly i64[]): void uses Yield<i64> {
  let sum: i64 = 0;
  for (const x of xs) { sum += x; yield sum; }
}

export function dot(xs: readonly f64[], ys: readonly f64[]): f64 {
  let total = 0.0;
  for (const [x, y] of xs.iter().zip(ys.iter())) { total += x * y; }
  total
}

export function firstSums(xs: readonly i64[], n: usize): Vec<i64> {
  generate(() => runningSums(xs)).take(n).collect()
}
```
*Awkward:* none. The chains borrow `xs` and `ys` for exactly as long as the generators live, with no annotations.

### A.4 Particles

```ts
import { par, parReduce } from "std/par";
import { Soa } from "std/layout";

export struct Vec2 { x: f32; y: f32; }
export struct Particle { pos: Vec2; vel: Vec2; mass: f32; }

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
  names: RegionList<{ name: Ref<str>; decl: Ref<Decl> }>;
}

impl<region R> Scope<R> {
  export function new(parent: Option<Ref<Scope>>): Ref<Scope> uses Region<R> {
    alloc({ parent, names: RegionList.new() })
  }
  export function define(self: readonly Self, name: Ref<str>): Ref<Decl> uses Region<R> {
    const d = alloc(Decl { name, ty: Cell.new(0), visiting: Cell.new(false) });
    self.names.push({ name, decl: d });
    d
  }
  export function lookup(self: readonly Self, name: str): Option<Ref<Decl>> {   // pure
    for (const b of self.names) { if (b.name == name) { return #Some(b.decl); } }
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
  for (const cmd of inbox) {
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
import { serveOne } from "./http_handler";

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

### A.9 Deriving JSON

```ts
import { ToJson, FromJson, JsonError, stringify, parse } from "std/json";

struct Signup { email: String; name: String; referrer: Option<String>; }
impl FromJson for Signup;

// Replies are structural tags: encoded with no declaration, each borrowing its reason only
// while `stringify` runs.
export function respond(body: str, nextId: u64): String {
  try {
    const s: Signup = parse(body);
    stringify(#Created { id: nextId, name: s.name })
  } catch (e) {
    match (e) {
      #MissingField(field) => stringify(#Rejected { reason: `missing ${field}` }),
      #BadJson(at) => stringify(#Rejected { reason: `not JSON at byte ${at}` }),
      _ => stringify(#Rejected { reason: "not a signup" }),
    }
  }
}
```
*Awkward:* none. The binding's type tells `parse` what to decode, and the failure arm sees exactly the errors decoding can raise.

### A.10 An inventory service

```ts
import { HashMap } from "std/collections";
import { ToJson, FromJson, JsonError, stringify, parse } from "std/json";

struct Item { sku: String; name: String; qty: u32; price: f64; }
impl ToJson for Item;
impl FromJson for Item;
impl Show for Item;
impl Clone for Item;

type Command =
  | #Add(Item)
  | #Remove { sku: String; qty: u32 }
  | #Get(String)
  | #Report;

type Problem = #Unknown(String) | #Short { sku: String; have: u32 } | #BadRequest(String);

export struct Store { items: HashMap<String, Item>; log: Vec<String>; }

impl Store {
  export function new(): Store { Store { items: HashMap.new(), log: Vec.new() } }

  export function apply(self: mut Self, cmd: Command): String uses Fail<Problem> {
    match (cmd) {
      #Add(item) => {
        self.log.push(`add ${item.sku}`);
        match (self.items.getMut(item.sku)) {
          #Some(existing) => { existing.qty += item.qty; },
          #None => { self.items.insert(item.sku.clone(), item); },
        }
        stringify({ ok: true })
      }
      #Remove { sku, qty } => {
        match (self.items.getMut(sku)) {
          #Some(it) => {
            if (it.qty < qty) { throw #Short { sku, have: it.qty }; }
            it.qty -= qty;
          },
          #None => throw #Unknown(sku),
        }
        self.log.push(`remove ${sku}`);
        stringify({ ok: true })
      }
      #Get(sku) => match (self.items.get(sku)) {
        #Some(it) => stringify(it),
        #None => throw #Unknown(sku),
      },
      #Report => {
        let total = 0.0;
        let count: u32 = 0;
        for (const it of self.items.values()) {
          total += it.price * (it.qty as f64);
          count += it.qty;
        }
        stringify({ items: count, value: total })
      }
    }
  }
}

export function handle(store: mut Store, body: str): String {
  try {
    const cmd: Command = parse(body);
    store.apply(cmd)
  } catch (e) {
    match (e) {
      #Unknown(sku) => stringify({ error: `no item ${sku}` }),
      #Short { sku, have } => stringify({ error: `only ${have} of ${sku}` }),
      _ => stringify({ error: "bad request" }),
    }
  }
}
```
*Awkward:* `self.items.insert(item.sku.clone(), item)` clones the key because the map owns it and `item` still holds it; a map keyed by a field of its values would need a different collection, not a different language.
