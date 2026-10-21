# Review: selfhost-next-steps

- spec: b92450a5659d
- request: 9bcf904cfec27de7
- tokens: prompt 62668, cached 0, answer 9086

## Question

Flyscript (spec 0.53 in docs/spec.md) now has a self-hosted compiler in `selfhost/`, written in Flyscript, which compiles Flyscript to JavaScript and reaches a fixpoint: the compiler run by the Rust interpreter (`flyc run`) compiles its own source to `stage1.js`; `node stage1.js` compiles the same source to `stage2.js`; the two files are byte-identical (`selfhost/bootstrap.sh`, enforced by `tests/selfhost.rs`). It is ~2,300 lines of Flyscript (lexer 210, AST 108, parser 956, codegen 934, driver 124) plus a 590-line JS runtime. Attached: gen.fly, runtime.js and main.fly.

Design of the backend as it stands:
- No types. The selfhost compiler parses and generates code; it does not type-check. Everything type-dependent is decided at run time from the value: integers are BigInt and floats numbers, so `/` and arithmetic are JS operators; `==` is a structural `$rt.eq`; method calls go through `$rt.call(recv, name, ...)`, which finds the impl from `$t` (structs), `$tag` (tags: the enums declaring that tag name), or the JS type (strings, arrays, maps); `T.f()` is `$rt.st("T", "f")`.
- Strings are byte strings (one byte per JS char), so lengths and offsets are Flyscript's byte counts; files are read and written as latin1.
- `mut` arguments are `Ref` objects with a `v` getter/setter; a `mut` parameter is read as `x.v`. A method that replaces a string receiver (`push`, `clear`) is called through a ref to the receiver's place.
- `Box`, `Arc`, region `Ref` are the values themselves; `alloc` is identity.
- Functions whose `uses` row mentions `Yield` are `function*`; a call to one in statement position inside a generator is `yield*`; closures that contain `yield` are `function*`.
- `Fail` is JS exceptions (`$rt.Fail`), `try/catch` filters on it.
- Copy-struct semantics: a `let` or assignment whose right side is a place shallow-copies plain objects.
- Records typed as a struct by context (`alloc({ parent, names })` building a `Scope`) carry no `$t`; the runtime finds a struct with exactly those fields for dispatch.

Against the 44 programs of tests/run that need no simulated world, 13 pass. The failures fall into three groups:
1. Control effects: effect handlers (`handle … with E { op(x) resumes k => … }`, including continuations resumed later), tasks (`Io.scope`, `spawn`, channels, `Mutex`), timers. The compiler reports "handling `E` is not supported".
2. Types: integer widths (`wrappingAdd`, overflow checks), interface functions on type parameters (`T.zero()`), `collect()` into a type other than `Vec`, struct-typed records shown without their name, float vs int equality in derived `Eq`.
3. `comptime`: derives (`std/json`, `std/layout`, `Soa`) and reflection. The compiler parses comptime code and reports it unsupported.

Question: what should come next, in what order, to make this a high-quality self-hosted compiler for a high-quality language — not a demo? Specifically:
(a) Should the selfhost compiler get a type checker now, and how much of the Rust checker's job should it do (inference, generics and interface resolution, effect rows, ownership/borrows, regions)? Is a "types for codegen only" checker a reasonable intermediate, or a trap?
(b) For control effects on a JavaScript target: compile effectful functions as generators (`yield` an operation to the nearest handler, `yield*` through effectful calls), selecting which functions by their effect rows, and run tasks on a scheduler over generators? Or a CPS transform? How to handle effect-polymorphic higher-order functions (`map(f)` where `f` may perform anything) without compiling everything as a generator — two versions of each polymorphic function, or a selective CPS keyed on rows? Multi-shot continuations are not in the language (a `Cont` is resumed at most once), which generators can represent.
(c) `comptime`: should the selfhost compiler run comptime code by having its own evaluator (an interpreter for the checked AST), or should comptime be compiled to JS and run at compile time inside the compiler process (the compiler is itself JS after stage 1)? The second is attractive but the stage-0 compiler runs on the Rust interpreter.
(d) Is JavaScript the right target for the long run, versus C or WebAssembly, given the language is a systems language (ownership, regions, `@layout`, unboxed values)? What would you do with the JS backend once a native one exists?
(e) Anything in the attached backend design that is wrong in a way that will hurt later (representation choices, the string-as-bytes decision, dispatch by tag name, refs for `mut`)?

Be concrete and opinionated; rank the work.

## Context files

- `selfhost/gen.fly`
- `selfhost/runtime.js`
- `selfhost/main.fly`

## Answer

### Verdicts

- **(a) Type checker in `selfhost` now vs "types for codegen only":** **Disagree with "types for codegen only"; Agree with adding the real type + effect checker now (deferring only the ownership/borrow pass to last).** A half-checker is a trap because Flyscript's type inference, `comptime` expansion (`Type.info`), interface resolution, and effect rows are mutually dependent (`§3.2`, `§3.6`, `§7.1`).
- **(b) Control effects on JS:** **Agree with changes.** Compile functions whose inferred effect row contains any effect other than `Fail` (or an open row variable instantiated with one) to JS generators (`function*` / `yield*`), driven by a single trampoline in `$rt` that handles both user `handle` blocks and the `Io` / `SimIo` fiber scheduler. Because `comptime` and generics are monomorphized (`§2.1`, `§3.2`), effect-polymorphic HOFs (`map`) naturally specialize into direct or generator versions with zero CPS machinery.
- **(c) `comptime` evaluation in `selfhost`:** **Disagree with compiling `comptime` to JS `eval`; Agree with a small AST evaluator in `selfhost` (~350 lines).** Compiling `comptime` to JS breaks Stage 0 (`flyc run`), violates the deterministic step budget (`§7`), and requires marshaling JS values back into compiler AST/Type nodes anyway.
- **(d) Long-term target (JS vs C / Wasm / Native):** **Disagree with JS as the primary target; Agree with keeping JS as the permanent fast-bootstrap/SimIo/browser backend alongside a C (or Cranelift/Wasm) systems backend.**
- **(e) Current `selfhost` backend design (`gen.fly`, `runtime.js`):** **Agree with changes.** Five concrete representation bugs in `gen.fly` / `runtime.js` will break real programs right now and will hurt as soon as you scale past the current 13 tests.

---

### Ranked Order of Work

1. **Fix the 5 representation/scoping bugs in `gen.fly` and `runtime.js`** (Problems 1–5 below; ~100 lines of changes).
2. **Add the Type, Effect, and Interface Solver (`check.fly`) + Monomorphizer** (Problem 6; ~1,200 lines, modeled on `examples/mini`). This immediately fixes Group 2 failures (struct literals without `$t`, static calls `T.zero()`, integer widths, float `-0.0`/`NaN` equality, colliding method/tag names) and tells codegen exactly which functions have non-`Fail` effects.
3. **Add the `comptime` Expander & AST Evaluator (`comptime.fly`)** (Problem 7; ~400 lines). Runs interleaved with/before checking `check.fly`, unlocking Group 3 (`std/json`, `Soa<T>`, `Eq`/`Hash`/`Show`/`Clone` derivations).
4. **Lower Control Effects (`handle`, `Yield`, `Io`, `SimIo`) via Monomorphized JS Generators** (Problem 8; ~300 lines in `gen.fly` + `runtime.js`). Unlocks Group 1 (all 44+ tests, tasks, channels, `SimIo`).
5. **Port the Ownership, Borrow, and Region Escape Checker (`own.fly`)** (~500 lines). Once `selfhost` has steps 1–4 + `own.fly`, `selfhost` is feature-complete with the Rust prototype and `flyc` in Rust can be retired.

---

### Problems

#### 1. Untyped dispatch in `gen.fly` and `runtime.js` silently miscompiles colliding methods, tags, and struct shapes (`§3.3`, `§3.4`)

In `gen.fly` (lines 469–475), every impl method is emitted into a flat module scope as `${target}$${f.name}` and registered in `$rt.methods` by the bare type name:
```ts
// gen.fly:470
#Impl(target, iface, methods) => {
  for (const f of methods) {
    const js = `${target}$${f.name}`;
    g.function(js.asStr(), f);
    g.line(`$rt.method(${quote(target)}, ${quote(f.name)}, ${js});`);
  }
```
And in `runtime.js` (lines 52–77), `userTypes(v)` guesses the Flyscript type of a runtime value `v` from:
- `tagOwners.get(v.$tag)` (every enum in the entire program that happens to have a tag `#None` or `#Error`),
- `structsShaped(v)` (every struct in the program whose sorted field names match `Object.keys(v)`),
- `INTS = ["i64", "usize", ...]` (every integer type in arbitrary order!).

Here is a valid Flyscript program that breaks in three ways under this design:
```ts
// Module A and Module B (or even one module):
struct Meters { val: f64; }
struct Seconds { val: f64; }

impl Meters {
  function scale(self: readonly Self): f64 { self.val * 100.0 }
}
impl Seconds {
  function scale(self: readonly Self): f64 { self.val * 60.0 }
}

function makeSeconds(v: f64): Seconds {
  { val: v } // §2.2: builds nominal `Seconds` from expected return type; no `$t` emitted by `gen.fly`!
}

export function main(): void uses Io {
  const s = makeSeconds(2.0);
  // `s` has no `$t`. `structsShaped(s)` returns `["Meters", "Seconds"]`.
  // `find(s, "scale")` checks `userTypes(s)` in registration order and calls `Meters$scale(s)`!
  // Prints 200.0 instead of 120.0!
  println(`${s.scale()}`);
}
```
Even worse:
1. If two modules declare a private `struct Node` with `impl Node { function step(...) }`, both register `"Node"` in `$rt.methods`, overwriting each other!
2. If two enums share a tag name (e.g. `enum A { #Empty }` and `enum B { #Empty }`) and both implement a method or `Show`, `tagOwners.get("Empty")` returns `["A", "B"]` and calls `A`'s method on a `B` value!
3. If a struct has a field whose value is a closure, e.g. `struct Handler { len: () => usize; }`, `runtime.js:322` checks `builtinTable(v)` and `userTypes(v)` before checking if `name` is a closure field, or conversely for a record `{ map: (x: i32) => x }`, calling `r.map(1)` works only by accident while `{ eq: (x: i32) => x }.eq(1)` calls `ANY.eq` instead of the field `r.eq`!

**Fix:**
- Prefix struct/enum runtime names with their module index (`m${k}$Meters`) in `gen.fly`.
- Once the type checker (`Problem 6`) runs before `gen.fly`, **every call site knows the static type (or dictionary) of the callee**. `gen.fly` can emit direct JS function calls `m2$Seconds$scale(s)` instead of `$rt.call(s, "scale")`, and annotate record literals that construct a nominal `struct` with `$t` (or not even need `$t` at all!).

---

#### 2. Shallow `$rt.copy` in `gen.fly` / `runtime.js` corrupts nested `Copy` structs, fixed arrays `T[N]`, and mutates through `const` (`§3.1`, `§4.1`)

In `gen.fly` (lines 201 and 432), `Copy` semantics on assignment and `let` is approximated by calling `$rt.copy(v)` only when the RHS is syntactically `#Ident`, `#Field`, or `#Index`, and `runtime.js:230` defines:
```js
function copy(v) {
  if (typeof v === "object" && v !== null && !Array.isArray(v) && Object.getPrototypeOf(v) === Object.prototype) return { ...v };
  return v;
}
```
Look at what goes wrong in valid Flyscript:
```ts
struct Vec2 { x: i32; y: i32; }
struct Rect { min: Vec2; max: Vec2; } // Copy! (§4.4: all fields are Copy)

function id(r: Rect): Rect { r }

export function main(): void uses Io {
  let a = Rect { min: Vec2 { x: 0, y: 0 }, max: Vec2 { x: 10, y: 10 } };
  let b = a;           // `$rt.copy(a)` does `{ ...a }` — `b.min` and `a.min` are the SAME JS object!
  b.min.x = 99;        // Mutates `a.min.x` to 99!
  let c = id(a);       // RHS is `#Call`, so `gen.fly` doesn't even call `$rt.copy`!
  let arr: i32[2] = [1, 2]; // `i32[2]` is `Copy` (§3.1), represented as a JS Array.
  let arr2 = arr;      // `copy` ignores Arrays (`!Array.isArray(v)`), so `arr2` aliases `arr`!
  arr2[0] = 42;        // Mutates `arr[0]`!
  println(`${a.min.x} ${arr[0]}`); // Prints "99 42" instead of "0 1"!
}
```
And worse: when passing a `Copy` struct by value to a function `function foo(p: Vec2) { p.x = 5; }` (`§2.2`: *"Parameters bind like `let`. An owned parameter may be mutated"*), `gen.fly` does not copy arguments or parameters at all, so mutating parameter `p.x` mutates the caller's struct!

**Fix:**
1. In `runtime.js`, `copy(v)` must recursively copy plain objects (`{ ... }`), and once types are known (or by tagging fixed arrays `T[N]` vs `Vec<T>`), copy `T[N]`. Even without types, `copy(v)` recursively copying plain objects (`for (const k of Object.keys(v)) out[k] = copy(v[k])`) is 4 lines and immediately fixes nested `Copy` structs like `Rect` (`A.4`'s `Particle { pos: Vec2; vel: Vec2; mass: f32 }`!).
2. In `gen.fly`, copy arguments passed by value (or copy value parameters at function entry if mutated).

---

#### 3. Mutating methods on `self: mut Self` value structs and `self.field` places silently discard mutations (`§2.2`, `§4.1`)

Look at `gen.fly:460`:
```ts
const isRef = match (p.ty) { #Mut(_) => p.name != "self", _ => false };
```
`self` is **never** passed as a `Ref`, even when `self: mut Self`! Instead, `gen.fly:307` only passes a `Ref` for `WRITEBACK = ["push", "clear"]` (for `String`).
What happens when a user writes a method `function reset(self: mut Self) { self = Counter { n: 0 }; }` or when a `mut` borrow is taken of a field of a `mut` parameter (`mut x.field`)?
Even more importantly, look at `gen.fly:264`:
```ts
function place(self: mut Self, e: readonly Expr): String uses Fail<GenError> {
  match (e) {
    #Ident(n) => self.ident(n),
    #Field(t, name) => {
      const target = self.ex(t);
      `${target}.${name}`
    }
```
And `gen.fly:281`:
```ts
function lend(self: mut Self, e: readonly Expr): String uses Fail<GenError> {
  if (const #Ident(n) = e) {
    if (const #Some(l) = self.local(n)) { if (l.isRef) { return l.js; } }
  }
  const p = self.place(e);
  `$rt.ref(() => ${p}, ($v) => ${p} = $v)`
}
```
Look at what `lend` emits when `e` is `mut arr[f()]` or `mut obj.vec[i]`:
1. In `place(#Field(t, name))`, if `t` is not `simple` (e.g. `getObj(mut s).field += 1` or `mut s.items[i]`), `p` is interpolated **twice** in `$rt.ref(() => ${p}, ($v) => ${p} = $v)`: once in the getter and once in the setter! If `t` is a function call `getSlot(mut x).count`, `self.ex(t)` emits statements *outside* the closure or evaluates `t` multiple times!
2. In `O.take` (`runtime.js:301`):
   ```js
   take: (o) => { const old = { ...o }; o.$tag = "None"; delete o.$; return old; }
   ```
   `o.take()` mutates the option object `o` in place (`o.$tag = "None"`). That works ONLY because `#Some(x)` and `#None` are mutated in place on the same JS object reference — EXCEPT look at `runtime.js:24`:
   ```js
   const none = () => ({ $tag: "None" });
   ```
   Wait: when a struct field is initialized with `state: #None` (as in `Gen` in `§5.5`) and another variable copied that `#None` before `copy` was called (e.g. from `none()`), `none()` returns a fresh object, which is fine, **but** what if someone assigns `self.state = #Some(...)` and later calls `self.state.take()` while someone else did `const snap = self.state`? Because `O.take` mutates the `#Some` object in place instead of writing `#None` to the `Ref` of `self.state`, `snap` is silently mutated from `#Some` to `#None`!

**Fix:**
- Any method with `self: mut Self` on `String`, an enum (like `Option.take`), or a struct that assigns to `self` should take `self` as a `Ref` (or for enums/structs, `Option.take` should be in `WRITEBACK` and write `{ $tag: "None" }` to `r.v` instead of mutating `o.$tag` in place!). Putting `"take"` in `WRITEBACK` and defining `SW.take` / `OW.take: (r) => { const old = r.v; r.v = none(); return old; }` in `runtime.js` is a 3-line fix that prevents `Option.take()` from corrupting aliased options.
- In `place(e)`, if `t` in `#Field(t, name)` is not a bare local/ref, `self.save(self.ex(t))` into a temp `const $t = ...;` before building `${$t}.${name}` so the getter and setter in `$rt.ref` never re-evaluate `t`.

---

#### 4. `yield` inside `for…of`, `match`, `if`, or callbacks in `gen.fly` (`§5.2`, `§5.5`)

Look at `gen.fly:311` (`call`):
```ts
const yields = statement && self.inGenerator && self.world.genMethods.has(name);
return `${if (yields) { "yield* " } else { "" }}${callee}(${all.join(", ")})`;
```
Three bugs here:
1. **`self.world.genMethods` is a flat `HashSet<String>` of method names across the whole program (`gen.fly:90`)!**
   If *any* type in the program defines a generator method named `get` or `run` or `step`, then `self.world.genMethods.has("get")` is `true` for **every** method named `get` on **every** type in the program! Inside a generator function (`self.inGenerator == true`), a statement-level call `map.get(k);` or `sc.eat(b',');` (if any type had a generator `eat`) will emit `yield* $rt.call(map, "get", k)` and crash at runtime because `map.get(k)` does not return an iterator!
2. **`statement` is `true` only when `#Call` is a direct child of `into` (`gen.fly:419`)!**
   What if a generator function has a tail expression (in a block, `if`, or `match` arm) that calls another generator returning `void`?
   In `function words(line: str): void uses Yield<str> { otherWords(line) }`, `otherWords(line)` is the `tail` of `body`, so `blockInto` calls `self.into(t, #Return)` (`dest = #Return`, still via `into`, so `statement = true`), which emits `return yield* otherWords(line);` (valid JS).
   **Wait**: what if a generator calls an adaptor that takes a closure that yields, e.g., inside `for (const x of xs)`? That works because `for` is in the same function, **unless** a helper uses `Iterable.each`:
   Look at `runtime.js:353`: if a user defines `impl Iterable<i32> for MyList { function each(self: readonly Self): void uses Yield<i32> { ... } }`, and then runs `for (const x of myList)`, `gen.fly:389` emits `for (const $1 of $rt.iter(myList))`.
   And what does `runtime.js:104` `iter(v)` do?!
   ```js
   function iter(v) {
     if (Array.isArray(v) || v instanceof Gen || isIterator(v)) return v;
     if (v instanceof HashMap) return v.entries();
     if (v instanceof HashSet) return v.values();
     panic(`cannot iterate over ${show(v)}`);
   }
   ```
   `iter(v)` in `runtime.js` **never looks up `userMethod(t, "each")`!** Any user type implementing `Iterable` (such as `RegionList` or a custom collection) panics with `cannot iterate over ...` in `for (const x of v)` and has no `.iter()` method!

**Fix in `runtime.js` (4 lines):**
In `iter(v)`:
```js
for (const t of userTypes(v)) {
  const each = userMethod(t, "each");
  if (each !== undefined) return new Gen(each(v));
}
```
And in `ANY`:
```js
iter: (v) => new Gen(iter(v)),
```
That immediately makes `for (const x of customIterable)` and `customIterable.iter().map(...)` work for every user type implementing `Iterable`!

---

#### 5. String-as-latin1 (`runtime.js`) breaks UTF-8 string literals and `str` slicing on non-ASCII (`§3.1`)

You asked in **(e)** whether the string-as-bytes (one byte per JS UTF-16 code unit via latin1) decision will hurt later.
Let's check what happens right now when a `.fly` source file contains UTF-8 (for example, `A.8` in the spec has `Dom.text("−")` with U+2212 MINUS SIGN, and `tests/run` has `\u` escapes in `std/json.fly`):
- In `main.fly` / `runtime.js:368`:
  ```js
  fs.readFileSync(Buffer.from(path, "latin1").toString("utf8")).toString("latin1")
  ```
  Reading the file with `.toString("latin1")` turns every UTF-8 byte in the `.fly` source into one JS char `0x00..0xFF`. That's actually very clever for byte offsets (`s.length` == byte length, `s.charCodeAt(i)` == `u8` byte `i`), **EXCEPT**:
  1. Look at `runtime.js:285`:
     ```js
     toLowerCase: (s) => s.toLowerCase(),
     toUpperCase: (s) => s.toUpperCase(),
     ```
     On a latin1-decoded UTF-8 string, bytes `0xC0..0xFF` are UTF-8 continuation/leading bytes, **not** Latin-1 characters! Calling JS `.toLowerCase()` or `.toUpperCase()` on a latin1 string containing UTF-8 bytes corrupts multi-byte UTF-8 sequences (e.g., byte `0xC3` 'Ã' is lowercased by JS to `0xE3` 'ã', mangling the UTF-8 byte stream!).
     In Flyscript (`std/json` etc.), ASCII case conversion is what's expected unless Unicode tables are used; at minimum, `toLowerCase` / `toUpperCase` on byte-strings must either only transform ASCII `A-Z` / `a-z` or convert latin1 -> utf8 -> case -> latin1:
     `Buffer.from(Buffer.from(s, "latin1").toString("utf8").toLowerCase(), "utf8").toString("latin1")`.
  2. Look at `runtime.js:252`:
     ```js
     function slice(a, lo, hi) {
       const l = Number(lo), h = hi === undefined ? a.length : Number(hi);
       if (l > h || h > a.length) panic(`range ${l}..${h} out of bounds (length ${a.length})`);
       return a.slice(l, h);
     }
     ```
     `§3.1` says: *"`s[a..b]` on a `str` lends a `str`, and panics unless both bounds fall on character boundaries."*
     Checking UTF-8 character boundary in latin1 byte-string is 2 lines: a byte `b = s.charCodeAt(idx)` at `0 < idx < s.length` is a UTF-8 char boundary iff `(b & 0xC0) !== 0x80`! Adding that check makes latin1 byte-strings 100% faithful to `§3.1`.
  So the **latin1 1-byte-per-char representation is actually a great fit for JS** (O(1) byte indexing and slicing, exact UTF-8 byte semantics matching native code), provided you fix those two spots (`toLowerCase`/`toUpperCase` and the UTF-8 boundary check in `S.slice`).

---

#### 6. Question (a): Why "types for codegen only" is a trap, and what the checker in `selfhost` should do

You asked whether a "types for codegen only" pass is a reasonable intermediate step. **It is a trap.** Here is why:

Look at the Group 2 and Group 3 failures you listed:
1. `const s: Signup = parse(body);` (`A.9`) or `xs.iter().collect()` into a return type: the return type of `parse` / `collect` is a type variable solved by **bidirectional expected-type propagation** (`§3.6`) and row unification (`§3.2`).
2. `alloc({ parent, names })` returning `Ref<Scope>` (`A.5`): `{ parent, names }` knows it is a `Scope` (and not an anonymous structural record) **only** because `alloc`'s return type `Ref<R, T>` is unified with expected type `Ref<R, Scope>` *before* checking the argument `{ parent, names }` (`§3.6`).
3. `comptime match (Type.info(T))` (`§7.2`, `§7.5`): `std/json.fly` branches on whether a field's type is `#Struct`, `#Record`, `#Union`, `#Int { signed, bits }`, or `Option<U>`. It cannot even expand the AST of a function or struct without knowing exact types!
4. Effect rows (`§3.2`, `§5.2`): to compile effectful functions to JS generators (Question b) without compiling *every* function to a JS generator, you must know which functions have non-`Fail` effects — which is inferred over the call graph and row variables!

Notice what this means: **to generate correct code and expand `comptime`, you already need 100% of the type/row/interface checker (`§3`).**
What you do *not* need for code generation on a GC target like JS is **§4 (the borrow/move/region-escape checker)**!

Therefore, split the front-end work cleanly into two independent passes, just like `§11` and `examples/mini`:
- **Pass 1 (Now): Type, Row, Interface, and `comptime` Checker (`check.fly` + `comptime.fly`).**
  - Bidirectional type inference + the single Rémy row unifier (`§3.2`) for records, tag unions, and effect rows.
  - Monomorphization of generic functions, structs, and templates (`<T>` and `<comptime T: Type>`).
  - Why monomorphize in `selfhost` instead of dictionary passing?
    1. `§2.1` and `§3.2` specify monomorphization.
    2. Once `selfhost` monomorphizes `<T>`, **every type parameter `T`, static call `T.zero()`, method call `x.foo()`, integer width `u8`/`i32`, and effect row `...E` becomes concrete at every call site!**
    3. You can delete almost all of the dynamic type-guessing machinery in `runtime.js` (`structsShaped`, `tagOwners`, `userTypes`, `$rt.st`), emit direct JS calls, emit `BigInt.asIntN(32, a + b)` with overflow checks for `i32` (`§5.7`), and specialize HOFs (`map`) per effect row!
- **Pass 2 (After all tests pass): Ownership, Borrow, and Region Checker (`own.fly`).**
  - Because `own.fly` runs *after* typing (`§11` step 4) and produces only diagnostics (on JS, the GC handles memory and regions), you can bring up all 44+ runtime tests first and then port `own.fly` to reach full spec compliance.

---

#### 7. Question (c): How to implement `comptime` in `selfhost`

Do **not** compile `comptime` expressions to JS and run `eval()` / `new Function()` at compile time.
Why:
1. **Stage 0 (`flyc run` in Rust) cannot run JS `eval()`!** If `selfhost` uses JS `eval()` to expand `comptime`, Stage 0 (running `selfhost` inside the Rust interpreter) cannot compile any program that uses `comptime` (including `std/json` or prelude derivations), breaking your bootstrap chain (`flyc run selfhost -> stage1.js -> stage2.js`)!
2. Even in Stage 1 (`node`), `comptime` code operates heavily on `Type` (`Type.info(T)`, `Type.name(T)`, `f.type`) and produces AST fragments (`comptime if`, `comptime for`, `comptime match`, `[f.name]`). Marshaling compiler `Type` representations into JS runtime objects and back is more code than writing the AST evaluator.
3. `§7` requires a deterministic interpreter with a step budget (`comptime panic` on budget exhaustion or failure).

How small is a direct AST evaluator for `comptime` in Flyscript (`comptime.fly`)?
- `comptime` functions have **no effects** (`§7`), **no concurrency**, **no `handle`/continuations**, and **no `Io`**.
- They only evaluate: primitives (`i64`, `f64`, `bool`, `str`/`String`), `Type`, records/structs, tags/enums, tuples/arrays/`Vec`, control flow (`if`, `match`, `while`, `for`), closures (`fields.any(...)`), and the two built-ins `Type.info(T)` and `Type.name(T)`.
- In `examples/mini`, the compile-time evaluator is ~200 lines of Flyscript. In `selfhost`, an AST/bytecode evaluator over checked AST nodes with a `steps: usize` counter is ~350–400 lines of pure Flyscript that runs identically under Stage 0 (Rust `flyc`) and Stage 1/2 (Node).

---

#### 8. Question (b): Lowering Control Effects (`handle`, `Cont`, `Io.scope`, `SimIo`) to JS Generators

JavaScript `function*` generators are **one-shot stack-frame continuations** natively supported by V8. Because Flyscript continuations (`Cont<A, B, E>`) are strictly **one-shot** (`§1` Non-goal 3, `§5.3`) and handlers are **deep** (`§5.3`), JS generators map 1-to-1 to Flyscript effects with **no CPS transform**!

Here is the exact design:

**1. Which functions compile to `function*`?**
Once `check.fly` monomorphizes functions and infers concrete effect rows:
- A monomorphized function (or closure) is *suspending* iff its concrete `uses` row contains any effect other than `Fail` (i.e. `Yield<T>`, `Io`, or any user effect `Eff`).
  *(Note: `Region<R>` operations `alloc`, `Cell.get/set`, `RegionList.push` never suspend — they are handled by the built-in region arena and never by a user `handle` block (`§4.6`), so `Region<R>` does NOT make a function a generator! And `Fail<E>` uses JS `throw new $rt.Fail(e)`, which unwinds through `function*` frames and `try/finally` (`defer`) natively in JS!)*
- Every pure function, `Fail`-only function, and `Region`-only function compiles to a normal JS `function` with zero generator overhead.
- What about higher-order functions like `Vec.map` or `Gen.map`? Because generic functions are monomorphized per instantiation (`(T, U, E)`), `xs.map(pureFn)` instantiates `map` with `E = []` (a normal JS `function`), while `xs.map(clockFn)` instantiates `map` with `E = [Clock]` (a `function*` that calls `yield* f(x)`). No duplicate hand-written code, no dynamic checking!

**2. How `perform`, `handle`, and `Cont` work in 40 lines of `runtime.js`:**
When a suspending function performs an effect operation `Eff.op(a, b)`, `gen.fly` emits:
```js
(yield { $eff: "Eff", $op: "op", $args: [a, b] })
```
When a suspending function calls another suspending function `g(x)`, `gen.fly` emits:
```js
(yield* g(x))
```
Now look at how `$rt.handle(bodyGenFn, effName, arms)` works in `runtime.js`:
```js
// Runs a generator `it` under handler `arms` for `effName`.
// This is itself a generator so unhandled outer effects `yield` right through to outer handlers!
function* runHandle(it, effName, arms, sendVal, throwing) {
  let step = throwing ? it.throw(sendVal) : it.next(sendVal);
  while (!step.done) {
    const req = step.value;
    if (req.$eff === effName) {
      const arm = arms[req.$op];
      if (arm.abortive) {
        // Abortive arm (§5.2): unwind the suspended generator first (runs `finally` / `defer`s!)
        it.return();
        return yield* arm.fn(...req.$args);
      } else {
        // Resumptive arm (§5.2): build one-shot continuation `k`!
        let used = false;
        const k = function* (resumeVal) {
          if (used) panic("continuation resumed more than once");
          used = true;
          return yield* runHandle(it, effName, arms, resumeVal, false);
        };
        // Attach a cleanup method if `k` is dropped without being called (§5.3)
        k.$drop = () => { if (!used) { used = true; it.return(); } };
        return yield* arm.fn(...req.$args, k);
      }
    } else {
      // Forward outer effect to enclosing handler, and pass its answer back into `it`!
      try {
        const ans = yield req;
        step = it.next(ans);
      } catch (err) {
        step = it.throw(err);
      }
    }
  }
  return step.value;
}
```
Look at what those 28 lines of JS give you:
- **Deep handlers (`§5.3`):** `k(resumeVal)` recursively calls `runHandle(it, effName, arms, resumeVal, false)`, so the handler remains installed beneath `it`!
- **Storing and returning `k` (`Gen` in `§5.5`, coroutines, schedulers):** Because `it` is a JS generator object on the heap, returning `k` from the arm without calling it simply returns the closure `k` holding `it`! Calling `k()` later from `Gen.next()` resumes `it` from the exact `yield` point!
- **Abortive handlers & `defer` unwinding (`§5.2`, `§5.6`):** Calling `it.return()` in JS immediately executes every `finally` block (`defer`) inside the suspended `yield*` generator chain from innermost to outermost!
- **Outer effects (`§5.2`):** When `req.$eff !== effName`, `const ans = yield req;` yields the outer effect up to the enclosing `runHandle` (or root `Io` scheduler), and if that outer handler throws a `$rt.Fail`, `catch (err) { step = it.throw(err); }` injects the exception right back into the inner generator at the `yield` point!
- **Root `Io` and `Io.scope` (`§6.1`):** The root runner is just a work-queue of generator fibers handling `$eff === "Io"` (`sleep`, `park`, `scope`, `spawn`, `fork`). Because Node is single-threaded, `Io.scope`, `Mutex`, `channel`, and `SimIo` (§6.4) run deterministically over the exact same generator queue!

---

#### 9. Question (d): Long-term target architecture (JS vs C / Wasm / Native)

1. **Keep the JS backend permanently.**
   Even after a native backend exists, the JS backend is:
   - Your zero-dependency bootstrap seed (runs anywhere `node` or a browser exists).
   - The natural backend for browser targets (`A.8` `Dom<M>` effect).
   - A fast reference oracle for differential testing against the native backend.
2. **For the systems backend, target C (or Wasm + C) from the monomorphized, effect-lowered IR — before LLVM/Cranelift.**
   Why C next (before Cranelift/LLVM):
   - In `selfhost`, emitting C from the monomorphized AST takes ~1,000 lines of Flyscript (comparable to `gen.fly`), whereas binding LLVM/Cranelift requires either FFI bindings or a 20,000-line backend.
   - C gives you real unboxed structs, `@layout(c)` / `@layout(packed)`, bump-pointer `region` arenas (`malloc` slab + pointer bump), deterministic `Drop`, and native speed via `clang -O3`.
   - For effects in C: abortive `Fail` lowers to a two-value return `{ bool failed; union { T ok; E err; }; }`; tail-resumptive handlers (like `Clock.now` or `for…of` over a generator) inline or pass a function pointer in an evidence vector (`§11`); and only resumptive handlers that *capture* `Cont` (like `generate` and `Io` fibers) switch a small `ucontext` / assembly fiber stack.

---

### Smaller points

- **Integer overflow and widths in JS (`runtime.js`):**
  Once types are known in `gen.fly`, integer addition `a + b` at type `i32` can call `$rt.add_i32(a, b)` (which checks `const r = a + b; if (r < -0x80000000n || r > 0x7fffffffn) panic("integer overflow"); return r;`) while `a.wrappingAdd(b)` emits `BigInt.asIntN(32, a + b)`. That fixes the Group 2 integer-width failures cleanly.
- **Float equality in derived `Eq` (`§3.5`, `runtime.js:158`):**
  `§3.5` specifies: *"On floats, `Eq`, `Ord` and `Hash` are total... `NaN` equals itself and orders after every number, and `-0.0` equals and hashes as `0.0` (the primitive operators on floats stay IEEE 754)."*
  In `runtime.js:158`, `eq(a, b)` starts with `if (a === b) return true; if (typeof a !== "object" ...) return false;`. For `NaN`, `NaN === NaN` is `false` in JS, so `eq(NaN, NaN)` returns `false`! And in `compare(a, b)` (`runtime.js:186`), `NaN < 1.0` and `NaN > 1.0` are both `false`, so `compare(NaN, 1.0)` returns `0` (`#Equal`)!
  Fix in `runtime.js`:
  - In `eq(a, b)`: add `if (typeof a === "number" && typeof b === "number") return (Number.isNaN(a) && Number.isNaN(b)) || a === b;` (and keep primitive `==` on floats as `===` in `gen.fly` once typed).
  - In `compare(a, b)` for `"number"`: add `if (Number.isNaN(a)) return Number.isNaN(b) ? 0 : 1; if (Number.isNaN(b)) return -1;`.
  - In `HASHER.writeFloat`: normalize `-0.0` (`f === 0 ? 0 : f`) and `NaN`.
