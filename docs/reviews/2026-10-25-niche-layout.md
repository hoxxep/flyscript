# Review: niche-layout

- spec: 59a14d4917fb
- request: 84034b98d9029a0a
- tokens: prompt 60409, cached 0, answer 4498

## Question

# Niche layout for tag unions

Today every tag union (and enum) is `struct { [bool live;] uint32_t tag; union { payloads } u; }` in the C and LLVM back ends, with a tag's number the same in every union (so converting between two unions with the same tags — a narrowed union widened, a catch-all arm's binding — is a copy). Consequences, measured: `Option<Box<T>>` is 16 bytes, not 8; binary-trees' `#Leaf | #Node(Box<Tree>, Box<Tree>)` node is 24 bytes, which the allocator rounds to 32, where C's is 16; binary-trees holds 34 MB to C's and Rust's 18. Lists (`next: Option<Box<Node>>`) pay 8 bytes a link.

Proposal: a union is laid out in a *niche* when exactly one of its tags has a payload, and that payload has a pointer that is never null at a fixed offset (a `Box`, `Arc`, `Ref`, a borrow, a function value's code pointer; or a tuple, record or struct with one of those as a field, at the first such field), and its other tags are payloadless and number at most one. Then the union *is* its payload's representation, and the payloadless tag is that pointer being null: `Option<Box<T>>` is one pointer, the tree node is two. Tag tests become null tests, construction of the empty tag writes a null, the payload is the value itself. Rust does this for `Option<Box<T>>`/`Option<&T>` and more generally with invalid-value niches.

Scope of the change: the C back end's `unionType`, every place it reads a tag (`.tag`), builds a union value (`(T){ .tag = …, .u.X = … }`, including some thirty library routines' C that return `Option`s and `Result`s), takes a payload (`.u.X`), drops one, and converts between unions; the LLVM back end's own layout (it emits GEPs for tags and payloads from its own size/offset computation) and its debug info; the WebAssembly build comes through LLVM; JavaScript and the reference evaluator keep their object representation.

## Questions

1. Is the rule right and general enough? Should it extend to (a) several payloadless tags using small invalid pointer values (1, 2, …, below the first page), (b) a payload that is itself a niche union (nesting, `Option<Option<Box<T>>>`), (c) `String`/`Vec` (whose pointer may be null when empty in this runtime — or should the runtime guarantee non-null and gain the niche)?
2. Converting between unions with the same tags: one may be in a niche and the other not (`#Some(Box<T>) | #None` widened to `#Some(Box<T>) | #None | #Err(E)`). A conversion is then a tag test and a rebuild rather than a copy. Is that acceptable, or should the layout decision be per tag *set* to keep conversions copies where possible?
3. Anything that makes this unsound or costly in ways I'm missing: drop flags/`live` bytes for unions with `Drop`, state-machine frames that keep union values across suspension, channel messages copied as bytes, `@layout(c)` structs, the simulated world, unions compared by `Hash`/`Eq` through `match` (fine), pointers into a union's payload held across a write of the union (borrow rules forbid?).
4. Is it worth it, given the size of the change, versus other uses of the time?

## Answer

### Verdicts

- **Proposal (Niche layout for tag unions with 1 non-null-pointer payload tag + 1 payloadless tag):** **Agree with changes.** Keep the exact 1+1 non-null-pointer rule, **except** for two soundness/implementation fixes below: (1) do **not** use a nested struct/tuple field's pointer as a niche if the outer union (or any sibling field of that payload) has a `live` drop flag or requires `sizeOf<T>()` consistency without updating the runtime's representation, and (2) add `str` / `T[]` (with dangling non-null empty pointer, or don't include slices unless empty slices use `(T*)alignOf(T)`), while **excluding** multi-tag small integers (`1, 2, ...`), nested `Option<Option<Box<T>>>`, and `String`/`Vec`.
- **Q1(a) (Small invalid pointers `1, 2, ...` for multiple payloadless tags):** **Disagree.** Breaks on WebAssembly (`wasm32` linear memory has **no unmapped first page**: addresses `1, 2, ...` are valid heap/global/stack addresses in Wasm!) and breaks region/heap alignment assumptions.
- **Q1(b) (Nested `Option<Option<Box<T>>>`):** **Disagree.** Can't represent `#Some(#None)` vs `#None` with a single null value unless you use non-zero sentinel pointers, which breaks on Wasm (`wasm32` address `1` is valid).
- **Q1(c) (`String` / `Vec` non-null guarantee):** **Disagree for `String`/`Vec`; Caution on `str` / `T[]` too!** See Problem 2: in your runtime right now, is an empty slice `[][0..0]` or `""` or `Vec.new().asSlice()` guaranteed to have a non-null `.ptr`? If `Vec.new()` has `ptr == NULL`, then `Vec.new()[0..0]` has `slice.ptr == NULL`!
- **Q2 (Widening/narrowing conversions between niche and tagged unions):** **Agree** — a tag test + rebuild on structural union widening/narrowing is already required conceptually and only occurs at structural union coercion points.
- **Q3 / Q4 (Soundness traps & whether it is worth the blast radius):** **Disagree with changing general structural unions + 30 C runtime helpers if a narrower rule gets 95% of the win for 10% of the code.** See Problem 1 and Problem 3.

---

### Problems

#### 1. [Soundness Bug] `str`, `readonly T[]`, `mut T[]`, and `Cont` Are *Not* Non-Null Unless Empty Slices Never Have `ptr == NULL` (`§3.1`, `§4.1`)

Your proposal says:
> *"when exactly one of its tags has a payload, and that payload has a pointer that is never null at a fixed offset (a `Box`, `Arc`, `Ref`, a borrow, a function value's code pointer; or a tuple, record or struct with one of those as a field, at the first such field)"*

Wait: what does "a borrow" include in `§4.2`?
In `§4.2`, `readonly T` and `mut T` are single pointers, **and `str` and `T[]` are borrowed slices (`{ ptr, len }`)**.
Check what your runtime puts in `.ptr` for:
```ts
const v: Vec<i32> = Vec.new();
const s: Option<readonly i32[]> = #Some(v[0..0]);
```
1. When `v` is an empty `Vec<i32>` (`Vec.new()`), its buffer pointer is `NULL` (`0`)!
2. When you slice `v[0..0]`, the resulting slice `readonly i32[]` has `{ ptr = NULL, len = 0 }`!
3. If `Option<readonly i32[]>` uses `slice.ptr` as a niche, then **`#Some(v[0..0])` has `slice.ptr == NULL`, which immediately turns `#Some([])` into `#None`!**
4. Same for `String.new().asStr()` if an empty `String` has `ptr == NULL` and `.asStr()` copies `{ ptr, len }`!

**Fix:**
- A **single-object borrow** (`readonly T` where `T` is not `U[]`, and `mut T` where `T` is not `U[]`), `Box<T>`, `Arc<T>`, `Ref<R, T>`, and a closure (`Fn`, whose code pointer `.fn` is never null) **are** guaranteed non-null.
- `str` and `T[]` (`readonly T[]`, `mut T[]`), `String`, and `Vec<T>` are **NOT** guaranteed non-null unless you audit and change every empty `Vec`, `String`, array-of-length-0, and slice construction in both C and LLVM to use a non-null dangling pointer `(T*)align`. Do **not** include `str`, `T[]`, `String`, or `Vec<T>` in the niche rule!

---

#### 2. [Soundness Bug] Using a Field's Pointer as a Niche Inside a Struct/Tuple Payload Clobbers Drop Flags (`live`) and Breaks Partial Moves (`§4.1`, `§5.6`)

Trace what happens when the payload is a struct, tuple, or record containing a non-null pointer field, e.g.:
```ts
struct Pair { a: String; b: Box<i64>; }
```
or an enum with `Drop`:
```ts
enum List {
  #Nil,
  #Cons(Box<List>, String),
}
impl Drop for List {
  function drop(self: mut Self): void { ... }
}
```
Suppose `Option<Pair>` or `List` is given a niche layout using `b: Box<i64>` (or `Box<List>`) as the niche:
1. **What about `List`'s own `bool live` drop flag?**
   You noted at the start of your question:
   > *"Today every tag union (and enum) is `struct { [bool live;] uint32_t tag; union { payloads } u; }`"*
   If `List` implements `Drop` (or contains droppable fields), your C and LLVM backends track whether a local binding of type `List` is currently live (not moved-from) using the `.live` field on the struct/union, OR by zeroing `.live` when moved!
   - If `List` becomes *just* its payload `{ Box<List>, String }` (with no outer `struct { bool live; ... }` wrapper), **where does `List`'s `.live` flag live?**
   - Worse: what if you say *"when `List` is moved, set its niche pointer to NULL"*?
     Now **`#Nil` (whose niche pointer is NULL) and a moved-from `List` look identical (`niche == NULL`)**!
     If `List` implements `Drop`, `drop` **must** run on `#Nil` when a live variable holding `#Nil` goes out of scope (`§5.6`), and **must NOT** run when a moved-from variable goes out of scope!
     ```ts
     enum Guard { #Empty, #Full(Box<i64>) }
     impl Drop for Guard {
       function drop(self: mut Self): void {
         println("dropped!"); // MUST run for a live #Empty! MUST NOT run after move!
       }
     }
     ```
     If `#Empty` is represented as `ptr == NULL`, and moving a `Guard` sets `ptr = NULL` (or has no `live` bit), then either `#Empty` is never dropped (violating `§5.6`) or a moved `Guard` is dropped twice (violating `§9.4`)!
2. **What if the payload is `{ a: String, b: Box<i64> }` and `#None` only zeroes the niche pointer `b`, leaving `a`'s `.live` bit uninitialized on the stack?**
   In C/LLVM, if creating `#None` only writes `val.b = NULL` (or if a variable is reassigned from `#Some(pair)` to `#None`), what happens to `val.a.live`? If the drop glue for `Option<Pair>` checks the niche pointer (`val.b != NULL`) before dropping `val.a` and `val.b`, that works — **unless** someone partially moves `pair.b` out after pattern matching, or unless `Option<Pair>` itself has a `.live` flag!

**Fix:**
- **Never apply niche layout to an `enum` that implements `Drop` itself** (an `enum` with a user `Drop` impl needs its own `live` bit distinct from its payloadless tag `#Empty`!). A type whose drop glue merely drops its payload fields (like `Option<Box<T>>` or `Tree`) only drops when the tag is the payload tag (`ptr != NULL`), so `ptr == NULL` serves as **both** "is `#None`/`#Leaf`" and "has nothing to drop when moved"!
- Even simpler: when moving a niche-layout union (which has no user `Drop` impl), zeroing the niche pointer (`ptr = NULL`) makes its drop glue a no-op, **just like `#None`/`#Leaf`**, because dropping `#None`/`#Leaf` is also a no-op!

---

#### 3. [Blast Radius vs. Payoff] Why Touch 30 C Runtime Helpers and Structural Union Coercions When `Box` / `Ref` / `Arc` / Borrow Payloads Need Almost None?

Look at your statement of scope:
> *"including some thirty library routines' C that return `Option`s and `Result`s ... and converts between unions"*

Stop and check those 30 C runtime routines!
1. **Can `Result<T, E>` (`#Ok(T) | #Err(E)`) EVER be a niche union under your rule?**
   **No!** Unless `T` is `void` (so `#Ok` has no payload) and `E` is a `Box` (never true in `std`), or `E` is `void`! Every `Result<T, E>` in the runtime has payloads on `#Ok` or `#Err` (or `#Err(IoErr)` where `IoErr` has 7 tags!). So **zero** `Result` types in the C runtime qualify for niche layout!
2. **Which `Option<T>` types returned by the 30 C runtime routines actually have a non-null pointer payload?**
   Let's check what C runtime routines return `Option<T>`:
   - `Option<usize>`, `Option<i64>`, `Option<u8>` (`indexOf`, `find`, channel `recv` of generic `T`, etc.) → scalars, **not** niche!
   - `Option<String>`, `Option<Vec<T>>` (`File.readLine`, etc.) → `String` and `Vec` have nullable pointers (`NULL` when empty), so under Problem 1 they are **not** niche!
   - `HashMap.get` / `HashMap.getMut` (`Option<readonly V>` / `Option<mut V>`): these are Flyscript or C functions returning `Option<readonly V>` / `Option<mut V>` (a single pointer!).
3. And look at **structural union conversions** (Q2):
   Why would `#Some(Box<T>) | #None` ever be widened to `#Some(Box<T>) | #None | #Err(E)`?
   `Option<T>` is a 2-tag structural union (`#Some(T) | #None`), and `Tree` (`enum Tree { #Leaf, #Node(Box<Tree>, Box<Tree>) }`) is a **nominal `enum`** (`§3.3`: *"An enum is a type of its own and is not narrowed"* — enums never convert to/from other unions!).
   What if you restrict niche layout to:
   - **Payload types that are themselves a single non-null pointer (`Box<T>`, `Arc<T>`, `Ref<R, T>`, `readonly T`, `mut T`) or a tuple/record/struct of `Box`/`Arc`/`Ref`/borrows** (like `#Node(Box<Tree>, Box<Tree>)`)?
   Wait: if you restrict the payload to:
   1. A direct `Box<T>`, `Arc<T>`, `Ref<R, T>`, `readonly T` (non-slice), or `mut T` (non-slice) — where the entire union representation is literally a single pointer `T*` (8 bytes)!
   2. Or, in an `enum` (or union) without `Drop`, a tuple/record/struct whose **first field** at offset 0 is one of those non-null pointers (which covers `#Node(Box<Tree>, Box<Tree>)`, reducing it from 24 bytes to 16 bytes)!

Let's check what happens if you Require the non-null pointer to be **at offset 0** of the payload:
- For `Option<Box<T>>`, `Option<Ref<R, T>>`, `Option<Arc<T>>`, `Option<readonly T>`, `Option<mut T>`: offset is `0`, total size is **8 bytes** (1 pointer).
- For `enum Tree { #Leaf, #Node(Box<Tree>, Box<Tree>) }`: `Box<Tree>` is at offset `0`, total size is **16 bytes** (2 pointers).
- What about `struct Node { v: i64; next: Option<Box<Node>> }`?
  Here, `Option<Box<Node>>` is **already a field** of `Node`!
  Wait: `Node` itself is a `struct`, not a union! The union is the field `next: Option<Box<Node>>`!
  And in `Option<Box<Node>>`, the payload is `Box<Node>`, which **is** at offset 0 of `Option<Box<Node>>`!
  So `Option<Box<Node>>` is 8 bytes, and `struct Node { v: i64; next: Option<Box<Node>> }` is **16 bytes** (`i64` + `Box<Node>`) even if the niche must be at offset 0!
- And because in Flyscript's canonical record/struct layout (`§3.2`: *"Physical layout is canonical (by alignment, then name)"*), any 8-byte pointer field (`Box`, `Arc`, `Ref`, borrow) has the maximum alignment (8 bytes), it is **already placed at offset 0** unless another 8-byte field precedes it alphabetically!

---

#### 4. Answers to Your Four Questions

1. **Q1 (Rule & extensions):**
   - **(a) Multiple payloadless tags as `1, 2, ...`:** **No.** In `wasm32`, linear memory starts at address `0` and addresses `1, 2, ...` are valid addresses (no unmapped zero page in WebAssembly). Even `0` (NULL) is only safe in Wasm because LLVM/clang reserves address `0` by starting `__data_end` / the stack above `0` (make sure your `wasm32` linker flags pass `-Wl,--no-entry` with default non-zero base or `--global-base=1024`, which `wasm-ld` does by default!).
   - **(b) Nested `Option<Option<Box<T>>>`:** **No.** Without invalid non-zero pointers `1, 2, ...`, `Option<Option<Box<T>>>` has *two* empty states (`#None` and `#Some(#None)`) and only *one* null value (`0`). Because an inner `Option<Box<T>>` can be `NULL` (`#None`), an outer `Option<Option<Box<T>>>` **must not** treat `Option<Box<T>>` as non-null! Be sure your predicate `hasNonNullPointer(T)` returns **`false`** for any niche union `T`!
   - **(c) `String` / `Vec`:** **No.** Keep empty `String`/`Vec` non-allocating (`ptr == NULL`). And as noted in Problem 1, exclude `str` and `T[]` too, because slicing an empty `Vec` (`v[0..0]`) produces a slice with `ptr == NULL`.

2. **Q2 (Widening/narrowing conversions between unions):**
   - **Yes, tag test + rebuild is right.** A 2-tag structural union `#Some(Box<T>) | #None` is niche-laid-out (8 bytes); widening it to a 3-tag union `#Some(Box<T>) | #None | #Other` converts it to a tagged union `(tag, u)`. Since your C and LLVM backends already have an explicit union-conversion step when the source and destination union types differ, changing that step from `memcpy`/cast to `if (src_is_niche) ...` is completely local to union coercion.

3. **Q3 (Other soundness hazards to check):**
   - **`Drop` / `.live` flag (Problem 2):** Do **not** use niche layout for an `enum` that has a user `impl Drop`, because a moved-from value (`ptr == NULL`) would be indistinguishable from the live payloadless variant (`#Nil`, `ptr == NULL`), which must run `Drop.drop`! For types without a user `Drop` impl, moving the union simply zeroes the niche pointer (`ptr = NULL`), and dropping a union with `ptr == NULL` is a no-op in both the `#None` and moved-from states.
   - **`sizeOf<T>()` / `alignOf<T>()` (`§8.2`) and channels (`memcpy`):** In C and LLVM, if `Option<Box<T>>` has C type `struct Option_Box_T { Box_T payload; }` (8 bytes), then C `sizeof` and LLVM `sizeOf` automatically agree (8 bytes), and channel sends/receives (which copy `sizeof(T)` bytes) and state-machine frames work without change.
   - **Mutable borrow of payload then write to outer union:** Forbidden by `§4.1` (borrowing the payload inside `match (u) { #Some(b) => ... }` locks `u` against mutation or reassignment for the duration of the borrow).
   - **C backend representation tip:** Even for a niche union, wrap the payload in a 1-field C struct `typedef struct { Payload v; } UnionName;` rather than aliasing `typedef Payload UnionName;`. That keeps distinct C struct types for distinct unions, avoids C type-collision errors when two unions have the same payload type, and ensures passing by value has identical ABI.

4. **Q4 (Is it worth it?):**
   - **Yes, if you keep the rule strict:**
     - Exactly 2 tags: one with payload `P`, one with no payload (`void`).
     - Union is not an `enum` with a user `Drop` impl.
     - `P` has a non-null pointer (`Box<T>`, `Arc<T>`, `Ref<R, T>`, or non-slice `readonly T` / `mut T`, or `Fn`) at offset 0 (recursively through single-variant/struct/tuple fields at offset 0, **not** through another union!).
   - Under that strict rule, **almost no C runtime helpers change** (only `HashMap.get` / `getMut` if they are in C rather than Flyscript, because `Option<usize>`, `Option<String>`, and `Result<T, E>` are untouched!), `Option<Box<T>>` and `Option<readonly T>` become 8 bytes, and `Tree` (`#Leaf | #Node(Box<Tree>, Box<Tree>)`) becomes 16 bytes.
