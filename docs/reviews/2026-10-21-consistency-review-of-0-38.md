# Review: consistency-review-of-0-38

- spec: 8603484c18d2
- request: 15bef00b3339b804
- tokens: prompt 70543, cached 0, answer 5804

## Question

Spec 0.38 (included). Since your review of 0.34, 0.35 adopted your two blockers (results, yields and closure results may borrow only parameters that are themselves borrows; tasks started outside the body of their `Io.scope` cannot capture borrows). Then an adversarial audit of about 40 small programs found and closed more escapes: escaping closures capturing region data (0.36), tasks mutating what they borrow (0.36), destructors reading bindings declared after them (0.36), and a continuation not holding the loans its body needed across the perform point (0.37). 0.38 aligned `Io`'s types with §5.1.

This is meant to be the last review before freezing 1.0. Please do a **consistency** pass rather than a design pass:
1. **Contradictions between sections**: places where two sections state rules that cannot both hold, or where §0's five laws are no longer accurate given later sections.
2. **Examples that break the spec's own rules**: inline examples (not the appendix, which is machine-checked) that a checker implementing the rules as written would reject, or that rely on something never defined.
3. **Undefined or drifting terms**: names used in normative text without definition, or the same thing called two names.
4. Anything you would be embarrassed to see in a 1.0 language specification.

Be concrete: quote the text and give the fix.

## Context files

- `docs/spec.md`

## Answer

### Verdicts

- **Contradictions between sections (`§0`–`§9`)**: **Agree with changes.** Five concrete contradictions remain between the prose rules, grammar, and `§9` core calculus (listed in Problems 1–5).
- **Inline examples (`§2`–`§7`)**: **Agree with changes.** Three inline examples (`§5.5` `Step`, `§5.2` `handle` snippet, and `§7.1` `Partial`) violate the grammar or rules stated in the same document (Problems 1, 6, 7).
- **Undefined or drifting terms**: **Agree with changes.** A few terms (`Channel<T>` vs `Sender`/`Receiver`, `asStr()` not in `§3.1`, loans vs borrows, `Type` as a `Prim` vs comptime-only) drift across sections (Problems 8–9).
- **1.0 presentation & editorial polish**: **Agree with changes.** The stacked `--- | :--- |` changelog tables in `§0.1` render as broken Markdown tables, and one changelog entry from 0.30 directly contradicts the 0.31 entry right above it (Problem 10).

---

### Problems

#### 1. Grammar vs. `§5.5` inline code: record-payload tag fields use `,` instead of `;` (`§2.3`, `§5.5`)

In `§2.3`, a tag with a record payload uses `Record`, which requires semicolons `;` after each `Field`:
> ```ebnf
> Tag    = "#" Ident [ "(" Type { "," Type } ")" | Record ] ;
> Record = "{" { Field } [ "..." Ident ] "}" ;
> Field  = FieldName ":" Type ";" | Generate(Field) ;
> ```
Every other record-payload tag in the spec uses `;` (`#Put { key: String; val: String }` in `§3.2`, `#Int { signed: bool; bits: u8 }` in `§7.2`, `#Short { sku: String; have: u32 }` in `A.10`).
However, the inline definition of `Step` in `§5.5` writes a comma `,` instead of `;`:
```ts
// §5.5 (broken against §2.3 grammar):
view enum Step<T, row E> { #Done, #Item { item: T, rest: Cont<void, Step<T, E>, E> } }
```

**Fix:**
In `§5.5`, change `item: T, rest: …` to semicolons to match `§2.3`:
```ts
view enum Step<T, row E> { #Done, #Item { item: T; rest: Cont<void, Step<T, E>, E>; } }
```

---

#### 2. `§4.6` vs. `§9` Core Calculus: `region (R)` escape condition omits closures (`§4.6`, `§9`)

In `§4.6` (updated in 0.36):
> *"1. **No escape.** `R` may not occur in the type of the region expression, in any variable assigned from outside the block, or in an unhandled effect. A closure's type does not say what it captured, so a closure that escapes (§4.3) may not capture region data at all..."*

Now look at the **Region** rule in `§9` (Core calculus):
> $\frac{\Delta, \rho \mid \Theta \mid \Gamma \vdash e : \tau / \text{Region}\langle\rho\rangle, \varepsilon \vdash \Theta' \quad \rho \notin \text{ftv}(\tau, \Theta', \varepsilon)}{\Delta \mid \Theta \mid \Gamma \vdash \text{region}(\rho)\ \{ e \} : \tau / \varepsilon \vdash \Theta'}$

Because a closure's type $\tau = \texttt{() => f64}$ has $\text{ftv}(\tau) = \emptyset$, the formal rule in `§9` still says $\rho \notin \text{ftv}(\tau, \Theta', \varepsilon)$ is sufficient, contradicting `§4.6`!
```ts
function bad(): () => f64 {
  region (R) {
    const r = alloc({ x: 1.0 });
    () => r.x   // τ is `() => f64`, so R ∉ ftv(τ), passing §9's rule while failing §4.6
  }
}
```

**Fix:**
Update the **Class** or **Region** bullet in `§9` to match `§4.6`:
- In `§9` (**Class**): *"Stores into class-1 places, escaping captures (which also cannot hold region references), `Send`, and untied returns require class 1."*
- Or in `§9` (**Region**): add side condition *"and no closure escaping $e$ captures $\rho$"*.

---

#### 3. `§5.3` vs. `§9` Core Calculus: what is the class of `Cont<A, B, E>`? (`§0.1`, `§4.2`, `§5.3`, `§9`)

Three places in the spec say slightly different things about the class of `Cont`:
1. `§0.1` (0.31 changelog): *"`Step` is a `view enum` and `Cont` a view (§5.3, §5.5, §8.2)"*
2. `§4.2`: *"Some types can hold a borrow without showing it: closures and continuations (§5.3), anything built from them (`Gen`), type parameters, and associated types until their base is known (`C.Slice`). A value of such a type is class 2 when it actually holds a borrow..."*
3. `§9` (**Class**): *"A continuation's class is 2 if the frame it captures holds a class-2 value."*

Wait:
- Look at `§5.5`:
  ```ts
  view enum Step<T, row E> { #Done, #Item { item: T; rest: Cont<void, Step<T, E>, E>; } }
  view enum State<T, row E> { #Fresh(once () => Step<T, E> uses ...E), #Paused(Cont<void, Step<T, E>, E>) }
  export view struct Gen<T, row E> { state: Option<State<T, E>>; }
  ```
  Why did `Step`, `State`, and `Gen` have to be declared `view enum` / `view struct` in `§5.5`?
  Because in `§3.3`, *"A struct or enum that holds a borrow (§4.2) must say so: `view struct ...`"*, and `Cont` can hold a borrow! If `Cont`'s type were only class 2 when its frame dynamically held a borrow (`§9`), then `Step<T, E>` wouldn't always hold a class-2 type, or conversely, if `Cont` is unconditionally a `view` type (class 2 at the type level, as `§0.1` says: *"`Cont` a view"*), then `Vec<Cont<void, void, []>>` is forbidden by `§4.2` (*"A nominal type's type parameters range over class-1 types unless the type is a `view`"*).
- Also in `§9`: *"A continuation's class is 2 if the frame it captures holds a class-2 value."* Even dynamically, a continuation is class 2 when the suspended body borrows a **class-1** local from outside the `handle` (e.g., `v: Vec<i32>` lent to the body, or a handler arm that borrows an outer local `out`), not only when the frame holds a class-2 value!

**Fix:**
Align `§4.2`, `§5.3`, and `§9`:
- In `§5.3`, state explicitly whether `Cont<A, B, E>` is a `view` type (so any struct/enum storing a `Cont` must be `view`, as `Step`, `State`, and `Gen` are in `§5.5`).
- In `§9` (**Class**), replace *"if the frame it captures holds a class-2 value"* with *"if the suspended computation or its handler holds a borrow"*.

---

#### 4. `§3.3` vs. `§0.1`: recursive or out-of-order type aliases (`§0.1`, `§3.3`)

In `§0.1`, the 0.30 changelog block still contains an entry that was reversed in 0.31:
- **0.30 entry in `§0.1`**: *"Tags built where no type was expected become an enum another branch gives (§3.3) | `const e = match (t) { #Some(#Num(n)) => #Lit(n), #Some(#LParen) => inner, … }` did not join"*
- **0.31 entry right above it in `§0.1`**: *"Tags built where no type was expected are a union, never an enum, and the error says to annotate (§3.3) | 0.31 let one value be both a `Copy` union and an enum with a destructor"*

Having both in `§0.1` under *"Changes from 0.37"* (see Problem 10) is self-contradictory.

More importantly, look at `§3.3` on type aliases:
> *"A type alias names a structural type, so one that refers to itself is an error that says to declare an `enum` or a `struct`; aliases may otherwise refer to each other in any order."*

Wait: a type alias can also name a nominal type (`type ByteRing = Ring<u8, 1024>;` in `§7.1`)! And mutual recursion between two type aliases (`type A = #A(B); type B = #B(A);`) is an alias referring to itself *through another alias*.
```ts
type Even = #Zero | #Succ(Odd);
type Odd  = #One  | #Succ(Even); // Cycle through two aliases!
```
**Fix:**
In `§3.3`, change *"one that refers to itself"* to *"a cycle of type aliases is an error that says to declare an `enum` or a `struct`"* (and drop *"names a structural type, so"*, since `type ByteRing = Ring<u8, 1024>` in `§7.1` aliases a nominal struct).

---

#### 5. `§2.3` Grammar: `Contextual words` rule says `"region (Ident) {"`, but `Region` appears in `TypeParam` and `Impl` too (`§2.3`)

In `§2.3` under **Contextual words**:
> *"`from`, `of`, `with`, `resumes`, `row`, `view` and `private` are keywords only where the grammar expects them. `match`, `handle`, `region` and `effect` are keywords only when followed by `(…) {`, `{`, `(Ident) {` and `Ident` respectively..."*

Look at `TypeParam` in `§2.3`:
> ```ebnf
> TypeParam = "region" Ident | "row" Ident [ "=" Type ] | "comptime" Ident ":" Type ...
> ```
In `function parse<region R>(...)` (`§10.2`) and `enum Json<region R>` (`§4.6`), `region` is followed by `Ident` (`region R`), **not** `(Ident) {`!
If `region` were a keyword *only* when followed by `(Ident) {`, then `<region R>` would not lex `region` as a keyword unless `region` is also contextual in `TypeParam` (just like `row`).

**Fix:**
In `§2.3` (**Contextual words**), change:
> *"`match`, `handle`, `region` and `effect` are keywords only when followed by `(…) {`, `{`, `(Ident) {` (or `Ident` in `<…>`) and `Ident` respectively"*
(or move `region` in `<region R>` under the first sentence with `row`, and state that in expression/statement position `region` is a keyword only before `(Ident) {`).

---

#### 6. Inline example in `§5.2` uses `Log.info(m: String)` with a string literal `"..."` or `m` (`§5.2` vs `A.11`)

In `§5.2`:
```ts
effect Clock { now(): u64; }
const d = handle { limiter.check(client) } with Clock { now() resumes k => k(t) } with Log { info(m) resumes k => { out.push(m); k() } };
```
Look at the `with` clause order in `§5.2`:
- Two sentences earlier in `§5.2`, the spec states:
  > *"Further `with` clauses nest: `handle { body } with A { … } with B { … }` is `handle { handle { body } with A { … } } with B { … }`, so an arm of `A` may perform `B`."*
- And in `§5.3` (**Arguments are lent to the arm**):
  > *"So a parameter whose type can hold a borrow is usable in a resumptive arm only until the arm calls `k`, and never past the arm: it cannot be the arm's value, nor stored where the arm's end would leave it dangling."*
In `§5.2`'s snippet, `effect Log` is not declared above the snippet (unlike `effect Clock`), so the reader doesn't see whether `m` is `String` (as in `A.11`) or `str`. If a reader assumes `info(m: str)`, `out.push(m)` violates both `Vec<str>` (`§4.2`) and storing a borrowed op parameter (`§5.3`).

**Fix:**
Include `effect Log { info(msg: String): void; }` right next to `effect Clock { now(): u64; }` in the `§5.2` snippet (matching `A.11`).

---

#### 7. Inline examples in `§7.1`, `§7.2`, `§7.4` call `fieldsOf(T)` and `nested(f.type)` without defining them (`§7.1`, `§7.2`, `§7.4`)

In `§7.1`, `§7.2`, and `§7.4`:
```ts
struct Partial<comptime T: Type> {
  comptime for (const f of fieldsOf(T)) { [f.name]: Option<f.type>; }
}
```
Wait:
1. Where does `fieldsOf(T)` come from? `§7.2` says:
   > *"`Type.info(T)` describes a type, and `Type.name(T)` names it; everything else is library code over these two."*
   Neither `§7.2` nor `§3.1` says whether `fieldsOf` is in the prelude or `std/layout` or user code, nor is its 4-line definition shown.
2. Worse, look at `Partial<comptime T: Type>` in `§7.1` when `T` is a struct or record that has a field `f` whose type is ALREADY `Option<U>`: `Option<f.type>` is `Option<Option<U>>`, which is fine, **unless** `f.type` is class 2 (e.g., `T` is `{ name: str }`), in which case `Partial<{ name: str }>` is a non-`view` `struct` holding `Option<str>` (class 2)! And the sentence right above `Partial` in `§7.1` says:
   > *"Each instance is checked as the struct it is, so a template not declared `view` cannot hold a borrow in any instance"*
   That's consistent, just worth making sure `fieldsOf` is either defined in `§7.2` (it's 3 lines!) or listed as a prelude helper.

**Fix:**
Show the 3-line `comptime function fieldsOf(T: Type): readonly Field[]` in `§7.2` right after `TypeInfo`:
```ts
comptime function fieldsOf(T: Type): readonly Field[] {
  match (Type.info(T)) { #Record(fs) | #Struct { fields: fs } => fs, _ => comptime panic("not a record or struct") }
}
```
This simultaneously demonstrates `comptime function`, `Type.info`, pattern matching, and `comptime panic`, and makes the examples in `§7.1`, `§7.2`, and `§7.4` self-contained!

---

#### 8. Undefined or drifting method/type names across sections (`§3.1`, `§4.2`, `§4.5`, `§6.2`, `§7.5`)

1. **`String.asStr()` is used in `§0.1`, `§4.2`, `§5.3`, and `§7.5`, but is missing from `§3.1`!**
   Look at `§3.1` (**Methods**):
   > *"`str` has TypeScript's string methods — `slice`, `split`, `trim`, `includes`, `startsWith`, `endsWith`, `indexOf`, `toUpperCase`, `toLowerCase`, `replaceAll` — plus `toString`, `asBytes`, and the generators `bytes()` and `splitWhitespace()`; a `String` lends them all, and adds `push`."*
   Now check `§4.2` (`v[0].asStr()`, `s.asStr()`), `§5.3` (`line.asStr()`), and `§7.5` (`key.asStr()`): they all call `.asStr()` on a `String`! Yet `§3.1` doesn't list `asStr` on `String` (or `str`).
   **Fix:** Add `asStr` (and `clone`, or note `Clone`) to `String` in `§3.1` (and `slice()` on `Vec`/`T[N]`, which `§7.4` calls in `self.[f.name].slice()`!).

2. **`Option.take()` and `Option.unwrap()` / `Result.unwrap()` (`§5.1`, `§5.4`, `§5.5` vs. `§3.2`/`§3.4`):**
   - `§5.5` calls `self.state.take()` on an `Option<State<T, E>>`.
   - `§5.1` and `§5.4` call `.unwrap()` on a `Result<T, E>`.
   - `§3.4` mentions `Option.cloned` as an inherent method on `Option`, and `A.6` calls `store.get(key).cloned()`.
   None of `Option`'s or `Result`'s inherent methods (`take`, `unwrap`, `cloned`, `isSome`, `isNone`) are listed in `§3.2` where `Option<T>` and `Result<T, E>` are defined.
   **Fix:** Add one sentence at the end of `§3.2` (**Standard aliases**):
   > *"`Option<T>` has `isSome`, `isNone`, `unwrap`, `take` (replacing `#Some(v)` with `#None` through `mut`) and, over a borrow, `cloned`; `Result<T, E>` has `isOk`, `isErr` and `unwrap`, which throws the `#Err` payload."*

3. **`Channel<T>` vs. `Sender<T>` and `Receiver<T>` (`§4.5`, `§6.2`):**
   - `§4.5` table writes: *"shared state goes through `Mutex`, `Atomic` and `Channel`, which are `Io`"*
   - `§6.2` writes: *"`Mutex<T>`, `Atomic*` and `Channel<T>` are library types... `channel<T>()` gives a `Sender<T>` and a `Receiver<T>`."*
   There is no type `Channel<T>` in `§6.2` — the types are `Sender<T>` and `Receiver<T>`, created by `channel<T>()`.
   **Fix:** In `§4.5` and `§6.2`, write *"`Sender<T>` and `Receiver<T>` (from `channel<T>()`) "*.

4. **`Type` in `Prim` (`§2.3`, `§3.1`, `§7.1`):**
   - `§2.3` puts `"Type"` in `Prim`.
   - `§3.1` lists all the other `Prim`s and says *"All are `Copy`"*, without mentioning `Type`.
   - `§7.1` says *"`Type` is a comptime-only type whose values are types."*
   **Fix:** No grammar change needed; just note in `§7.1` that `Type` is `Copy`.

---

#### 9. Terminology drift: "borrow" vs. "loan" (`§4.1`, `§4.2`, `§4.4`, `§5.3`, `§11`)

In `§4.1` and most of `§4.2`, what a value holds is called a **borrow** (*"Every value carries the set of borrows it holds"*).
In `§0.1` (0.37), `§4.2` (last paragraph: *"carries a loan of its own"*), `§4.4` (*"carries it as a loan"*), and `§11` (*"every value carries the loans it holds, loans flow through call results..."*), the spec switches to calling it a **loan**.

**Fix:**
Either define *loan* once in `§4.1` (*"Every value carries the set of borrows (*loans*) it holds"*) or use *borrow* consistently in `§4.2`, `§4.4`, and `§11`. Defining *"borrows (or loans)"* parenthetically in `§4.1` is a 3-word fix that legitimizes both terms everywhere.

---

#### 10. `§0.1` Changelog formatting & leftover history before a 1.0 freeze (`§0.1`)

Look at `§0.1`:
1. Seven separate tables from versions 0.30 through 0.38 are concatenated together under the heading `### 0.1 Changes from 0.37`, separated by raw:
   ```markdown
   --- | :--- |
   ```
   In standard Markdown / CommonMark / GitHub Flavored Markdown, `--- | :--- |` without a preceding header row renders as literal text `--- | :--- |` or merges into one giant table with alignment syntax strings `---` and `:---` as visible cell contents!
2. As noted in Problem 4, the 0.30 block in `§0.1` contains an entry (*"Tags built where no type was expected become an enum another branch gives"*) that was explicitly repealed in the 0.31 block right above it (*"Tags built where no type was expected are a union, never an enum"*).
3. For a **1.0 specification**, having 9 versions of incremental prototype bug-fix changelogs at the very top of `§0` (before the reader even reaches `§1 Goals`) undermines the document's authority.

**Fix:**
For 1.0, either:
- Remove `§0.1` from the top of the spec (or move a clean summary to an appendix / release notes), **or**
- If you keep `§0.1` during the 0.38 → 1.0 transition, remove the contradicted 0.30 enum entry and replace the broken `--- | :--- |` separators with a single unified table (or proper subheadings).

---

### Smaller points

- **`§2.3` Grammar: `Expr` and `Unary` and `Unsafe` are not expanded (`§2.3`)**:
  `BlockLike` lists `If | IfConst | While | WhileConst | For | Match | Try | Region | Handle | Unsafe | Block | "comptime" ( If | Match | For )`, and defines productions for `Match`, `IfConst`, `WhileConst`, `For`, `Try`, `Region`, `Handle`, `Block` — but omits the EBNF lines for `If`, `While`, and `Unsafe` (`Unsafe = "unsafe" Block ;`). Adding those three one-line productions makes `BlockLike` complete.
- **`§2.3` Grammar: `Record` inside `PatAtom` vs `PatRecord` (`§2.3`, `§7.5`)**:
  In `§7.5`:
  ```ts
  #Record(fields) | #Struct { fields } =>
  ```
  Here `#Struct { fields }` is a tag pattern with a record payload that binds only `fields` (ignoring `name: str` in `#Struct { name: str; fields: Field[] }`). That works because `PatRecord` allows partial field matching (`"{" [ Ident [ ":" Pattern ] { "," Ident [ ":" Pattern ] } ] "}"`). Mentioning in `§3.2` or `§2.2` that record patterns `{ x }` may omit fields (ignoring the rest without needing `..`) makes it clear why `#Struct { fields }` is valid.
