# Review: mechanized-ownership-proof

- spec: 83d6edcbb1cb
- request: b8c1e49622dcf044
- tokens: prompt 67748, cached 0, answer 3086

## Question

# Review request: is this mechanized ownership theorem meaningful, and is the planned claim honest?

Flyscript's spec (§9.4) lists guarantees of the core calculus λ-fly. I have just finished a Lean 4 proof (no sorry, standard axioms only) for an *ownership fragment*. Files attached: `Ownership.lean` (syntax, store, semantics `eval` with fuel, typing `Typed`/`Args`/`Lends`/`Exclusive`), `OwnershipSound.lean` (the theorem `eval_ok` by induction on fuel, and `program_ok`), `OwnershipExamples.lean` (a lending program typed and covered; an aliasing program shown stuck at runtime and rejected by the types).

`program_ok`: for `FnsOk F` and `Typed F [] e τ Γ'`, for every fuel n, `eval F n Store.empty [] e` is never `stuck`, and if it gives value v in store σ', there is L with `VT σ' τ v L` (v owns exactly cells L as a tree of its type) and `∀ l, σ'.mem l ≠ none ↔ l ∈ L` (nothing else allocated).

I plan to write in the spec §9.5: "Ownership is proved: a program that checks never gets stuck — it never reads a moved value, reaches a freed cell or frees one twice — and when it ends nothing is allocated but what its result owns: every other value was dropped exactly once. This is guarantee 2 for these terms, and guarantee 5's 'exactly once'." Plus a similar paragraph for an already-proved effects fragment (`Effects.lean`, not attached: deep resumptive/abortive handlers, try/throw; theorem: well-typed closed program never stuck, no unhandled operation).

Please attack:
1. Adequacy: can the semantics be "never stuck" for a bad reason? E.g., does `eval` silently tolerate a use-after-free, double free, or leak in some construct (so that `stuck` doesn't actually capture the error)? Is "no leak" really implied (e.g. could cells be leaked yet still counted in L)? Does `drop`/`dropCell` actually check for double free?
2. Typing vacuity: is `Typed` too restrictive in a way that makes the theorem uninteresting, or does it fail to reflect §4.2's actual rule for lends (several places at once, `Exclusive`)? Any missing case that the surface language allows and the fragment cannot express that matters for the claim's wording?
3. The planned spec wording: does it overclaim? What precise phrasing would you use? What should §12.3 list as still open (I plan: combining effects with ownership — unwinding that drops; loops, closures, generators, regions, tasks, unsafe; data-race freedom not mechanized)?
Be concrete and brief; rank findings by severity.

## Context files

- `proof/FlyCore/Ownership.lean`
- `proof/FlyCore/OwnershipSound.lean`
- `proof/FlyCore/OwnershipExamples.lean`

## Answer

### Verdicts

- **(1) Adequacy of `eval` and `program_ok`:** **Agree.** `eval`, `resolve`, `drop`, and `dropCell` are genuinely fail-stop: any use-after-move, use-after-free, or double-free returns `.stuck`. And because `Store.alloc` never reuses addresses (`σ.next + 1`), `∀ l, σ'.mem l ≠ none ↔ l ∈ L` together with `VT σ' τ v L` (which walks only the cells reachable from `v`) mathematically rules out both leaks and double-frees.
- **(2) Typing non-vacuity and fidelity to `§4.1`–`§4.2`:** **Disagree that this covers "these terms" of `§9.1`.** The fragment proves parameter-only lending (`call f owned lent`), which is the *easy* half of ownership. It omits the three hardest parts of Flyscript's actual ownership design: (a) local borrows and tied returns (`str from s`, `L` loan sets in `§4.1`–`§4.2`), (b) per-field disjoint borrows (`x.f` vs `x.g` in `§4.1`), and (c) branch/join move-merging (`if`/`match` where one branch moves and the other drops in `§9.2`).
- **(3) Planned `§9.5` and `§12.3` wording:** **Disagree with the proposed wording ("Ownership is proved... This is guarantee 2 for these terms").** It overclaims in two ways: `Ownership.lean` does not cover the `borrowᵘ π` or `if`/`match` terms of `§9.1`, and proving `Ownership.lean` and `Effects.lean` *separately* misses the core soundness interaction of Flyscript (`§5.2`–`§5.3`): **borrows held across effect suspension (`Cont`) and unwinding (`handle` / `try`)**.

---

### Problems

#### 1. The Planned Spec Claim Overstates What the Fragment Covers (`§4.1`, `§4.2`, `§9.1`–`§9.5`)

You plan to write in `§9.5`:
> *"Ownership is proved: a program that checks never gets stuck — it never reads a moved value, reaches a freed cell or frees one twice — and when it ends nothing is allocated but what its result owns: every other value was dropped exactly once. This is guarantee 2 for these terms, and guarantee 5's 'exactly once'."*

Look at the terms in `§9.1` and the rules in `§9.2`–`§9.3`:
- `§9.1` has first-class expression form `borrowᵘ π`, `let x = e in e` (where `x` can hold a borrow!), `if e then e else e`, and `match e { ... }`.
- `§9.2` has the judgment `Δ | Θ | Γ ⊢ e : τ / ε ⊣ Θ′ ; L`, where `Γ` is the live borrow ledger and `L` is the set of **loans** `e`'s value holds (`§4.1`–`§4.2`).

In `Ownership.lean`, none of `Γ` (live loans), `L` (returned/stored loans), `borrowᵘ π` as an expression, or `if`/`match` exist:
1. **No local borrow bindings or tied returns (`§4.1`–`§4.2`):**
   In Flyscript, a function can return a borrow tied to a parameter (`function pick(a: readonly Box<i32>, b: readonly Box<i32>): readonly i32 from a`), and a local `let r = pick(x, y);` holds a loan `{x : ro}` until `r`'s last use:
   ```ts
   function id(x: readonly Box<i32>): readonly i32 { x }
   export function main(): i32 {
     let x = Box.new(1);
     const r: readonly i32 = id(x);
     x = Box.new(2); // Must be rejected while `r` is still used below!
     r
   }
   ```
   `Ownership.lean` cannot express returning a borrow (`Fn.ret` is `Ty`, which has only `.int` and `.box τ`, no `Slot.ref`), nor `let r: readonly int = ...`, nor last-use loan expiration. In `Ownership.lean`, borrows exist *only* as call-site arguments (`lent : List (Mode × Place)`) that end when the call returns.
2. **No branch join / drop-on-unmoved-branch (`§4.1`, `§9.2`):**
   `§9.2` states: *"Where branches disagree, a path moved on any branch is moved where they meet, and the branches that did not move it drop it."* `Ownership.lean` is straight-line code (`seq`, `let_`, `call`) with no `if` or `match`.
3. **No field-disjoint borrows (`§4.1`, `§9.2`):**
   `Exclusive` in `Ownership.lean` is variable-granular (`a.2 = b.2 → a.1 = .ro ∧ b.1 = .ro`), whereas `§4.1` and `§9.2` lock paths *per field* (`x.f` vs `x.g`).
4. **Reassigning a moved variable (`§4.1`):**
   In `§4.1`: *"a moved-from binding is dead until it is assigned again."*
   In `Ownership.lean`, `PlaceTy.own` requires `lookup x Γ = some (.own τ true)`. So once `x` is moved (`live = false`), `assign (.var x) τ e` is rejected by `Typed.assign` (and at runtime `assign` calls `drop` on the old cell content, which would return `none` / `.stuck` on `.moved`!). That is fine for an SSA-like core, but worth noting.

**Fix for `§9.5` wording:**
Do not say *"Ownership is proved... This is guarantee 2 for these terms."* State accurately what each mechanized fragment covers so a PL reviewer reading both `§9.5` and `proof/FlyCore/` trusts the claim completely:

> ** mechanized fragments (`proof/FlyCore/`).** Two fragments of λ-fly are proved in Lean 4:
> - **Moves, drops and parameter borrows (`Ownership.lean`).** For straight-line code with heap boxes, moves, lexical drops, in-place mutation and `readonly`/`mut` parameter lending, a well-typed program never gets stuck — it never reads a moved value, reaches a freed cell, or frees one twice — and when it finishes, nothing remains allocated except the cells owned by its result (every other box was dropped exactly once).
> - **Effect handlers (`Effects.lean`).** For deep resumptive and abortive handlers, one-shot continuations and `Fail`, a well-typed closed program with no unhandled effects never gets stuck and performs no unhandled operation.

---

#### 2. The Most Important Open Soundness Question for `§12.3`: Combining Borrows with Resumptive Continuations (`§5.2`–`§5.3`)

Proving `Ownership.lean` (pure calls with parameter borrows) and `Effects.lean` (handlers without heap cells/borrows) separately leaves open the **single highest-risk soundness interaction in Flyscript**: what happens when a `handle` body holds a borrow (`mut` or `readonly`) across an effect operation!

Look at these two programs in surface Flyscript (`§5.2`–`§5.3`):

```ts
// Program A: Abortive arm or after-handle code accesses a place the suspended body lent `mut`
effect Pause { pause(): void; }

function touch(r: mut Box<i32>): void uses Pause {
  Pause.pause();
  r = Box.new(99); // Mutates and drops old Box after resume!
}

export function main(): i32 {
  let x = Box.new(1);
  let saved = handle {
    touch(mut x);
    #Done
  } with Pause {
    pause() resumes k => #Saved(k), // k escapes the handle block holding `mut x`!
  };
  // While `saved` holds `k`, `x` is still borrowed `mut` by the suspended `touch(mut x)` frame!
  const val: i32 = x; // MUST be rejected while `saved` is live; otherwise `k()` frees `x`!
  match (saved) { #Saved(k) => { k(); }, #Done => {} };
  val
}
```
And even without `k` escaping the `handle`:
```ts
// Program B: Inside a resumptive arm, accessing `x` before calling `k()`
export function main(): i32 {
  let x = Box.new(1);
  handle {
    touch(mut x);
  } with Pause {
    pause() resumes k => {
      x = Box.new(2); // MUST be rejected: `touch` is suspended holding `mut x` inside `k`!
      k()
    }
  };
  x
}
```
Neither `Ownership.lean` (no suspension) nor `Effects.lean` (no borrows/cells) tests or proves this invariant (`§5.3` bullets 4, 6, 7), nor does either prove that dropping an unresumed `k` (`§5.3` bullet 2) or unwinding to an abortive arm (`§5.2` bullet 1) drops every live owned cell in the suspended frames exactly once and releases their borrows.

**Fix for `§12.3` (Open Questions — Item 3):**
Put **the interaction of ownership and effects** (loans held by `Cont`, and unwinding that drops owned locals on abortive handling or `Cont` drop) at the very top of `§12.3` item 3, followed by **loan tracking for local/returned borrows (`L`) and branch joins**, regions (`Region<R>`), and concurrency (`Send` / data-race freedom).

---

### Answers to Your Specific Questions

1. **Adequacy of `eval`, `drop`, `dropCell`, and `program_ok`:**
   - **Can `eval` silently tolerate use-after-free, use-after-move, or double-free?** No.
     - *Use-after-move:* `.move x` sets `σ.mem c` to `some .moved`. Any subsequent `.read`, `.move`, `.write`, `.assign`, or `resolve (.deref (.var x))` pattern-matches on `σ.mem c` for `.int` or `.ptr` and hits `.stuck` on `.moved`.
     - *Use-after-free:* `drop` and `dropCell` set `σ.mem l` to `none`. Because `Store.alloc` strictly increments `σ.next`, a freed location `l` is never reallocated; any subsequent `resolve`, `read`, `write`, `assign`, or `drop` on `l` sees `none` and hits `.stuck`.
     - *Double-free:* `drop` on `.box τ` requires `σ.mem l = some w` and recursively drops `w` before setting `l` to `none`. If two pointers aliased the same box cell `l`, the second `drop` sees `σ.mem l = none` and returns `none`, which `eval` turns into `.stuck`.
     - *No leaks:* In `program_ok`, `VT σ' τ v L` is defined inductively on the type `τ` of the returned value `v` (`L = []` for `.int`, `L = l :: R` for `.box τ`), so `L` contains *only* the cells reachable from the return value `v`. And `∀ l, σ'.mem l ≠ none ↔ l ∈ L` proves that every other cell ever allocated during execution has `σ'.mem l = none` at termination. When `τ = .int` (as in `Examples.lends`), `VT σ' .int v L` forces `L = []`, so `∀ l, σ'.mem l = none`: literally every allocated cell was freed.

2. **Two minor observations in `Ownership.lean` (not bugs, but good to know if a reviewer asks):**
   - **Two-phase borrows (`§4.1`):** In `eval` for `.call f owned lent`, `owned` arguments are evaluated *first* (`evalArgs`), and `lent` places are resolved *after* (`lent.mapM (resolve σ1 env)`), and in `Typed.call`, `Lends Γ₁` checks the lent places in `Γ₁` (the context *after* `Args F Γ owned ... Γ₁`). That means `call f [move x] [(ro, var x)]` is rejected, and `call f [read (var x)] [(mut, var x)]` is accepted! That actually matches `§4.1`'s two-phase borrow rule for owned vs borrowed arguments nicely.
   - **Moving out of a box (`move` vs `Place`):** In `Ownership.lean`, `.move x` takes a `Var`, not a `Place` (so you cannot move a nested box `*x` out of an outer box `x: Box<Box<int>>`), whereas `.read`, `.write`, and `.assign` work on arbitrary `Place`s (`var` and `deref`). That matches `§4.1` (*"Nothing is moved out of a box by a pattern"* / `Box` owns its contents as a unit).
