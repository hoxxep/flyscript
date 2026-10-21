# Review: parsplit-for-library-soa

- spec: 4df670d1510b
- request: 8776a3ab338e7dad
- tokens: prompt 32282, cached 0, answer 3924

## Question

Focused design question on §6.5 `ParSplit`, which the spec (0.23, included) gives as:

```ts
interface ParSplit {
  type View; type ReadView;
  function len(self: readonly Self): usize;
  function split(self: mut Self, at: usize): [mut Self, mut Self] from self;
  function viewAt(self: mut Self, i: usize): Self.View from self;
  function readAt(self: readonly Self, i: usize): Self.ReadView from self;
}
```

Since your last review, template structs and associated types in impls work, and I am making `Soa<T>` library code:

```ts
export struct Soa<comptime T: Type> {
  comptime for (const f of fieldsOf(T)) {
    comptime match (Type.info(f.type)) {
      #Struct(_) | #Record(_) => { [f.name]: Soa<f.type>; }
      _ => { [f.name]: Vec<f.type>; }
    }
  }
}
export view struct SoaView<comptime T: Type> { /* mut f.type, or a nested SoaView */ }
```

The problem: `split(self: mut Self, at): [mut Self, mut Self]` works for a slice, but an owning `Soa<T>` (a record of `Vec`s) cannot be split into two `mut Soa<T>` halves — there is no such value. The built-in `Soa` hid this. Options I see:

1. **Halves are a view type** (Rayon's `Producer::split_at`): `type Part extends ParSplit; function split(self: Self.Part, at: usize): [Self.Part, Self.Part]; function part(self: mut Self): Self.Part from self;` — a slice's part is `mut T[]`, a `Soa`'s is `SoaSlice<T>` (a view struct of `mut f.type[]` planes). Sound, but every implementer writes two types.
2. **ParSplit is implemented by views only**: `par<C extends ParSplit>(c: C, f)` takes a view by value; `impl<T> ParSplit for mut T[]`, `impl ParSplit for SoaSlice<T>`; `split(self: Self, at): [Self, Self]` consumes the view. A caller writes `par(mut xs, f)` for a slice and `par(ps.slices(), f)` for a `Soa`. One type per implementer, but the call site for `Soa` changes and A.4's `par(mut ps, …)` loses its directness — unless an owner lends its view (`Soa<T>` lends `SoaSlice<T>` the way `Vec<T>` lends `T[]`), which is a new kind of lending.
3. **Drop `split`**: `par` takes views for a chunk of indices up front from `viewAt`. Unsound as stated, since `viewAt` borrows `self` exclusively.

Which is right for Flyscript — or is there a better shape? Give the interface text, how `Soa`'s impl reads, and what A.4 looks like. Keep it short: this is one decision.

## Answer

### Verdicts

- **Current `ParSplit` (`§6.5`)**: **Disagree.** It is unsound even for `T[]`: `split(self: mut T[], at)` returns `[mut (mut T[]), mut (mut T[])]` instead of `[mut T[], mut T[]]`, and `parReduce` (`readonly C`) cannot call `split(mut Self)` at all.
- **Option 1 (associated `Part`)**: **Disagree.** It duplicates the interface or requires two types per implementer (`Soa` + `SoaSlice`) just to convert an owner into a view once at the entry to `par`.
- **Option 2 (with a small change — separate `ParMut` and `ParRead` on view types, or an entry conversion)**: **Agree with changes.** If you separate the splittable view from the container — or even simpler, make `ParMut` and `ParRead` implemented by the *views* (`mut T[]` / `readonly T[]`, `SoaMut<T>` / `SoaRef<T>`) OR have the container produce its splittable slice once — you fix `parReduce`, fix `mut (mut T[])`, and write only **one** view type per mode.
- **Option 3 (drop `split`)**: **Disagree.** Calling `viewAt(mut self, i)` multiple times in parallel requires simultaneous `mut` borrows of `self`.

---

### Problems

#### 1. The current `ParSplit` is broken for `parReduce` and for `T[]` (`§6.5`)

Even before considering `Soa<T>`, look at how `ParSplit` in `§6.5` behaves on an ordinary slice `T[]`:

```ts
import { par, parReduce, ParSplit } from "std/par";

function brokenSlice(xs: readonly f32[]): f32 {
  // 1. `parReduce` takes `c: readonly C`.
  //    How can `parReduce` split `c` in parallel when `split` requires `self: mut Self`?!
  //    It can't! `parReduce` can only call `readAt(i)` sequentially or share `readonly C` without splitting!
  // 2. If `Self` is `T[]`, `split(self: mut Self, at): [mut Self, mut Self]`
  //     works only because `mut (T[])` is a slice.
  //    Wait: what is `Self` in `impl<T> ParSplit for T[]`?
  //    In Flyscript (§3.1), bare `T[]` is not a value type (`T[]` is always `readonly T[]` or `mut T[]`).
  //    If `Self = mut T[]`, then `mut Self` is `mut (mut T[])` — a borrow of a local slice header,
  //    which cannot return two sub-slices `[mut (mut T[]), mut (mut T[])]` because the new `{ ptr, len }`
  //    headers don't exist in memory to be borrowed!
  parReduce(xs, 0.0, (x, _) => x, (a, b) => a + b)
}
```
Notice why `split` on a slice returns two *by-value* class-2 views `[mut T[], mut T[]]`, **not** two borrows `[mut Self, mut Self]` of an existing place! A sub-slice creates a *new* `{ ptr, len }` descriptor on the stack that carries the borrow of the original; it is not a reference to an existing descriptor in memory.

And the exact same thing is true for `Soa<T>`: splitting a `Soa` at index `at` creates two new stack descriptors (`SoaSlice<T>`) of `{ ptr, len }` planes, carrying the borrow from the original `Soa<T>`.

---

#### 2. Why Option 1 and Option 2 can be combined without extra types or new lending rules

Look at what `Soa<T>` actually needs:
1. To run `par`, the worker tasks need a splittable mutable view of a range of elements: call it `SoaSlice<T>` (a `view struct` where each scalar field is `mut f.type[]` and each nested struct is `SoaSlice<f.type>`).
2. Wait: does `Soa<T>` need *both* `SoaSlice<T>` (a slice of elements) *and* `SoaView<T>` (a single element at index `i`)?
   Yes, because the closure `(p, i) => { p.pos.x += ... }` needs `p.pos.x` to be `mut f32`, not `mut f32[]`!
3. Now compare Option 1 and Option 2:
   - In **both** Option 1 and Option 2, `Soa` already has to define `Soa<T>` (the `Vec` planes), `SoaSlice<T>` (the `mut f.type[]` planes that `split` divides), and `SoaView<T>` (the single element `mut f.type` passed to `f`)!
   - Why? Because `Soa<T>` owns `Vec`s, `SoaSlice<T>` holds `mut T[]` slices (which `a[0..at]` and `a[at..]` can split!), and `SoaView<T>` holds `mut T` references (`a[i]`).
   - The **only** difference between Option 1 and Option 2 is how `par(mut ps, ...)` gets from `mut Soa<T>` to `SoaSlice<T>`!

Look at how Option 1 does that without duplicating `ParSplit`:
`par` does **not** need `Self` and `Self.Part` to implement two different interfaces, nor does `Self.Part` need its own `part()` method!
Wait: why did `par(mut ps, ...)` take `mut C` in the first place?
Because in `§6.5`:
- For `Vec<T>` or `T[N]`, `mut v` lends `mut T[]` at the call site (`§4.1`).
- For `Soa<T>`, `mut ps` is `mut Soa<T>`.
If `ParSplit` is the interface on the container/slice (`T[]` and `Soa<T>`), and its `Slice` associated type is the splittable view (`mut T[]` for `T[]`, `SoaSlice<T>` for `Soa<T>`), look what happens if `split` and `at` take `Self.Slice` by value:

```ts
export interface ParSplit {
  type Slice;      // splittable mutable range view (class 2)
  type View;       // single-element mutable view (class 2)
  type ReadView;   // single-element read-only view (class 2)

  function len(self: readonly Self): usize;
  function slice(self: mut Self): Self.Slice from self;
  function split(s: Self.Slice, at: usize): [Self.Slice, Self.Slice] from s;
  function viewAt(s: Self.Slice, i: usize): Self.View from s;
  function readAt(self: readonly Self, i: usize): Self.ReadView from self;
}
```

Check every property of this 5-method interface:
1. **No recursive `Part extends ParSplit` bound (`Option 1`'s flaw is gone!):** `Self.Slice` is just an associated type manipulated by `ParSplit`'s own static/value methods `slice`, `split`, and `viewAt`. You do **not** implement `ParSplit` a second time for `SoaSlice<T>`!
2. **Fixes `T[]` soundness too:** For `impl<T extends Send> ParSplit for T[]`, `type Slice = mut T[];`.
   - `slice(self: mut T[]): mut T[] from self { self }`
   - `split(s: mut T[], at: usize): [mut T[], mut T[]] from s { [s[0..at], s[at..]] }`
   - `viewAt(s: mut T[], i: usize): mut T from s { mut s[i] }`
   Notice there is no bogus `[mut Self, mut Self]` anywhere! `s` is consumed by value (`mut T[]` is affine, class 2) and split into two disjoint `mut T[]` slices tied to `s`!
3. **Fixes `parReduce`:** `parReduce` only reads (`readonly Self`). A `readonly Self` is `Copy` (`§4.1`), so `parReduce` doesn't need `split` at all — tasks share `c: readonly C` directly and call `c.readAt(i)` on disjoint index ranges!
4. **Preserves `A.4` verbatim:**
   - `par(mut ps, ...)` takes `c: mut C` where `C = Soa<Particle>`.
   - `parReduce(ps, ...)` takes `c: readonly C` where `C = Soa<Particle>`.
   - For a `Vec<T>` or `T[N]` or `T[]`, `par(mut xs, ...)` lends `mut T[]` (so `C = T[]`), and `parReduce(xs, ...)` lends `readonly T[]`.

---

### Concrete Spec Text (`§6.5`), `Soa<T>` Impl, and `A.4`

#### 1. Spec text for `§6.5 Data parallelism`

```ts
interface ParSplit {
  type Slice;       // a splittable mutable view of a range
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

*(Body prose for `§6.5`:)*
> `f` has no effects and receives a disjoint `mut` view of one element, so it cannot race; `par` borrows `c` into `c.slice()` and divides the work with `split`, which consumes a range view and returns two disjoint halves. `parReduce` shares `readonly C` across tasks and reads elements with `readAt`. For `T[]`, `Slice = mut T[]`, `View = mut T` and `ReadView = readonly T`; for `Soa<T>`, `Slice` is a record of plane slices and `View` and `ReadView` are records of field borrows (§7.4).

#### 2. How `Soa<T>`'s impl reads (`std/layout.fly`)

Because records can be class 2 (`§4.2`, `§7.4`), `SoaSlice<T>`, `SoaView<T>`, and `SoaRead<T>` don't even need nominal `view struct` declarations if written as `comptime` type functions returning structural records — or as template `view struct`s:

```ts
export struct Soa<comptime T: Type> {
  len: usize;
  comptime for (const f of fieldsOf(T)) {
    comptime match (Type.info(f.type)) {
      #Struct(_) | #Record(_) => { [f.name]: Soa<f.type>; }
      _                       => { [f.name]: Vec<f.type>; }
    }
  }
}

export view struct SoaSlice<comptime T: Type> {
  comptime for (const f of fieldsOf(T)) {
    comptime match (Type.info(f.type)) {
      #Struct(_) | #Record(_) => { [f.name]: SoaSlice<f.type>; }
      _                       => { [f.name]: mut f.type[]; }
    }
  }
}

comptime function ViewOf(T: Type): Type {
  {
    comptime for (const f of fieldsOf(T)) {
      comptime match (Type.info(f.type)) {
        #Struct(_) | #Record(_) => { [f.name]: ViewOf(f.type); }
        _                       => { [f.name]: mut f.type; }
      }
    }
  }
}

comptime function ReadViewOf(T: Type): Type {
  {
    comptime for (const f of fieldsOf(T)) {
      comptime match (Type.info(f.type)) {
        #Struct(_) | #Record(_) => { [f.name]: ReadViewOf(f.type); }
        _                       => { [f.name]: readonly f.type; }
      }
    }
  }
}

impl<comptime T: Type> ParSplit for Soa<T> {
  type Slice    = SoaSlice<T>;
  type View     = ViewOf(T);
  type ReadView = ReadViewOf(T);

  function len(self: readonly Self): usize { self.len }

  function slice(self: mut Self): SoaSlice<T> from self {
    SoaSlice<T> {
      comptime for (const f of fieldsOf(T)) {
        comptime match (Type.info(f.type)) {
          #Struct(_) | #Record(_) => { [f.name]: self.[f.name].slice(), }
          _                       => { [f.name]: self.[f.name][0..self.len], }
        }
      }
    }
  }

  function split(s: SoaSlice<T>, at: usize): [SoaSlice<T>, SoaSlice<T>] from s {
    let left: SoaSlice<T> = ...;   // or split each field into [l, r]
    ...
  }

  function viewAt(s: SoaSlice<T>, i: usize): ViewOf(T) from s {
    {
      comptime for (const f of fieldsOf(T)) {
        comptime match (Type.info(f.type)) {
          #Struct(_) | #Record(_) => { [f.name]: Soa<f.type>.viewAt(s.[f.name], i), }
          _                       => { [f.name]: mut s.[f.name][i], }
        }
      }
    }
  }

  function readAt(self: readonly Self, i: usize): ReadViewOf(T) from self {
    {
      comptime for (const f of fieldsOf(T)) {
        comptime match (Type.info(f.type)) {
          #Struct(_) | #Record(_) => { [f.name]: self.[f.name].readAt(i), }
          _                       => { [f.name]: self.[f.name][i], }
        }
      }
    }
  }
}
```
*(One tiny note on `split` inside `Soa<T>`: in `split(s: SoaSlice<T>, at: usize)`, each field `s.[f.name]` is `mut f.type[]` (which is affine, not `Copy`). Splitting a slice `s.[f.name]` into `[s.[f.name][0..at], s.[f.name][at..]]` moves or reborrows `s.[f.name]` twice if written in two loops `{ comptime for ... s.[f.name][0..at] }` and `{ comptime for ... s.[f.name][at..] }`! Make sure `xs.splitAt(at): [mut T[], mut T[]] from self` is a built-in slice method so `s.[f.name].splitAt(at)` consumes `s.[f.name]` once and returns the pair `[left, right]`!)*

#### 3. What `A.4` looks like

Unchanged to the character:

```ts
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
