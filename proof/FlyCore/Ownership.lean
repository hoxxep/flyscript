/-!
# Ownership and effects

λ-fly's core (spec §4, §5, §9): a heap of cells, owned boxes that are allocated and freed, moves,
drops at the end of a scope, assignment that drops what a place held, branches, loops, borrows —
`readonly` and `mut` — that exist only as parameters, so they cannot outlive what they borrow (§4.2),
and effects: failures and user effects, performed where the code is and handled where a `handle`
or a `try` installed a handler for them. A handler resumes the code that performed its operation,
the arm's value the operation's result, or ends its `handle` with the arm's value, the code that
performed it unwinding through the scopes and calls between. Handlers are deep, and an arm runs in
the context of its `handle`: what it performs goes to the handlers around the `handle`.

Every variable lives in a cell of the store; a box is a pointer to a cell holding its contents. A
borrowed parameter is bound to the location it borrows, not to a cell of its own. A value is an
integer, a pointer, or the mark a move leaves in a variable's cell. An arm that resumes may use
places of its `handle`'s scope, lent to it `readonly` or `mut` for as long as the `handle` runs.

The semantics is an interpreter with fuel, and anything no rule covers is `stuck`: reading a value
that was moved, reaching a cell that was freed, freeing one twice, performing an operation nothing
handles. The theorems are that a well-typed program never gets stuck, and that when it ends, with
a value or a failure, every cell it allocated has been freed but those of its result: each owned
value is dropped exactly once.
-/

namespace FlyCore.Ownership

inductive Mode where
  | ro
  | mut
  deriving DecidableEq, Repr

abbrev Var := String

/-- What a row may hold: `Fail`, or a user effect by number. -/
inductive Label where
  | fail
  | eff (n : Nat)
  /-- What no row holds: the barrier code is unwound to as it is dropped. -/
  | drop
  deriving DecidableEq, Repr

abbrev Row := List Label

/-- How a closure is called: once, consuming it; or through a borrow, `readonly` or `mut`, the
same borrow of what it captured lent to its body. -/
inductive Kind where
  | once
  | shared
  | excl
  deriving DecidableEq, Repr

mutual
inductive Ty where
  | int
  | box (τ : Ty)
  /-- A closure called as `k`, taking an `A` and giving a `B`, performing what `r` names: what it
  captured is not part of its type. -/
  | fn (k : Kind) (A B : Ty) (r : Row) (R : TyList)
  /-- Two values, each in a cell of its own: a record of two fields. -/
  | pair (A B : Ty)
  /-- A value of one type or the other, and which: a union of two tags. -/
  | sum (A B : Ty)
  /-- A place lent to a borrow: what holds it holds a `τ` there, but not for now. -/
  | hole (τ : Ty)
  /-- A reference into the region `k` regions out from here (`0` the innermost), to data of type
  `τ`, which is said of that region: its references count regions from there. -/
  | rref (c : Bool) (k : Nat) (τ : Ty)
  /-- The arena of the region `k` regions out from here. -/
  | arena (k : Nat)
  /-- A vector of `τ`s, each in a cell of its own: a `Vec`, which grows as it is pushed to, or, not
  `g`, a slice `τ[]`, a run of some vector's elements, which does not. -/
  | vec (g : Bool) (τ : Ty)
  /-- A continuation kept as a value: resumed with an `A`, it gives what its `handle` does, a `B`,
  performing what `r` names. -/
  | cont (A B : Ty) (r : Row)
  deriving DecidableEq, Repr

/-- The types of the places a closure's code is lent `readonly` when called: none, but for a
scope's task, the places its scope froze. -/
inductive TyList where
  | nil
  | cons (τ : Ty) (rest : TyList)
  deriving DecidableEq, Repr
end

def TyList.toList : TyList → List Ty
  | .nil => []
  | .cons τ rest => τ :: rest.toList

/-- Plain data: integers and boxes of them, which a closure may capture. -/
def Ty.data : Ty → Bool
  | .int => true
  | .box τ => τ.data
  | .fn _ _ _ _ _ => false
  | .pair A B => A.data && B.data
  | .sum A B => A.data && B.data
  | .hole _ => false
  | .rref _ _ _ => false
  | .arena _ => false
  | .vec _ _ => false
  | .cont _ _ _ => false

/-- A pair whose first field, or whose second, is lent. -/
def Ty.lent1 (t : Bool) (A B : Ty) : Ty := if t then .pair (.hole A) B else .pair A (.hole B)

/-- A type with no place lent out of it. -/
def Ty.complete : Ty → Bool
  | .int => true
  | .box τ => τ.complete
  | .fn _ _ _ _ _ => true
  | .pair A B => A.complete && B.complete
  | .sum A B => A.complete && B.complete
  | .hole _ => false
  | .rref _ _ _ => true
  | .arena _ => false
  | .vec _ τ => τ.complete
  | .cont _ _ _ => true

/-- What a borrow may be of: a value with no place lent out of it, or a region's arena. -/
def Ty.whole : Ty → Bool
  | .arena _ => true
  | τ => τ.complete

theorem Ty.complete_whole {τ : Ty} (h : τ.complete = true) : τ.whole = true := by
  cases τ <;> simp_all [Ty.whole, Ty.complete]

def Ty.isHole : Ty → Bool
  | .hole _ => true
  | _ => false

/-- Plain data has no place lent out of it. -/
theorem Ty.data_complete : ∀ {τ : Ty}, τ.data = true → τ.complete = true
  | .int, _ => rfl
  | .box τ, h => by simp only [Ty.data] at h; simp only [Ty.complete]; exact Ty.data_complete h
  | .fn _ _ _ _ _, h => by simp [Ty.data] at h
  | .pair A B, h => by
    simp only [Ty.data, Bool.and_eq_true] at h
    simp only [Ty.complete, Bool.and_eq_true]; exact ⟨Ty.data_complete h.1, Ty.data_complete h.2⟩
  | .sum A B, h => by
    simp only [Ty.data, Bool.and_eq_true] at h
    simp only [Ty.complete, Bool.and_eq_true]; exact ⟨Ty.data_complete h.1, Ty.data_complete h.2⟩
  | .hole _, h => by simp [Ty.data] at h
  | .rref _ _ _, h => by simp [Ty.data] at h
  | .arena _, h => by simp [Ty.data] at h
  | .vec _ _, h => by simp [Ty.data] at h
  | .cont _ _ _, h => by simp [Ty.data] at h

theorem Ty.complete_ite {t : Bool} {A B : Ty} (hA : A.complete = true) (hB : B.complete = true) :
    (if t then A else B).complete = true := by
  cases t <;> simpa

theorem Ty.complete_not_hole {τ : Ty} (h : τ.complete = true) : τ.isHole = false := by
  cases τ <;> simp_all [Ty.complete, Ty.isHole]

theorem Ty.lent1_complete : (Ty.lent1 t A B).complete = false := by
  cases t <;> simp [Ty.lent1, Ty.complete]

theorem Ty.whole_not_hole {τ : Ty} (h : τ.whole = true) : τ.isHole = false := by
  cases τ <;> simp_all [Ty.whole, Ty.complete, Ty.isHole]

theorem Ty.lent1_whole : (Ty.lent1 t A B).whole = false := by
  cases t <;> simp [Ty.lent1, Ty.whole, Ty.complete]


theorem Ty.lent1_isHole : (Ty.lent1 t A B).isHole = false := by
  cases t <;> rfl

/-- A type whose `mut` borrow is a shell, which may change what it holds but not its own first cell:
a closure, which may be called, changing what it captured, but not replaced; or a slice, whose
elements may be changed but not which run of them it is. -/
def Ty.shell : Ty → Bool
  | .fn _ _ _ _ _ => true
  | .vec false _ => true
  | _ => false

/-- A type no region is part of, which says the same of a value wherever it is. -/
def Ty.rfree : Ty → Bool
  | .int => true
  | .box τ => τ.rfree
  | .fn _ _ _ _ _ => true
  | .pair A B => A.rfree && B.rfree
  | .sum A B => A.rfree && B.rfree
  | .hole τ => τ.rfree
  | .rref _ _ _ => false
  | .arena _ => false
  | .vec _ τ => τ.rfree
  | .cont _ _ _ => true

/-- What may pass into and out of a fiber: a value of no region and with no place lent out of it. -/
def Ty.cross (τ : Ty) : Bool := τ.rfree && τ.complete

theorem Ty.data_rfree : ∀ {τ : Ty}, τ.data = true → τ.rfree = true
  | .int, _ => rfl
  | .box τ, h => by simp only [Ty.data] at h; simp only [Ty.rfree]; exact Ty.data_rfree h
  | .fn _ _ _ _ _, _ => rfl
  | .pair A B, h => by
    simp only [Ty.data, Bool.and_eq_true] at h
    simp only [Ty.rfree, Bool.and_eq_true]; exact ⟨Ty.data_rfree h.1, Ty.data_rfree h.2⟩
  | .sum A B, h => by
    simp only [Ty.data, Bool.and_eq_true] at h
    simp only [Ty.rfree, Bool.and_eq_true]; exact ⟨Ty.data_rfree h.1, Ty.data_rfree h.2⟩
  | .hole _, h => by simp [Ty.data] at h
  | .rref _ _ _, h => by simp [Ty.data] at h
  | .arena _, h => by simp [Ty.data] at h
  | .vec _ _, h => by simp [Ty.data] at h
  | .cont _ _ _, h => by simp [Ty.data] at h

/-- Data a region may hold: integers, and references into it or the regions around it, to data or to
a list of data. -/
def Ty.rdata : Ty → Bool
  | .int => true
  | .rref _ _ (.vec _ τ) => τ.rdata
  | .rref _ _ τ => τ.rdata
  | _ => false

/-- A type said of a place `n` regions further in: references count `n` more regions out. -/
def Ty.shiftBy (n : Nat) : Ty → Ty
  | .int => .int
  | .box τ => .box (τ.shiftBy n)
  | .fn k A B r R => .fn k A B r R
  | .pair A B => .pair (A.shiftBy n) (B.shiftBy n)
  | .sum A B => .sum (A.shiftBy n) (B.shiftBy n)
  | .hole τ => .hole (τ.shiftBy n)
  | .rref c k τ => .rref c (k + n) τ
  | .arena k => .arena (k + n)
  | .vec g τ => .vec g (τ.shiftBy n)
  | .cont A B r => .cont A B r

/-- A type said of a place `n` regions further out: what `shiftBy n` undoes. -/
def Ty.lowerBy (n : Nat) : Ty → Ty
  | .int => .int
  | .box τ => .box (τ.lowerBy n)
  | .fn k A B r R => .fn k A B r R
  | .pair A B => .pair (A.lowerBy n) (B.lowerBy n)
  | .sum A B => .sum (A.lowerBy n) (B.lowerBy n)
  | .hole τ => .hole (τ.lowerBy n)
  | .rref c k τ => .rref c (k - n) τ
  | .arena k => .arena (k - n)
  | .vec g τ => .vec g (τ.lowerBy n)
  | .cont A B r => .cont A B r

@[simp] theorem Ty.lowerBy_shiftBy : ∀ {τ : Ty}, (τ.shiftBy n).lowerBy n = τ
  | .int => rfl
  | .box τ => by simp [Ty.shiftBy, Ty.lowerBy, Ty.lowerBy_shiftBy (τ := τ)]
  | .fn _ _ _ _ _ => rfl
  | .pair A B => by simp [Ty.shiftBy, Ty.lowerBy, Ty.lowerBy_shiftBy (τ := A), Ty.lowerBy_shiftBy (τ := B)]
  | .sum A B => by simp [Ty.shiftBy, Ty.lowerBy, Ty.lowerBy_shiftBy (τ := A), Ty.lowerBy_shiftBy (τ := B)]
  | .hole τ => by simp [Ty.shiftBy, Ty.lowerBy, Ty.lowerBy_shiftBy (τ := τ)]
  | .rref _ _ _ => by simp [Ty.shiftBy, Ty.lowerBy]
  | .arena _ => by simp [Ty.shiftBy, Ty.lowerBy]
  | .vec _ τ => by simp [Ty.shiftBy, Ty.lowerBy, Ty.lowerBy_shiftBy (τ := τ)]
  | .cont _ _ _ => rfl

@[simp] theorem Ty.shiftBy_zero : ∀ {τ : Ty}, τ.shiftBy 0 = τ
  | .int => rfl
  | .box τ => by simp [Ty.shiftBy, Ty.shiftBy_zero (τ := τ)]
  | .fn _ _ _ _ _ => rfl
  | .pair A B => by simp [Ty.shiftBy, Ty.shiftBy_zero (τ := A), Ty.shiftBy_zero (τ := B)]
  | .sum A B => by simp [Ty.shiftBy, Ty.shiftBy_zero (τ := A), Ty.shiftBy_zero (τ := B)]
  | .hole τ => by simp [Ty.shiftBy, Ty.shiftBy_zero (τ := τ)]
  | .rref _ _ _ => rfl
  | .arena _ => rfl
  | .vec _ τ => by simp [Ty.shiftBy, Ty.shiftBy_zero (τ := τ)]
  | .cont _ _ _ => rfl

@[simp] theorem Ty.lowerBy_zero : ∀ {τ : Ty}, τ.lowerBy 0 = τ
  | .int => rfl
  | .box τ => by simp [Ty.lowerBy, Ty.lowerBy_zero (τ := τ)]
  | .fn _ _ _ _ _ => rfl
  | .pair A B => by simp [Ty.lowerBy, Ty.lowerBy_zero (τ := A), Ty.lowerBy_zero (τ := B)]
  | .sum A B => by simp [Ty.lowerBy, Ty.lowerBy_zero (τ := A), Ty.lowerBy_zero (τ := B)]
  | .hole τ => by simp [Ty.lowerBy, Ty.lowerBy_zero (τ := τ)]
  | .rref _ _ _ => rfl
  | .arena _ => rfl
  | .vec _ τ => by simp [Ty.lowerBy, Ty.lowerBy_zero (τ := τ)]
  | .cont _ _ _ => rfl

theorem Ty.shell_lowerBy {τ : Ty} : (τ.lowerBy n).shell = τ.shell := by
  cases τ <;> try rfl
  rename_i g τ; cases g <;> rfl

theorem Ty.data_not_fn {τ : Ty} (h : τ.data = true) : τ.shell = false := by
  cases τ <;> simp_all [Ty.data, Ty.shell]

/-- What a `handle` lends its arm: the name the arm knows it by, the mode it is lent in, its type,
and where it is — a place in the program, a location once the `handle` runs. -/
structure Cap (α : Type) where
  name : Var
  mode : Mode
  ty : Ty
  loc : α
  deriving Repr

/-- What the arm sees of a capture: its name, mode and type. -/
def Cap.sig (c : Cap α) : Var × Mode × Ty := (c.name, c.mode, c.ty)

/-- A capture as its frame has it: where its place was when the `handle` began. -/
def Cap.at (c : Cap Place) (l : Nat) : Cap Nat := ⟨c.name, c.mode, c.ty, l⟩

/-- A place: a variable, what a box at a place points to, or a field of a pair at a place. -/
inductive Place where
  | var (x : Var)
  | deref (p : Place)
  | fst (p : Place)
  | snd (p : Place)
  deriving DecidableEq, Repr

/-- What an operation takes: a value had at once, with no evaluation of its own. -/
inductive Atom where
  | lit (n : Int)
  /-- The integer at a place, copied. -/
  | read (p : Place)
  /-- The box in an owned variable, which is left moved. -/
  | move (x : Var)
  deriving Repr

/-- An operation on two integers: arithmetic, or a comparison, which gives `1` or `0`. -/
inductive IntOp where
  | add | sub | mul | div | rem | eq | ne | lt | le
  deriving DecidableEq, Repr

/-- What it gives; nothing for a division by zero, which panics. Division and remainder truncate
toward zero, as Flyscript's do. -/
def IntOp.apply : IntOp → Int → Int → Option Int
  | .add, x, y => some (x + y)
  | .sub, x, y => some (x - y)
  | .mul, x, y => some (x * y)
  | .div, x, y => if y = 0 then none else some (x.tdiv y)
  | .rem, x, y => if y = 0 then none else some (x.tmod y)
  | .eq, x, y => some (if x = y then 1 else 0)
  | .ne, x, y => some (if x = y then 0 else 1)
  | .lt, x, y => some (if x < y then 1 else 0)
  | .le, x, y => some (if x ≤ y then 1 else 0)

/-- Expressions in A-normal form: what an operation takes is an atom, and `let` is the one way to
name what an expression gives, so that the code an expression is part of is a stack of `let`s and
of the scopes, calls and handlers around them. -/
inductive Expr where
  | atom (a : Atom)
  /-- An operation on two integers. -/
  | arith (o : IntOp) (a b : Atom)
  /-- `Box.new(a)`. -/
  | new (a : Atom)
  /-- A pair of two values, each put in a cell of its own. -/
  | pair (a b : Atom)
  /-- A tag, left or right, of a union of an `A` and a `B`, carrying a value put in a cell of its own. -/
  | inj (A B : Ty) (left : Bool) (a : Atom)
  /-- `match (x) { #Left(y) => e₁, #Right(y) => e₂ }`, taking `x` apart: `y` owns what the tag
  carried, an `A` or a `B`, for the arm, and `x` is left moved. -/
  | case (x y : Var) (A B : Ty) (e₁ e₂ : Expr)
  /-- `match (p) { … }` through a borrow, `readonly` or `mut`: `x` is a borrow of what the tag at `p`
  carries, for the arm. -/
  | caseRef (x : Var) (m : Mode) (p : Place) (e₁ e₂ : Expr)
  /-- `let x: τ = a; b`, `x` dropped when `b` ends unless it was moved. -/
  | let_ (x : Var) (τ : Ty) (a b : Expr)
  /-- `p = a` for an integer place. -/
  | write (p : Place) (a : Atom)
  /-- `p = a` for a place holding a `box τ`: what it held is dropped. -/
  | assign (p : Place) (τ : Ty) (a : Atom)
  /-- A call: the owned arguments, in order, then the places lent, each with its mode. -/
  | call (f : Nat) (owned : List Atom) (lent : List (Mode × Place))
  /-- `(p) => body`, the closure of code `f`, capturing what `a` gives: plain data, moved in. -/
  | lam (f : Nat) (a : Atom)
  /-- `p(a)`, calling the closure at `p` as it is called: once, moving it out of the variable `p`;
  or through a borrow of `p`. -/
  | apply (k : Kind) (p : Place) (a : Atom)
  /-- `{ const x = (q) => …; body }`, `x` the closure of code `f` over a `readonly` borrow of `p`,
  for as long as `body` runs: it may be called, or lent on, but what `p` is rooted at is only read
  meanwhile. -/
  | lendClo (x : Var) (f : Nat) (p : Place) (body : Expr)
  /-- `{ const x = f(…); body }` for a function that returns a borrow, `readonly` or `mut`, of one of
  the places it was lent: `x` is that borrow for as long as `body` runs. -/
  | lendCall (x : Var) (m : Mode) (f : Nat) (owned : List Atom) (lent : List (Mode × Place)) (body : Expr)
  /-- `if (c) a else b`: `b` when `c` is zero. -/
  | ite (c : Atom) (a b : Expr)
  /-- `throw a`: a failure carrying an integer. -/
  | throw_ (a : Atom)
  /-- `try { body } catch (x) { h }`: a failure of `body` is handled by `h`, `x` its payload. -/
  | try_ (body : Expr) (x : Var) (h : Expr)
  /-- `while (c) { body }`, while `c` is not zero. -/
  | while_ (c body : Expr)
  /-- `{ defer { d }; body }`, `body` of type `τ`: `d` runs once `body` ends, with a value or
  unwinding. If `d` unwinds, its unwinding goes on out, `body`'s value dropped. -/
  | defer (τ : Ty) (d body : Expr)
  /-- `{ const x = p; body }` with `x` a borrow of `p` — `readonly` or `mut` — for as long as
  `body` runs. -/
  | lend (x : Var) (m : Mode) (p : Place) (body : Expr)
  /-- `E.op(…)`: the operation of user effect `e`, with its owned arguments and its places lent. -/
  | perform (e : Nat) (owned : List Atom) (lent : List (Mode × Place))
  /-- `handle { body } with E { op(…) resumes k => k(arm) }`: where `body` performs the operation,
  `arm` runs, its value the operation's result, given the operation's arguments — owned as `owns`,
  lent as `refs` — and the places of `caps`, each lent to it `readonly` or `mut` for as long as the
  `handle` runs: the state the arm keeps from one operation to the next. -/
  | handle (τ : Ty) (body : Expr) (e : Nat) (caps : List (Cap Place)) (owns refs : List Var) (arm : Expr)
  /-- `handle { body } with E { op(x) => h }`: where `body` performs the operation, whose argument
  is an integer, it unwinds, and `h` gives the `handle`'s value. -/
  | handleAbort (body : Expr) (e : Nat) (x : Var) (h : Expr)
  /-- `handle { body } with E { op(xs) resumes k => { const [v, c] = arm; const r = k(v); post(c, r) } }`:
  where `body` performs the operation, `arm` runs, given the operation's owned arguments and the places
  of `caps`, and gives the value to resume the code with and what it carries past the resumption, of
  type `C`; the code goes on under the `handle` to its end, and then function `post` runs, given what
  the arm carried and what the rest of the `handle` gave, the places of `caps` lent to it again, its
  value the `handle`'s. -/
  | handleR (τ : Ty) (body : Expr) (e : Nat) (caps : List (Cap Place)) (owns refs : List Var) (arm : Expr)
      (C : Ty) (post : Nat)
  /-- `{ const a = spawn fa(…); const b = spawn fb(…); [await a, await b] }`: two tasks, calls of `fa`
  and `fb`, given their owned arguments and lent places only `readonly`, run as one, each giving way
  to the other wherever it performs `e`, and the pair of what they give is the value. -/
  | par (e : Nat) (fa : Nat) (oa : List Atom) (la : List Place) (fb : Nat) (ob : List Atom) (lb : List Place)
  /-- `region (R) { body }`, of type `τ`: `R` the arena of a region for as long as `body` runs, which is
  then released at once. -/
  | region (R : Var) (τ : Ty) (body : Expr)
  /-- `R.alloc(a)`: `a`, a `τ` said of the region of arena `R`, put in a new cell of the region; a
  reference to it. -/
  | ralloc (R : Var) (c : Bool) (τ : Ty) (a : Atom)
  /-- `*p` for a reference `p` into a region: a copy of what the cell holds. -/
  | rget (p : Place)
  /-- `p.set(a)` for a `Cell` `p` of the region of arena `R`: `a` put in its cell in place of what it
  held. -/
  | rset (R : Var) (p : Place) (a : Atom)
  /-- `RegionList.new()` in the region of arena `R`: a list of the region, of `τ`s, empty. -/
  | rlnew (R : Var) (τ : Ty)
  /-- `p.push(a)` for a list `p` of the region of arena `R`: `a`, a `τ`, put in a new cell of the
  region, at the list's end. -/
  | rpush (R : Var) (τ : Ty) (p : Place) (a : Atom)
  /-- `p[z]` for a list `p` of the region of arena `R`: a copy of its element `z`; a panic if there is
  none. -/
  | rnth (R : Var) (p : Place) (z : Var)
  /-- `p.len()` for a list `p` of the region of arena `R`. -/
  | rlen (R : Var) (p : Place)
  /-- `[]`, an empty vector. -/
  | vnew
  /-- `p.len()`: how many elements the vector at `p` has. -/
  | vlen (p : Place)
  /-- `p.push(a)`: `a` moved to the end of the vector at `p`, whose elements move to new cells as it
  grows. -/
  | vpush (p : Place) (a : Atom)
  /-- `p.pop()`: the last element of the vector at `p`, moved out, as `#Some`, or `#None` if it is
  empty. -/
  | vpop (p : Place)
  /-- `{ const x = m p[lo..hi]; body }`, `x` a slice, `readonly` or `mut`, of the vector at `p`, its
  elements from `lo` up to `hi`, for as long as `body` runs; a panic if they are not there. -/
  | lendSlice (x : Var) (m : Mode) (p : Place) (lo hi : Var) (body : Expr)
  /-- `{ const g = generate(f(owned, caps)); body }`: `f` runs as `body` asks for its values, each a
  `τy` it yields by performing `eY`; `body` asks by performing `eN`, which gives `#Some(v)`, or
  `#Done` once `f` has ended. `body` has type `τb`; `f` is lent the places of `caps`, `readonly` or,
  whole bindings, `mut`. -/
  | gen (eN eY : Nat) (τy τb : Ty) (f : Nat) (owned : List Atom) (caps : List (Cap Place)) (body : Expr)
  /-- `scope (s) { body }`: `body` starts tasks as it runs, each by performing `eS` with a closure
  called once, `spawn(s, () => …)`, each lent the places `caps` — `readonly` borrows in scope — and
  each, `body` too, gives way by performing `e`; the scope ends once `body` and every task it
  started have. -/
  | scope (e eS : Nat) (caps : List (Cap Place)) (τ : Ty) (body : Expr)
  /-- `handle { f(owned) } with E { op(x…) resumes k => fa(x…, k) }`, of type `τ`, its body a call of `f`
  on a fiber of its own, its arm a call of `fa` given what the operation takes and the continuation,
  which it may keep. -/
  | handleV (τ : Ty) (e : Nat) (f : Nat) (owned : List Atom) (fa : Nat)
  /-- `k(a)`, the continuation `k` moved out of its variable and resumed with `a`. -/
  | resume (x : Var) (a : Atom)
  /-- `{ const x = p[z]; body }` with `x` a borrow — `readonly` or `mut` — of the element of the
  vector at `p` that the integer `z` names, for as long as `body` runs; a panic if there is none. -/
  | lendIdx (x : Var) (m : Mode) (p : Place) (z : Var) (body : Expr)
  deriving Repr

/-- `a + b`. -/
@[match_pattern] abbrev Expr.add (a b : Atom) : Expr := .arith .add a b

/-- A user effect's operation: what it takes, owned and lent, and what it gives. -/
structure Op where
  owns : List Ty
  refs : List (Mode × Ty)
  ret : Ty
  /-- An operation by which tasks give way to each other: only the frame of their tasks takes it,
  and a task may be made to give way by it before anything it does, as if it had performed it. -/
  task : Bool := false
  /-- What an operation takes and gives is said of no region: its arm may run regions out from
  where it was performed. -/
  rfree : (owns.all Ty.rfree && refs.all (fun p => p.2.rfree) && ret.rfree) = true := by decide

/-- A function: its owned parameters, its borrowed ones, its result, the effects it may perform,
its body. A function that returns a borrow says which it may be, `retp`: in a mode, of one of
several places, each rooted at a borrowed parameter, taken once its body has run, which picks one by
the value it gives; `ret` is then their type. -/
structure Fn where
  owns : List (Var × Ty)
  refs : List (Var × Mode × Ty)
  ret : Ty
  row : Row
  body : Expr
  retp : Option (Mode × List (Nat × Place)) := none
  /-- The code of a closure: the name its body knows what it captured by, of what type, and how the
  closure is called. -/
  cap : Option (Var × Ty × Kind) := none

/-- A closure's code as a function: what it captured one more parameter, owned if the closure is
called once, borrowed as the closure is otherwise. -/
def cloFn (d : Fn) (xc : Var) (τc : Ty) : Kind → Fn
  | .once => { d with owns := d.owns ++ [(xc, τc)], cap := none }
  | .shared => { d with refs := [(xc, .ro, τc)], cap := none }
  | .excl => { d with refs := [(xc, .mut, τc)], cap := none }

abbrev Env := List (Var × Nat)

/-- What a `handle` whose arm resumes in its midst runs after: the type of what the arm carries, the
function that runs once the rest of the `handle` ends, and the `handle`'s variables and places it
lends that function. -/
abbrev PostR := Option (Ty × Ty × Nat × Env × List (Cap Place))

mutual
inductive Val where
  | int (n : Int)
  | ptr (l : Nat)
  | moved
  /-- A closure: its code, and the cell holding what it captured, a `τc`. -/
  | clo (f : Nat) (c : Nat) (τc : Ty)
  /-- A pair: the cells of its fields. -/
  | pair (b c : Nat)
  /-- A tag, left or right, of a union of an `A` and a `B`, and the cell of what it carries. -/
  | tag (A B : Ty) (left : Bool) (l : Nat)
  /-- A reference to a cell of a region. -/
  | rptr (l : Nat)
  /-- A region's arena: the cells allocated in it. -/
  | arena (cs : List Nat)
  /-- A vector: the cells of its elements, in order. -/
  | vec (cs : List Nat)
  /-- A continuation taken where a fiber gave way: its frames, and the cells it owns. -/
  | kont (K : List Kont) (X : List Nat)

/-- How a computation that was dropped ended: with a value, or unwinding. -/
inductive Outcome where
  | val (v : Val)
  | abort (j : Nat) (k : Int)

/-- A frame of the code around what is being evaluated: what a construct does with what the code
it runs gives. The frames between an operation and the `handle` that handles it are its
continuation, taken whole when the operation is performed, and given back when it is resumed. -/
inductive Kont where
  /-- `let x: τ = □; b`. -/
  | letK (x : Var) (τ : Ty) (env : Env) (b : Expr)
  /-- The scope of a variable in cell `c`, which is dropped as it ends. -/
  | scopeK (τ : Ty) (c : Nat)
  /-- A call's body: the parameters it owns, dropped as it returns. -/
  | callK (cells : List (Ty × Nat))
  /-- The body of a call that returns a borrow of `p`, in the callee's variables `cenv`: once it
  ends, the borrow is taken, the parameters it owns dropped, and `body` runs in the caller's
  variables `env` with `x` the borrow. -/
  | callLendK (x : Var) (ps : List Place) (cenv : Env) (cells : List (Ty × Nat)) (env : Env) (body : Expr)
  /-- The body of a `try`, or of a `handle` whose arm ends it, handling `l`, its handler named `id`. -/
  | catchK (l : Label) (id : Nat) (x : Var) (env : Env) (h : Expr)
  /-- A loop's condition, and its body. -/
  | whileC (env : Env) (c b : Expr)
  | whileB (env : Env) (c b : Expr)
  /-- A body with cleanup `d` to run as it ends; the cleanup running as the body gave `v`, or as it
  unwound. -/
  | deferK (τ : Ty) (env : Env) (d : Expr)
  | deferV (τ : Ty) (v : Val)
  | deferA (j : Nat) (k : Int)
  /-- The code a borrow is in scope for. -/
  | lendK
  /-- The code a closure over a borrow is in scope for, the closure in cell `a`, freed as it ends. -/
  | cloK (a : Nat)
  /-- The body of a `handle` of type `τ` whose arm resumes, its handler named `id`. -/
  | capK (τ : Ty) (e : Nat) (id : Nat) (caps : List (Cap Nat)) (os rs : List Var) (arm : Expr) (post : PostR)
  /-- An arm running, the parameters it owns dropped as it ends: then the code its `handle` (of type
  `τ`) ran, `K`, goes on with the arm's value, or, if the arm unwinds, is dropped. -/
  | armK (τ : Ty) (cells : List (Ty × Nat)) (K : List Kont) (post : PostR)
  /-- What a `handle`'s arm carried, `v` of type `C`, waiting for the rest of the `handle` to end: then
  function `f` runs, given `v` and that value, the places `caps` of the `handle`'s scope, in `env`, lent
  to it. -/
  | postR (C : Ty) (f : Nat) (v : Val) (env : Env) (caps : List (Cap Place))
  /-- Code of type `τ` being dropped as an arm unwinds with `o`, by unwinding it to a barrier named
  `d`. -/
  | dropK (τ : Ty) (o : Outcome) (d : Nat)
  /-- A task's body, run once the task is first given its turn. -/
  | startK (env : Env) (b : Expr)
  /-- Two tasks of types `τa` and `τb`, the one running `side` (the first if `true`), the other
  waiting as `K` where it last gave way; each gives way by performing `e`, handled here as `id`. -/
  | parS (e id : Nat) (τa τb : Ty) (side : Bool) (K : List Kont)
  /-- Two tasks, the one running `side`, the other done with `w`. -/
  | parD (e id : Nat) (τa τb : Ty) (side : Bool) (w : Val)
  /-- A task running alone as it is dropped, its turns given back at once. -/
  | parY (e id : Nat)
  /-- The code around two tasks, one of which failed, the other being dropped. -/
  | parE
  /-- A region's body, its arena in cell `a`: as it ends, the region's cells and the arena are freed. -/
  | regionK (a : Nat)
  /-- A generator's consumer running, asking by `eN`, handled here as `id`; its producer waiting as
  `Kp`, or ended. -/
  | genC (eN eY id : Nat) (τy τb : Ty) (Kp : Option (List Kont))
  /-- A generator's producer running, yielding by `eY`, handled here as `id`; its consumer waiting as
  `Kc` for what it asked. -/
  | genP (eN eY id : Nat) (τy τb : Ty) (Kc : List Kont)
  /-- A producer being dropped: what it yields is dropped, and it goes on at once. -/
  | genY (eY id : Nat) (τy : Ty)
  /-- A consumer being dropped: what it asks is answered `#Done`. -/
  | genN (eN id : Nat) (τy : Ty)
  /-- A producer being dropped as its consumer ended with `o`, of type `τb`, by unwinding it to the
  barrier `d`: once the unwinding reaches it, `o` goes on. -/
  | genE (τb : Ty) (o : Outcome) (d : Nat)
  /-- A scope's body running, of type `τ`, its tasks waiting as `Q`, each where it last gave way;
  giving way by `e` and starting tasks by `eS`, handled here as `id`. -/
  | scB (e eS id : Nat) (τ : Ty) (cz : List (Cap Nat)) (Q : List (List Kont))
  /-- A scope's task running, its body waiting as `Kb` where it last gave way, its other tasks as `Q`. -/
  | scW (e eS id : Nat) (τ : Ty) (cz : List (Cap Nat)) (Kb : List Kont) (Q : List (List Kont))
  /-- A scope's task running, its body done with `v`, its other tasks waiting as `Q`. -/
  | scV (e eS id : Nat) (τ : Ty) (cz : List (Cap Nat)) (v : Val) (Q : List (List Kont))
  /-- A scope's body or task being dropped: it goes on at once where it gives way, and a task it
  starts is dropped. -/
  | scX (e eS id : Nat)
  /-- A scope that failed, or whose body or task did, with `o`, of type `τ`: what is being dropped, of
  type `τd`, is unwinding to the barrier `d`; then each task of `Q` is, and `o` goes on. -/
  | scE (e eS id : Nat) (τ τd : Ty) (o : Outcome) (d : Nat) (Q : List (List Kont))
  /-- The fiber of a `handle` whose arm keeps its continuation, its handler named `g`, which a failure
  of its body unwinds to if `ff`: its arm, the function `fa`, is called with what the operation takes
  and the continuation. Since the fiber was last entered, owning the cells `B`, the cells it allocated
  are those from `s` on. -/
  | capV (τ : Ty) (e : Nat) (g : Nat) (fa : Nat) (ff : Bool) (B : List Nat) (s : Nat)
  /-- Such a fiber, given way by an operation of the code around, which lends it the places at `ls`:
  once the code around answers, it is entered again, owning the cells `X` and what is at `ls` then. -/
  | enterK (τ : Ty) (e : Nat) (g : Nat) (fa : Nat) (ff : Bool) (K : List Kont) (X : List Nat) (ls : List Nat)
  /-- A kept continuation being dropped, unwinding to the barrier `d`: its operation, performed by its
  cleanup, is cancelled, the cleanup unwinding from it. -/
  | capD (τ : Ty) (e : Nat) (g : Nat) (d : Nat)
end


/-- The store: its cells, `none` once freed or before allocation, the next to allocate, and the
next name for a handler put in force. -/
structure Store where
  mem : Nat → Option Val
  next : Nat
  ids : Nat := 0
  /-- Which task goes on at each point where one could give way to the other: any schedule. -/
  sched : Nat → Bool := fun _ => true
  /-- Where a running task is stopped, before an operation, for another to run: any interleaving of
  their operations, as on many cores at once. -/
  pre : Nat → Bool := fun _ => false
  /-- The region and type of each cell allocated in a region, kept once set. -/
  rt : Nat → Option (Nat × Ty) := fun _ => none
  /-- A region is named by its arena's cell: a tagged cell, and its region's arena, were allocated. -/
  rtwf : ∀ l a x, rt l = some (a, x) → a < next ∧ l < next := by intro l a x h; simp at h

/-- A fresh name for a handler. -/
def Store.fresh (σ : Store) : Nat × Store := (σ.ids, { σ with ids := σ.ids + 1 })

def Store.set (σ : Store) (l : Nat) (v : Option Val) : Store :=
  { σ with mem := fun k => if k = l then v else σ.mem k }

/-- Tags cell `l` as a cell of the region whose arena is cell `a`, holding a `τ`. -/
def Store.tag (σ : Store) (l a : Nat) (τ : Ty) : Store :=
  if h : a < σ.next ∧ l < σ.next then
    { σ with rt := fun k => if k = l then some (a, τ) else σ.rt k,
             rtwf := fun k b x hk => by
               split at hk
               · rename_i hkl; cases hk; exact ⟨h.1, hkl ▸ h.2⟩
               · exact σ.rtwf k b x hk }
  else σ

/-- Frees the cells `cs`. -/
def Store.freeAll (σ : Store) : List Nat → Store
  | [] => σ
  | l :: cs => (σ.set l none).freeAll cs

def Store.alloc (σ : Store) (v : Val) : Nat × Store :=
  (σ.next, { σ with mem := fun k => if k = σ.next then some v else σ.mem k, next := σ.next + 1,
                    rtwf := fun l a x h => ⟨Nat.lt_succ_of_lt (σ.rtwf l a x h).1, Nat.lt_succ_of_lt (σ.rtwf l a x h).2⟩ })

/-- Moves what each of the cells `cs` holds to a fresh cell, freeing it: a vector's elements, as it
grows into new storage. -/
def Store.moveAll (σ : Store) : List Nat → Option (List Nat × Store)
  | [] => some ([], σ)
  | c :: cs =>
    match σ.mem c with
    | some w =>
      let (c', σ1) := σ.alloc w
      match (σ1.set c none).moveAll cs with
      | some (cs', σ2) => some (c' :: cs', σ2)
      | none => none
    | none => none


def lookup {α : Type} (x : Var) : List (Var × α) → Option α
  | [] => none
  | (y, v) :: r => if x = y then some v else lookup x r

/-- The location a place denotes. -/
def resolve (σ : Store) (env : Env) : Place → Option Nat
  | .var x => lookup x env
  | .deref p =>
    match resolve σ env p with
    | some l =>
      match σ.mem l with
      | some (.ptr l') => some l'
      | _ => none
    | none => none
  | .fst p =>
    match resolve σ env p with
    | some l =>
      match σ.mem l with
      | some (.pair b _) => some b
      | _ => none
    | none => none
  | .snd p =>
    match resolve σ env p with
    | some l =>
      match σ.mem l with
      | some (.pair _ c) => some c
      | _ => none
    | none => none

/-- Drops the cells `cs` in order, with `drop1` for what each holds. -/
def dropCellsWith (drop1 : Store → Val → Option Store) : Store → List Nat → Option Store
  | σ, [] => some σ
  | σ, c :: cs =>
    match σ.mem c with
    | some w =>
      match drop1 σ w with
      | some σ' => dropCellsWith drop1 (σ'.set c none) cs
      | none => none
    | none => none

/-- Drops a value of type `τ` with `k` cells to spare: frees the cells of its boxes, innermost
first, and what a closure captured, which may hold closures in turn. `none` if a cell it should free
is not there, a double free, or it runs out of cells to spare. -/
def dropK : Nat → Store → Ty → Val → Option Store
  | _, σ, .int, .int _ => some σ
  | _, σ, .rref _ _ _, .rptr _ => some σ
  | k + 1, σ, .box τ, .ptr l =>
    match σ.mem l with
    | some w =>
      match dropK k σ τ w with
      | some σ' => some (σ'.set l none)
      | none => none
    | none => none
  | k + 1, σ, .fn _ _ _ _ _, .clo _ c τc =>
    match σ.mem c with
    | some w =>
      match dropK k σ τc w with
      | some σ' => some (σ'.set c none)
      | none => none
    | none => none
  | k + 1, σ, .sum A B, .tag _ _ t l =>
    match σ.mem l with
    | some w =>
      match dropK k σ (if t then A else B) w with
      | some σ' => some (σ'.set l none)
      | none => none
    | none => none
  | k + 1, σ, .pair A B, .pair b c =>
    match σ.mem b with
    | some w =>
      match dropK k σ A w with
      | some σ1 =>
        match σ1.mem c with
        | some u =>
          match dropK k (σ1.set b none) B u with
          | some σ2 => some (σ2.set c none)
          | none => none
        | none => none
      | none => none
    | none => none
  | 0, σ, .vec _ _, .vec [] => some σ
  | k + 1, σ, .vec _ τ, .vec cs => dropCellsWith (fun σ w => dropK k σ τ w) σ cs
  | _, σ, .cont _ _ _, .kont _ _ => some σ
  | _, _, _, _ => none

/-- Drops a value of type `τ`: a value owns fewer cells than the store has. -/
def drop (σ : Store) (τ : Ty) (v : Val) : Option Store := dropK σ.next σ τ v

/-- Drops what a variable's cell holds, unless it was moved, then frees the cell. -/
def dropCell (σ : Store) (τ : Ty) (c : Nat) : Option Store :=
  match σ.mem c with
  | some .moved => some (σ.set c none)
  | some v => (drop σ τ v).map fun σ' => σ'.set c none
  | none => none

/-- What a function's value picks among the places it may return a borrow of: the one it counts to,
or the last. -/
def pick {α : Type} (ps : List α) (k : Int) : Option α := ps[min k.toNat (ps.length - 1)]?

/-- Drops values of the types `τs`, in order. -/
def dropAll (σ : Store) : List Ty → List Val → Option Store
  | [], [] => some σ
  | τ :: τs, v :: vs =>
    match drop σ τ v with
    | some σ' => dropAll σ' τs vs
    | none => none
  | _, _ => none

def dropCells (σ : Store) : List (Ty × Nat) → Option Store
  | [] => some σ
  | (τ, c) :: rest =>
    match dropCell σ τ c with
    | some σ' => dropCells σ' rest
    | none => none

/-- The continuations a value of type `τ` holds, which dropping it leaves to be dropped: they have
cleanup to run. -/
def kontsK : Nat → Store → Ty → Val → List Val
  | _, _, .cont _ _ _, .kont K X => [.kont K X]
  | k + 1, σ, .box τ, .ptr l =>
    match σ.mem l with
    | some w => kontsK k σ τ w
    | none => []
  | k + 1, σ, .fn _ _ _ _ _, .clo _ c τc =>
    match σ.mem c with
    | some w => kontsK k σ τc w
    | none => []
  | k + 1, σ, .sum A B, .tag _ _ t l =>
    match σ.mem l with
    | some w => kontsK k σ (if t then A else B) w
    | none => []
  | k + 1, σ, .pair A B, .pair b c =>
    (match σ.mem b with
     | some w => kontsK k σ A w
     | none => []) ++
    (match σ.mem c with
     | some u => kontsK k σ B u
     | none => [])
  | k + 1, σ, .vec _ τ, .vec cs =>
    cs.flatMap fun c =>
      match σ.mem c with
      | some w => kontsK k σ τ w
      | none => []
  | _, _, _, _ => []

def konts (σ : Store) (τ : Ty) (v : Val) : List Val := kontsK σ.next σ τ v

/-- The continuations values of the types `τs` hold. -/
def kontsAll (σ : Store) : List Ty → List Val → List Val
  | τ :: τs, v :: vs => konts σ τ v ++ kontsAll σ τs vs
  | _, _ => []

/-- The continuations what a variable's cell holds holds. -/
def cellKonts (σ : Store) (τ : Ty) (c : Nat) : List Val :=
  match σ.mem c with
  | some .moved => []
  | some v => konts σ τ v
  | none => []

def cellsKonts (σ : Store) : List (Ty × Nat) → List Val
  | [] => []
  | (τ, c) :: rest => cellKonts σ τ c ++ cellsKonts σ rest




/-- A handler in force, by name: one that unwinds — an abortive arm, or a `try` — handling `l`; or
one whose arm takes the code that performed `e` as its continuation, resuming it with its value.
An unwinding or a continuation taken is aimed at a handler by its name, which the handler keeps
wherever the code around it goes on. -/
inductive Frame where
  | abort (l : Label) (id : Nat)
  | capture (e : Nat) (id : Nat)
  /-- Code being dropped: every operation it performs is taken, by `id`, to be cancelled. -/
  | cancel (id : Nat)

abbrev HS := List Frame

def Frame.handles : Frame → Label → Bool
  | .abort l _, l' => l == l'
  | .capture e _, .eff e' => e == e'
  | .cancel _, .eff _ => true
  | _, _ => false

/-- The innermost frame of tasks: a handler of an operation by which tasks give way. -/
def preTarget (O : List Op) : HS → Option (Nat × Nat)
  | [] => none
  | .capture e id :: hs =>
    match O[e]? with
    | some op => if op.task ∧ op.owns = [] ∧ op.refs = [] ∧ op.ret = .int then some (e, id) else preTarget O hs
    | none => preTarget O hs
  | _ :: hs => preTarget O hs

/-- The innermost frame handling `l`. -/
def find (l : Label) : HS → Option Frame
  | [] => none
  | f :: rest => if f.handles l then some f else find l rest

/-- The handlers in force for code running on a fiber whose continuation is kept: those of the code
around, each operation taken as a continuation — one a handler there would end its `handle` with as
well, which drops it — failures unwinding to the fiber's own handler `g`, if its body may fail. -/
def hsConv : HS → HS
  | [] => []
  | .capture e id :: hs => .capture e id :: hsConv hs
  | .cancel id :: hs => .cancel id :: hsConv hs
  | .abort (.eff e) id :: hs => .capture e id :: hsConv hs
  | .abort _ _ :: hs => hsConv hs

def fiberHS (e g : Nat) (ff : Bool) (hs : HS) : HS :=
  .capture e g :: ((if ff then [.abort .fail g] else []) ++ hsConv hs)

/-- The handlers in force for a fiber `g` being dropped, unwinding to `d`: a failure unwinds on to
`d`; what the fiber's frames were unwinding to, `g`, is aimed at as it was. -/
def hsDie (g d : Nat) : HS := [.abort .fail d, .abort .drop d, .abort .drop g]

/-- The frame a construct puts in force for the code it runs, if any. -/
def Kont.push : Kont → HS → HS
  | .catchK (.eff ef) id _ _ _, hs => .capture ef id :: .abort (.eff ef) id :: hs
  | .catchK l id _ _ _, hs => .abort l id :: hs
  | .capK _ e id _ _ _ _ _, hs => .capture e id :: hs
  | .dropK _ _ d, hs => .abort .drop d :: hs
  | .parS e id _ _ _ _, hs => .capture e id :: hs
  | .parD e id _ _ _ _, hs => .capture e id :: hs
  | .parY e id, hs => .capture e id :: hs
  | .genC eN _ id _ _ _, hs => .capture eN id :: hs
  | .genP _ eY id _ _ _, hs => .capture eY id :: hs
  | .genY eY id _, hs => .capture eY id :: hs
  | .genN eN id _, hs => .capture eN id :: hs
  | .genE _ _ d, hs => .abort .drop d :: hs
  | .scB e eS id _ _ _, hs => .capture e id :: .capture eS id :: hs
  | .scW e eS id _ _ _ _, hs => .capture e id :: .capture eS id :: hs
  | .scV e eS id _ _ _ _, hs => .capture e id :: .capture eS id :: hs
  | .scX e eS id, hs => .capture e id :: .capture eS id :: hs
  | .scE _ _ _ _ _ _ d _, hs => .abort .drop d :: hs
  | .capD _ _ g _, hs => .cancel g :: hs
  | _, hs => hs

/-- The cells a continuation kept as a value owns. -/
def Val.foot : Val → List Nat
  | .kont _ X => X
  | _ => []

/-- The cells a value owns, read off the store: those of its boxes, fields, tag, elements and
capture, each with what it holds, and a continuation's. `k` bounds the depth. -/
def treeK : Nat → Store → Val → List Nat
  | _, _, .kont _ X => X
  | k + 1, σ, .ptr b => b :: (σ.mem b).elim [] (treeK k σ)
  | k + 1, σ, .clo _ c _ => c :: (σ.mem c).elim [] (treeK k σ)
  | k + 1, σ, .tag _ _ _ b => b :: (σ.mem b).elim [] (treeK k σ)
  | k + 1, σ, .pair b c => (b :: (σ.mem b).elim [] (treeK k σ)) ++ (c :: (σ.mem c).elim [] (treeK k σ))
  | k + 1, σ, .vec cs => cs.flatMap fun c => c :: (σ.mem c).elim [] (treeK k σ)
  | _, _, _ => []

/-- The cells a value owns: no deeper than the store has cells. -/
def Val.tree (σ : Store) (v : Val) : List Nat := treeK σ.next σ v

/-- A list with each element once. -/
def dedupL : List Nat → List Nat
  | [] => []
  | x :: xs => if x ∈ xs then dedupL xs else x :: dedupL xs

/-- The cells of what the cell `l` holds, with `l`. -/
def cellTree (σ : Store) (l : Nat) : List Nat := l :: (σ.mem l).elim [] (treeK σ.next σ)

/-- What a fiber that was entered owning the cells `B`, and has allocated those from `s` on, owns
where it gives way, the store `σ`, passing out the values `vs`: those of its cells still there that
`vs` do not own. -/
def kfoot (σ : Store) (B : List Nat) (s : Nat) (vs : List Val) : List Nat :=
  (dedupL (B ++ List.range' s (σ.next - s))).filter fun l => (σ.mem l).isSome && !(vs.flatMap (Val.tree σ)).contains l

inductive Res where
  | val (v : Val)
  /-- Unwinding to the handler named `id`, with the operation's integer argument. -/
  | abort (id : Nat) (k : Int)
  /-- An operation of effect `e` performed, its handler named `id` taking the code as its
  continuation: the operation's owned arguments, the locations it lends, and the frames so far, the
  outermost first. A `handle` takes it if it is that handler, for that effect. -/
  | susp (id : Nat) (e : Nat) (vs : List Val) (ls : List Nat) (K : List Kont)
  | stuck
  | timeout
  /-- The program ends at once, nothing dropped and no cleanup run: an index out of bounds. -/
  | panic

/-- The value of a result, if it is one. -/
def Res.value? : Res → Option Val
  | .val v => some v
  | _ => none

/-- Evaluation ended, with a value or by unwinding: a scope it leaves drops what it owns. -/
def Res.done : Res → Bool
  | .val _ | .abort _ _ => true
  | _ => false

/-- What goes on once the continuations a drop left have been dropped, `fl` dropping them. -/
def andThen (x : Res × Store) (k : Store → Res × Store) : Res × Store :=
  match x with
  | (.val _, σ) => k σ
  | x => x

/-- How the continuations a drop leaves are dropped: unwinding each, its cleanup running. -/
abbrev Flush := List Val → Store → Res × Store

/-- Leaving a scope whose variable is in cell `c`: dropped on every way out but a timeout, or kept
with the continuation taken in it. -/
def leave (fl : Flush) (τ : Ty) (c : Nat) : Res × Store → Res × Store
  | (.susp j ef vs ls K, σ) => (.susp j ef vs ls (.scopeK τ c :: K), σ)
  | (r, σ) =>
    if r.done then
      match dropCell σ τ c with
      | some σ' => andThen (fl (cellKonts σ τ c) σ') fun σ'' => (r, σ'')
      | none => (.stuck, σ)
    else (r, σ)

/-- A body's cleanup ended, the body having given `v`. -/
def cleanV (fl : Flush) (τ : Ty) (v : Val) : Res × Store → Res × Store
  | (.val (.int _), σ) => (.val v, σ)
  | (.abort j k, σ) =>
    match drop σ τ v with
    | some σ' => andThen (fl (konts σ τ v) σ') fun σ'' => (.abort j k, σ'')
    | none => (.stuck, σ)
  | (.susp j ef vs ls K, σ) => (.susp j ef vs ls (.deferV τ v :: K), σ)
  | (.val _, σ) => (.stuck, σ)
  | r => r

/-- A body's cleanup ended, the body unwinding to `j`. -/
def cleanA (j : Nat) (k : Int) : Res × Store → Res × Store
  | (.val (.int _), σ) => (.abort j k, σ)
  | (.susp j' ef vs ls K, σ) => (.susp j' ef vs ls (.deferA j k :: K), σ)
  | (.val _, σ) => (.stuck, σ)
  | r => r

/-- Allocates a cell for each value, binding the names to them. -/
def allocAll (σ : Store) : List (Var × Val) → Env × Store
  | [] => ([], σ)
  | (x, v) :: rest =>
    let (c, σ1) := σ.alloc v
    let (env, σ2) := allocAll σ1 rest
    ((x, c) :: env, σ2)

def Outcome.res : Outcome → Res
  | .val v => .val v
  | .abort j k => .abort j k

/-- Code of type `τ` dropped as an arm unwound with `o`, by unwinding it to the barrier named `d`:
once the unwinding reaches it, `o` goes on, unless the dropping itself unwound elsewhere; and if the
code gave a value after all, the value is dropped. -/
def dropRet (fl : Flush) (τ : Ty) (o : Outcome) (d : Nat) : Res × Store → Res × Store
  | (.abort j k, σ) =>
    if j = d then (o.res, σ) else
    match o with
    | .val u =>
      match drop σ τ u with
      | some σ' => andThen (fl (konts σ τ u) σ') fun σ'' => (.abort j k, σ'')
      | none => (.stuck, σ)
    | .abort _ _ => (.abort j k, σ)
  | (.val v, σ) =>
    match drop σ τ v with
    | some σ' => andThen (fl (konts σ τ v) σ') fun σ'' => (o.res, σ'')
    | none => (.stuck, σ)
  | (.susp j ef vs ls K, σ) => (.susp j ef vs ls (.dropK τ o d :: K), σ)
  | r => r

/-- A task started from a closure called once, `v`: what it captured moved to a parameter of its
code, which is called with `0` once the task first goes on, lent the places `cz`. -/
def mkTask (F : List Fn) (cz : List (Cap Nat)) (σ : Store) : Val → Option (List Kont × Store)
  | .clo f c τc =>
    match F[f]?, σ.mem c with
    | some d, some w =>
      match d.cap with
      | some (xc, _, _) =>
        let d' := cloFn d xc τc .once
        if 2 = d'.owns.length ∧ d'.refs.length = cz.length then
          let (cells, σ2) := allocAll (σ.set c none) ((d'.owns.map Prod.fst).zip [.int 0, w])
          some ([.callK ((d'.owns.map Prod.snd).zip (cells.map Prod.snd)),
            .startK (cells ++ (d'.refs.map Prod.fst).zip (cz.map Cap.loc)) d'.body], σ2)
        else none
      | none => none
    | _, _ => none
  | _ => none

/-- A call's body ended: the parameters it owns are dropped; a continuation taken in it keeps them. -/
def callRet (fl : Flush) (cells : List (Ty × Nat)) : Res × Store → Res × Store
  | (.susp j ef vs ls K, σ) => (.susp j ef vs ls (.callK cells :: K), σ)
  | (.stuck, σ) => (.stuck, σ)
  | (.timeout, σ) => (.timeout, σ)
  | (.panic, σ) => (.panic, σ)
  | (r, σ) =>
    match dropCells σ cells with
    | some σ' => andThen (fl (cellsKonts σ cells) σ') fun σ'' => (r, σ'')
    | none => (.stuck, σ)

/-- An arm ended: its parameters are dropped, and the code its `handle` ran, `K`, goes on with
the arm's value (`resuming`), or, if the arm unwinds with `o`, is dropped (`dropping`). -/
def armEnd (fl : Flush) (τ : Ty) (cells : List (Ty × Nat)) (K : List Kont) (post : PostR)
    (resuming : Store → Val → Res × Store) (dropping : Store → Outcome → Res × Store) : Res × Store → Res × Store
  | (.susp j ef vs ls K', σ) => (.susp j ef vs ls (.armK τ cells K post :: K'), σ)
  | (.val v, σ) =>
    match dropCells σ cells with
    | some σ' => andThen (fl (cellsKonts σ cells) σ') fun σ'' => resuming σ'' v
    | none => (.stuck, σ)
  | (.abort j k, σ) =>
    match dropCells σ cells with
    | some σ' => andThen (fl (cellsKonts σ cells) σ') fun σ'' => dropping σ'' (.abort j k)
    | none => (.stuck, σ)
  | r => r

/-- An atom's value, and the store after: a move leaves its variable's cell marked moved. -/
def evalAtom (σ : Store) (env : Env) : Atom → Option (Val × Store)
  | .lit k => some (.int k, σ)
  | .read p =>
    match resolve σ env p with
    | some l =>
      match σ.mem l with
      | some (.int k) => some (.int k, σ)
      | some (.rptr r) => some (.rptr r, σ)
      | _ => none
    | none => none
  | .move x =>
    match lookup x env with
    | some c =>
      match σ.mem c with
      | some .moved | none => none
      | some v => some (v, σ.set c (some .moved))
    | none => none

/-- The atoms' values, in order. -/
def evalAtoms (σ : Store) (env : Env) : List Atom → Option (List Val × Store)
  | [] => some ([], σ)
  | a :: rest =>
    match evalAtom σ env a with
    | some (v, σ1) =>
      match evalAtoms σ1 env rest with
      | some (vs, σ2) => some (v :: vs, σ2)
      | none => none
    | none => none

mutual
/-- The interpreter: the program's functions and operations, fuel, the handlers in force. -/
def eval (F : List Fn) (O : List Op) : Nat → HS → Store → Env → Expr → Res × Store
  | 0, _, σ, _, _ => (.timeout, σ)
  | n + 1, hs, σ, env, e =>
    match (if σ.pre σ.ids then preTarget O hs else none) with
    | some (e0, j) => (.susp j e0 [] [] [.startK env e], σ.fresh.2)
    | none => evalS F O n hs σ.fresh.2 env e
termination_by n _ _ _ _ => (n, 0, 0)

/-- One step of the interpreter, `e` evaluated with the fuel left, `n`. -/
def evalS (F : List Fn) (O : List Op) (n : Nat) (hs : HS) (σ : Store) (env : Env) (e : Expr) : Res × Store :=
    match e with
    | .atom a =>
      match evalAtom σ env a with
      | some (v, σ1) => (.val v, σ1)
      | none => (.stuck, σ)
    | .arith o a b =>
      match evalAtom σ env a with
      | some (.int x, σ1) =>
        match evalAtom σ1 env b with
        | some (.int y, σ2) =>
          match o.apply x y with
          | some z => (.val (.int z), σ2)
          | none => (.panic, σ2)
        | _ => (.stuck, σ1)
      | _ => (.stuck, σ)
    | .new a =>
      match evalAtom σ env a with
      | some (v, σ1) =>
        let (l, σ2) := σ1.alloc v
        (.val (.ptr l), σ2)
      | none => (.stuck, σ)
    | .pair a b =>
      match evalAtom σ env a with
      | some (v, σ1) =>
        match evalAtom σ1 env b with
        | some (w, σ2) =>
          let (lb, σ3) := σ2.alloc v
          let (lc, σ4) := σ3.alloc w
          (.val (.pair lb lc), σ4)
        | none => (.stuck, σ)
      | none => (.stuck, σ)
    | .inj A B t a =>
      match evalAtom σ env a with
      | some (v, σ1) =>
        let (l, σ2) := σ1.alloc v
        (.val (.tag A B t l), σ2)
      | none => (.stuck, σ)
    | .case x y A B e₁ e₂ =>
      match lookup x env with
      | some c =>
        match σ.mem c with
        | some (.tag _ _ t l) =>
          ret F O n hs (.scopeK (if t then A else B) l)
            (eval F O n hs (σ.set c (some .moved)) ((y, l) :: env) (if t then e₁ else e₂))
        | _ => (.stuck, σ)
      | none => (.stuck, σ)
    | .caseRef x _ p e₁ e₂ =>
      match resolve σ env p with
      | some l0 =>
        match σ.mem l0 with
        | some (.tag _ _ t l) => ret F O n hs .lendK (eval F O n hs σ ((x, l) :: env) (if t then e₁ else e₂))
        | _ => (.stuck, σ)
      | none => (.stuck, σ)
    | .let_ x τ a b => ret F O n hs (.letK x τ env b) (eval F O n hs σ env a)
    | .write p a =>
      match evalAtom σ env a with
      | some (.int k, σ1) =>
        match resolve σ1 env p with
        | some l =>
          match σ1.mem l with
          | some (.int _) => (.val (.int 0), σ1.set l (some (.int k)))
          | _ => (.stuck, σ1)
        | none => (.stuck, σ1)
      | _ => (.stuck, σ)
    | .assign p τ a =>
      match evalAtom σ env a with
      | some (v, σ1) =>
        match resolve σ1 env p with
        | some l =>
          match σ1.mem l with
          | some old =>
            match drop σ1 τ old with
            | some σ2 => andThen (flushR F O n (konts σ1 τ old) σ2) fun σ3 => (.val (.int 0), σ3.set l (some v))
            | none => (.stuck, σ1)
          | none => (.stuck, σ1)
        | none => (.stuck, σ1)
      | none => (.stuck, σ)
    | .call f owned lent =>
      match F[f]? with
      | none => (.stuck, σ)
      | some d =>
        match evalAtoms σ env owned with
        | some (vs, σ1) =>
          match lent.mapM (fun (_, p) => resolve σ1 env p) with
          | some ls =>
            if vs.length = d.owns.length ∧ ls.length = d.refs.length then
              let (cells, σ2) := allocAll σ1 ((d.owns.map Prod.fst).zip vs)
              ret F O n hs (.callK ((d.owns.map Prod.snd).zip (cells.map Prod.snd)))
                (eval F O n hs σ2 (cells ++ (d.refs.map Prod.fst).zip ls) d.body)
            else (.stuck, σ1)
          | none => (.stuck, σ1)
        | none => (.stuck, σ)
    | .lam f a =>
      match F[f]?, evalAtom σ env a with
      | some d, some (v, σ1) =>
        match d.cap with
        | some (_, τc, _) =>
          let (c, σ2) := σ1.alloc v
          (.val (.clo f c τc), σ2)
        | none => (.stuck, σ1)
      | _, _ => (.stuck, σ)
    | .apply .once (.var x) a =>
      match lookup x env with
      | some cx =>
        match σ.mem cx with
        | some (.clo f c τc) =>
          match evalAtom (σ.set cx (some .moved)) env a, F[f]? with
          | some (v, σ1), some d =>
            match d.cap, σ1.mem c with
            | some (xc, _, _), some w =>
              let d' := cloFn d xc τc .once
              let vs := [v, w]
              let ls : List Nat := []
              if vs.length = d'.owns.length ∧ ls.length = d'.refs.length then
                let (cells, σ2) := allocAll (σ1.set c none) ((d'.owns.map Prod.fst).zip vs)
                ret F O n hs (.callK ((d'.owns.map Prod.snd).zip (cells.map Prod.snd)))
                  (eval F O n hs σ2 (cells ++ (d'.refs.map Prod.fst).zip ls) d'.body)
              else (.stuck, σ1)
            | _, _ => (.stuck, σ1)
          | _, _ => (.stuck, σ)
        | _ => (.stuck, σ)
      | none => (.stuck, σ)
    | .apply .once _ _ => (.stuck, σ)
    | .apply k p a =>
      match evalAtom σ env a with
      | some (v, σ1) =>
        match resolve σ1 env p with
        | some la =>
          match σ1.mem la with
          | some (.clo f c τc) =>
            match F[f]? with
            | some d =>
              match d.cap with
              | some (xc, _, _) =>
                let d' := cloFn d xc τc k
                let vs := [v]
                let ls := [c]
                if vs.length = d'.owns.length ∧ ls.length = d'.refs.length then
                  let (cells, σ2) := allocAll σ1 ((d'.owns.map Prod.fst).zip vs)
                  ret F O n hs (.callK ((d'.owns.map Prod.snd).zip (cells.map Prod.snd)))
                    (eval F O n hs σ2 (cells ++ (d'.refs.map Prod.fst).zip ls) d'.body)
                else (.stuck, σ1)
              | none => (.stuck, σ1)
            | none => (.stuck, σ1)
          | _ => (.stuck, σ1)
        | none => (.stuck, σ1)
      | none => (.stuck, σ)
    | .lendClo x f p body =>
      match F[f]?, resolve σ env p with
      | some d, some l =>
        match d.cap with
        | some (_, τc, _) =>
          let (a, σ1) := σ.alloc (.clo f l τc)
          ret F O n hs (.cloK a) (eval F O n hs σ1 ((x, a) :: env) body)
        | none => (.stuck, σ)
      | _, _ => (.stuck, σ)
    | .lendCall x _ f owned lent body =>
      match F[f]? with
      | none => (.stuck, σ)
      | some d =>
        match d.retp, evalAtoms σ env owned with
        | some (_, cs), some (vs, σ1) =>
          match lent.mapM (fun (_, p) => resolve σ1 env p) with
          | some ls =>
            if vs.length = d.owns.length ∧ ls.length = d.refs.length then
              let (cells, σ2) := allocAll σ1 ((d.owns.map Prod.fst).zip vs)
              let cenv := cells ++ (d.refs.map Prod.fst).zip ls
              ret F O n hs (.callLendK x (cs.map Prod.snd) cenv ((d.owns.map Prod.snd).zip (cells.map Prod.snd)) env body)
                (eval F O n hs σ2 cenv d.body)
            else (.stuck, σ1)
          | none => (.stuck, σ1)
        | _, _ => (.stuck, σ)
    | .ite c a b =>
      match evalAtom σ env c with
      | some (.int k, σ1) => if k = 0 then eval F O n hs σ1 env b else eval F O n hs σ1 env a
      | _ => (.stuck, σ)
    | .throw_ a =>
      match evalAtom σ env a with
      | some (.int k, σ1) =>
        match find .fail hs with
        | some (.abort _ id) => (.abort id k, σ1)
        | _ => (.stuck, σ1)
      | _ => (.stuck, σ)
    | .try_ body x h =>
      let (id, σ1) := σ.fresh
      ret F O n hs (.catchK .fail id x env h) (eval F O n (.abort .fail id :: hs) σ1 env body)
    | .while_ c b => ret F O n hs (.whileC env c b) (eval F O n hs σ env c)
    | .defer τ d body => ret F O n hs (.deferK τ env d) (eval F O n hs σ env body)
    | .lend x _ p body =>
      match resolve σ env p with
      | some l => ret F O n hs .lendK (eval F O n hs σ ((x, l) :: env) body)
      | none => (.stuck, σ)
    | .lendIdx x _ p z body =>
      match resolve σ env p, lookup z env with
      | some c, some lz =>
        match σ.mem c, σ.mem lz with
        | some (.vec cs), some (.int k) =>
          if 0 ≤ k then
            match cs[k.toNat]? with
            | some l => ret F O n hs .lendK (eval F O n hs σ ((x, l) :: env) body)
            | none => (.panic, σ)
          else (.panic, σ)
        | _, _ => (.stuck, σ)
      | _, _ => (.stuck, σ)
    | .perform ef owned lent =>
      match O[ef]? with
      | none => (.stuck, σ)
      | some _ =>
        match evalAtoms σ env owned with
        | some (vs, σ1) =>
          match lent.mapM (fun (_, p) => resolve σ1 env p) with
          | some ls =>
            match find (.eff ef) hs with
            | some (.capture _ id) => (.susp id ef vs ls [], σ1)
            | some (.cancel id) => (.susp id ef vs ls [], σ1)
            | some (.abort _ id) =>
              match vs with
              | [.int k] => (.abort id k, σ1)
              | _ => (.stuck, σ1)
            | _ => (.stuck, σ1)
          | none => (.stuck, σ1)
        | none => (.stuck, σ)
    | .handle τ body ef caps os rs arm =>
      match caps.mapM (fun c => resolve σ env c.loc) with
      | some ls =>
        let (id, σ1) := σ.fresh
        ret F O n hs (.capK τ ef id (List.zipWith Cap.at caps ls) os rs arm none)
          (eval F O n (.capture ef id :: hs) σ1 env body)
      | none => (.stuck, σ)
    | .handleAbort body ef x h =>
      let (id, σ1) := σ.fresh
      ret F O n hs (.catchK (.eff ef) id x env h) (eval F O n (.capture ef id :: .abort (.eff ef) id :: hs) σ1 env body)
    | .handleR τ body ef caps os rs arm C f =>
      match caps.mapM (fun c => resolve σ env c.loc) with
      | some ls =>
        let (id, σ1) := σ.fresh
        ret F O n hs (.capK τ ef id (List.zipWith Cap.at caps ls) os rs arm (some (C, τ, f, env, caps)))
          (eval F O n (.capture ef id :: hs) σ1 env body)
      | none => (.stuck, σ)
    | .par ef fa oa la fb ob lb =>
      match F[fa]?, F[fb]? with
      | some da, some db =>
        match evalAtoms σ env (oa ++ ob) with
        | some (vs, σ1) =>
          match (la ++ lb).mapM (fun p => resolve σ1 env p) with
          | some ls =>
            if vs.length = da.owns.length + db.owns.length ∧ ls.length = da.refs.length + db.refs.length then
              let (cA, σ2) := allocAll σ1 ((da.owns.map Prod.fst).zip (vs.take da.owns.length))
              let (cB, σ3) := allocAll σ2 ((db.owns.map Prod.fst).zip (vs.drop da.owns.length))
              let (id, σ4) := σ3.fresh
              ret F O n hs (.parS ef id da.ret db.ret true
                  [.callK ((db.owns.map Prod.snd).zip (cB.map Prod.snd)),
                    .startK (cB ++ (db.refs.map Prod.fst).zip (ls.drop da.refs.length)) db.body])
                (evalK F O n (.capture ef id :: hs) σ4
                  [.callK ((da.owns.map Prod.snd).zip (cA.map Prod.snd)),
                    .startK (cA ++ (da.refs.map Prod.fst).zip (ls.take da.refs.length)) da.body]
                  (.val (.int 0)))
            else (.stuck, σ1)
          | none => (.stuck, σ1)
        | none => (.stuck, σ)
      | _, _ => (.stuck, σ)
    | .scope e eS caps τ body =>
      match caps.mapM (fun c => resolve σ env c.loc) with
      | some ls =>
        let (id, σ1) := σ.fresh
        ret F O n hs (.scB e eS id τ (List.zipWith Cap.at caps ls) [])
          (eval F O n (.capture e id :: .capture eS id :: hs) σ1 env body)
      | none => (.stuck, σ)
    | .handleV τ e f owned fa =>
      match F[f]? with
      | some d =>
        match evalAtoms σ env owned with
        | some (vs, σ1) =>
          if vs.length = d.owns.length ∧ d.refs = [] then
            let (g, σ2) := σ1.fresh
            let ff := decide (Label.fail ∈ d.row)
            ret F O n hs (.capV τ e g fa ff (vs.flatMap (Val.tree σ1)) σ2.next)
              (let (cells, σ4) := allocAll σ2 ((d.owns.map Prod.fst).zip vs)
               ret F O n (fiberHS e g ff hs) (.callK ((d.owns.map Prod.snd).zip (cells.map Prod.snd)))
                 (eval F O n (fiberHS e g ff hs) σ4 cells d.body))
          else (.stuck, σ1)
        | none => (.stuck, σ)
      | none => (.stuck, σ)
    | .resume x a =>
      match lookup x env with
      | some c =>
        match σ.mem c with
        | some (.kont (.capV τ e g fa ff _ _ :: K) X) =>
          match evalAtom (σ.set c (some .moved)) env a with
          | some (v, σ1) =>
            ret F O n hs (.capV τ e g fa ff (X ++ v.tree σ1) σ1.next) (evalK F O n (fiberHS e g ff hs) σ1 K (.val v))
          | none => (.stuck, σ)
        | _ => (.stuck, σ)
      | none => (.stuck, σ)
    | .gen eN eY τy τb f owned caps body =>
      match F[f]? with
      | some d =>
        match evalAtoms σ env owned with
        | some (vs, σ1) =>
          match caps.mapM (fun c => resolve σ1 env c.loc) with
          | some ls =>
            if vs.length = d.owns.length ∧ ls.length = d.refs.length then
              let (cP, σ2) := allocAll σ1 ((d.owns.map Prod.fst).zip vs)
              let (id, σ3) := σ2.fresh
              ret F O n hs (.genC eN eY id τy τb (some [.callK ((d.owns.map Prod.snd).zip (cP.map Prod.snd)),
                  .startK (cP ++ (d.refs.map Prod.fst).zip ls) d.body]))
                (eval F O n (.capture eN id :: hs) σ3 env body)
            else (.stuck, σ1)
          | none => (.stuck, σ1)
        | none => (.stuck, σ)
      | none => (.stuck, σ)
    | .region R _ body =>
      let (a, σ1) := σ.alloc (.arena [])
      ret F O n hs (.regionK a) (eval F O n hs σ1 ((R, a) :: env) body)
    | .ralloc R c τ a =>
      match lookup R env with
      | some c =>
        match σ.mem c with
        | some (.arena cs) =>
          match evalAtom σ env a with
          | some (v, σ1) =>
            let (l, σ2) := σ1.alloc v
            (.val (.rptr l), (σ2.set c (some (.arena (cs ++ [l])))).tag l c τ)
          | none => (.stuck, σ)
        | _ => (.stuck, σ)
      | none => (.stuck, σ)
    | .rget p =>
      match resolve σ env p with
      | some c =>
        match σ.mem c with
        | some (.rptr l) =>
          match σ.mem l with
          | some v => (.val v, σ)
          | none => (.stuck, σ)
        | _ => (.stuck, σ)
      | none => (.stuck, σ)
    | .rset _ p a =>
      match evalAtom σ env a with
      | some (v, σ1) =>
        match resolve σ1 env p with
        | some c =>
          match σ1.mem c with
          | some (.rptr l) =>
            match σ1.mem l with
            | some _ => (.val (.int 0), σ1.set l (some v))
            | none => (.stuck, σ)
          | _ => (.stuck, σ)
        | none => (.stuck, σ)
      | none => (.stuck, σ)
    | .rlnew R τ =>
      match lookup R env with
      | some c =>
        match σ.mem c with
        | some (.arena cs) =>
          let (l, σ2) := σ.alloc (.vec [])
          (.val (.rptr l), (σ2.set c (some (.arena (cs ++ [l])))).tag l c (.vec true τ))
        | _ => (.stuck, σ)
      | none => (.stuck, σ)
    | .rpush R τ p a =>
      match lookup R env, evalAtom σ env a with
      | some c, some (v, σ1) =>
        match σ1.mem c, resolve σ1 env p with
        | some (.arena cs), some q =>
          match σ1.mem q with
          | some (.rptr lc) =>
            match σ1.mem lc with
            | some (.vec ls) =>
              let (l, σ2) := σ1.alloc v
              let σ3 := (σ2.set c (some (.arena (cs ++ [l])))).tag l c τ
              (.val (.int 0), σ3.set lc (some (.vec (ls ++ [l]))))
            | _ => (.stuck, σ1)
          | _ => (.stuck, σ1)
        | _, _ => (.stuck, σ1)
      | _, _ => (.stuck, σ)
    | .rnth _ p z =>
      match resolve σ env p, lookup z env with
      | some q, some lz =>
        match σ.mem q, σ.mem lz with
        | some (.rptr lc), some (.int i) =>
          match σ.mem lc with
          | some (.vec ls) =>
            if 0 ≤ i then
              match ls[i.toNat]? with
              | some l =>
                match σ.mem l with
                | some v => (.val v, σ)
                | none => (.stuck, σ)
              | none => (.panic, σ)
            else (.panic, σ)
          | _ => (.stuck, σ)
        | _, _ => (.stuck, σ)
      | _, _ => (.stuck, σ)
    | .rlen _ p =>
      match resolve σ env p with
      | some q =>
        match σ.mem q with
        | some (.rptr lc) =>
          match σ.mem lc with
          | some (.vec ls) => (.val (.int ls.length), σ)
          | _ => (.stuck, σ)
        | _ => (.stuck, σ)
      | none => (.stuck, σ)
    | .vnew => (.val (.vec []), σ)
    | .vlen p =>
      match resolve σ env p with
      | some c =>
        match σ.mem c with
        | some (.vec cs) => (.val (.int cs.length), σ)
        | _ => (.stuck, σ)
      | none => (.stuck, σ)
    | .lendSlice x _ p lo hi body =>
      match resolve σ env p, lookup lo env, lookup hi env with
      | some c, some l1, some l2 =>
        match σ.mem c, σ.mem l1, σ.mem l2 with
        | some (.vec cs), some (.int i), some (.int j) =>
          if 0 ≤ i ∧ i ≤ j ∧ j ≤ cs.length then
            let (a, σ1) := σ.alloc (.vec ((cs.drop i.toNat).take (j.toNat - i.toNat)))
            ret F O n hs (.cloK a) (eval F O n hs σ1 ((x, a) :: env) body)
          else (.panic, σ)
        | _, _, _ => (.stuck, σ)
      | _, _, _ => (.stuck, σ)
    | .vpop p =>
      match resolve σ env p with
      | some c =>
        match σ.mem c with
        | some (.vec cs) =>
          match cs.getLast? with
          | some l => (.val (.tag .int .int false l), σ.set c (some (.vec cs.dropLast)))
          | none =>
            let (b, σ1) := σ.alloc (.int 0)
            (.val (.tag .int .int true b), σ1)
        | _ => (.stuck, σ)
      | none => (.stuck, σ)
    | .vpush p a =>
      match evalAtom σ env a with
      | some (v, σ1) =>
        match resolve σ1 env p with
        | some c =>
          match σ1.mem c with
          | some (.vec cs) =>
            match σ1.moveAll cs with
            | some (cs', σ2) =>
              let (l, σ3) := σ2.alloc v
              (.val (.int 0), σ3.set c (some (.vec (cs' ++ [l]))))
            | none => (.stuck, σ1)
          | _ => (.stuck, σ1)
        | none => (.stuck, σ1)
      | none => (.stuck, σ)
termination_by (n, 2, 0)

/-- What frame `f` does with what the code it ran gave, under the handlers `hs` around it. -/
def ret (F : List Fn) (O : List Op) (n : Nat) (hs : HS) : Kont → Res × Store → Res × Store
  | .capK τ e id caps os rs arm post, (.susp j ef vs ls K, σ) =>
    if j ≠ id ∨ ef ≠ e then (.susp j ef vs ls (.capK τ e id caps os rs arm post :: K), σ) else
    match O[e]? with
    | none => (.stuck, σ)
    | some op =>
      if vs.length = os.length ∧ ls.length = rs.length then
        let K' := Kont.capK τ e id caps os rs arm post :: K
        let (cells, σ2) := allocAll σ (os.zip vs)
        armEnd (flushR F O n) τ (op.owns.zip (cells.map Prod.snd)) K' post
          (fun σ v => match n with
            | 0 => (.timeout, σ)
            | m + 1 =>
              match post with
              | none => evalK F O m hs σ K' (.val v)
              | some (C, _, f, env', cps) =>
                match v with
                | .tag _ _ t l =>
                  match σ.mem l with
                  | some w =>
                    if t then
                      match w with
                      | .pair b c =>
                        match σ.mem b, σ.mem c with
                        | some vr, some vc =>
                          ret F O m hs (.postR C f vc env' cps)
                            (evalK F O m hs (((σ.set l none).set b none).set c none) K' (.val vr))
                        | _, _ => (.stuck, σ)
                      | _ => (.stuck, σ)
                    else
                      let (d, σ1) := (σ.set l none).fresh
                      dropRet (flushR F O (m + 1)) τ (.val w) d (evalK F O m (.abort .drop d :: hs) σ1 K' (.abort d 0))
                  | none => (.stuck, σ)
                | _ => (.stuck, σ))
          (fun σ o => match n with
            | 0 => (.timeout, σ)
            | m + 1 =>
              let (d, σ1) := σ.fresh
              dropRet (flushR F O (m + 1)) τ o d (evalK F O m (.abort .drop d :: hs) σ1 K' (.abort d 0)))
          (eval F O n hs σ2 (cells ++ rs.zip ls ++ caps.map (fun c => (c.name, c.loc))) arm)
      else (.stuck, σ)
  | .parS e id τa τb side Ko, (.susp j ef vs ls K, σ) =>
    if j ≠ id ∨ ef ≠ e then (.susp j ef vs ls (.parS e id τa τb side Ko :: K), σ) else
    match n with
    | 0 => (.timeout, σ)
    | m + 1 =>
      let (t, σ1) := σ.fresh
      if σ.sched t then
        ret F O m hs (.parS e id τa τb side Ko) (evalK F O m (.capture e id :: hs) σ1 K (.val (.int 0)))
      else
        ret F O m hs (.parS e id τa τb (!side) K) (evalK F O m (.capture e id :: hs) σ1 Ko (.val (.int 0)))
  | .parD e id τa τb side w, (.susp j ef vs ls K, σ) =>
    if j ≠ id ∨ ef ≠ e then (.susp j ef vs ls (.parD e id τa τb side w :: K), σ) else
    match n with
    | 0 => (.timeout, σ)
    | m + 1 => ret F O m hs (.parD e id τa τb side w) (evalK F O m (.capture e id :: hs) σ K (.val (.int 0)))
  | .parY e id, (.susp j ef vs ls K, σ) =>
    if j ≠ id ∨ ef ≠ e then (.susp j ef vs ls (.parY e id :: K), σ) else
    match n with
    | 0 => (.timeout, σ)
    | m + 1 => ret F O m hs (.parY e id) (evalK F O m (.capture e id :: hs) σ K (.val (.int 0)))
  | .genC eN eY id τy τb Kp, (.susp j ef vs ls K, σ) =>
    if j ≠ id ∨ ef ≠ eN then (.susp j ef vs ls (.genC eN eY id τy τb Kp :: K), σ) else
    match n with
    | 0 => (.timeout, σ)
    | m + 1 =>
      match Kp with
      | some Kq => ret F O m hs (.genP eN eY id τy τb K) (evalK F O m (.capture eY id :: hs) σ Kq (.val (.int 0)))
      | none =>
        let (b, σ1) := σ.alloc (.int 0)
        ret F O m hs (.genC eN eY id τy τb none) (evalK F O m (.capture eN id :: hs) σ1 K (.val (.tag .int τy true b)))
  | .genP eN eY id τy τb Kc, (.susp j ef vs ls K, σ) =>
    if j ≠ id ∨ ef ≠ eY then (.susp j ef vs ls (.genP eN eY id τy τb Kc :: K), σ) else
    match n, vs with
    | 0, _ => (.timeout, σ)
    | m + 1, [v] =>
      let (b, σ1) := σ.alloc v
      ret F O m hs (.genC eN eY id τy τb (some K)) (evalK F O m (.capture eN id :: hs) σ1 Kc (.val (.tag .int τy false b)))
    | _ + 1, _ => (.stuck, σ)
  | .genY eY id τy, (.susp j ef vs ls K, σ) =>
    if j ≠ id ∨ ef ≠ eY then (.susp j ef vs ls (.genY eY id τy :: K), σ) else
    match n, vs with
    | 0, _ => (.timeout, σ)
    | m + 1, [v] =>
      match drop σ τy v with
      | some σ1 =>
        andThen (flushR F O (m + 1) (konts σ τy v) σ1) fun σ2 =>
          ret F O m hs (.genY eY id τy) (evalK F O m (.capture eY id :: hs) σ2 K (.val (.int 0)))
      | none => (.stuck, σ)
    | _ + 1, _ => (.stuck, σ)
  | .genN eN id τy, (.susp j ef vs ls K, σ) =>
    if j ≠ id ∨ ef ≠ eN then (.susp j ef vs ls (.genN eN id τy :: K), σ) else
    match n with
    | 0 => (.timeout, σ)
    | m + 1 =>
      let (b, σ1) := σ.alloc (.int 0)
      ret F O m hs (.genN eN id τy) (evalK F O m (.capture eN id :: hs) σ1 K (.val (.tag .int τy true b)))
  | .genE τb o d, (.susp j ef vs ls K, σ) => (.susp j ef vs ls (.genE τb o d :: K), σ)
  | .scB e eS id τ cz Q, (.susp j ef vs ls K, σ) =>
    if j ≠ id ∨ (ef ≠ e ∧ ef ≠ eS) then (.susp j ef vs ls (.scB e eS id τ cz Q :: K), σ) else
    match n with
    | 0 => (.timeout, σ)
    | m + 1 =>
      if ef = eS then
        match vs with
        | [v] =>
          match mkTask F cz σ v with
          | some (Kt, σ1) =>
            ret F O m hs (.scB e eS id τ cz (Q ++ [Kt]))
              (evalK F O m (.capture e id :: .capture eS id :: hs) σ1 K (.val (.int 0)))
          | none => (.stuck, σ)
        | _ => (.stuck, σ)
      else
        let (t, σ1) := σ.fresh
        match Q with
        | [] => ret F O m hs (.scB e eS id τ cz []) (evalK F O m (.capture e id :: .capture eS id :: hs) σ1 K (.val (.int 0)))
        | Kt :: Q' =>
          if σ.sched t then
            ret F O m hs (.scB e eS id τ cz (Kt :: Q')) (evalK F O m (.capture e id :: .capture eS id :: hs) σ1 K (.val (.int 0)))
          else
            ret F O m hs (.scW e eS id τ cz K Q') (evalK F O m (.capture e id :: .capture eS id :: hs) σ1 Kt (.val (.int 0)))
  | .scW e eS id τ cz Kb Q, (.susp j ef vs ls K, σ) =>
    if j ≠ id ∨ (ef ≠ e ∧ ef ≠ eS) then (.susp j ef vs ls (.scW e eS id τ cz Kb Q :: K), σ) else
    match n with
    | 0 => (.timeout, σ)
    | m + 1 =>
      if ef = eS then
        match vs with
        | [v] =>
          match mkTask F cz σ v with
          | some (Kt, σ1) =>
            ret F O m hs (.scW e eS id τ cz Kb (Q ++ [Kt]))
              (evalK F O m (.capture e id :: .capture eS id :: hs) σ1 K (.val (.int 0)))
          | none => (.stuck, σ)
        | _ => (.stuck, σ)
      else
        let (t, σ1) := σ.fresh
        if σ.sched t then
          ret F O m hs (.scW e eS id τ cz Kb Q) (evalK F O m (.capture e id :: .capture eS id :: hs) σ1 K (.val (.int 0)))
        else
          ret F O m hs (.scB e eS id τ cz (Q ++ [K])) (evalK F O m (.capture e id :: .capture eS id :: hs) σ1 Kb (.val (.int 0)))
  | .scV e eS id τ cz v Q, (.susp j ef vs ls K, σ) =>
    if j ≠ id ∨ (ef ≠ e ∧ ef ≠ eS) then (.susp j ef vs ls (.scV e eS id τ cz v Q :: K), σ) else
    match n with
    | 0 => (.timeout, σ)
    | m + 1 =>
      if ef = eS then
        match vs with
        | [w] =>
          match mkTask F cz σ w with
          | some (Kt, σ1) =>
            ret F O m hs (.scV e eS id τ cz v (Q ++ [Kt]))
              (evalK F O m (.capture e id :: .capture eS id :: hs) σ1 K (.val (.int 0)))
          | none => (.stuck, σ)
        | _ => (.stuck, σ)
      else
        let (t, σ1) := σ.fresh
        match Q with
        | [] => ret F O m hs (.scV e eS id τ cz v []) (evalK F O m (.capture e id :: .capture eS id :: hs) σ1 K (.val (.int 0)))
        | Kt :: Q' =>
          if σ.sched t then
            ret F O m hs (.scV e eS id τ cz v (Kt :: Q')) (evalK F O m (.capture e id :: .capture eS id :: hs) σ1 K (.val (.int 0)))
          else
            ret F O m hs (.scV e eS id τ cz v (Q' ++ [K])) (evalK F O m (.capture e id :: .capture eS id :: hs) σ1 Kt (.val (.int 0)))
  | .scX e eS id, (.susp j ef vs ls K, σ) =>
    if j ≠ id ∨ (ef ≠ e ∧ ef ≠ eS) then (.susp j ef vs ls (.scX e eS id :: K), σ) else
    match n with
    | 0 => (.timeout, σ)
    | m + 1 =>
      if ef = eS then
        match vs with
        | [w] =>
          match drop σ (.fn .once .int .int [] .nil) w with
          | some σ1 =>
            andThen (flushR F O (m + 1) (konts σ (.fn .once .int .int [] .nil) w) σ1) fun σ2 =>
              ret F O m hs (.scX e eS id) (evalK F O m (.capture e id :: .capture eS id :: hs) σ2 K (.val (.int 0)))
          | none => (.stuck, σ)
        | _ => (.stuck, σ)
      else ret F O m hs (.scX e eS id) (evalK F O m (.capture e id :: .capture eS id :: hs) σ K (.val (.int 0)))
  | .scE e eS id τ τd o d Q, (.susp j ef vs ls K, σ) => (.susp j ef vs ls (.scE e eS id τ τd o d Q :: K), σ)
  | .catchK l id x env h, (.susp j ef vs ls K, σ) =>
    if l = .eff ef ∧ j = id then
      match n, vs with
      | 0, _ => (.timeout, σ)
      | m + 1, [.int k] =>
        ret F O m hs (.catchK l id x env h) (evalK F O m ((Kont.catchK l id x env h).push hs) σ K (.abort id k))
      | _ + 1, _ => (.stuck, σ)
    else (.susp j ef vs ls (.catchK l id x env h :: K), σ)
  | .capV τ e g fa ff B s, (.susp j ef vs ls K, σ) =>
    if j = g ∧ ef = e then
      match n with
      | 0 => (.timeout, σ)
      | m + 1 =>
        match F[fa]? with
        | some da =>
          let args := vs ++ [.kont (.capV τ e g fa ff B s :: K) (kfoot σ B s vs)]
          if args.length = da.owns.length ∧ ls = [] then
            let (cells, σ2) := allocAll σ ((da.owns.map Prod.fst).zip args)
            ret F O m hs (.callK ((da.owns.map Prod.snd).zip (cells.map Prod.snd))) (eval F O m hs σ2 cells da.body)
          else (.stuck, σ)
        | none => (.stuck, σ)
    else (.susp j ef vs ls [.enterK τ e g fa ff K
      ((kfoot σ B s vs).filter fun l => !(ls.flatMap (cellTree σ)).contains l) ls], σ)
  | .capD τ e g d, (.susp j ef vs ls K, σ) =>
    if j = g then
      match n with
      | 0 => (.timeout, σ)
      | m + 1 =>
        match O[ef]? with
        | some op =>
          match dropAll σ op.owns vs with
          | some σ1 =>
            andThen (flushR F O (m + 1) (kontsAll σ op.owns vs) σ1) fun σ2 =>
              ret F O m hs (.capD τ e g d) (evalK F O m (.cancel g :: hs) σ2 K
                (if op.task ∧ op.owns = [] ∧ op.refs = [] ∧ op.ret = .int then .val (.int 0) else .abort d 0))
          | none => (.stuck, σ)
        | none => (.stuck, σ)
    else (.susp j ef vs ls (.capD τ e g d :: K), σ)
  | f, (.susp j ef vs ls K, σ) =>
    match f with
    | .scopeK τ c => leave (flushR F O n) τ c (.susp j ef vs ls K, σ)
    | .deferV τ v => cleanV (flushR F O n) τ v (.susp j ef vs ls K, σ)
    | .deferA j' k => cleanA j' k (.susp j ef vs ls K, σ)
    | .armK τ cells K0 post => (.susp j ef vs ls (.armK τ cells K0 post :: K), σ)
    | .dropK τ o d => dropRet (flushR F O n) τ o d (.susp j ef vs ls K, σ)
    | f => (.susp j ef vs ls (f :: K), σ)
  | _, (.stuck, σ) => (.stuck, σ)
  | _, (.timeout, σ) => (.timeout, σ)
  | _, (.panic, σ) => (.panic, σ)
  | .letK x τ env b, (.val v, σ) =>
    let (c, σ2) := σ.alloc v
    leave (flushR F O n) τ c (eval F O n hs σ2 ((x, c) :: env) b)
  | .letK _ _ _ _, (.abort j k, σ) => (.abort j k, σ)
  | .scopeK τ c, r => leave (flushR F O n) τ c r
  | .callK cells, (r, σ) =>
    match dropCells σ cells with
    | some σ' => andThen (flushR F O n (cellsKonts σ cells) σ') fun σ'' => (r, σ'')
    | none => (.stuck, σ)
  | .callLendK x ps cenv cells env body, (.val (.int k), σ) =>
    match pick ps k with
    | some p =>
      match resolve σ cenv p with
      | some l =>
        match dropCells σ cells with
        | some σ' =>
          andThen (flushR F O n (cellsKonts σ cells) σ') fun σ1 =>
            match eval F O n hs σ1 ((x, l) :: env) body with
            | (.susp j ef vs ls K, σ'') => (.susp j ef vs ls (.lendK :: K), σ'')
            | r => r
        | none => (.stuck, σ)
      | none => (.stuck, σ)
    | none => (.stuck, σ)
  | .callLendK _ _ _ _ _ _, (.val _, σ) => (.stuck, σ)
  | .callLendK _ _ _ cells _ _, (.abort j k, σ) =>
    match dropCells σ cells with
    | some σ' => andThen (flushR F O n (cellsKonts σ cells) σ') fun σ'' => (.abort j k, σ'')
    | none => (.stuck, σ)
  | .catchK _ id x env h, (.abort j k, σ) =>
    if j = id then
      let (c, σ2) := σ.alloc (.int k)
      leave (flushR F O n) .int c (eval F O n hs σ2 ((x, c) :: env) h)
    else (.abort j k, σ)
  | .catchK _ _ _ _ _, (.val v, σ) => (.val v, σ)
  | .whileC _ _ _, (.val (.int 0), σ) => (.val (.int 0), σ)
  | .whileC env c b, (.val (.int _), σ) =>
    match eval F O n hs σ env b with
    | (.val (.int _), σ2) => eval F O n hs σ2 env (.while_ c b)
    | (.susp j ef vs ls K, σ2) => (.susp j ef vs ls (.whileB env c b :: K), σ2)
    | (.val _, σ2) => (.stuck, σ2)
    | r => r
  | .whileC _ _ _, (.val _, σ) => (.stuck, σ)
  | .whileC _ _ _, (.abort j k, σ) => (.abort j k, σ)
  | .whileB env c b, (.val (.int _), σ) => eval F O n hs σ env (.while_ c b)
  | .whileB _ _ _, (.val _, σ) => (.stuck, σ)
  | .whileB _ _ _, (.abort j k, σ) => (.abort j k, σ)
  | .deferK τ env d, (.val v, σ) => cleanV (flushR F O n) τ v (eval F O n hs σ env d)
  | .deferK _ env d, (.abort j k, σ) => cleanA j k (eval F O n hs σ env d)
  | .deferV τ v, r => cleanV (flushR F O n) τ v r
  | .deferA j k, r => cleanA j k r
  | .lendK, r => r
  | .cloK a, (r, σ) =>
    match σ.mem a with
    | some _ => (r, σ.set a none)
    | none => (.stuck, σ)
  | .capK _ _ _ _ _ _ _ _, (.val v, σ) => (.val v, σ)
  | .capK _ _ _ _ _ _ _ _, (.abort j k, σ) => (.abort j k, σ)
  | .postR _ f vc env' cps, (.val w, σ) =>
    match cps.mapM (fun c => resolve σ env' c.loc), F[f]? with
    | some ls, some d =>
      if [vc, w].length = d.owns.length ∧ ls.length = d.refs.length then
        let (cells, σ2) := allocAll σ ((d.owns.map Prod.fst).zip [vc, w])
        callRet (flushR F O n) ((d.owns.map Prod.snd).zip (cells.map Prod.snd))
          (eval F O n hs σ2 (cells ++ (d.refs.map Prod.fst).zip ls) d.body)
      else (.stuck, σ)
    | _, _ => (.stuck, σ)
  | .postR C _ vc _ _, (.abort j k, σ) =>
    match drop σ C vc with
    | some σ' => andThen (flushR F O n (konts σ C vc) σ') fun σ'' => (.abort j k, σ'')
    | none => (.stuck, σ)
  | .armK τ cells K post, r =>
    armEnd (flushR F O n) τ cells K post
      (fun σ v => match n with
        | 0 => (.timeout, σ)
        | m + 1 =>
          match post with
          | none => evalK F O m hs σ K (.val v)
          | some (C, _, f, env', cps) =>
            match v with
            | .tag _ _ t l =>
              match σ.mem l with
              | some w =>
                if t then
                  match w with
                  | .pair b c =>
                    match σ.mem b, σ.mem c with
                    | some vr, some vc =>
                      ret F O m hs (.postR C f vc env' cps)
                        (evalK F O m hs (((σ.set l none).set b none).set c none) K (.val vr))
                    | _, _ => (.stuck, σ)
                  | _ => (.stuck, σ)
                else
                  let (d, σ1) := (σ.set l none).fresh
                  dropRet (flushR F O (m + 1)) τ (.val w) d (evalK F O m (.abort .drop d :: hs) σ1 K (.abort d 0))
              | none => (.stuck, σ)
            | _ => (.stuck, σ))
      (fun σ o => match n with
        | 0 => (.timeout, σ)
        | m + 1 =>
          let (d, σ1) := σ.fresh
          dropRet (flushR F O (m + 1)) τ o d (evalK F O m (.abort .drop d :: hs) σ1 K (.abort d 0))) r
  | .dropK τ o d, r => dropRet (flushR F O n) τ o d r
  | .startK env b, (.val _, σ) => eval F O n hs σ env b
  | .startK _ _, (.abort j k, σ) => (.abort j k, σ)
  | .parS e id τa τb side Ko, (.val v, σ) =>
    match n with
    | 0 => (.timeout, σ)
    | m + 1 => ret F O m hs (.parD e id τa τb (!side) v) (evalK F O m (.capture e id :: hs) σ Ko (.val (.int 0)))
  | .parS e id τa τb side Ko, (.abort j k, σ) =>
    match n with
    | 0 => (.timeout, σ)
    | m + 1 =>
      let (d, σ1) := σ.fresh
      ret F O m hs .parE (dropRet (flushR F O (m + 1)) (if side then τb else τa) (.abort j k) d
        (ret F O m (.abort .drop d :: hs) (.parY e id)
          (evalK F O m (.capture e id :: .abort .drop d :: hs) σ1 Ko (.abort d 0))))
  | .parD _ _ _ _ side w, (.val v, σ) =>
    let (la, σ1) := σ.alloc (if side then v else w)
    let (lb, σ2) := σ1.alloc (if side then w else v)
    (.val (.pair la lb), σ2)
  | .parD _ _ τa τb side w, (.abort j k, σ) =>
    match drop σ (if side then τb else τa) w with
    | some σ' => andThen (flushR F O n (konts σ (if side then τb else τa) w) σ') fun σ'' => (.abort j k, σ'')
    | none => (.stuck, σ)
  | .parY _ _, r => r
  | .parE, r => r
  | .genC _ eY id τy τb Kp, (.val v, σ) =>
    match Kp with
    | none => (.val v, σ)
    | some Kq =>
      match n with
      | 0 => (.timeout, σ)
      | m + 1 =>
        let (d, σ1) := σ.fresh
        ret F O m hs (.genE τb (.val v) d) (ret F O m (.abort .drop d :: hs) (.genY eY id τy)
          (evalK F O m (.capture eY id :: .abort .drop d :: hs) σ1 Kq (.abort d 0)))
  | .genC _ eY id τy τb Kp, (.abort j k, σ) =>
    match Kp with
    | none => (.abort j k, σ)
    | some Kq =>
      match n with
      | 0 => (.timeout, σ)
      | m + 1 =>
        let (d, σ1) := σ.fresh
        ret F O m hs (.genE τb (.abort j k) d) (ret F O m (.abort .drop d :: hs) (.genY eY id τy)
          (evalK F O m (.capture eY id :: .abort .drop d :: hs) σ1 Kq (.abort d 0)))
  | .genP eN eY id τy τb Kc, (.val _, σ) =>
    match n with
    | 0 => (.timeout, σ)
    | m + 1 =>
      let (b, σ1) := σ.alloc (.int 0)
      ret F O m hs (.genC eN eY id τy τb none) (evalK F O m (.capture eN id :: hs) σ1 Kc (.val (.tag .int τy true b)))
  | .genP eN _ id τy τb Kc, (.abort j k, σ) =>
    match n with
    | 0 => (.timeout, σ)
    | m + 1 =>
      let (d, σ1) := σ.fresh
      ret F O m hs .lendK (dropRet (flushR F O (m + 1)) τb (.abort j k) d (ret F O m (.abort .drop d :: hs) (.genN eN id τy)
        (evalK F O m (.capture eN id :: .abort .drop d :: hs) σ1 Kc (.abort d 0))))
  | .genY _ _ _, r => r
  | .genN _ _ _, r => r
  | .genE τb o d, (.abort j k, σ) =>
    if j = d then (o.res, σ) else
    match o with
    | .val u =>
      match drop σ τb u with
      | some σ' => andThen (flushR F O n (konts σ τb u) σ') fun σ'' => (.abort j k, σ'')
      | none => (.stuck, σ)
    | .abort _ _ => (.abort j k, σ)
  | .genE τb o _, (.val _, σ) => (o.res, σ)
  | .scB e eS id τ cz Q, (.val v, σ) =>
    match Q, n with
    | [], _ => (.val v, σ)
    | _ :: _, 0 => (.timeout, σ)
    | Kt :: Q', m + 1 =>
      ret F O m hs (.scV e eS id τ cz v Q') (evalK F O m (.capture e id :: .capture eS id :: hs) σ Kt (.val (.int 0)))
  | .scB e eS id τ cz Q, (.abort j k, σ) =>
    match Q, n with
    | [], _ => (.abort j k, σ)
    | _ :: _, 0 => (.timeout, σ)
    | Kt :: Q', m + 1 =>
      let (d, σ1) := σ.fresh
      ret F O m hs (.scE e eS id τ .int (.abort j k) d Q') (ret F O m (.abort .drop d :: hs) (.scX e eS id)
        (evalK F O m (.capture e id :: .capture eS id :: .abort .drop d :: hs) σ1 Kt (.abort d 0)))
  | .scW e eS id τ cz Kb Q, (.val _, σ) =>
    match n with
    | 0 => (.timeout, σ)
    | m + 1 => ret F O m hs (.scB e eS id τ cz Q) (evalK F O m (.capture e id :: .capture eS id :: hs) σ Kb (.val (.int 0)))
  | .scW e eS id τ cz Kb Q, (.abort j k, σ) =>
    match n with
    | 0 => (.timeout, σ)
    | m + 1 =>
      let (d, σ1) := σ.fresh
      ret F O m hs (.scE e eS id τ τ (.abort j k) d Q) (ret F O m (.abort .drop d :: hs) (.scX e eS id)
        (evalK F O m (.capture e id :: .capture eS id :: .abort .drop d :: hs) σ1 Kb (.abort d 0)))
  | .scV e eS id τ cz v Q, (.val _, σ) =>
    match Q, n with
    | [], _ => (.val v, σ)
    | _ :: _, 0 => (.timeout, σ)
    | Kt :: Q', m + 1 =>
      ret F O m hs (.scV e eS id τ cz v Q') (evalK F O m (.capture e id :: .capture eS id :: hs) σ Kt (.val (.int 0)))
  | .scV e eS id τ cz v Q, (.abort j k, σ) =>
    match drop σ τ v with
    | none => (.stuck, σ)
    | some σ0 =>
      andThen (flushR F O n (konts σ τ v) σ0) fun σ' =>
      match Q, n with
      | [], _ => (.abort j k, σ')
      | _ :: _, 0 => (.timeout, σ')
      | Kt :: Q', m + 1 =>
        let (d, σ1) := σ'.fresh
        ret F O m hs (.scE e eS id τ .int (.abort j k) d Q') (ret F O m (.abort .drop d :: hs) (.scX e eS id)
          (evalK F O m (.capture e id :: .capture eS id :: .abort .drop d :: hs) σ1 Kt (.abort d 0)))
  | .scX _ _ _, r => r
  | .scE e eS id τ τd o d Q, (r, σ) =>
    let next : Option (Outcome × Store × List Val) :=
      match r with
      | .abort j k =>
        if j = d then some (o, σ, []) else
        match o with
        | .val u => (drop σ τ u).map fun σ' => (.abort j k, σ', konts σ τ u)
        | .abort _ _ => some (.abort j k, σ, [])
      | .val v => (drop σ τd v).map fun σ' => (o, σ', konts σ τd v)
      | _ => some (o, σ, [])
    match next with
    | none => (.stuck, σ)
    | some (o', σ0, ks) =>
      andThen (flushR F O n ks σ0) fun σ' =>
      match Q, n with
      | [], _ => (o'.res, σ')
      | _ :: _, 0 => (.timeout, σ')
      | Kt :: Q', m + 1 =>
        let (d', σ1) := σ'.fresh
        ret F O m hs (.scE e eS id τ .int o' d' Q') (ret F O m (.abort .drop d' :: hs) (.scX e eS id)
          (evalK F O m (.capture e id :: .capture eS id :: .abort .drop d' :: hs) σ1 Kt (.abort d' 0)))
  | .regionK a, (r, σ) =>
    match σ.mem a with
    | some (.arena cs) => (r, (σ.freeAll cs).set a none)
    | _ => (.stuck, σ)
  | .capV _ _ g _ _ _ _, (.abort j k, σ) =>
    if j = g then
      match find .fail hs with
      | some (.abort _ j') => (.abort j' k, σ)
      | _ => (.stuck, σ)
    else (.abort j k, σ)
  | .capV _ _ _ _ _ _ _, r => r
  | .enterK τ e g fa ff K X ls, (.val v, σ) =>
    match n with
    | 0 => (.timeout, σ)
    | m + 1 =>
      ret F O m hs (.capV τ e g fa ff (X ++ ls.flatMap (cellTree σ) ++ v.tree σ) σ.next)
        (evalK F O m (fiberHS e g ff hs) σ K (.val v))
  | .enterK τ e g _ _ K _ _, (.abort j k, σ) =>
    match n with
    | 0 => (.timeout, σ)
    | m + 1 =>
      let (d, σ1) := σ.fresh
      match evalK F O m (hsDie g d) σ1 (.capD τ e g d :: K) (.abort d 0) with
      | (.val _, σ2) => (.abort j k, σ2)
      | (.abort _ _, σ2) => (.abort j k, σ2)
      | r => r
  | .capD τ _ _ _, (.val v, σ) =>
    match drop σ τ v with
    | some σ1 => andThen (flushR F O n (konts σ τ v) σ1) fun σ2 => (.val (.int 0), σ2)
    | none => (.stuck, σ)
  | .capD _ _ _ _, (.abort j k, σ) => (.abort j k, σ)
termination_by _ _ => (n, 1, 0)

/-- A continuation given what the code it was taken at gives: its frames, the outermost first, each
putting in force the handler it did. -/
def evalK (F : List Fn) (O : List Op) (n : Nat) (hs : HS) (σ : Store) : List Kont → Res → Res × Store
  | [], r => (r, σ)
  | f :: K, r => ret F O n hs f (evalK F O n (f.push hs) σ K r)
termination_by K _ => (n, 1, sizeOf K + 1)

/-- Drops the continuations `vs`, each unwound to a barrier of its own, its cleanup running. -/
def flush (F : List Fn) (O : List Op) (n : Nat) : List Val → Store → Res × Store
  | [], σ => (.val (.int 0), σ)
  | .kont (.capV τ e g _ _ _ _ :: K) _ :: vs, σ =>
    let (d, σ1) := σ.fresh
    match evalK F O n (hsDie g d) σ1 (.capD τ e g d :: K) (.abort d 0) with
    | (.val _, σ2) => flush F O n vs σ2
    | (.abort _ _, σ2) => flush F O n vs σ2
    | r => r
  | _ :: _, σ => (.stuck, σ)
termination_by vs _ => (n, 3, sizeOf vs)

/-- Drops the values `vs` with what fuel is left. -/
def flushR (F : List Fn) (O : List Op) (n : Nat) (ks : List Val) (σ : Store) : Res × Store :=
  match n with
  | 0 => (.timeout, σ)
  | m + 1 => flush F O m ks σ
termination_by (n, 0, 1)
end


/-! ## Types -/

/-- What a variable is to the code it is in scope in: owned, live or moved; a borrow; lent `mut`
to a borrow the code holds for a while, and not to be reached until it ends; or one field of the pair
it holds lent to such a borrow, the field a hole in its type. -/
inductive Slot where
  | own (τ : Ty) (live : Bool)
  | ref (m : Mode) (τ : Ty)
  | lent (τ : Ty) (head : Bool)
  | half (t : Bool) (A B : Ty)
  deriving DecidableEq, Repr

def Slot.ty : Slot → Ty
  | .own τ _ | .ref _ τ | .lent τ _ => τ
  | .half t A B => .lent1 t A B

/-- A slot that may change what it holds but not its own first cell: a `mut` borrow of a closure,
which may call the closure, changing what it captured, but not put another closure in its place; or
a variable one field of whose pair is lent, which may change the other field but not the pair's
cell, which says where the field lent is. -/
def Slot.shell : Slot → Bool
  | .ref .mut τ => τ.shell
  | .half _ _ _ => true
  | _ => false

abbrev Ctx := List (Var × Slot)

/-- A slot said of a place `n` regions further in. -/
def Slot.shiftBy (n : Nat) : Slot → Slot
  | .own τ live => .own (τ.shiftBy n) live
  | .ref m τ => .ref m (τ.shiftBy n)
  | .lent τ h => .lent (τ.shiftBy n) h
  | .half t A B => .half t (A.shiftBy n) (B.shiftBy n)

/-- A context said of the body of a region inside it. -/
def Ctx.shift (Γ : Ctx) : Ctx := Γ.map fun p => (p.1, p.2.shiftBy 1)

def setSlot (Γ : Ctx) (x : Var) (s : Slot) : Ctx :=
  Γ.map fun (y, t) => if y = x then (y, s) else (y, t)

/-- A place's type, whether it may be changed through it, and the variable it is rooted at. -/
inductive PlaceTy (Γ : Ctx) : Place → Ty → Bool → Var → Prop
  | own : lookup x Γ = some (.own τ true) → PlaceTy Γ (.var x) τ true x
  | ref : lookup x Γ = some (.ref m τ) → PlaceTy Γ (.var x) τ (m == .mut) x
  | half : lookup x Γ = some (.half t A B) → τ = .lent1 t A B → PlaceTy Γ (.var x) τ true x
  | deref : PlaceTy Γ p (.box τ) w r → PlaceTy Γ (.deref p) τ w r
  | fst : PlaceTy Γ p (.pair A B) w r → PlaceTy Γ (.fst p) A w r
  | snd : PlaceTy Γ p (.pair A B) w r → PlaceTy Γ (.snd p) B w r

/-- `s'` is `s`, or, for an owned variable, `s` with what it holds perhaps moved: where branches
disagree, or where a failure may have left. -/
inductive Slot.Le : Slot → Slot → Prop
  | refl : Slot.Le s s
  | forget : τ.isHole = false → Slot.Le (.own τ false) (.own τ true)

/-- `Γ'` is `Γ` with some owned variables perhaps moved. -/
inductive Weaker : Ctx → Ctx → Prop
  | nil : Weaker [] []
  | cons : Slot.Le s' s → Weaker Γ' Γ → Weaker ((x, s') :: Γ') ((x, s) :: Γ)

/-- The places lent, each of the parameter's type and changeable where lent `mut`, with the mode
each is lent in and the variable it is rooted at. -/
inductive Lends (Γ : Ctx) : List (Mode × Place) → List (Mode × Ty) → List (Mode × Var) → Prop
  | nil : Lends Γ [] [] []
  | cons : PlaceTy Γ p τ w y → (m = .mut → w = true) → τ.whole = true → Lends Γ rest ts ys →
      Lends Γ ((m, p) :: rest) ((m, τ) :: ts) ((m, y) :: ys)

/-- A field of the pair a variable holds: the first, or the second. -/
def fieldOf (t : Bool) (y : Var) : Place := if t then .fst (.var y) else .snd (.var y)

/-- The variable a place is rooted at. -/
def Place.root : Place → Var
  | .var x => x
  | .deref p => p.root
  | .fst p => p.root
  | .snd p => p.root

/-- `q` is `p`, or a place reached from it. -/
inductive Place.Within : Place → Place → Prop
  | refl : Place.Within p p
  | deref : Place.Within q p → Place.Within (.deref q) p
  | fst : Place.Within q p → Place.Within (.fst q) p
  | snd : Place.Within q p → Place.Within (.snd q) p

/-- Two places in different fields of one pair. -/
def Place.Apart (p q : Place) : Prop :=
  ∃ r, (p.Within (.fst r) ∧ q.Within (.snd r)) ∨ (p.Within (.snd r) ∧ q.Within (.fst r))

theorem Place.Apart.not_var : ¬ Place.Apart (.var x) q := by
  rintro ⟨r, ⟨h, -⟩ | ⟨h, -⟩⟩ <;> cases h

theorem Place.apart_fields : Place.Apart (.fst p) (.snd p) := ⟨p, .inl ⟨.refl, .refl⟩⟩

/-- No field of `y`'s pair is lent: what it holds is whole. -/
def Unsplit (Γ : Ctx) (y : Var) : Prop := ∀ t A B, lookup y Γ ≠ some (.half t A B)

/-- No place is lent `mut` alongside another borrow of it, of what it holds, or of what holds it:
two places rooted at one variable are both lent `readonly`, or in different fields of a pair. -/
def LentApart (lent : List (Mode × Place)) : Prop :=
  lent.Pairwise fun a b => a.2.root = b.2.root → (a.1 = .ro ∧ b.1 = .ro) ∨ Place.Apart a.2 b.2

/-- No variable is lent `mut` alongside another borrow of it, or of what it holds: two places rooted
at one variable are both lent `readonly`. -/
def Exclusive (ys : List (Mode × Var)) : Prop :=
  ys.Pairwise fun a b => a.2 = b.2 → a.1 = .ro ∧ b.1 = .ro

/-- A slot only read: what the code a `handle` runs sees of a place it lent its arm. -/
def Slot.ro : Slot → Slot
  | .own τ _ => .ref .ro τ
  | .ref _ τ => .ref .ro τ
  | .lent τ h => .lent τ h
  | .half t A B => .ref .ro (.lent1 t A B)

/-- `Γ` with the variables `ys` only read. -/
def freeze (Γ : Ctx) (ys : List Var) : Ctx :=
  Γ.map fun (y, s) => if y ∈ ys then (y, s.ro) else (y, s)

/-- `Γ` with the variable `y` lent `mut` to a borrow: not to be reached while the borrow lives. -/
def hide (Γ : Ctx) (y : Var) : Ctx :=
  Γ.map fun (z, s) => if z = y then (z, .lent s.ty s.shell) else (z, s)

/-- What the code a borrow of a place rooted at `y` is in scope for sees of `y`: only read, if the
borrow is `readonly`, and nothing, if it is `mut`. -/
def lendCtx : Mode → Ctx → Var → Ctx
  | .ro, Γ, y => freeze Γ [y]
  | .mut, Γ, y => hide Γ y

/-- `Γb`, a context of the same variables as `Γ`, with the variables `ys` as `Γ` has them. -/
def thaw (Γ : Ctx) (ys : List Var) (Γb : Ctx) : Ctx :=
  List.zipWith (fun p q => if p.1 ∈ ys then p else q) Γ Γb

/-- `Γ` with the variables `ys` not to be reached, each lent `mut` in turn. -/
def hideAll (Γ : Ctx) : List Var → Ctx
  | [] => Γ
  | y :: ys => hideAll (hide Γ y) ys

/-- `Γb`, a context of the same variables as `hideAll Γ ys`, with the variables `ys` given back. -/
def unhideAll (Γ : Ctx) : List Var → Ctx → Ctx
  | [], Γb => Γb
  | y :: ys, Γb => thaw Γ [y] (unhideAll (hide Γ y) ys Γb)

/-- Two lists, element by element related by `R`. -/
inductive Pairs {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Pairs R [] []
  | cons : R a b → Pairs R as bs → Pairs R (a :: as) (b :: bs)

/-- What code sees of the variables `ys` while a borrow of a place rooted at one of them lives: only
read, if the borrow is `readonly`, and nothing, if it is `mut`; and once it ends, as they were. -/
def lendCtxs : Mode → Ctx → List Var → Ctx
  | .ro, Γ, ys => freeze Γ ys
  | .mut, Γ, ys => hideAll Γ ys

def unlend : Mode → Ctx → List Var → Ctx → Ctx
  | .ro, Γ, ys, Γb => thaw Γ ys Γb
  | .mut, Γ, ys, Γb => unhideAll Γ ys Γb

/-- The variables lent in mode `m`. -/
def roots (m : Mode) (ys : List (Mode × Var)) : List Var := (ys.filter (·.1 = m)).map Prod.snd

/-- The places a `handle` lends its arm, each of its type, and the variable each is rooted at, with
the mode it is lent in. What is lent `mut` is a whole variable the arm may change, live or itself a
`mut` borrow. -/
inductive Caps (Γ : Ctx) : List (Cap Place) → List (Mode × Var) → Prop
  | nil : Caps Γ [] []
  | ro : PlaceTy Γ p τ w y → τ.complete = true → Caps Γ rest ys → Caps Γ (⟨x, .ro, τ, p⟩ :: rest) ((.ro, y) :: ys)
  | mut : PlaceTy Γ (.var y) τ true y → τ.shell = false → τ.complete = true → Caps Γ rest ys →
      Caps Γ (⟨x, .mut, τ, .var y⟩ :: rest) ((.mut, y) :: ys)

/-- An arm's context: the operation's owned arguments, live, then its borrowed ones, then the
places its `handle` lent it, each as it was lent. -/
def armCtx (os : List Var) (rs : List Var) (op : Op) (caps : List (Var × Mode × Ty)) : Ctx :=
  (os.zip op.owns).map (fun p => (p.1, Slot.own p.2 true)) ++ (rs.zip op.refs).map (fun p => (p.1, Slot.ref p.2.1 p.2.2)) ++
    caps.map (fun c => (c.1, Slot.ref c.2.1 c.2.2))

/-- `AtomTy Γ a τ Γ'`: `a` has type `τ`, and leaves its variables as `Γ'` says. -/
inductive AtomTy (Γ : Ctx) : Atom → Ty → Ctx → Prop
  | lit : AtomTy Γ (.lit n) .int Γ
  | read : PlaceTy Γ p .int w y → AtomTy Γ (.read p) .int Γ
  /-- A reference into a region, copied. -/
  | readRef : PlaceTy Γ p (.rref c k τ) w y → AtomTy Γ (.read p) (.rref c k τ) Γ
  /-- A value moved out of its variable: a box, or a closure, passed or returned by value. -/
  | move : lookup x Γ = some (.own τ true) → τ.complete = true → AtomTy Γ (.move x) τ (setSlot Γ x (.own τ false))

/-- The owned arguments, in order, against the parameters' types. -/
inductive AtomsTy : Ctx → List Atom → List Ty → Ctx → Prop
  | nil : AtomsTy Γ [] [] Γ
  | cons : AtomTy Γ a τ Γ₁ → AtomsTy Γ₁ as τs Γ₂ → AtomsTy Γ (a :: as) (τ :: τs) Γ₂

/-- `Typed F O Γ e τ Γ' r`: `e` has type `τ`, leaves its variables as `Γ'` says — moved or not —
and performs only what the row `r` names. -/
inductive Typed (F : List Fn) (O : List Op) : Ctx → Expr → Ty → Ctx → Row → Prop
  | atom : AtomTy Γ a τ Γ₁ → Typed F O Γ (.atom a) τ Γ₁ r
  | add : AtomTy Γ a .int Γ₁ → AtomTy Γ₁ b .int Γ₂ → Typed F O Γ (.arith o a b) .int Γ₂ r
  | new : AtomTy Γ a τ Γ₁ → Typed F O Γ (.new a) (.box τ) Γ₁ r
  | pair : AtomTy Γ a A Γ₁ → AtomTy Γ₁ b B Γ₂ → Typed F O Γ (.pair a b) (.pair A B) Γ₂ r
  | inj : AtomTy Γ a (if t then A else B) Γ₁ → (Ty.sum A B).complete = true →
      Typed F O Γ (.inj A B t a) (.sum A B) Γ₁ r
  /-- Each arm owns what the tag carried; where they disagree, a variable is perhaps moved. -/
  | case : lookup x Γ = some (.own (.sum A B) true) → (Ty.sum A B).complete = true → lookup y Γ = none →
      Typed F O ((y, .own A true) :: setSlot Γ x (.own (.sum A B) false)) e₁ τ ((y, .own A l₁) :: Γ₁) r →
      Typed F O ((y, .own B true) :: setSlot Γ x (.own (.sum A B) false)) e₂ τ ((y, .own B l₂) :: Γ₂) r →
      Weaker Γ' Γ₁ → Weaker Γ' Γ₂ → Typed F O Γ (.case x y A B e₁ e₂) τ Γ' r
  /-- Each arm borrows what the tag carries, as a borrow of a place does. -/
  | caseRef : lookup x Γ = none → PlaceTy Γ p (.sum A B) w y → Unsplit Γ y → (m = .mut → w = true) →
      (m = .mut → A.shell = false ∧ B.shell = false) →
      Typed F O ((x, .ref m A) :: lendCtx m Γ y) e₁ τ ((x, .ref m A) :: Γb₁) r →
      Typed F O ((x, .ref m B) :: lendCtx m Γ y) e₂ τ ((x, .ref m B) :: Γb₂) r →
      Weaker Γb Γb₁ → Weaker Γb Γb₂ → Typed F O Γ (.caseRef x m p e₁ e₂) τ (thaw Γ [y] Γb) r
  | let_ : lookup x Γ = none → Typed F O Γ a τ Γ₁ r →
      Typed F O ((x, .own τ true) :: Γ₁) b τb ((x, .own τ live) :: Γ₂) r → Typed F O Γ (.let_ x τ a b) τb Γ₂ r
  | write : AtomTy Γ a .int Γ₁ → PlaceTy Γ₁ p .int true y → Typed F O Γ (.write p a) .int Γ₁ r
  /-- Nothing is put in place of a closure borrowed `mut`, or of what it captured. -/
  | assign : AtomTy Γ a τ Γ₁ → PlaceTy Γ₁ p τ true y → (∀ τ', lookup y Γ₁ = some (.ref .mut τ') → τ'.shell = false) →
      Typed F O Γ (.assign p τ a) .int Γ₁ r
  /-- A call: the function's regions are those of the code around, the `k`th of them its innermost. -/
  | call : F[f]? = some d → d.retp = none → d.cap = none → (∀ l ∈ d.row, l ∈ r) →
      AtomsTy Γ owned (d.owns.map fun p => p.2.shiftBy k) Γ₁ →
      Lends Γ₁ lent (d.refs.map fun p => (p.2.1, p.2.2.shiftBy k)) ys → LentApart lent →
      Typed F O Γ (.call f owned lent) (d.ret.shiftBy k) Γ₁ r
  /-- A closure captures a value, moved in, which may be a closure; its type says how it is called,
  what it takes and gives, and what it may perform, but not what it captured. -/
  | lam : F[f]? = some d → d.cap = some (xc, τc, k) → d.owns = [(pn, A)] →
      d.refs.map Prod.snd = R.toList.map (fun τ => (Mode.ro, τ)) →
      d.retp = none → AtomTy Γ a τc Γ₁ → τc.rfree = true → Typed F O Γ (.lam f a) (.fn k A d.ret d.row R) Γ₁ r
  /-- A closure called once is moved out of its variable. -/
  | applyOnce : lookup x Γ = some (.own (.fn .once A B r' .nil) true) → (∀ l ∈ r', l ∈ r) →
      AtomTy (setSlot Γ x (.own (.fn .once A B r' .nil) false)) a A Γ₁ →
      Typed F O Γ (.apply .once (.var x) a) B Γ₁ r
  /-- A closure called through a borrow: `mut` for one that changes what it captured. -/
  | applyBorrow : k ≠ .once → AtomTy Γ a A Γ₁ → PlaceTy Γ₁ p (.fn k A B r' .nil) w y → (k = .excl → w = true) →
      (∀ l ∈ r', l ∈ r) → Typed F O Γ (.apply k p a) B Γ₁ r
  /-- A closure over a `readonly` borrow is a borrow too: it is in scope for `body`, which may call
  it or lend it on, but not move it, and what the borrowed place is rooted at is only read meanwhile. -/
  | lendClo : F[f]? = some d → d.cap = some (xc, τc, .shared) → d.owns = [(pn, A)] → d.refs = [] →
      d.retp = none → τc.data = true → PlaceTy Γ p τc w y → lookup x Γ = none →
      Typed F O ((x, .ref .ro (.fn .shared A d.ret d.row .nil)) :: freeze Γ [y]) body τb
        ((x, .ref .ro (.fn .shared A d.ret d.row .nil)) :: Γb) r →
      Typed F O Γ (.lendClo x f p body) τb (thaw Γ [y] Γb) r
  /-- A closure over a `mut` borrow is a `mut` borrow too: `body` may call it, changing what it
  captured, or lend it on, but not move it or put another closure in its place; what the borrowed
  place is rooted at is out of reach meanwhile. -/
  | lendCloMut : F[f]? = some d → d.cap = some (xc, τc, .excl) → d.owns = [(pn, A)] → d.refs = [] →
      d.retp = none → τc.data = true → PlaceTy Γ p τc true y → Unsplit Γ y → lookup x Γ = none →
      Typed F O ((x, .ref .mut (.fn .excl A d.ret d.row .nil)) :: hide Γ y) body τb
        ((x, .ref .mut (.fn .excl A d.ret d.row .nil)) :: Γb) r →
      Typed F O Γ (.lendClo x f p body) τb (thaw Γ [y] Γb) r
  /-- The borrow a call returns is of what the caller lent it as one of its borrowed arguments,
  which the callee picks as it runs: as for a borrow of a place, the variables those it may pick are
  rooted at, `zs`, are only read, or not reached, while the borrow lives. -/
  | lendCall : F[f]? = some d → d.retp = some (m, cs) → d.cap = none → (∀ l ∈ d.row, l ∈ r) →
      AtomsTy Γ owned (d.owns.map Prod.snd) Γ₁ → Lends Γ₁ lent (d.refs.map Prod.snd) ys → LentApart lent →
      Pairs (fun c z => ∃ mi, ys[c.1]? = some (mi, z) ∧ (m = .mut → mi = .mut)) cs zs →
      (m = .mut → zs.Nodup ∧ d.ret.shell = false ∧ (∀ c ∈ cs, ∀ e, d.refs[c.1]? = some e → e.2.2.shell = false) ∧
        ∀ z ∈ zs, Unsplit Γ₁ z) →
      lookup x Γ₁ = none →
      Typed F O ((x, .ref m d.ret) :: lendCtxs m Γ₁ zs) body τb ((x, .ref m d.ret) :: Γb) r →
      Typed F O Γ (.lendCall x m f owned lent body) τb (unlend m Γ₁ zs Γb) r
  /-- Where the branches disagree, a variable is perhaps moved. -/
  | ite : AtomTy Γ c .int Γ₀ → Typed F O Γ₀ a τ Γa r → Typed F O Γ₀ b τ Γb r → Weaker Γ' Γa →
      Weaker Γ' Γb → Typed F O Γ (.ite c a b) τ Γ' r
  | throw_ : AtomTy Γ a .int Γ₁ → Label.fail ∈ r → Typed F O Γ (.throw_ a) τ Γ₁ r
  /-- The handler starts where the body would have ended: what the body moves is perhaps moved. -/
  | try_ : lookup x Γb = none → Typed F O Γ body τ Γb (.fail :: r) →
      Typed F O ((x, .own .int true) :: Γb) h τ ((x, .own .int live) :: Γh) r →
      Typed F O Γ (.try_ body x h) τ Γh r
  /-- A loop moves nothing: each pass starts where the one before started. -/
  | while_ : Typed F O Γ c .int Γ r → Typed F O Γ b .int Γ r → Typed F O Γ (.while_ c b) .int Γ r
  /-- A borrow lives as long as the code it is in scope for: what the place is rooted at is only
  read, or not reached, until it ends. -/
  | lend : lookup x Γ = none → PlaceTy Γ p τ w y → (m = .mut → w = true) → (m = .mut → τ.shell = false) →
      (m = .mut → Unsplit Γ y) →
      Typed F O ((x, .ref m τ) :: lendCtx m Γ y) body τb ((x, .ref m τ) :: Γb) r →
      Typed F O Γ (.lend x m p body) τb (thaw Γ [y] Γb) r
  /-- A generator: `body` asks for the values `f`'s run yields, each by `eN`, which gives `#Some` of
  one or `#Done`; `f` yields each by `eY`, and is lent the places of `caps` as a handler's arm is:
  `readonly`, which `body` may then only read, or whole bindings `mut`, which it may not reach. -/
  | gen : O[eN]? = some opN → opN.owns = [] → opN.refs = [] → opN.ret = .sum .int τy →
      O[eY]? = some opY → opY.owns = [τy] → opY.refs = [] → opY.ret = .int → τy.complete = true →
      F[f]? = some d → d.retp = none → d.cap = none → d.ret = .int → (∀ l ∈ d.row, l ∈ .eff eY :: r) →
      Label.eff eY ∈ d.row → d.refs = caps.map Cap.sig →
      AtomsTy Γ owned (d.owns.map Prod.snd) Γ₁ → Caps Γ₁ caps ys → Exclusive ys →
      Typed F O (freeze (hideAll Γ₁ (roots .mut ys)) (roots .ro ys)) body τb Γb (.eff eN :: r) → τb.complete = true →
      Typed F O Γ (.gen eN eY τy τb f owned caps body) τb
        (unhideAll Γ₁ (roots .mut ys) (thaw (hideAll Γ₁ (roots .mut ys)) (roots .ro ys) Γb)) r
  /-- A scope: its body, and every task it starts — a closure called once, which took what it captured
by moving it, and is lent `readonly` the scope's places `caps`, each a `readonly` borrow in scope —
give way by `e` and start tasks by `eS`; what else they perform goes on to the code around. -/
  | scope : O[e]? = some op → op.task = true → op.owns = [] → op.refs = [] → op.ret = .int →
      O[eS]? = some opS → opS.owns = [.fn .once .int .int rT R] → opS.refs = [] → opS.ret = .int → e ≠ eS →
      (∀ l ∈ rT, l ∈ .eff e :: .eff eS :: r) → Label.eff e ∈ rT → τ.complete = true →
      R.toList = caps.map Cap.ty →
      (∀ c ∈ caps, c.mode = .ro ∧ ∃ y, c.loc = .var y ∧ lookup y Γ = some (.ref .ro c.ty)) →
      Typed F O Γ body τ Γb (.eff e :: .eff eS :: r) → Typed F O Γ (.scope e eS caps τ body) τ Γb r
  /-- A borrow of an element of a vector, for the code it is in scope for: it is a borrow of the
  whole vector, which is only read, or not reached, until it ends. -/
  | lendIdx : lookup x Γ = none → PlaceTy Γ p (.vec g τ) w y → PlaceTy Γ (.var z) .int wz yz →
      (m = .mut → w = true) → (m = .mut → τ.shell = false) → (m = .mut → Unsplit Γ y) →
      Typed F O ((x, .ref m τ) :: lendCtx m Γ y) body τb ((x, .ref m τ) :: Γb) r →
      Typed F O Γ (.lendIdx x m p z body) τb (thaw Γ [y] Γb) r
  /-- A borrow of one field of a variable's pair, for the code it is in scope for: the variable
  stays in reach, the field a hole in its type, and the field beside it may be read, changed or
  lent meanwhile. -/
  | lendField : lookup x Γ = none → lookup y Γ = some s →
      s.ty = .pair A B → ((∃ τ, s = .own τ true) ∨ (∃ τ, s = .ref .mut τ) ∨ ∃ t' A' B', s = .half t' A' B') →
      (if t then A else B).complete = true → (m = .mut → (if t then A else B).shell = false) →
      Typed F O ((x, .ref m (if t then A else B)) ::
          setSlot Γ y (.half t A B)) body τb
        ((x, .ref m (if t then A else B)) :: Γb) r →
      Typed F O Γ (.lend x m (fieldOf t y) body) τb (thaw Γ [y] Γb) r
  /-- Cleanup starts where the body would have ended, and moves nothing. -/
  | defer : Typed F O Γ body τ Γb r → Typed F O Γb d .int Γb r → Typed F O Γ (.defer τ d body) τ Γb r
  | perform : O[e]? = some op → Label.eff e ∈ r → AtomsTy Γ owned op.owns Γ₁ →
      Lends Γ₁ lent op.refs ys → LentApart lent → Typed F O Γ (.perform e owned lent) op.ret Γ₁ r
  /-- The arm runs in the context of the `handle`: its row is the `handle`'s. What it is lent of
  the `handle`'s scope the body may only read, or, lent `mut`, not reach. -/
  | handle : O[e]? = some op → op.task = false → (∀ τ ∈ op.owns, τ.complete = true) → os.length = op.owns.length →
      rs.length = op.refs.length →
      Caps Γ caps ys → Exclusive ys → (os ++ rs ++ caps.map Cap.name).Nodup →
      Typed F O (armCtx os rs op (caps.map Cap.sig)) arm op.ret Γa r →
      Typed F O (freeze (hideAll Γ (roots .mut ys)) (roots .ro ys)) body τ Γb (.eff e :: r) →
      Typed F O Γ (.handle τ body e caps os rs arm) τ
        (unhideAll Γ (roots .mut ys) (thaw (hideAll Γ (roots .mut ys)) (roots .ro ys) Γb)) r
  /-- An arm that may resume in its midst: it takes the operation's arguments and the places of
  `caps`, and gives `#Resume([v, c])`, what the code resumes with and what it carries, or `#Done(u)`,
  the `handle`'s value, the code dropped; once the rest of a resumed `handle` ends, `post` takes what
  the arm carried and that value, the places lent to it again, as a call would. -/
  | handleR : O[e]? = some op → op.task = false → (∀ τ ∈ op.owns, τ.complete = true) →
      os.length = op.owns.length → rs.length = op.refs.length → Caps Γ caps ys → Exclusive ys →
      (os ++ rs ++ caps.map Cap.name).Nodup →
      F[f]? = some d → d.owns.map Prod.snd = [C, τ] → d.refs = caps.map Cap.sig → d.retp = none →
      d.cap = none → d.ret = τ → (∀ l ∈ d.row, l ∈ r) → C.complete = true →
      Typed F O (armCtx os rs op (caps.map Cap.sig)) arm (.sum (.pair op.ret C) τ) Γa r →
      Typed F O (freeze (hideAll Γ (roots .mut ys)) (roots .ro ys)) body τ Γb (.eff e :: r) →
      Typed F O Γ (.handleR τ body e caps os rs arm C f) τ
        (unhideAll Γ (roots .mut ys) (thaw (hideAll Γ (roots .mut ys)) (roots .ro ys) Γb)) r
  /-- As for `try`, the arm starts where the body would have ended. -/
  | handleAbort : O[e]? = some op → op.owns = [.int] → op.refs = [] → lookup x Γb = none →
      Typed F O Γ body τ Γb (.eff e :: r) →
      Typed F O ((x, .own .int true) :: Γb) h τ ((x, .own .int live) :: Γh) r →
      Typed F O Γ (.handleAbort body e x h) τ Γh r

  /-- Two tasks: calls that take their owned arguments and are lent places only `readonly`, both
  of which the code around reads at most meanwhile; each may give way by performing `e`, which takes
  nothing and gives an integer, and may perform what the code around may. -/
  | par : O[e]? = some op → op.task = true → op.owns = [] → op.refs = [] → op.ret = .int →
      F[fa]? = some da → F[fb]? = some db → da.retp = none → da.cap = none → db.retp = none → db.cap = none →
      Label.eff e ∈ da.row → Label.eff e ∈ db.row → (∀ l ∈ da.row, l ∈ .eff e :: r) → (∀ l ∈ db.row, l ∈ .eff e :: r) →
      da.ret.complete = true → db.ret.complete = true →
      AtomsTy Γ (oa ++ ob) (da.owns.map Prod.snd ++ db.owns.map Prod.snd) Γ₁ →
      Lends Γ₁ ((la ++ lb).map fun p => (.ro, p)) (da.refs.map Prod.snd ++ db.refs.map Prod.snd) ys →
      Typed F O Γ (.par e fa oa la fb ob lb) (.pair da.ret db.ret) Γ₁ r
  /-- A `handle` whose arm keeps its continuation: its body, a call of `f` given what may pass into
  a fiber, performs its operation, which no task gives way by, lends nothing, gives what may pass
  into a fiber and takes what may pass out of one, and what else the arm may; its value may pass out
  too; its arm, `fa`, takes what the operation does and the continuation, and performs `ra`, which the
  code around may. -/
  | handleV : O[e]? = some op → op.task = false → op.refs = [] → op.ret.cross = true →
      (∀ τ' ∈ op.owns, τ'.cross = true) → τ.cross = true →
      F[fa]? = some da → da.owns.map Prod.snd = op.owns ++ [.cont op.ret τ ra] → da.refs = [] → da.ret = τ →
      da.row = ra → da.retp = none → da.cap = none → (∀ l ∈ ra, l ∈ r) →
      F[f]? = some d → d.refs = [] → d.ret = τ → d.retp = none → d.cap = none → Label.eff e ∈ d.row →
      (∀ l ∈ d.row, l = .eff e ∨ (l ∈ ra ∧ l ≠ .drop)) → (∀ τ' ∈ d.owns.map Prod.snd, τ'.cross = true) →
      AtomsTy Γ owned (d.owns.map Prod.snd) Γ₁ →
      Typed F O Γ (.handleV τ e f owned fa) τ Γ₁ r
  /-- A kept continuation resumed: it is moved out of its variable, and what it performs, the code
  around may. -/
  | resume : lookup x Γ = some (.own (.cont A τ ra) true) → (∀ l ∈ ra, l ∈ r) →
      AtomTy (setSlot Γ x (.own (.cont A τ ra) false)) a A Γ₁ →
      Typed F O Γ (.resume x a) τ Γ₁ r
  /-- A region: its body sees its arena `R` as the innermost region, and the variables around it a
  region further out. Nothing the region holds outlives it: the type of its value, and what its body
  leaves of the variables around, are said of the code around. -/
  | region : lookup R Γ = none → τ.complete = true →
      Typed F O ((R, .own (.arena 0) true) :: Ctx.shift Γ) body (τ.shiftBy 1) ((R, .own (.arena 0) true) :: Ctx.shift Γ') r →
      Typed F O Γ (.region R τ body) τ Γ' r
  /-- Allocating in a region, through its arena, owned or lent `mut`: data the region may hold. -/
  | ralloc : lookup R Γ = some s → (s = .own (.arena k) true ∨ s = .ref .mut (.arena k)) → τ.rdata = true →
      AtomTy Γ a (τ.shiftBy k) Γ → Typed F O Γ (.ralloc R c τ a) (.rref c k τ) Γ r
  /-- Reading what a reference into a region refers to, its arena in reach. -/
  | rget : PlaceTy Γ p (.rref c k τ) w y → lookup R Γ = some s → (s = .own (.arena k) true ∨ ∃ m, s = .ref m (.arena k)) →
      τ.rdata = true → Typed F O Γ (.rget p) (τ.shiftBy k) Γ r
  /-- A new list of a region, through its arena, owned or lent `mut`, of data the region may hold. -/
  | rlnew : lookup R Γ = some s → (s = .own (.arena k) true ∨ s = .ref .mut (.arena k)) → τ.rdata = true →
      Typed F O Γ (.rlnew R τ) (.rref false k (.vec true τ)) Γ r
  /-- Pushing to a list of a region, through its arena, owned or lent `mut`. -/
  | rpush : PlaceTy Γ p (.rref c k (.vec true τ)) w y → lookup R Γ = some s →
      (s = .own (.arena k) true ∨ s = .ref .mut (.arena k)) → τ.rdata = true → AtomTy Γ a (τ.shiftBy k) Γ →
      Typed F O Γ (.rpush R τ p a) .int Γ r
  /-- Reading an element of a list of a region, its arena in reach. -/
  | rnth : PlaceTy Γ p (.rref c k (.vec true τ)) w y → PlaceTy Γ (.var z) .int wz yz → lookup R Γ = some s →
      (s = .own (.arena k) true ∨ ∃ m, s = .ref m (.arena k)) → τ.rdata = true →
      Typed F O Γ (.rnth R p z) (τ.shiftBy k) Γ r
  /-- A list's length, its arena in reach. -/
  | rlen : PlaceTy Γ p (.rref c k (.vec true τ)) w y → lookup R Γ = some s →
      (s = .own (.arena k) true ∨ ∃ m, s = .ref m (.arena k)) → Typed F O Γ (.rlen R p) .int Γ r
  /-- An empty vector. -/
  | vnew : τ.complete = true → Typed F O Γ .vnew (.vec true τ) Γ r
  /-- A vector's length, which reading it says. -/
  | vlen : PlaceTy Γ p (.vec g τ) w y → Typed F O Γ (.vlen p) .int Γ r
  /-- Pushing to a vector at a place that may be changed, the element moved in. -/
  | vpush : AtomTy Γ a τ Γ₁ → PlaceTy Γ₁ p (.vec true τ) true y → Typed F O Γ (.vpush p a) .int Γ₁ r
  /-- A slice of a vector, for the code it is in scope for: a run of the vector's elements, which it may
  change if it is `mut`, but not which run it is; the vector is only read, or not reached,
  meanwhile. -/
  | lendSlice : lookup x Γ = none → PlaceTy Γ p (.vec g τ) w y → PlaceTy Γ (.var lo) .int w1 y1 →
      PlaceTy Γ (.var hi) .int w2 y2 → (m = .mut → w = true) →
      Typed F O ((x, .ref m (.vec false τ)) :: lendCtx m Γ y) body τb ((x, .ref m (.vec false τ)) :: Γb) r →
      Typed F O Γ (.lendSlice x m p lo hi body) τb (thaw Γ [y] Γb) r
  /-- Taking the last element out of a vector at a place that may be changed. -/
  | vpop : PlaceTy Γ p (.vec true τ) true y → τ.complete = true → Typed F O Γ (.vpop p) (.sum .int τ) Γ r
  /-- Changing what a `Cell` of a region holds, through its arena, owned or lent `mut`. -/
  | rset : PlaceTy Γ p (.rref true k τ) w y → lookup R Γ = some s → (s = .own (.arena k) true ∨ s = .ref .mut (.arena k)) →
      τ.rdata = true → AtomTy Γ a (τ.shiftBy k) Γ → Typed F O Γ (.rset R p a) .int Γ r


end FlyCore.Ownership
