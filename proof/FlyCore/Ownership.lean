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

inductive Ty where
  | int
  | box (τ : Ty)
  /-- A closure called as `k`, taking an `A` and giving a `B`, performing what `r` names: what it
  captured is not part of its type. -/
  | fn (k : Kind) (A B : Ty) (r : Row)
  /-- Two values, each in a cell of its own: a record of two fields. -/
  | pair (A B : Ty)
  /-- A value of one type or the other, and which: a union of two tags. -/
  | sum (A B : Ty)
  /-- A place lent to a borrow: what holds it holds a `τ` there, but not for now. -/
  | hole (τ : Ty)
  deriving DecidableEq, Repr

/-- Plain data: integers and boxes of them, which a closure may capture. -/
def Ty.data : Ty → Bool
  | .int => true
  | .box τ => τ.data
  | .fn _ _ _ _ => false
  | .pair A B => A.data && B.data
  | .sum A B => A.data && B.data
  | .hole _ => false

/-- A pair whose first field, or whose second, is lent. -/
def Ty.lent1 (t : Bool) (A B : Ty) : Ty := if t then .pair (.hole A) B else .pair A (.hole B)

/-- A type with no place lent out of it. -/
def Ty.complete : Ty → Bool
  | .int => true
  | .box τ => τ.complete
  | .fn _ _ _ _ => true
  | .pair A B => A.complete && B.complete
  | .sum A B => A.complete && B.complete
  | .hole _ => false

def Ty.isHole : Ty → Bool
  | .hole _ => true
  | _ => false

/-- Plain data has no place lent out of it. -/
theorem Ty.data_complete : ∀ {τ : Ty}, τ.data = true → τ.complete = true
  | .int, _ => rfl
  | .box τ, h => by simp only [Ty.data] at h; simp only [Ty.complete]; exact Ty.data_complete h
  | .fn _ _ _ _, h => by simp [Ty.data] at h
  | .pair A B, h => by
    simp only [Ty.data, Bool.and_eq_true] at h
    simp only [Ty.complete, Bool.and_eq_true]; exact ⟨Ty.data_complete h.1, Ty.data_complete h.2⟩
  | .sum A B, h => by
    simp only [Ty.data, Bool.and_eq_true] at h
    simp only [Ty.complete, Bool.and_eq_true]; exact ⟨Ty.data_complete h.1, Ty.data_complete h.2⟩
  | .hole _, h => by simp [Ty.data] at h

theorem Ty.complete_ite {t : Bool} {A B : Ty} (hA : A.complete = true) (hB : B.complete = true) :
    (if t then A else B).complete = true := by
  cases t <;> simpa

theorem Ty.complete_not_hole {τ : Ty} (h : τ.complete = true) : τ.isHole = false := by
  cases τ <;> simp_all [Ty.complete, Ty.isHole]

theorem Ty.lent1_complete : (Ty.lent1 t A B).complete = false := by
  cases t <;> simp [Ty.lent1, Ty.complete]

theorem Ty.lent1_isHole : (Ty.lent1 t A B).isHole = false := by
  cases t <;> rfl

def Ty.isFn : Ty → Bool
  | .fn _ _ _ _ => true
  | _ => false

theorem Ty.data_not_fn {τ : Ty} (h : τ.data = true) : τ.isFn = false := by
  cases τ <;> simp_all [Ty.data, Ty.isFn]

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

/-- Expressions in A-normal form: what an operation takes is an atom, and `let` is the one way to
name what an expression gives, so that the code an expression is part of is a stack of `let`s and
of the scopes, calls and handlers around them. -/
inductive Expr where
  | atom (a : Atom)
  | add (a b : Atom)
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
  deriving Repr

/-- A user effect's operation: what it takes, owned and lent, and what it gives. -/
structure Op where
  owns : List Ty
  refs : List (Mode × Ty)
  ret : Ty

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
  deriving DecidableEq, Repr

/-- The store: its cells, `none` once freed or before allocation, the next to allocate, and the
next name for a handler put in force. -/
structure Store where
  mem : Nat → Option Val
  next : Nat
  ids : Nat := 0

/-- A fresh name for a handler. -/
def Store.fresh (σ : Store) : Nat × Store := (σ.ids, { σ with ids := σ.ids + 1 })

def Store.set (σ : Store) (l : Nat) (v : Option Val) : Store :=
  { σ with mem := fun k => if k = l then v else σ.mem k }

def Store.alloc (σ : Store) (v : Val) : Nat × Store :=
  (σ.next, { σ with mem := fun k => if k = σ.next then some v else σ.mem k, next := σ.next + 1 })

abbrev Env := List (Var × Nat)

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

/-- Drops a value of type `τ` with `k` cells to spare: frees the cells of its boxes, innermost
first, and what a closure captured, which may hold closures in turn. `none` if a cell it should free
is not there, a double free, or it runs out of cells to spare. -/
def dropK : Nat → Store → Ty → Val → Option Store
  | _, σ, .int, .int _ => some σ
  | k + 1, σ, .box τ, .ptr l =>
    match σ.mem l with
    | some w =>
      match dropK k σ τ w with
      | some σ' => some (σ'.set l none)
      | none => none
    | none => none
  | k + 1, σ, .fn _ _ _ _, .clo _ c τc =>
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

def dropCells (σ : Store) : List (Ty × Nat) → Option Store
  | [] => some σ
  | (τ, c) :: rest =>
    match dropCell σ τ c with
    | some σ' => dropCells σ' rest
    | none => none

/-- How a computation that was dropped ended: with a value, or unwinding. -/
inductive Outcome where
  | val (v : Val)
  | abort (j : Nat) (k : Int)
  deriving Repr

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
  | capK (τ : Ty) (e : Nat) (id : Nat) (caps : List (Cap Nat)) (os rs : List Var) (arm : Expr)
  /-- An arm running, the parameters it owns dropped as it ends: then the code its `handle` (of type
  `τ`) ran, `K`, goes on with the arm's value, or, if the arm unwinds, is dropped. -/
  | armK (τ : Ty) (cells : List (Ty × Nat)) (K : List Kont)
  /-- Code of type `τ` being dropped as an arm unwinds with `o`, by unwinding it to a barrier named
  `d`. -/
  | dropK (τ : Ty) (o : Outcome) (d : Nat)

/-- A handler in force, by name: one that unwinds — an abortive arm, or a `try` — handling `l`; or
one whose arm takes the code that performed `e` as its continuation, resuming it with its value.
An unwinding or a continuation taken is aimed at a handler by its name, which the handler keeps
wherever the code around it goes on. -/
inductive Frame where
  | abort (l : Label) (id : Nat)
  | capture (e : Nat) (id : Nat)

abbrev HS := List Frame

def Frame.handles : Frame → Label → Bool
  | .abort l _, l' => l == l'
  | .capture e _, .eff e' => e == e'
  | _, _ => false

/-- The innermost frame handling `l`. -/
def find (l : Label) : HS → Option Frame
  | [] => none
  | f :: rest => if f.handles l then some f else find l rest

/-- The frame a construct puts in force for the code it runs, if any. -/
def Kont.push : Kont → HS → HS
  | .catchK l id _ _ _, hs => .abort l id :: hs
  | .capK _ e id _ _ _ _, hs => .capture e id :: hs
  | .dropK _ _ d, hs => .abort .drop d :: hs
  | _, hs => hs

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

/-- The value of a result, if it is one. -/
def Res.value? : Res → Option Val
  | .val v => some v
  | _ => none

/-- Evaluation ended, with a value or by unwinding: a scope it leaves drops what it owns. -/
def Res.done : Res → Bool
  | .val _ | .abort _ _ => true
  | _ => false

/-- Leaving a scope whose variable is in cell `c`: dropped on every way out but a timeout, or kept
with the continuation taken in it. -/
def leave (τ : Ty) (c : Nat) : Res × Store → Res × Store
  | (.susp j ef vs ls K, σ) => (.susp j ef vs ls (.scopeK τ c :: K), σ)
  | (r, σ) =>
    if r.done then
      match dropCell σ τ c with
      | some σ' => (r, σ')
      | none => (.stuck, σ)
    else (r, σ)

/-- A body's cleanup ended, the body having given `v`. -/
def cleanV (τ : Ty) (v : Val) : Res × Store → Res × Store
  | (.val (.int _), σ) => (.val v, σ)
  | (.abort j k, σ) =>
    match drop σ τ v with
    | some σ' => (.abort j k, σ')
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
def dropRet (τ : Ty) (o : Outcome) (d : Nat) : Res × Store → Res × Store
  | (.abort j k, σ) => if j = d then (o.res, σ) else (.abort j k, σ)
  | (.val v, σ) =>
    match drop σ τ v with
    | some σ' => (o.res, σ')
    | none => (.stuck, σ)
  | (.susp j ef vs ls K, σ) => (.susp j ef vs ls (.dropK τ o d :: K), σ)
  | r => r

/-- An arm ended: its parameters are dropped, and the code its `handle` ran, `K`, goes on with
the arm's value (`resuming`), or, if the arm unwinds with `o`, is dropped (`dropping`). -/
def armEnd (τ : Ty) (cells : List (Ty × Nat)) (K : List Kont) (resuming : Store → Val → Res × Store)
    (dropping : Store → Outcome → Res × Store) : Res × Store → Res × Store
  | (.susp j ef vs ls K', σ) => (.susp j ef vs ls (.armK τ cells K :: K'), σ)
  | (.val v, σ) =>
    match dropCells σ cells with
    | some σ' => resuming σ' v
    | none => (.stuck, σ)
  | (.abort j k, σ) =>
    match dropCells σ cells with
    | some σ' => dropping σ' (.abort j k)
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
    match e with
    | .atom a =>
      match evalAtom σ env a with
      | some (v, σ1) => (.val v, σ1)
      | none => (.stuck, σ)
    | .add a b =>
      match evalAtom σ env a with
      | some (.int x, σ1) =>
        match evalAtom σ1 env b with
        | some (.int y, σ2) => (.val (.int (x + y)), σ2)
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
            | some σ2 => (.val (.int 0), σ2.set l (some v))
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
        ret F O n hs (.capK τ ef id (List.zipWith Cap.at caps ls) os rs arm)
          (eval F O n (.capture ef id :: hs) σ1 env body)
      | none => (.stuck, σ)
    | .handleAbort body ef x h =>
      let (id, σ1) := σ.fresh
      ret F O n hs (.catchK (.eff ef) id x env h) (eval F O n (.abort (.eff ef) id :: hs) σ1 env body)
termination_by n _ _ _ _ => (n, 0, 0)

/-- What frame `f` does with what the code it ran gave, under the handlers `hs` around it. -/
def ret (F : List Fn) (O : List Op) (n : Nat) (hs : HS) : Kont → Res × Store → Res × Store
  | .capK τ e id caps os rs arm, (.susp j ef vs ls K, σ) =>
    if j ≠ id ∨ ef ≠ e then (.susp j ef vs ls (.capK τ e id caps os rs arm :: K), σ) else
    match O[e]? with
    | none => (.stuck, σ)
    | some op =>
      if vs.length = os.length ∧ ls.length = rs.length then
        let K' := Kont.capK τ e id caps os rs arm :: K
        let (cells, σ2) := allocAll σ (os.zip vs)
        armEnd τ (op.owns.zip (cells.map Prod.snd)) K'
          (fun σ v => match n with
            | 0 => (.timeout, σ)
            | m + 1 => evalK F O m hs σ K' (.val v))
          (fun σ o => match n with
            | 0 => (.timeout, σ)
            | m + 1 =>
              let (d, σ1) := σ.fresh
              dropRet τ o d (evalK F O m (.abort .drop d :: hs) σ1 K' (.abort d 0)))
          (eval F O n hs σ2 (cells ++ rs.zip ls ++ caps.map (fun c => (c.name, c.loc))) arm)
      else (.stuck, σ)
  | f, (.susp j ef vs ls K, σ) =>
    match f with
    | .scopeK τ c => leave τ c (.susp j ef vs ls K, σ)
    | .deferV τ v => cleanV τ v (.susp j ef vs ls K, σ)
    | .deferA j' k => cleanA j' k (.susp j ef vs ls K, σ)
    | .armK τ cells K0 => (.susp j ef vs ls (.armK τ cells K0 :: K), σ)
    | .dropK τ o d => dropRet τ o d (.susp j ef vs ls K, σ)
    | f => (.susp j ef vs ls (f :: K), σ)
  | _, (.stuck, σ) => (.stuck, σ)
  | _, (.timeout, σ) => (.timeout, σ)
  | .letK x τ env b, (.val v, σ) =>
    let (c, σ2) := σ.alloc v
    leave τ c (eval F O n hs σ2 ((x, c) :: env) b)
  | .letK _ _ _ _, (.abort j k, σ) => (.abort j k, σ)
  | .scopeK τ c, r => leave τ c r
  | .callK cells, (r, σ) =>
    match dropCells σ cells with
    | some σ' => (r, σ')
    | none => (.stuck, σ)
  | .callLendK x ps cenv cells env body, (.val (.int k), σ) =>
    match pick ps k with
    | some p =>
      match resolve σ cenv p with
      | some l =>
        match dropCells σ cells with
        | some σ' =>
          match eval F O n hs σ' ((x, l) :: env) body with
          | (.susp j ef vs ls K, σ'') => (.susp j ef vs ls (.lendK :: K), σ'')
          | r => r
        | none => (.stuck, σ)
      | none => (.stuck, σ)
    | none => (.stuck, σ)
  | .callLendK _ _ _ _ _ _, (.val _, σ) => (.stuck, σ)
  | .callLendK _ _ _ cells _ _, (.abort j k, σ) =>
    match dropCells σ cells with
    | some σ' => (.abort j k, σ')
    | none => (.stuck, σ)
  | .catchK _ id x env h, (.abort j k, σ) =>
    if j = id then
      let (c, σ2) := σ.alloc (.int k)
      leave .int c (eval F O n hs σ2 ((x, c) :: env) h)
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
  | .deferK τ env d, (.val v, σ) => cleanV τ v (eval F O n hs σ env d)
  | .deferK _ env d, (.abort j k, σ) => cleanA j k (eval F O n hs σ env d)
  | .deferV τ v, r => cleanV τ v r
  | .deferA j k, r => cleanA j k r
  | .lendK, r => r
  | .cloK a, (r, σ) =>
    match σ.mem a with
    | some _ => (r, σ.set a none)
    | none => (.stuck, σ)
  | .capK _ _ _ _ _ _ _, (.val v, σ) => (.val v, σ)
  | .capK _ _ _ _ _ _ _, (.abort j k, σ) => (.abort j k, σ)
  | .armK τ cells K, r =>
    armEnd τ cells K
      (fun σ v => match n with
        | 0 => (.timeout, σ)
        | m + 1 => evalK F O m hs σ K (.val v))
      (fun σ o => match n with
        | 0 => (.timeout, σ)
        | m + 1 =>
          let (d, σ1) := σ.fresh
          dropRet τ o d (evalK F O m (.abort .drop d :: hs) σ1 K (.abort d 0))) r
  | .dropK τ o d, r => dropRet τ o d r
termination_by _ _ => (n, 1, 0)

/-- A continuation given what the code it was taken at gives: its frames, the outermost first, each
putting in force the handler it did. -/
def evalK (F : List Fn) (O : List Op) (n : Nat) (hs : HS) (σ : Store) : List Kont → Res → Res × Store
  | [], r => (r, σ)
  | f :: K, r => ret F O n hs f (evalK F O n (f.push hs) σ K r)
termination_by K _ => (n, 1, sizeOf K + 1)
end


/-! ## Types -/

/-- What a variable is to the code it is in scope in: owned, live or moved; a borrow; lent `mut`
to a borrow the code holds for a while, and not to be reached until it ends; or one field of the pair
it holds lent to such a borrow, the field a hole in its type. -/
inductive Slot where
  | own (τ : Ty) (live : Bool)
  | ref (m : Mode) (τ : Ty)
  | lent (τ : Ty)
  | half (t : Bool) (A B : Ty)
  deriving DecidableEq, Repr

def Slot.ty : Slot → Ty
  | .own τ _ | .ref _ τ | .lent τ => τ
  | .half t A B => .lent1 t A B

/-- A slot that may change what it holds but not its own first cell: a `mut` borrow of a closure,
which may call the closure, changing what it captured, but not put another closure in its place; or
a variable one field of whose pair is lent, which may change the other field but not the pair's
cell, which says where the field lent is. -/
def Slot.shell : Slot → Bool
  | .ref .mut (.fn _ _ _ _) => true
  | .half _ _ _ => true
  | _ => false

abbrev Ctx := List (Var × Slot)

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
  | cons : PlaceTy Γ p τ w y → (m = .mut → w = true) → τ.complete = true → Lends Γ rest ts ys →
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
  | .lent τ => .lent τ
  | .half t A B => .ref .ro (.lent1 t A B)

/-- `Γ` with the variables `ys` only read. -/
def freeze (Γ : Ctx) (ys : List Var) : Ctx :=
  Γ.map fun (y, s) => if y ∈ ys then (y, s.ro) else (y, s)

/-- `Γ` with the variable `y` lent `mut` to a borrow: not to be reached while the borrow lives. -/
def hide (Γ : Ctx) (y : Var) : Ctx :=
  Γ.map fun (z, s) => if z = y then (z, .lent s.ty) else (z, s)

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
  | mut : PlaceTy Γ (.var y) τ true y → τ.isFn = false → τ.complete = true → Caps Γ rest ys →
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
  | add : AtomTy Γ a .int Γ₁ → AtomTy Γ₁ b .int Γ₂ → Typed F O Γ (.add a b) .int Γ₂ r
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
      (m = .mut → A.isFn = false ∧ B.isFn = false) →
      Typed F O ((x, .ref m A) :: lendCtx m Γ y) e₁ τ ((x, .ref m A) :: Γb₁) r →
      Typed F O ((x, .ref m B) :: lendCtx m Γ y) e₂ τ ((x, .ref m B) :: Γb₂) r →
      Weaker Γb Γb₁ → Weaker Γb Γb₂ → Typed F O Γ (.caseRef x m p e₁ e₂) τ (thaw Γ [y] Γb) r
  | let_ : lookup x Γ = none → Typed F O Γ a τ Γ₁ r →
      Typed F O ((x, .own τ true) :: Γ₁) b τb ((x, .own τ live) :: Γ₂) r → Typed F O Γ (.let_ x τ a b) τb Γ₂ r
  | write : AtomTy Γ a .int Γ₁ → PlaceTy Γ₁ p .int true y → Typed F O Γ (.write p a) .int Γ₁ r
  /-- Nothing is put in place of a closure borrowed `mut`, or of what it captured. -/
  | assign : AtomTy Γ a τ Γ₁ → PlaceTy Γ₁ p τ true y → (∀ s, lookup y Γ₁ = some s → s.shell = false) →
      Typed F O Γ (.assign p τ a) .int Γ₁ r
  | call : F[f]? = some d → d.retp = none → d.cap = none → (∀ l ∈ d.row, l ∈ r) → AtomsTy Γ owned (d.owns.map Prod.snd) Γ₁ →
      Lends Γ₁ lent (d.refs.map Prod.snd) ys → LentApart lent →
      Typed F O Γ (.call f owned lent) d.ret Γ₁ r
  /-- A closure captures a value, moved in, which may be a closure; its type says how it is called,
  what it takes and gives, and what it may perform, but not what it captured. -/
  | lam : F[f]? = some d → d.cap = some (xc, τc, k) → d.owns = [(pn, A)] → d.refs = [] →
      d.retp = none → AtomTy Γ a τc Γ₁ → Typed F O Γ (.lam f a) (.fn k A d.ret d.row) Γ₁ r
  /-- A closure called once is moved out of its variable. -/
  | applyOnce : lookup x Γ = some (.own (.fn .once A B r') true) → (∀ l ∈ r', l ∈ r) →
      AtomTy (setSlot Γ x (.own (.fn .once A B r') false)) a A Γ₁ →
      Typed F O Γ (.apply .once (.var x) a) B Γ₁ r
  /-- A closure called through a borrow: `mut` for one that changes what it captured. -/
  | applyBorrow : k ≠ .once → AtomTy Γ a A Γ₁ → PlaceTy Γ₁ p (.fn k A B r') w y → (k = .excl → w = true) →
      (∀ l ∈ r', l ∈ r) → Typed F O Γ (.apply k p a) B Γ₁ r
  /-- A closure over a `readonly` borrow is a borrow too: it is in scope for `body`, which may call
  it or lend it on, but not move it, and what the borrowed place is rooted at is only read meanwhile. -/
  | lendClo : F[f]? = some d → d.cap = some (xc, τc, .shared) → d.owns = [(pn, A)] → d.refs = [] →
      d.retp = none → τc.data = true → PlaceTy Γ p τc w y → lookup x Γ = none →
      Typed F O ((x, .ref .ro (.fn .shared A d.ret d.row)) :: freeze Γ [y]) body τb
        ((x, .ref .ro (.fn .shared A d.ret d.row)) :: Γb) r →
      Typed F O Γ (.lendClo x f p body) τb (thaw Γ [y] Γb) r
  /-- A closure over a `mut` borrow is a `mut` borrow too: `body` may call it, changing what it
  captured, or lend it on, but not move it or put another closure in its place; what the borrowed
  place is rooted at is out of reach meanwhile. -/
  | lendCloMut : F[f]? = some d → d.cap = some (xc, τc, .excl) → d.owns = [(pn, A)] → d.refs = [] →
      d.retp = none → τc.data = true → PlaceTy Γ p τc true y → Unsplit Γ y → lookup x Γ = none →
      Typed F O ((x, .ref .mut (.fn .excl A d.ret d.row)) :: hide Γ y) body τb
        ((x, .ref .mut (.fn .excl A d.ret d.row)) :: Γb) r →
      Typed F O Γ (.lendClo x f p body) τb (thaw Γ [y] Γb) r
  /-- The borrow a call returns is of what the caller lent it as one of its borrowed arguments,
  which the callee picks as it runs: as for a borrow of a place, the variables those it may pick are
  rooted at, `zs`, are only read, or not reached, while the borrow lives. -/
  | lendCall : F[f]? = some d → d.retp = some (m, cs) → d.cap = none → (∀ l ∈ d.row, l ∈ r) →
      AtomsTy Γ owned (d.owns.map Prod.snd) Γ₁ → Lends Γ₁ lent (d.refs.map Prod.snd) ys → LentApart lent →
      Pairs (fun c z => ∃ mi, ys[c.1]? = some (mi, z) ∧ (m = .mut → mi = .mut)) cs zs →
      (m = .mut → zs.Nodup ∧ d.ret.isFn = false ∧ (∀ c ∈ cs, ∀ e, d.refs[c.1]? = some e → e.2.2.isFn = false) ∧
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
  | lend : lookup x Γ = none → PlaceTy Γ p τ w y → (m = .mut → w = true) → (m = .mut → τ.isFn = false) →
      (m = .mut → Unsplit Γ y) →
      Typed F O ((x, .ref m τ) :: lendCtx m Γ y) body τb ((x, .ref m τ) :: Γb) r →
      Typed F O Γ (.lend x m p body) τb (thaw Γ [y] Γb) r
  /-- A borrow of one field of a variable's pair, for the code it is in scope for: the variable
  stays in reach, the field a hole in its type, and the field beside it may be read, changed or
  lent meanwhile. -/
  | lendField : lookup x Γ = none → lookup y Γ = some s →
      s.ty = .pair A B → ((∃ τ, s = .own τ true) ∨ (∃ τ, s = .ref .mut τ) ∨ ∃ t' A' B', s = .half t' A' B') →
      (if t then A else B).complete = true → (m = .mut → (if t then A else B).isFn = false) →
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
  | handle : O[e]? = some op → (∀ τ ∈ op.owns, τ.complete = true) → os.length = op.owns.length →
      rs.length = op.refs.length →
      Caps Γ caps ys → Exclusive ys → (os ++ rs ++ caps.map Cap.name).Nodup →
      Typed F O (armCtx os rs op (caps.map Cap.sig)) arm op.ret Γa r →
      Typed F O (freeze (hideAll Γ (roots .mut ys)) (roots .ro ys)) body τ Γb (.eff e :: r) →
      Typed F O Γ (.handle τ body e caps os rs arm) τ
        (unhideAll Γ (roots .mut ys) (thaw (hideAll Γ (roots .mut ys)) (roots .ro ys) Γb)) r
  /-- As for `try`, the arm starts where the body would have ended. -/
  | handleAbort : O[e]? = some op → op.owns = [.int] → op.refs = [] → lookup x Γb = none →
      Typed F O Γ body τ Γb (.eff e :: r) →
      Typed F O ((x, .own .int true) :: Γb) h τ ((x, .own .int live) :: Γh) r →
      Typed F O Γ (.handleAbort body e x h) τ Γh r


end FlyCore.Ownership
