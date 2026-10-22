/-!
# Ownership

The ownership fragment of λ-fly (spec §4, §9): a heap of cells, owned boxes that are allocated and
freed, moves, drops at the end of a scope, assignment that drops what a place held, and borrows —
`readonly` and `mut` — that exist only as parameters, so they cannot outlive what they borrow (§4.2).

Every variable lives in a cell of the store; a box is a pointer to a cell holding its contents. A
borrowed parameter is bound to the location it borrows, not to a cell of its own. A value is an
integer, a pointer, or the mark a move leaves in a variable's cell.

The semantics is an interpreter with fuel, and anything no rule covers is `stuck`: reading a value
that was moved, reaching a cell that was freed, freeing one twice. The theorems are that a
well-typed program never gets stuck, and that when it ends every cell it allocated has been freed
but those of its result: each owned value is dropped exactly once.
-/

namespace FlyCore.Ownership

inductive Ty where
  | int
  | box (τ : Ty)
  deriving DecidableEq, Repr

inductive Mode where
  | ro
  | mut
  deriving DecidableEq, Repr

abbrev Var := String

/-- A place: a variable, or what a box at a place points to. -/
inductive Place where
  | var (x : Var)
  | deref (p : Place)
  deriving DecidableEq, Repr

inductive Expr where
  | lit (n : Int)
  /-- The integer at a place, copied. -/
  | read (p : Place)
  /-- The box in an owned variable, which is left moved. -/
  | move (x : Var)
  | add (a b : Expr)
  /-- `Box.new(a)`. -/
  | new (a : Expr)
  /-- `let x: τ = a; b`, `x` dropped when `b` ends unless it was moved. -/
  | let_ (x : Var) (τ : Ty) (a b : Expr)
  /-- `p = a` for an integer place. -/
  | write (p : Place) (a : Expr)
  /-- `p = a` for a place holding a `box τ`: what it held is dropped. -/
  | assign (p : Place) (τ : Ty) (a : Expr)
  /-- A call: the owned arguments, evaluated in order, then the places lent, each with its mode. -/
  | call (f : Nat) (owned : List Expr) (lent : List (Mode × Place))
  | seq (a b : Expr)
  deriving Repr

/-- A function: its owned parameters, its borrowed ones, its result, its body. -/
structure Fn where
  owns : List (Var × Ty)
  refs : List (Var × Mode × Ty)
  ret : Ty
  body : Expr

inductive Val where
  | int (n : Int)
  | ptr (l : Nat)
  | moved
  deriving DecidableEq, Repr

/-- The store: its cells, `none` once freed or before allocation, and the next to allocate. -/
structure Store where
  mem : Nat → Option Val
  next : Nat

def Store.set (σ : Store) (l : Nat) (v : Option Val) : Store :=
  { σ with mem := fun k => if k = l then v else σ.mem k }

def Store.alloc (σ : Store) (v : Val) : Nat × Store :=
  (σ.next, { mem := fun k => if k = σ.next then some v else σ.mem k, next := σ.next + 1 })

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

/-- Drops a value of type `τ`: frees the cells of its boxes, innermost first. `none` if a cell it
should free is not there: a double free. -/
def drop (σ : Store) : Ty → Val → Option Store
  | .int, .int _ => some σ
  | .box τ, .ptr l =>
    match σ.mem l with
    | some w =>
      match drop σ τ w with
      | some σ' => some (σ'.set l none)
      | none => none
    | none => none
  | _, _ => none

/-- Drops what a variable's cell holds, unless it was moved, then frees the cell. -/
def dropCell (σ : Store) (τ : Ty) (c : Nat) : Option Store :=
  match σ.mem c with
  | some .moved => some (σ.set c none)
  | some v => (drop σ τ v).map fun σ' => σ'.set c none
  | none => none

def dropCells (σ : Store) : List (Ty × Nat) → Option Store
  | [] => some σ
  | (τ, c) :: rest =>
    match dropCell σ τ c with
    | some σ' => dropCells σ' rest
    | none => none

inductive Res where
  | val (v : Val)
  | stuck
  | timeout
  deriving DecidableEq, Repr

/-- Allocates a cell for each value, binding the names to them. -/
def allocAll (σ : Store) : List (Var × Val) → Env × Store
  | [] => ([], σ)
  | (x, v) :: rest =>
    let (c, σ1) := σ.alloc v
    let (env, σ2) := allocAll σ1 rest
    ((x, c) :: env, σ2)

/-- The owned arguments of a call, in order, by `ev`: their values, or what stopped them. -/
def evalArgs (ev : Store → Env → Expr → Res × Store) : Store → Env → List Expr → (List Val ⊕ Res) × Store
  | σ, _, [] => (.inl [], σ)
  | σ, env, a :: rest =>
    match ev σ env a with
    | (.val v, σ1) =>
      match evalArgs ev σ1 env rest with
      | (.inl vs, σ2) => (.inl (v :: vs), σ2)
      | r => r
    | (r, σ1) => (.inr r, σ1)

def eval (F : List Fn) : Nat → Store → Env → Expr → Res × Store
  | 0, σ, _, _ => (.timeout, σ)
  | n + 1, σ, env, e =>
    match e with
    | .lit k => (.val (.int k), σ)
    | .read p =>
      match resolve σ env p with
      | some l =>
        match σ.mem l with
        | some (.int k) => (.val (.int k), σ)
        | _ => (.stuck, σ)
      | none => (.stuck, σ)
    | .move x =>
      match lookup x env with
      | some c =>
        match σ.mem c with
        | some (.ptr l) => (.val (.ptr l), σ.set c (some .moved))
        | _ => (.stuck, σ)
      | none => (.stuck, σ)
    | .add a b =>
      match eval F n σ env a with
      | (.val (.int x), σ1) =>
        match eval F n σ1 env b with
        | (.val (.int y), σ2) => (.val (.int (x + y)), σ2)
        | (.val _, σ2) => (.stuck, σ2)
        | r => r
      | (.val _, σ1) => (.stuck, σ1)
      | r => r
    | .new a =>
      match eval F n σ env a with
      | (.val v, σ1) =>
        let (l, σ2) := σ1.alloc v
        (.val (.ptr l), σ2)
      | r => r
    | .let_ x τ a b =>
      match eval F n σ env a with
      | (.val v, σ1) =>
        let (c, σ2) := σ1.alloc v
        match eval F n σ2 ((x, c) :: env) b with
        | (.val w, σ3) =>
          match dropCell σ3 τ c with
          | some σ4 => (.val w, σ4)
          | none => (.stuck, σ3)
        | r => r
      | r => r
    | .write p a =>
      match eval F n σ env a with
      | (.val (.int k), σ1) =>
        match resolve σ1 env p with
        | some l =>
          match σ1.mem l with
          | some (.int _) => (.val (.int 0), σ1.set l (some (.int k)))
          | _ => (.stuck, σ1)
        | none => (.stuck, σ1)
      | (.val _, σ1) => (.stuck, σ1)
      | r => r
    | .assign p τ a =>
      match eval F n σ env a with
      | (.val v, σ1) =>
        match resolve σ1 env p with
        | some l =>
          match σ1.mem l with
          | some old =>
            match drop σ1 τ old with
            | some σ2 => (.val (.int 0), σ2.set l (some v))
            | none => (.stuck, σ1)
          | none => (.stuck, σ1)
        | none => (.stuck, σ1)
      | r => r
    | .call f owned lent =>
      match F[f]? with
      | none => (.stuck, σ)
      | some d =>
        match evalArgs (eval F n) σ env owned with
        | (.inl vs, σ1) =>
          match lent.mapM (fun (_, p) => resolve σ1 env p) with
          | some ls =>
            if vs.length = d.owns.length ∧ ls.length = d.refs.length then
              let (cells, σ2) := allocAll σ1 (d.owns.map Prod.fst |>.zip vs)
              let env' := cells ++ (d.refs.map Prod.fst |>.zip ls)
              match eval F n σ2 env' d.body with
              | (.val w, σ3) =>
                match dropCells σ3 (d.owns.map Prod.snd |>.zip (cells.map Prod.snd)) with
                | some σ4 => (.val w, σ4)
                | none => (.stuck, σ3)
              | r => r
            else (.stuck, σ1)
          | none => (.stuck, σ1)
        | (.inr r, σ1) => (r, σ1)
    | .seq a b =>
      match eval F n σ env a with
      | (.val (.int _), σ1) => eval F n σ1 env b
      | (.val _, σ1) => (.stuck, σ1)
      | r => r


/-! ## Types -/

/-- What a variable is to the code it is in scope in: owned, live or moved; or a borrow. -/
inductive Slot where
  | own (τ : Ty) (live : Bool)
  | ref (m : Mode) (τ : Ty)
  deriving DecidableEq, Repr

abbrev Ctx := List (Var × Slot)

def setSlot (Γ : Ctx) (x : Var) (s : Slot) : Ctx :=
  Γ.map fun (y, t) => if y = x then (y, s) else (y, t)

/-- A place's type, whether it may be changed through it, and the variable it is rooted at. -/
inductive PlaceTy (Γ : Ctx) : Place → Ty → Bool → Var → Prop
  | own : lookup x Γ = some (.own τ true) → PlaceTy Γ (.var x) τ true x
  | ref : lookup x Γ = some (.ref m τ) → PlaceTy Γ (.var x) τ (m == .mut) x
  | deref : PlaceTy Γ p (.box τ) w r → PlaceTy Γ (.deref p) τ w r

/-- The places lent, each of the parameter's type and changeable where lent `mut`, with the mode
each is lent in and the variable it is rooted at. -/
inductive Lends (Γ : Ctx) : List (Mode × Place) → List (Mode × Ty) → List (Mode × Var) → Prop
  | nil : Lends Γ [] [] []
  | cons : PlaceTy Γ p τ w y → (m = .mut → w = true) → Lends Γ rest ts ys →
      Lends Γ ((m, p) :: rest) ((m, τ) :: ts) ((m, y) :: ys)

/-- No variable is lent `mut` alongside another borrow of it, or of what it holds: two places rooted
at one variable are both lent `readonly`. -/
def Exclusive (ys : List (Mode × Var)) : Prop :=
  ys.Pairwise fun a b => a.2 = b.2 → a.1 = .ro ∧ b.1 = .ro

mutual
/-- `Typed F Γ e τ Γ'`: `e` has type `τ`, and leaves its variables as `Γ'` says — moved or not. -/
inductive Typed (F : List Fn) : Ctx → Expr → Ty → Ctx → Prop
  | lit : Typed F Γ (.lit n) .int Γ
  | read : PlaceTy Γ p .int w r → Typed F Γ (.read p) .int Γ
  | move : lookup x Γ = some (.own (.box τ) true) →
      Typed F Γ (.move x) (.box τ) (setSlot Γ x (.own (.box τ) false))
  | add : Typed F Γ a .int Γ₁ → Typed F Γ₁ b .int Γ₂ → Typed F Γ (.add a b) .int Γ₂
  | new : Typed F Γ a τ Γ₁ → Typed F Γ (.new a) (.box τ) Γ₁
  | let_ : lookup x Γ = none → Typed F Γ a τ Γ₁ →
      Typed F ((x, .own τ true) :: Γ₁) b τb ((x, .own τ live) :: Γ₂) → Typed F Γ (.let_ x τ a b) τb Γ₂
  | write : Typed F Γ a .int Γ₁ → PlaceTy Γ₁ p .int true r → Typed F Γ (.write p a) .int Γ₁
  | assign : Typed F Γ a τ Γ₁ → PlaceTy Γ₁ p τ true r → Typed F Γ (.assign p τ a) .int Γ₁
  | call : F[f]? = some d → Args F Γ owned (d.owns.map Prod.snd) Γ₁ →
      Lends Γ₁ lent (d.refs.map Prod.snd) ys → Exclusive ys →
      Typed F Γ (.call f owned lent) d.ret Γ₁
  | seq : Typed F Γ a .int Γ₁ → Typed F Γ₁ b τ Γ₂ → Typed F Γ (.seq a b) τ Γ₂

/-- The owned arguments, in order, against the parameters' types. -/
inductive Args (F : List Fn) : Ctx → List Expr → List Ty → Ctx → Prop
  | nil : Args F Γ [] [] Γ
  | cons : Typed F Γ a τ Γ₁ → Args F Γ₁ as τs Γ₂ → Args F Γ (a :: as) (τ :: τs) Γ₂

end


end FlyCore.Ownership
