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

inductive Ty where
  | int
  | box (τ : Ty)
  deriving DecidableEq, Repr

inductive Mode where
  | ro
  | mut
  deriving DecidableEq, Repr

abbrev Var := String

/-- What a row may hold: `Fail`, or a user effect by number. -/
inductive Label where
  | fail
  | eff (n : Nat)
  deriving DecidableEq, Repr

abbrev Row := List Label

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
  /-- `if (c) a else b`: `b` when `c` is zero. -/
  | ite (c a b : Expr)
  /-- `throw a`: a failure carrying an integer. -/
  | throw_ (a : Expr)
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
  | perform (e : Nat) (owned : List Expr) (lent : List (Mode × Place))
  /-- `handle { body } with E { op(…) resumes k => k(arm) }`: where `body` performs the operation,
  `arm` runs, its value the operation's result, given the operation's arguments — owned as `owns`,
  lent as `refs` — and the places of `caps`, each lent to it `readonly` or `mut` for as long as the
  `handle` runs: the state the arm keeps from one operation to the next. -/
  | handle (body : Expr) (e : Nat) (caps : List (Cap Place)) (owns refs : List Var) (arm : Expr)
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
its body. -/
structure Fn where
  owns : List (Var × Ty)
  refs : List (Var × Mode × Ty)
  ret : Ty
  row : Row
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

/-- A handler in force: one that resumes, with its arm and the places its `handle` lent it; or
one that unwinds — an abortive arm, or a `try` — by the depth of the stack it was installed on,
which the unwinding is aimed at. -/
inductive Frame where
  | resume (e : Nat) (caps : List (Cap Nat)) (owns refs : List Var) (arm : Expr)
  | abort (l : Label) (id : Nat)

abbrev HS := List Frame

def Frame.handles : Frame → Label → Bool
  | .resume e _ _ _ _, .eff e' => e == e'
  | .resume _ _ _ _ _, .fail => false
  | .abort l _, l' => l == l'

/-- The innermost frame handling `l`, and the frames below it: the context its arm runs in. -/
def find (l : Label) : HS → Option (Frame × HS)
  | [] => none
  | f :: rest => if f.handles l then some (f, rest) else find l rest

inductive Res where
  | val (v : Val)
  /-- Unwinding to the handler installed at depth `id`, with the operation's integer argument. -/
  | abort (id : Nat) (k : Int)
  | stuck
  | timeout
  deriving DecidableEq, Repr

/-- Evaluation ended, with a value or by unwinding: a scope it leaves drops what it owns. -/
def Res.done : Res → Bool
  | .val _ | .abort _ _ => true
  | _ => false

/-- Allocates a cell for each value, binding the names to them. -/
def allocAll (σ : Store) : List (Var × Val) → Env × Store
  | [] => ([], σ)
  | (x, v) :: rest =>
    let (c, σ1) := σ.alloc v
    let (env, σ2) := allocAll σ1 rest
    ((x, c) :: env, σ2)

/-- The owned arguments of a call, in order, by `ev`, against the parameters' types: their values,
or what stopped them, the values of those before dropped. -/
def evalArgs (ev : Store → Env → Expr → Res × Store) :
    Store → Env → List Expr → List Ty → (List Val ⊕ Res) × Store
  | σ, _, [], _ => (.inl [], σ)
  | σ, _, _ :: _, [] => (.inr .stuck, σ)
  | σ, env, a :: rest, τ :: τs =>
    match ev σ env a with
    | (.val v, σ1) =>
      match evalArgs ev σ1 env rest τs with
      | (.inl vs, σ2) => (.inl (v :: vs), σ2)
      | (.inr r, σ2) =>
        if r.done then
          match drop σ2 τ v with
          | some σ3 => (.inr r, σ3)
          | none => (.inr .stuck, σ2)
        else (.inr r, σ2)
    | (r, σ1) => (.inr r, σ1)

/-- Leaving a scope whose variable is in cell `c`: dropped on every way out but a timeout. -/
def leave (τ : Ty) (c : Nat) : Res × Store → Res × Store
  | (r, σ) =>
    if r.done then
      match dropCell σ τ c with
      | some σ' => (r, σ')
      | none => (.stuck, σ)
    else (r, σ)

/-- Binds a function's or an arm's owned parameters in fresh cells, runs `body` with them, the
places lent it and those of `post` — what an arm's `handle` lent it — then drops the parameters it
owns. -/
def enter (ev : Store → Env → Expr → Res × Store) (σ : Store)
    (owns : List (Var × Ty)) (vs : List Val) (refs : List Var) (ls : List Nat) (post : Env) (body : Expr) :
    Res × Store :=
  let (cells, σ2) := allocAll σ (owns.map Prod.fst |>.zip vs)
  match ev σ2 (cells ++ refs.zip ls ++ post) body with
  | (r, σ3) =>
    if r.done then
      match dropCells σ3 (owns.map Prod.snd |>.zip (cells.map Prod.snd)) with
      | some σ4 => (r, σ4)
      | none => (.stuck, σ3)
    else (r, σ3)

/-- Catches an unwinding aimed at the handler installed at depth `d`, going on with `k`. -/
def catchAt (d : Nat) : Res × Store → (Int → Store → Res × Store) → Res × Store
  | (.abort id k, σ), h => if id = d then h k σ else (.abort id k, σ)
  | r, _ => r

/-- The interpreter: the program's functions and operations, fuel, the handlers in force. -/
def eval (F : List Fn) (O : List Op) : Nat → HS → Store → Env → Expr → Res × Store
  | 0, _, σ, _, _ => (.timeout, σ)
  | n + 1, hs, σ, env, e =>
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
      match eval F O n hs σ env a with
      | (.val (.int x), σ1) =>
        match eval F O n hs σ1 env b with
        | (.val (.int y), σ2) => (.val (.int (x + y)), σ2)
        | (.val _, σ2) => (.stuck, σ2)
        | r => r
      | (.val _, σ1) => (.stuck, σ1)
      | r => r
    | .new a =>
      match eval F O n hs σ env a with
      | (.val v, σ1) =>
        let (l, σ2) := σ1.alloc v
        (.val (.ptr l), σ2)
      | r => r
    | .let_ x τ a b =>
      match eval F O n hs σ env a with
      | (.val v, σ1) =>
        let (c, σ2) := σ1.alloc v
        leave τ c (eval F O n hs σ2 ((x, c) :: env) b)
      | r => r
    | .write p a =>
      match eval F O n hs σ env a with
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
      match eval F O n hs σ env a with
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
        match evalArgs (eval F O n hs) σ env owned (d.owns.map Prod.snd) with
        | (.inl vs, σ1) =>
          match lent.mapM (fun (_, p) => resolve σ1 env p) with
          | some ls =>
            if vs.length = d.owns.length ∧ ls.length = d.refs.length then
              enter (eval F O n hs) σ1 d.owns vs (d.refs.map Prod.fst) ls [] d.body
            else (.stuck, σ1)
          | none => (.stuck, σ1)
        | (.inr r, σ1) => (r, σ1)
    | .seq a b =>
      match eval F O n hs σ env a with
      | (.val (.int _), σ1) => eval F O n hs σ1 env b
      | (.val _, σ1) => (.stuck, σ1)
      | r => r
    | .ite c a b =>
      match eval F O n hs σ env c with
      | (.val (.int k), σ1) => if k = 0 then eval F O n hs σ1 env b else eval F O n hs σ1 env a
      | (.val _, σ1) => (.stuck, σ1)
      | r => r
    | .throw_ a =>
      match eval F O n hs σ env a with
      | (.val (.int k), σ1) =>
        match find .fail hs with
        | some (.abort _ id, _) => (.abort id k, σ1)
        | _ => (.stuck, σ1)
      | (.val _, σ1) => (.stuck, σ1)
      | r => r
    | .try_ body x h =>
      catchAt hs.length (eval F O n (.abort .fail hs.length :: hs) σ env body) fun k σ1 =>
        let (c, σ2) := σ1.alloc (.int k)
        leave .int c (eval F O n hs σ2 ((x, c) :: env) h)
    | .while_ c b =>
      match eval F O n hs σ env c with
      | (.val (.int k), σ1) =>
        if k = 0 then (.val (.int 0), σ1) else
        match eval F O n hs σ1 env b with
        | (.val (.int _), σ2) => eval F O n hs σ2 env (.while_ c b)
        | (.val _, σ2) => (.stuck, σ2)
        | r => r
      | (.val _, σ1) => (.stuck, σ1)
      | r => r
    | .defer τ d body =>
      match eval F O n hs σ env body with
      | (.val v, σ1) =>
        match eval F O n hs σ1 env d with
        | (.val (.int _), σ2) => (.val v, σ2)
        | (.abort i k, σ2) =>
          match drop σ2 τ v with
          | some σ3 => (.abort i k, σ3)
          | none => (.stuck, σ2)
        | (.val _, σ2) => (.stuck, σ2)
        | r => r
      | (.abort i k, σ1) =>
        match eval F O n hs σ1 env d with
        | (.val (.int _), σ2) => (.abort i k, σ2)
        | (.val _, σ2) => (.stuck, σ2)
        | r => r
      | r => r
    | .lend x _ p body =>
      match resolve σ env p with
      | some l => eval F O n hs σ ((x, l) :: env) body
      | none => (.stuck, σ)
    | .perform ef owned lent =>
      match O[ef]? with
      | none => (.stuck, σ)
      | some op =>
        match evalArgs (eval F O n hs) σ env owned op.owns with
        | (.inl vs, σ1) =>
          match lent.mapM (fun (_, p) => resolve σ1 env p) with
          | some ls =>
            match find (.eff ef) hs with
            | some (.resume _ caps os rs arm, rest) =>
              if vs.length = os.length ∧ ls.length = rs.length then
                enter (eval F O n rest) σ1 (os.zip op.owns) vs rs ls (caps.map fun c => (c.name, c.loc)) arm
              else (.stuck, σ1)
            | some (.abort _ id, _) =>
              match vs with
              | [.int k] => (.abort id k, σ1)
              | _ => (.stuck, σ1)
            | none => (.stuck, σ1)
          | none => (.stuck, σ1)
        | (.inr r, σ1) => (r, σ1)
    | .handle body ef caps os rs arm =>
      match caps.mapM (fun c => resolve σ env c.loc) with
      | some ls => eval F O n (.resume ef (List.zipWith (fun c l => ⟨c.name, c.mode, c.ty, l⟩) caps ls) os rs arm :: hs) σ env body
      | none => (.stuck, σ)
    | .handleAbort body ef x h =>
      catchAt hs.length (eval F O n (.abort (.eff ef) hs.length :: hs) σ env body) fun k σ1 =>
        let (c, σ2) := σ1.alloc (.int k)
        leave .int c (eval F O n hs σ2 ((x, c) :: env) h)


/-! ## Types -/

/-- What a variable is to the code it is in scope in: owned, live or moved; a borrow; or lent `mut`
to a borrow the code holds for a while, and not to be reached until it ends. -/
inductive Slot where
  | own (τ : Ty) (live : Bool)
  | ref (m : Mode) (τ : Ty)
  | lent (τ : Ty)
  deriving DecidableEq, Repr

def Slot.ty : Slot → Ty
  | .own τ _ | .ref _ τ | .lent τ => τ

abbrev Ctx := List (Var × Slot)

def setSlot (Γ : Ctx) (x : Var) (s : Slot) : Ctx :=
  Γ.map fun (y, t) => if y = x then (y, s) else (y, t)

/-- A place's type, whether it may be changed through it, and the variable it is rooted at. -/
inductive PlaceTy (Γ : Ctx) : Place → Ty → Bool → Var → Prop
  | own : lookup x Γ = some (.own τ true) → PlaceTy Γ (.var x) τ true x
  | ref : lookup x Γ = some (.ref m τ) → PlaceTy Γ (.var x) τ (m == .mut) x
  | deref : PlaceTy Γ p (.box τ) w r → PlaceTy Γ (.deref p) τ w r

/-- `s'` is `s`, or, for an owned variable, `s` with what it holds perhaps moved: where branches
disagree, or where a failure may have left. -/
inductive Slot.Le : Slot → Slot → Prop
  | refl : Slot.Le s s
  | forget : Slot.Le (.own τ false) (.own τ true)

/-- `Γ'` is `Γ` with some owned variables perhaps moved. -/
inductive Weaker : Ctx → Ctx → Prop
  | nil : Weaker [] []
  | cons : Slot.Le s' s → Weaker Γ' Γ → Weaker ((x, s') :: Γ') ((x, s) :: Γ)

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

/-- A slot only read: what the code a `handle` runs sees of a place it lent its arm. -/
def Slot.ro : Slot → Slot
  | .own τ _ => .ref .ro τ
  | .ref _ τ => .ref .ro τ
  | .lent τ => .lent τ

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

/-- The variables lent in mode `m`. -/
def roots (m : Mode) (ys : List (Mode × Var)) : List Var := (ys.filter (·.1 = m)).map Prod.snd

/-- The places a `handle` lends its arm, each of its type, and the variable each is rooted at, with
the mode it is lent in. What is lent `mut` is a whole variable the arm may change, live or itself a
`mut` borrow. -/
inductive Caps (Γ : Ctx) : List (Cap Place) → List (Mode × Var) → Prop
  | nil : Caps Γ [] []
  | ro : PlaceTy Γ p τ w y → Caps Γ rest ys → Caps Γ (⟨x, .ro, τ, p⟩ :: rest) ((.ro, y) :: ys)
  | mut : PlaceTy Γ (.var y) τ true y → Caps Γ rest ys → Caps Γ (⟨x, .mut, τ, .var y⟩ :: rest) ((.mut, y) :: ys)

/-- An arm's context: the operation's owned arguments, live, then its borrowed ones, then the
places its `handle` lent it, each as it was lent. -/
def armCtx (os : List Var) (rs : List Var) (op : Op) (caps : List (Var × Mode × Ty)) : Ctx :=
  (os.zip op.owns).map (fun p => (p.1, Slot.own p.2 true)) ++ (rs.zip op.refs).map (fun p => (p.1, Slot.ref p.2.1 p.2.2)) ++
    caps.map (fun c => (c.1, Slot.ref c.2.1 c.2.2))

mutual
/-- `Typed F O Γ e τ Γ' r`: `e` has type `τ`, leaves its variables as `Γ'` says — moved or not —
and performs only what the row `r` names. -/
inductive Typed (F : List Fn) (O : List Op) : Ctx → Expr → Ty → Ctx → Row → Prop
  | lit : Typed F O Γ (.lit n) .int Γ r
  | read : PlaceTy Γ p .int w y → Typed F O Γ (.read p) .int Γ r
  | move : lookup x Γ = some (.own (.box τ) true) →
      Typed F O Γ (.move x) (.box τ) (setSlot Γ x (.own (.box τ) false)) r
  | add : Typed F O Γ a .int Γ₁ r → Typed F O Γ₁ b .int Γ₂ r → Typed F O Γ (.add a b) .int Γ₂ r
  | new : Typed F O Γ a τ Γ₁ r → Typed F O Γ (.new a) (.box τ) Γ₁ r
  | let_ : lookup x Γ = none → Typed F O Γ a τ Γ₁ r →
      Typed F O ((x, .own τ true) :: Γ₁) b τb ((x, .own τ live) :: Γ₂) r → Typed F O Γ (.let_ x τ a b) τb Γ₂ r
  | write : Typed F O Γ a .int Γ₁ r → PlaceTy Γ₁ p .int true y → Typed F O Γ (.write p a) .int Γ₁ r
  | assign : Typed F O Γ a τ Γ₁ r → PlaceTy Γ₁ p τ true y → Typed F O Γ (.assign p τ a) .int Γ₁ r
  | call : F[f]? = some d → (∀ l ∈ d.row, l ∈ r) → Args F O Γ owned (d.owns.map Prod.snd) Γ₁ r →
      Lends Γ₁ lent (d.refs.map Prod.snd) ys → Exclusive ys →
      Typed F O Γ (.call f owned lent) d.ret Γ₁ r
  | seq : Typed F O Γ a .int Γ₁ r → Typed F O Γ₁ b τ Γ₂ r → Typed F O Γ (.seq a b) τ Γ₂ r
  /-- Where the branches disagree, a variable is perhaps moved. -/
  | ite : Typed F O Γ c .int Γ₀ r → Typed F O Γ₀ a τ Γa r → Typed F O Γ₀ b τ Γb r → Weaker Γ' Γa →
      Weaker Γ' Γb → Typed F O Γ (.ite c a b) τ Γ' r
  | throw_ : Typed F O Γ a .int Γ₁ r → Label.fail ∈ r → Typed F O Γ (.throw_ a) τ Γ₁ r
  /-- The handler starts where the body would have ended: what the body moves is perhaps moved. -/
  | try_ : lookup x Γb = none → Typed F O Γ body τ Γb (.fail :: r) →
      Typed F O ((x, .own .int true) :: Γb) h τ ((x, .own .int live) :: Γh) r →
      Typed F O Γ (.try_ body x h) τ Γh r
  /-- A loop moves nothing: each pass starts where the one before started. -/
  | while_ : Typed F O Γ c .int Γ r → Typed F O Γ b .int Γ r → Typed F O Γ (.while_ c b) .int Γ r
  /-- A borrow lives as long as the code it is in scope for: what the place is rooted at is only
  read, or not reached, until it ends. -/
  | lend : lookup x Γ = none → PlaceTy Γ p τ w y → (m = .mut → w = true) →
      Typed F O ((x, .ref m τ) :: lendCtx m Γ y) body τb ((x, .ref m τ) :: Γb) r →
      Typed F O Γ (.lend x m p body) τb (thaw Γ [y] Γb) r
  /-- Cleanup starts where the body would have ended, and moves nothing. -/
  | defer : Typed F O Γ body τ Γb r → Typed F O Γb d .int Γb r → Typed F O Γ (.defer τ d body) τ Γb r
  | perform : O[e]? = some op → Label.eff e ∈ r → Args F O Γ owned op.owns Γ₁ r →
      Lends Γ₁ lent op.refs ys → Exclusive ys → Typed F O Γ (.perform e owned lent) op.ret Γ₁ r
  /-- The arm runs in the context of the `handle`: its row is the `handle`'s. What it is lent of
  the `handle`'s scope the body may only read, or, lent `mut`, not reach. -/
  | handle : O[e]? = some op → os.length = op.owns.length → rs.length = op.refs.length →
      Caps Γ caps ys → Exclusive ys → (os ++ rs ++ caps.map Cap.name).Nodup →
      Typed F O (armCtx os rs op (caps.map Cap.sig)) arm op.ret Γa r →
      Typed F O (freeze (hideAll Γ (roots .mut ys)) (roots .ro ys)) body τ Γb (.eff e :: r) →
      Typed F O Γ (.handle body e caps os rs arm) τ
        (unhideAll Γ (roots .mut ys) (thaw (hideAll Γ (roots .mut ys)) (roots .ro ys) Γb)) r
  /-- As for `try`, the arm starts where the body would have ended. -/
  | handleAbort : O[e]? = some op → op.owns = [.int] → op.refs = [] → lookup x Γb = none →
      Typed F O Γ body τ Γb (.eff e :: r) →
      Typed F O ((x, .own .int true) :: Γb) h τ ((x, .own .int live) :: Γh) r →
      Typed F O Γ (.handleAbort body e x h) τ Γh r

/-- The owned arguments, in order, against the parameters' types. -/
inductive Args (F : List Fn) (O : List Op) : Ctx → List Expr → List Ty → Ctx → Row → Prop
  | nil : Args F O Γ [] [] Γ r
  | cons : Typed F O Γ a τ Γ₁ r → Args F O Γ₁ as τs Γ₂ r → Args F O Γ (a :: as) (τ :: τs) Γ₂ r

end


end FlyCore.Ownership
