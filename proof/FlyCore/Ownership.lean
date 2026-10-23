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
  /-- What no row holds: the barrier code is unwound to as it is dropped. -/
  | drop
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

/-- A capture as its frame has it: where its place was when the `handle` began. -/
def Cap.at (c : Cap Place) (l : Nat) : Cap Nat := ⟨c.name, c.mode, c.ty, l⟩

/-- A place: a variable, or what a box at a place points to. -/
inductive Place where
  | var (x : Var)
  | deref (p : Place)
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
  /-- `let x: τ = a; b`, `x` dropped when `b` ends unless it was moved. -/
  | let_ (x : Var) (τ : Ty) (a b : Expr)
  /-- `p = a` for an integer place. -/
  | write (p : Place) (a : Atom)
  /-- `p = a` for a place holding a `box τ`: what it held is dropped. -/
  | assign (p : Place) (τ : Ty) (a : Atom)
  /-- A call: the owned arguments, in order, then the places lent, each with its mode. -/
  | call (f : Nat) (owned : List Atom) (lent : List (Mode × Place))
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
      | some (.ptr l) => some (.ptr l, σ.set c (some .moved))
      | _ => none
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

/-- `AtomTy Γ a τ Γ'`: `a` has type `τ`, and leaves its variables as `Γ'` says. -/
inductive AtomTy (Γ : Ctx) : Atom → Ty → Ctx → Prop
  | lit : AtomTy Γ (.lit n) .int Γ
  | read : PlaceTy Γ p .int w y → AtomTy Γ (.read p) .int Γ
  | move : lookup x Γ = some (.own (.box τ) true) →
      AtomTy Γ (.move x) (.box τ) (setSlot Γ x (.own (.box τ) false))

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
  | let_ : lookup x Γ = none → Typed F O Γ a τ Γ₁ r →
      Typed F O ((x, .own τ true) :: Γ₁) b τb ((x, .own τ live) :: Γ₂) r → Typed F O Γ (.let_ x τ a b) τb Γ₂ r
  | write : AtomTy Γ a .int Γ₁ → PlaceTy Γ₁ p .int true y → Typed F O Γ (.write p a) .int Γ₁ r
  | assign : AtomTy Γ a τ Γ₁ → PlaceTy Γ₁ p τ true y → Typed F O Γ (.assign p τ a) .int Γ₁ r
  | call : F[f]? = some d → (∀ l ∈ d.row, l ∈ r) → AtomsTy Γ owned (d.owns.map Prod.snd) Γ₁ →
      Lends Γ₁ lent (d.refs.map Prod.snd) ys → Exclusive ys →
      Typed F O Γ (.call f owned lent) d.ret Γ₁ r
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
  | lend : lookup x Γ = none → PlaceTy Γ p τ w y → (m = .mut → w = true) →
      Typed F O ((x, .ref m τ) :: lendCtx m Γ y) body τb ((x, .ref m τ) :: Γb) r →
      Typed F O Γ (.lend x m p body) τb (thaw Γ [y] Γb) r
  /-- Cleanup starts where the body would have ended, and moves nothing. -/
  | defer : Typed F O Γ body τ Γb r → Typed F O Γb d .int Γb r → Typed F O Γ (.defer τ d body) τ Γb r
  | perform : O[e]? = some op → Label.eff e ∈ r → AtomsTy Γ owned op.owns Γ₁ →
      Lends Γ₁ lent op.refs ys → Exclusive ys → Typed F O Γ (.perform e owned lent) op.ret Γ₁ r
  /-- The arm runs in the context of the `handle`: its row is the `handle`'s. What it is lent of
  the `handle`'s scope the body may only read, or, lent `mut`, not reach. -/
  | handle : O[e]? = some op → os.length = op.owns.length → rs.length = op.refs.length →
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
