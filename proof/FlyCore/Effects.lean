/-!
# Effects and handlers

The effect fragment of λ-fly (spec §5, §9): functions, failures (`throw`, `try`), and handlers of
user effects, both kinds — an arm that resumes the body with the operation's result, and an arm
that ends the `handle` with its own value. Handlers are deep, and an arm runs in the context of its
`handle`: what it performs goes to the handlers around the `handle`, not to those the body
installed.

The semantics is an interpreter with fuel. Running out of fuel is `timeout`; reaching a state no
rule covers — an unbound variable, an operation nothing handles, an operand of the wrong kind — is
`stuck`. The theorem `sound` is that a well-typed expression, run where every effect its row names
is handled, never gets stuck: it gives a value of its type, or an abort aimed at a frame of the
handler stack it ran under.
-/

namespace FlyCore.Effects

inductive Ty where
  | int
  | bool
  deriving DecidableEq, Repr

/-- What a row may hold: `Fail`, or a user effect by number. Every user effect has one operation,
from `int` to `int`; failures carry an `int`. -/
inductive Label where
  | fail
  | eff (n : Nat)
  deriving DecidableEq, Repr

abbrev Row := List Label
abbrev Var := String

inductive Val where
  | int (n : Int)
  | bool (b : Bool)
  deriving DecidableEq, Repr

def Val.ty : Val → Ty
  | .int _ => .int
  | .bool _ => .bool

inductive Expr where
  | lit (n : Int)
  | blit (b : Bool)
  | var (x : Var)
  | add (a b : Expr)
  | lt (a b : Expr)
  | ite (c a b : Expr)
  | let_ (x : Var) (a b : Expr)
  | call (f : Nat) (a : Expr)
  | throw_ (a : Expr)
  | try_ (body : Expr) (x : Var) (h : Expr)
  | perform (e : Nat) (a : Expr)
  /-- `handle { body } with E { op(x) resumes k => k(arm) }`: the arm's value resumes the body. -/
  | handle (body : Expr) (e : Nat) (x : Var) (arm : Expr)
  /-- `handle { body } with E { op(x) => arm }`: the arm's value is the `handle`'s. -/
  | handleAbort (body : Expr) (e : Nat) (x : Var) (arm : Expr)

abbrev Env := List (Var × Val)
abbrev Ctx := List (Var × Ty)

def lookup {α : Type} (x : Var) : List (Var × α) → Option α
  | [] => none
  | (y, v) :: r => if x = y then some v else lookup x r

/-- A function of the program: one parameter, its result, and the effects it may perform. -/
structure Fn where
  param : Var
  pty : Ty
  ret : Ty
  row : Row
  body : Expr

/-- A handler in force: one that resumes, with its arm and the environment of its `handle`; or one
that aborts — an abortive arm, or a `try` — by the number of the `handle` it unwinds to. -/
inductive Frame where
  | resume (e : Nat) (env : Env) (x : Var) (arm : Expr)
  | abort (l : Label) (id : Nat)

abbrev HS := List Frame

def Frame.handles : Frame → Label → Bool
  | .resume e _ _ _, .eff e' => e == e'
  | .resume _ _ _ _, .fail => false
  | .abort l _, l' => l == l'

/-- The innermost frame handling `l`, and the frames below it: the context its arm runs in. -/
def find (l : Label) : HS → Option (Frame × HS)
  | [] => none
  | f :: rest => if f.handles l then some (f, rest) else find l rest

inductive Res where
  | val (v : Val)
  /-- Unwinding to the `handle` or `try` numbered `id`, with the operation's argument. -/
  | abort (id : Nat) (v : Val)
  | stuck
  | timeout
  deriving DecidableEq

/-- Goes on with `k` after a value; anything else goes on out. -/
def bind : Res × Nat → (Val → Nat → Res × Nat) → Res × Nat
  | (.val v, c), k => k v c
  | r, _ => r

/-- Catches an abort aimed at the `handle` or `try` numbered `c`, going on with `k`; anything else
goes on out. -/
def catchAt (c : Nat) : Res × Nat → (Val → Nat → Res × Nat) → Res × Nat
  | (.abort id v, c1), k => if id = c then k v c1 else (.abort id v, c1)
  | r, _ => r

/-- The interpreter: fuel, the next number for a `handle`, the handlers in force, the environment.
-/
def eval (F : List Fn) : Nat → Nat → HS → Env → Expr → Res × Nat
  | 0, c, _, _, _ => (.timeout, c)
  | n + 1, c, hs, env, e =>
    match e with
    | .lit k => (.val (.int k), c)
    | .blit b => (.val (.bool b), c)
    | .var x =>
      match lookup x env with
      | some v => (.val v, c)
      | none => (.stuck, c)
    | .add a b =>
      bind (eval F n c hs env a) fun va c1 =>
        bind (eval F n c1 hs env b) fun vb c2 =>
          match va, vb with
          | .int x, .int y => (.val (.int (x + y)), c2)
          | _, _ => (.stuck, c2)
    | .lt a b =>
      bind (eval F n c hs env a) fun va c1 =>
        bind (eval F n c1 hs env b) fun vb c2 =>
          match va, vb with
          | .int x, .int y => (.val (.bool (decide (x < y))), c2)
          | _, _ => (.stuck, c2)
    | .ite cnd a b =>
      bind (eval F n c hs env cnd) fun v c1 =>
        match v with
        | .bool true => eval F n c1 hs env a
        | .bool false => eval F n c1 hs env b
        | _ => (.stuck, c1)
    | .let_ x a b =>
      bind (eval F n c hs env a) fun v c1 => eval F n c1 hs ((x, v) :: env) b
    | .call f a =>
      match F[f]? with
      | none => (.stuck, c)
      | some d => bind (eval F n c hs env a) fun v c1 => eval F n c1 hs [(d.param, v)] d.body
    | .throw_ a =>
      bind (eval F n c hs env a) fun v c1 =>
        match find .fail hs with
        | some (.abort _ id, _) => (.abort id v, c1)
        | _ => (.stuck, c1)
    | .try_ body x h =>
      catchAt c (eval F n (c + 1) (.abort .fail c :: hs) env body) fun v c1 =>
        eval F n c1 hs ((x, v) :: env) h
    | .perform ef a =>
      bind (eval F n c hs env a) fun v c1 =>
        match find (.eff ef) hs with
        | some (.resume _ henv x arm, rest) => eval F n c1 rest ((x, v) :: henv) arm
        | some (.abort _ id, _) => (.abort id v, c1)
        | none => (.stuck, c1)
    | .handle body ef x arm => eval F n c (.resume ef env x arm :: hs) env body
    | .handleAbort body ef x arm =>
      catchAt c (eval F n (c + 1) (.abort (.eff ef) c :: hs) env body) fun v c1 =>
        eval F n c1 hs ((x, v) :: env) arm

/-! ## Types -/

inductive Typed (F : List Fn) : Ctx → Expr → Ty → Row → Prop
  | lit : Typed F Γ (.lit k) .int r
  | blit : Typed F Γ (.blit b) .bool r
  | var : lookup x Γ = some τ → Typed F Γ (.var x) τ r
  | add : Typed F Γ a .int r → Typed F Γ b .int r → Typed F Γ (.add a b) .int r
  | lt : Typed F Γ a .int r → Typed F Γ b .int r → Typed F Γ (.lt a b) .bool r
  | ite : Typed F Γ c .bool r → Typed F Γ a τ r → Typed F Γ b τ r → Typed F Γ (.ite c a b) τ r
  | let_ : Typed F Γ a τ₁ r → Typed F ((x, τ₁) :: Γ) b τ r → Typed F Γ (.let_ x a b) τ r
  | call : F[f]? = some d → Typed F Γ a d.pty r → (∀ l ∈ d.row, l ∈ r) →
      Typed F Γ (.call f a) d.ret r
  | throw_ : Typed F Γ a .int r → Label.fail ∈ r → Typed F Γ (.throw_ a) τ r
  | try_ : Typed F Γ body τ (.fail :: r) → Typed F ((x, .int) :: Γ) h τ r →
      Typed F Γ (.try_ body x h) τ r
  | perform : Typed F Γ a .int r → Label.eff e ∈ r → Typed F Γ (.perform e a) .int r
  | handle : Typed F Γ body τ (.eff e :: r) → Typed F ((x, .int) :: Γ) arm .int r →
      Typed F Γ (.handle body e x arm) τ r
  | handleAbort : Typed F Γ body τ (.eff e :: r) → Typed F ((x, .int) :: Γ) arm τ r →
      Typed F Γ (.handleAbort body e x arm) τ r

/-- Every function's body has its declared type and performs only its declared effects. -/
def FnsOk (F : List Fn) : Prop :=
  ∀ d ∈ F, Typed F [(d.param, d.pty)] d.body d.ret d.row

inductive EnvOk : Env → Ctx → Prop
  | nil : EnvOk [] []
  | cons : v.ty = τ → EnvOk env Γ → EnvOk ((x, v) :: env) ((x, τ) :: Γ)

/-- Every label of the row has a handler. -/
def Covers (hs : HS) (r : Row) : Prop :=
  ∀ l ∈ r, ∃ p, find l hs = some p

/-- A handler stack whose resuming arms are well typed in the context they run in: the
environment of their `handle`, and the frames below them. -/
inductive HSOk (F : List Fn) : HS → Prop
  | nil : HSOk F []
  | abort : HSOk F rest → HSOk F (.abort l i :: rest)
  | resume : EnvOk env Γ → Typed F ((x, .int) :: Γ) arm .int r → Covers rest r → HSOk F rest →
      HSOk F (.resume e env x arm :: rest)

/-- An abort is aimed at a frame of the stack. -/
def AimedIn (i : Nat) (hs : HS) : Prop :=
  ∃ l, Frame.abort l i ∈ hs

/-- What running under `hs` at type `τ` may give. -/
def Ok (hs : HS) (τ : Ty) : Res × Nat → Prop
  | (.val v, _) => v.ty = τ
  | (.abort i v, _) => v.ty = .int ∧ AimedIn i hs
  | (.stuck, _) => False
  | (.timeout, _) => True

/-! ## Lemmas -/

theorem lookup_ok {x : Var} : ∀ {env : Env} {Γ : Ctx} {τ : Ty},
    EnvOk env Γ → lookup x Γ = some τ → ∃ v, lookup x env = some v ∧ v.ty = τ
  | _, _, _, .nil, h => by simp [lookup] at h
  | _, _, _, .cons (x := y) (v := v) hv hr, h => by
    by_cases hx : x = y
    · simp only [lookup, hx, ↓reduceIte, Option.some.injEq] at h ⊢
      exact ⟨v, rfl, h ▸ hv⟩
    · simp only [lookup, hx, ↓reduceIte] at h ⊢
      exact lookup_ok hr h

theorem bind_ok {r : Res × Nat} {k : Val → Nat → Res × Nat} :
    Ok hs τ₁ r → (∀ v c, v.ty = τ₁ → Ok hs τ₂ (k v c)) → Ok hs τ₂ (bind r k) := by
  intro h hk
  rcases r with ⟨r, c⟩
  cases r <;> simp_all [bind, Ok]

theorem find_mem : find l hs = some (f, rest) → f ∈ hs ∧ ∀ g ∈ rest, g ∈ hs := by
  induction hs with
  | nil => simp [find]
  | cons g hs ih =>
    intro h
    simp only [find] at h
    split at h
    · simp at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨List.mem_cons_self .., fun x hx => List.mem_cons_of_mem _ hx⟩
    · obtain ⟨h1, h2⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ h1, fun x hx => List.mem_cons_of_mem _ (h2 x hx)⟩

theorem find_handles : find l hs = some (f, rest) → f.handles l = true := by
  induction hs with
  | nil => simp [find]
  | cons g hs ih =>
    intro h
    simp only [find] at h
    split at h
    · simp at h
      obtain ⟨rfl, rfl⟩ := h
      assumption
    · exact ih h

/-- The frame a label finds, in a well-formed stack, is well formed where its arm runs. -/
theorem find_ok : HSOk F hs → find l hs = some (.resume e env x arm, rest) →
    HSOk F rest ∧ ∃ Γ r, EnvOk env Γ ∧ Typed F ((x, .int) :: Γ) arm .int r ∧ Covers rest r := by
  intro h
  induction h with
  | nil => simp [find]
  | @abort rest' l i _ ih =>
    intro hf
    simp only [find] at hf
    split at hf
    · simp at hf
    · exact ih hf
  | @resume env' Γ x' arm' r rest' e' hE hT hC hR ih =>
    intro hf
    simp only [find] at hf
    split at hf
    · simp at hf
      obtain ⟨⟨rfl, rfl, rfl, rfl⟩, rfl⟩ := hf
      exact ⟨hR, Γ, r, hE, hT, hC⟩
    · exact ih hf

theorem ok_lift : (∀ g ∈ rest, g ∈ hs) → Ok rest τ p → Ok hs τ p := by
  intro hsub h
  rcases p with ⟨r, c⟩
  cases r with
  | abort i v =>
    obtain ⟨hv, l, hl⟩ := h
    exact ⟨hv, l, hsub _ hl⟩
  | _ => exact h

theorem covers_cons (f : Frame) : Covers hs r → Covers (f :: hs) r := by
  intro h l hl
  obtain ⟨p, hp⟩ := h l hl
  by_cases hf : f.handles l = true
  · exact ⟨(f, hs), by simp [find, hf]⟩
  · exact ⟨p, by simp [find, hf, hp]⟩

/-- Unwinding out of a `handle` or `try` numbered `c`: an abort aimed elsewhere was aimed below. -/
theorem aimed_pop {i c : Nat} : AimedIn i (.abort l c :: hs) → i ≠ c → AimedIn i hs := by
  intro ⟨l', h⟩ hne
  rcases List.mem_cons.mp h with h | h
  · cases h; exact absurd rfl hne
  · exact ⟨l', h⟩

theorem catch_ok {r : Res × Nat} {k : Val → Nat → Res × Nat} :
    Ok (.abort l c :: hs) τ r → (∀ v c1, v.ty = .int → Ok hs τ (k v c1)) →
      Ok hs τ (catchAt c r k) := by
  intro h hk
  rcases r with ⟨r, c1⟩
  cases r with
  | abort i v =>
    obtain ⟨hv, hai⟩ := h
    simp only [catchAt]
    split
    · exact hk v c1 hv
    · exact ⟨hv, aimed_pop hai (by assumption)⟩
  | _ => exact h

/-- A resuming frame is aimed at by nothing: what its body gives, the `handle` gives. -/
theorem pop_resume : Ok (.resume e env x arm :: hs) τ r → Ok hs τ r := by
  intro h
  rcases r with ⟨r, c1⟩
  cases r with
  | abort i v =>
    obtain ⟨hv, l, hl⟩ := h
    rcases List.mem_cons.mp hl with h | h
    · cases h
    · exact ⟨hv, l, h⟩
  | _ => exact h

theorem covers_push (f : Frame) (hf : f.handles l = true) : Covers hs r → Covers (f :: hs) (l :: r) := by
  intro h l' hl
  rcases List.mem_cons.mp hl with rfl | hl
  · exact ⟨(f, hs), by simp [find, hf]⟩
  · exact covers_cons _ h l' hl

/-! ## Soundness -/

theorem sound (F : List Fn) (hF : FnsOk F) :
    ∀ n c hs env Γ e τ r, Typed F Γ e τ r → EnvOk env Γ → HSOk F hs → Covers hs r →
      Ok hs τ (eval F n c hs env e) := by
  intro n
  induction n with
  | zero => intros; simp [eval, Ok]
  | succ n ih =>
    intro c hs env Γ e τ r ht hE hH hC
    cases ht with
    | lit => simp [eval, Ok, Val.ty]
    | blit => simp [eval, Ok, Val.ty]
    | var hx =>
      obtain ⟨v, hv, hty⟩ := lookup_ok hE hx
      simp [eval, hv, Ok, hty]
    | add ha hb =>
      simp only [eval]
      refine bind_ok (ih _ _ _ _ _ _ _ ha hE hH hC) fun va c1 hva => ?_
      refine bind_ok (ih _ _ _ _ _ _ _ hb hE hH hC) fun vb c2 hvb => ?_
      cases va <;> cases vb <;> simp_all [Val.ty, Ok]
    | lt ha hb =>
      simp only [eval]
      refine bind_ok (ih _ _ _ _ _ _ _ ha hE hH hC) fun va c1 hva => ?_
      refine bind_ok (ih _ _ _ _ _ _ _ hb hE hH hC) fun vb c2 hvb => ?_
      cases va <;> cases vb <;> simp_all [Val.ty, Ok]
    | ite hc ha hb =>
      simp only [eval]
      refine bind_ok (ih _ _ _ _ _ _ _ hc hE hH hC) fun v c1 hv => ?_
      cases v with
      | int => simp [Val.ty] at hv
      | bool b =>
        cases b
        · exact ih _ _ _ _ _ _ _ hb hE hH hC
        · exact ih _ _ _ _ _ _ _ ha hE hH hC
    | let_ ha hb =>
      simp only [eval]
      refine bind_ok (ih _ _ _ _ _ _ _ ha hE hH hC) fun v c1 hv => ?_
      exact ih _ _ _ _ _ _ _ hb (.cons hv hE) hH hC
    | call hf ha hrow =>
      simp only [eval, hf]
      refine bind_ok (ih _ _ _ _ _ _ _ ha hE hH hC) fun v c1 hv => ?_
      have hd := hF _ (List.mem_of_getElem? hf)
      exact ih _ _ _ _ _ _ _ hd (.cons hv .nil) hH (fun l hl => hC l (hrow l hl))
    | throw_ ha hfail =>
      simp only [eval]
      refine bind_ok (ih _ _ _ _ _ _ _ ha hE hH hC) fun v c1 hv => ?_
      obtain ⟨⟨f, rest⟩, hfind⟩ := hC _ hfail
      have hmem := (find_mem hfind).1
      have hh := find_handles hfind
      cases f with
      | resume => simp [Frame.handles] at hh
      | abort l id => simp [hfind, Ok, hv]; exact ⟨l, hmem⟩
    | try_ hb hh =>
      simp only [eval]
      exact catch_ok (ih _ _ _ _ _ _ _ hb hE (.abort hH) (covers_push _ (by simp [Frame.handles]) hC))
        fun v c1 hv => ih _ _ _ _ _ _ _ hh (.cons hv hE) hH hC
    | perform ha hin =>
      simp only [eval]
      refine bind_ok (ih _ _ _ _ _ _ _ ha hE hH hC) fun v c1 hv => ?_
      obtain ⟨⟨f, rest⟩, hfind⟩ := hC _ hin
      have ⟨hmem, hsub⟩ := find_mem hfind
      cases f with
      | resume e' henv x arm =>
        simp only [hfind]
        obtain ⟨hR, Γ', r', hE', hT', hC'⟩ := find_ok hH hfind
        exact ok_lift hsub (ih _ _ _ _ _ _ _ hT' (.cons hv hE') hR hC')
      | abort l id => simp [hfind, Ok, hv]; exact ⟨l, hmem⟩
    | handle hb ha =>
      simp only [eval]
      exact pop_resume (ih _ _ _ _ _ _ _ hb hE (.resume hE ha hC hH)
        (covers_push _ (by simp [Frame.handles]) hC))
    | handleAbort hb ha =>
      simp only [eval]
      exact catch_ok (ih _ _ _ _ _ _ _ hb hE (.abort hH) (covers_push _ (by simp [Frame.handles]) hC))
        fun v c1 hv => ih _ _ _ _ _ _ _ ha (.cons hv hE) hH hC

/-- A whole program: a closed expression that performs nothing gives a value of its type, or runs
out of fuel. It is never stuck, and no operation goes unhandled. -/
theorem program_sound (F : List Fn) (hF : FnsOk F) (ht : Typed F [] e τ []) (n : Nat) :
    (∃ v c, eval F n 0 [] [] e = (.val v, c) ∧ v.ty = τ) ∨ ∃ c, eval F n 0 [] [] e = (.timeout, c) := by
  have h := sound F hF n 0 [] [] [] e τ [] ht .nil .nil (by simp [Covers])
  generalize eval F n 0 [] [] e = res at h
  rcases res with ⟨res, c⟩
  cases res with
  | val v => exact .inl ⟨v, c, rfl, h⟩
  | abort i v => obtain ⟨_, _, hl⟩ := h; simp at hl
  | stuck => exact h.elim
  | timeout => exact .inr ⟨c, rfl⟩

end FlyCore.Effects
