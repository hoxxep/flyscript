import FlyCore.OwnershipMain

/-!
# A checker for λ-fly, proved sound

`infer` decides, for a program the compiler elaborated into λ-fly (`--core`), what type each
expression has and what it leaves of its variables, by the rules of `Typed`, choosing as the rules
leave open: where branches disagree about a move, the variable is moved. It is sound: whatever it
accepts is well typed (`infer_sound`), so `program_ok` holds of it, and a program it accepts never
gets stuck. It is not complete — it takes λ-fly's first-order part: integers, boxes, pairs, unions of
two, `let`, branches, loops, borrows of places, calls of functions, failures, cleanup and vectors —
and answers `none` for the rest, closures, handlers, regions, tasks and generators, which the
compiler's own checker and its tests answer for.
-/

namespace FlyCore.Ownership.Check
open FlyCore.Ownership

/-- A place's type, whether it may be changed through it, and the variable it is rooted at. -/
def placeTy (Γ : Ctx) : Place → Option (Ty × Bool × Var)
  | .var x =>
    match lookup x Γ with
    | some (.own τ true) => some (τ, true, x)
    | some (.ref m τ) => some (τ, m == .mut, x)
    | some (.half t A B) => some (.lent1 t A B, true, x)
    | _ => none
  | .deref p =>
    match placeTy Γ p with
    | some (.box τ, w, y) => some (τ, w, y)
    | _ => none
  | .fst p =>
    match placeTy Γ p with
    | some (.pair A _, w, y) => some (A, w, y)
    | _ => none
  | .snd p =>
    match placeTy Γ p with
    | some (.pair _ B, w, y) => some (B, w, y)
    | _ => none

theorem placeTy_sound : ∀ {p : Place} {τ w y}, placeTy Γ p = some (τ, w, y) → PlaceTy Γ p τ w y
  | .var x, τ, w, y, h => by
    simp only [placeTy] at h
    split at h <;> (try simp only [Option.some.injEq, Prod.mk.injEq] at h) <;> (try contradiction)
    · obtain ⟨rfl, rfl, rfl⟩ := h; exact .own ‹_›
    · obtain ⟨rfl, rfl, rfl⟩ := h; exact .ref ‹_›
    · obtain ⟨rfl, rfl, rfl⟩ := h; exact .half ‹_› rfl
  | .deref p, τ, w, y, h => by
    simp only [placeTy] at h
    split at h <;> (try simp only [Option.some.injEq, Prod.mk.injEq] at h) <;> (try contradiction)
    obtain ⟨rfl, rfl, rfl⟩ := h; exact .deref (placeTy_sound ‹_›)
  | .fst p, τ, w, y, h => by
    simp only [placeTy] at h
    split at h <;> (try simp only [Option.some.injEq, Prod.mk.injEq] at h) <;> (try contradiction)
    obtain ⟨rfl, rfl, rfl⟩ := h; exact .fst (placeTy_sound ‹_›)
  | .snd p, τ, w, y, h => by
    simp only [placeTy] at h
    split at h <;> (try simp only [Option.some.injEq, Prod.mk.injEq] at h) <;> (try contradiction)
    obtain ⟨rfl, rfl, rfl⟩ := h; exact .snd (placeTy_sound ‹_›)

/-- An atom's type, and what it leaves of its variables. -/
def atomTy (Γ : Ctx) : Atom → Option (Ty × Ctx)
  | .lit _ => some (.int, Γ)
  | .read p =>
    match placeTy Γ p with
    | some (.int, _, _) => some (.int, Γ)
    | some (.rref c k τ, _, _) => some (.rref c k τ, Γ)
    | _ => none
  | .move x =>
    match lookup x Γ with
    | some (.own τ true) => if τ.complete = true then some (τ, setSlot Γ x (.own τ false)) else none
    | _ => none

theorem atomTy_sound : ∀ {a : Atom} {τ Γ'}, atomTy Γ a = some (τ, Γ') → AtomTy Γ a τ Γ'
  | .lit n, τ, Γ', h => by
    simp only [atomTy, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact .lit
  | .read p, τ, Γ', h => by
    simp only [atomTy] at h
    split at h <;> (try simp only [Option.some.injEq, Prod.mk.injEq] at h) <;> (try contradiction)
    · obtain ⟨rfl, rfl⟩ := h; exact .read (placeTy_sound ‹_›)
    · obtain ⟨rfl, rfl⟩ := h; exact .readRef (placeTy_sound ‹_›)
  | .move x, τ, Γ', h => by
    simp only [atomTy] at h
    split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; exact .move ‹_› ‹_›
      · contradiction
    · contradiction

/-- The owned arguments against the parameters' types, and what they leave. -/
def atomsTy (Γ : Ctx) : List Atom → List Ty → Option Ctx
  | [], [] => some Γ
  | a :: as, τ :: τs =>
    match atomTy Γ a with
    | some (τ', Γ₁) => if τ' = τ then atomsTy Γ₁ as τs else none
    | none => none
  | _, _ => none

theorem atomsTy_sound : ∀ {as : List Atom} {τs : List Ty} {Γ Γ'}, atomsTy Γ as τs = some Γ' → AtomsTy Γ as τs Γ'
  | [], [], Γ, Γ', h => by simp only [atomsTy, Option.some.injEq] at h; subst h; exact .nil
  | a :: as, τ :: τs, Γ, Γ', h => by
    unfold atomsTy at h
    split at h
    · split at h
      · subst_vars
        exact .cons (atomTy_sound ‹_›) (atomsTy_sound h)
      · contradiction
    · contradiction
  | [], _ :: _, _, _, h => by simp [atomsTy] at h
  | _ :: _, [], _, _, h => by simp [atomsTy] at h

/-- The places lent, against the parameters' modes and types; the variables they are rooted at. -/
def lendsTy (Γ : Ctx) : List (Mode × Place) → List (Mode × Ty) → Option (List (Mode × Var))
  | [], [] => some []
  | (m, p) :: rest, (m', τ') :: ts =>
    if m = m' then
      match placeTy Γ p with
      | some (τ, w, y) =>
        if τ = τ' ∧ (m = .mut → w = true) ∧ τ.whole = true then
          match lendsTy Γ rest ts with
          | some ys => some ((m, y) :: ys)
          | none => none
        else none
      | none => none
    else none
  | _, _ => none

theorem lendsTy_sound : ∀ {lent : List (Mode × Place)} {ts ys}, lendsTy Γ lent ts = some ys → Lends Γ lent ts ys
  | [], [], ys, h => by simp only [lendsTy, Option.some.injEq] at h; subst h; exact .nil
  | (m, p) :: rest, (m', τ') :: ts, ys, h => by
    unfold lendsTy at h
    split at h
    · subst_vars
      split at h
      · split at h
        · rename_i hc
          obtain ⟨rfl, hw, hwh⟩ := hc
          split at h
          · simp only [Option.some.injEq] at h
            subst h
            exact .cons (placeTy_sound ‹_›) hw hwh (lendsTy_sound ‹_›)
          · contradiction
        · contradiction
      · contradiction
    · contradiction
  | [], _ :: _, _, h => by simp [lendsTy] at h
  | _ :: _, [], _, h => by simp [lendsTy] at h

/-- Places lent apart, simply: two rooted at one variable are both lent `readonly`. -/
def apart (lent : List (Mode × Place)) : Bool :=
  decide (lent.Pairwise fun a b => a.2.root ≠ b.2.root ∨ (a.1 = .ro ∧ b.1 = .ro))

theorem apart_sound : apart lent = true → LentApart lent := by
  intro h
  simp only [apart, decide_eq_true_eq] at h
  refine h.imp fun {a b} hab hr => ?_
  rcases hab with hne | hro
  · exact absurd hr hne
  · exact .inl hro

/-- What two branches leave, where they agree; a variable one of them moved is moved. -/
def slotMeet (s t : Slot) : Option Slot :=
  if s = t then some s
  else
    match s, t with
    | .own τ _, .own τ' _ => if τ = τ' ∧ τ.isHole = false then some (.own τ false) else none
    | _, _ => none

theorem slotMeet_sound : slotMeet s t = some u → Slot.Le u s ∧ Slot.Le u t := by
  intro h
  unfold slotMeet at h
  split at h
  · simp only [Option.some.injEq] at h
    subst_vars
    exact ⟨.refl, .refl⟩
  · split at h
    · rename_i τ a τ' b _
      split at h
      · rename_i hc
        obtain ⟨rfl, hh⟩ := hc
        simp only [Option.some.injEq] at h
        subst h
        constructor
        · cases a
          · exact .refl
          · exact .forget hh
        · cases b
          · exact .refl
          · exact .forget hh
      · contradiction
    · contradiction

def meet : Ctx → Ctx → Option Ctx
  | [], [] => some []
  | (x, s) :: Γ, (y, t) :: Δ =>
    if x = y then
      match slotMeet s t, meet Γ Δ with
      | some u, some r => some ((x, u) :: r)
      | _, _ => none
    else none
  | _, _ => none

theorem meet_sound : ∀ {Γ Δ Γ' : Ctx}, meet Γ Δ = some Γ' → Weaker Γ' Γ ∧ Weaker Γ' Δ
  | [], [], Γ', h => by simp only [meet, Option.some.injEq] at h; subst h; exact ⟨.nil, .nil⟩
  | (x, s) :: Γ, (y, t) :: Δ, Γ', h => by
    unfold meet at h
    split at h
    · subst_vars
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        obtain ⟨h1, h2⟩ := slotMeet_sound ‹_›
        obtain ⟨w1, w2⟩ := meet_sound ‹_›
        exact ⟨.cons h1 w1, .cons h2 w2⟩
      · contradiction
    · contradiction
  | [], _ :: _, _, h => by simp [meet] at h
  | _ :: _, [], _, h => by simp [meet] at h

/-- No field of `y`'s pair is lent. -/
def unsplit (Γ : Ctx) (y : Var) : Bool :=
  match lookup y Γ with
  | some (.half _ _ _) => false
  | _ => true

theorem unsplit_sound : unsplit Γ y = true → Unsplit Γ y := by
  intro h t A B he
  simp [unsplit, he] at h

/-- Nothing is put in place of a closure borrowed `mut`. -/
def noShell (Γ : Ctx) (y : Var) : Bool :=
  match lookup y Γ with
  | some (.ref .mut τ') => !τ'.shell
  | _ => true

theorem noShell_sound : noShell Γ y = true → ∀ τ', lookup y Γ = some (.ref .mut τ') → τ'.shell = false := by
  intro h τ' he
  simp [noShell, he] at h
  exact h

/-- The type an expression has, given the type it is wanted at if that is known, and what it leaves
of its variables, under the row `r`; `none` if it is not well typed, or not of the part of λ-fly
this checker takes. -/
def infer (F : List Fn) (O : List Op) : Ctx → Expr → Option Ty → Row → Option (Ty × Ctx)
  | Γ, .atom a, _, _ => atomTy Γ a
  | Γ, .arith _ a b, _, _ =>
    match atomTy Γ a with
    | some (.int, Γ₁) =>
      match atomTy Γ₁ b with
      | some (.int, Γ₂) => some (.int, Γ₂)
      | _ => none
    | _ => none
  | Γ, .new a, _, _ =>
    match atomTy Γ a with
    | some (τ, Γ₁) => some (.box τ, Γ₁)
    | none => none
  | Γ, .pair a b, _, _ =>
    match atomTy Γ a with
    | some (A, Γ₁) =>
      match atomTy Γ₁ b with
      | some (B, Γ₂) => some (.pair A B, Γ₂)
      | none => none
    | none => none
  | Γ, .inj A B t a, _, _ =>
    match atomTy Γ a with
    | some (τ, Γ₁) => if τ = (if t then A else B) ∧ (Ty.sum A B).complete = true then some (.sum A B, Γ₁) else none
    | none => none
  | Γ, .case x y A B e₁ e₂, exp, r =>
    if lookup x Γ = some (.own (.sum A B) true) ∧ (Ty.sum A B).complete = true ∧ lookup y Γ = none then
      match infer F O ((y, .own A true) :: setSlot Γ x (.own (.sum A B) false)) e₁ exp r with
      | some (τ, (y₁, .own A₁ _) :: Γ₁) =>
        if y₁ = y ∧ A₁ = A then
          match infer F O ((y, .own B true) :: setSlot Γ x (.own (.sum A B) false)) e₂ (some τ) r with
          | some (τ₂, (y₂, .own B₂ _) :: Γ₂) =>
            if τ₂ = τ ∧ y₂ = y ∧ B₂ = B then
              match meet Γ₁ Γ₂ with
              | some Γ' => some (τ, Γ')
              | none => none
            else none
          | _ => none
        else none
      | _ => none
    else none
  | Γ, .let_ x τ a b, exp, r =>
    if lookup x Γ = none then
      match infer F O Γ a (some τ) r with
      | some (τa, Γ₁) =>
        if τa = τ then
          match infer F O ((x, .own τ true) :: Γ₁) b exp r with
          | some (τb, (x', .own τ' _) :: Γ₂) => if x' = x ∧ τ' = τ then some (τb, Γ₂) else none
          | _ => none
        else none
      | none => none
    else none
  | Γ, .write p a, _, _ =>
    match atomTy Γ a with
    | some (.int, Γ₁) =>
      match placeTy Γ₁ p with
      | some (.int, true, _) => some (.int, Γ₁)
      | _ => none
    | _ => none
  | Γ, .assign p τ a, _, _ =>
    match atomTy Γ a with
    | some (τa, Γ₁) =>
      match placeTy Γ₁ p with
      | some (τp, true, y) => if τa = τ ∧ τp = τ ∧ noShell Γ₁ y = true then some (.int, Γ₁) else none
      | _ => none
    | none => none
  | Γ, .call f owned lent, _, r =>
    match F[f]? with
    | some d =>
      if d.retp = none ∧ d.cap = none ∧ (∀ l ∈ d.row, l ∈ r) then
        match atomsTy Γ owned (d.owns.map fun p => p.2.shiftBy 0) with
        | some Γ₁ =>
          match lendsTy Γ₁ lent (d.refs.map fun p => (p.2.1, p.2.2.shiftBy 0)) with
          | some _ => if apart lent = true then some (d.ret.shiftBy 0, Γ₁) else none
          | none => none
        | none => none
      else none
    | none => none
  | Γ, .ite c a b, exp, r =>
    match atomTy Γ c with
    | some (.int, Γ₀) =>
      match infer F O Γ₀ a exp r with
      | some (τ, Γa) =>
        match infer F O Γ₀ b (some τ) r with
        | some (τb, Γb) =>
          if τb = τ then
            match meet Γa Γb with
            | some Γ' => some (τ, Γ')
            | none => none
          else none
        | none => none
      | none => none
    | _ => none
  | Γ, .throw_ a, exp, r =>
    match exp, atomTy Γ a with
    | some τ, some (.int, Γ₁) => if Label.fail ∈ r then some (τ, Γ₁) else none
    | _, _ => none
  | Γ, .try_ body x h, exp, r =>
    match infer F O Γ body exp (.fail :: r) with
    | some (τ, Γb) =>
      if lookup x Γb = none then
        match infer F O ((x, .own .int true) :: Γb) h (some τ) r with
        | some (τh, (x', .own .int _) :: Γh) => if τh = τ ∧ x' = x then some (τ, Γh) else none
        | _ => none
      else none
    | none => none
  | Γ, .while_ c b, _, r =>
    match infer F O Γ c (some .int) r, infer F O Γ b (some .int) r with
    | some (.int, Γc), some (.int, Γb) => if Γc = Γ ∧ Γb = Γ then some (.int, Γ) else none
    | _, _ => none
  | Γ, .lend x m p body, exp, r =>
    if lookup x Γ = none then
      match placeTy Γ p with
      | some (τ, w, y) =>
        if (m = .mut → w = true) ∧ (m = .mut → τ.shell = false) ∧ (m = .mut → unsplit Γ y = true) then
          match infer F O ((x, .ref m τ) :: lendCtx m Γ y) body exp r with
          | some (τb, (x', .ref m' τ') :: Γb) =>
            if x' = x ∧ m' = m ∧ τ' = τ then some (τb, thaw Γ [y] Γb) else none
          | _ => none
        else none
      | none => none
    else none
  | Γ, .defer τ d body, _, r =>
    match infer F O Γ body (some τ) r with
    | some (τb, Γb) =>
      if τb = τ then
        match infer F O Γb d (some .int) r with
        | some (.int, Γd) => if Γd = Γb then some (τ, Γb) else none
        | _ => none
      else none
    | none => none
  | Γ, .vnew, exp, _ =>
    match exp with
    | some (.vec true τ) => if τ.complete = true then some (.vec true τ, Γ) else none
    | _ => none
  | Γ, .vlen p, _, _ =>
    match placeTy Γ p with
    | some (.vec _ _, _, _) => some (.int, Γ)
    | _ => none
  | Γ, .vpush p a, _, _ =>
    match atomTy Γ a with
    | some (τ, Γ₁) =>
      match placeTy Γ₁ p with
      | some (.vec true τ', true, _) => if τ' = τ then some (.int, Γ₁) else none
      | _ => none
    | none => none
  | Γ, .vpop p, _, _ =>
    match placeTy Γ p with
    | some (.vec true τ, true, _) => if τ.complete = true then some (.sum .int τ, Γ) else none
    | _ => none
  | _, _, _, _ => none

/-- What `infer` accepts is well typed. -/
theorem infer_sound : ∀ {e : Expr} {Γ : Ctx} {exp : Option Ty} {r : Row} {τ : Ty} {Γ' : Ctx},
    infer F O Γ e exp r = some (τ, Γ') → Typed F O Γ e τ Γ' r
  | .atom a, Γ, exp, r, τ, Γ', h => by
    simp only [infer] at h
    exact .atom (atomTy_sound h)
  | .arith o a b, Γ, exp, r, τ, Γ', h => by
    simp only [infer] at h
    split at h <;> (try contradiction)
    split at h <;> (try contradiction)
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .add (atomTy_sound ‹_›) (atomTy_sound ‹_›)
  | .new a, Γ, exp, r, τ, Γ', h => by
    simp only [infer] at h
    split at h <;> (try contradiction)
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .new (atomTy_sound ‹_›)
  | .pair a b, Γ, exp, r, τ, Γ', h => by
    simp only [infer] at h
    split at h <;> (try contradiction)
    split at h <;> (try contradiction)
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .pair (atomTy_sound ‹_›) (atomTy_sound ‹_›)
  | .inj A B t a, Γ, exp, r, τ, Γ', h => by
    simp only [infer] at h
    split at h <;> (try contradiction)
    rename_i ha
    cases t <;> simp only [Bool.false_eq_true, ite_false, ite_true] at h <;>
      (split at h <;> (try contradiction)) <;> rename_i hc <;> obtain ⟨rfl, hcomp⟩ := hc <;> cases h <;>
      exact .inj (atomTy_sound ha) hcomp
  | .case x y A B e₁ e₂, Γ, exp, r, τ, Γ', h => by
    simp only [infer] at h
    split at h <;> (try contradiction)
    rename_i hc
    obtain ⟨hx, hcomp, hy⟩ := hc
    split at h <;> (try contradiction)
    rename_i h₁
    split at h <;> (try contradiction)
    rename_i hc1
    obtain ⟨rfl, rfl⟩ := hc1
    split at h <;> (try contradiction)
    rename_i h₂
    split at h <;> (try contradiction)
    rename_i hc2
    obtain ⟨rfl, rfl, rfl⟩ := hc2
    split at h <;> (try contradiction)
    rename_i hm
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨w1, w2⟩ := meet_sound hm
    exact .case hx hcomp hy (infer_sound h₁) (infer_sound h₂) w1 w2
  | .let_ x σ a b, Γ, exp, r, τ, Γ', h => by
    simp only [infer] at h
    split at h <;> (try contradiction)
    rename_i hx
    split at h <;> (try contradiction)
    rename_i ha
    split at h <;> (try contradiction)
    rename_i hτ
    subst hτ
    split at h <;> (try contradiction)
    rename_i hb
    split at h <;> (try contradiction)
    rename_i hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .let_ hx (infer_sound ha) (infer_sound hb)
  | .write p a, Γ, exp, r, τ, Γ', h => by
    simp only [infer] at h
    split at h <;> (try contradiction)
    split at h <;> (try contradiction)
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .write (atomTy_sound ‹_›) (placeTy_sound ‹_›)
  | .assign p σ a, Γ, exp, r, τ, Γ', h => by
    simp only [infer] at h
    split at h <;> (try contradiction)
    rename_i ha
    split at h <;> (try contradiction)
    rename_i hp
    split at h <;> (try contradiction)
    rename_i hc
    obtain ⟨rfl, rfl, hs⟩ := hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .assign (atomTy_sound ha) (placeTy_sound hp) (noShell_sound hs)
  | .call f owned lent, Γ, exp, r, τ, Γ', h => by
    simp only [infer] at h
    split at h <;> (try contradiction)
    rename_i hf
    split at h <;> (try contradiction)
    rename_i hc
    obtain ⟨hr, hcap, hrow⟩ := hc
    split at h <;> (try contradiction)
    rename_i hown
    split at h <;> (try contradiction)
    rename_i hlent
    split at h <;> (try contradiction)
    rename_i hap
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .call hf hr hcap hrow (atomsTy_sound hown) (lendsTy_sound hlent) (apart_sound hap)
  | .ite c a b, Γ, exp, r, τ, Γ', h => by
    simp only [infer] at h
    split at h <;> (try contradiction)
    rename_i hc
    split at h <;> (try contradiction)
    rename_i ha
    split at h <;> (try contradiction)
    rename_i hb
    split at h <;> (try contradiction)
    rename_i hτ
    subst hτ
    split at h <;> (try contradiction)
    rename_i hm
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨w1, w2⟩ := meet_sound hm
    exact .ite (atomTy_sound hc) (infer_sound ha) (infer_sound hb) w1 w2
  | .throw_ a, Γ, exp, r, τ, Γ', h => by
    simp only [infer] at h
    split at h <;> (try contradiction)
    rename_i ha
    split at h <;> (try contradiction)
    rename_i hr
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .throw_ (atomTy_sound ha) hr
  | .try_ body x hd, Γ, exp, r, τ, Γ', h => by
    simp only [infer] at h
    split at h <;> (try contradiction)
    rename_i hb
    split at h <;> (try contradiction)
    rename_i hx
    split at h <;> (try contradiction)
    rename_i hh
    split at h <;> (try contradiction)
    rename_i hc
    obtain ⟨rfl, rfl⟩ := hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .try_ hx (infer_sound hb) (infer_sound hh)
  | .while_ c b, Γ, exp, r, τ, Γ', h => by
    simp only [infer] at h
    split at h <;> (try contradiction)
    rename_i hc hb
    split at h <;> (try contradiction)
    rename_i he
    obtain ⟨rfl, rfl⟩ := he
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .while_ (infer_sound hc) (infer_sound hb)
  | .lend x m p body, Γ, exp, r, τ, Γ', h => by
    simp only [infer] at h
    split at h <;> (try contradiction)
    rename_i hx
    split at h <;> (try contradiction)
    rename_i hp
    split at h <;> (try contradiction)
    rename_i hc
    obtain ⟨hw, hs, hu⟩ := hc
    split at h <;> (try contradiction)
    rename_i hb
    split at h <;> (try contradiction)
    rename_i he
    obtain ⟨rfl, rfl, rfl⟩ := he
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .lend hx (placeTy_sound hp) hw hs (fun hm => unsplit_sound (hu hm)) (infer_sound hb)
  | .defer σ d body, Γ, exp, r, τ, Γ', h => by
    simp only [infer] at h
    split at h <;> (try contradiction)
    rename_i hb
    split at h <;> (try contradiction)
    rename_i hτ
    subst hτ
    split at h <;> (try contradiction)
    rename_i hd
    split at h <;> (try contradiction)
    rename_i he
    subst he
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .defer (infer_sound hb) (infer_sound hd)
  | .vnew, Γ, exp, r, τ, Γ', h => by
    simp only [infer] at h
    split at h <;> (try contradiction)
    split at h <;> (try contradiction)
    rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .vnew hc
  | .vlen p, Γ, exp, r, τ, Γ', h => by
    simp only [infer] at h
    split at h <;> (try contradiction)
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .vlen (placeTy_sound ‹_›)
  | .vpush p a, Γ, exp, r, τ, Γ', h => by
    simp only [infer] at h
    split at h <;> (try contradiction)
    rename_i ha
    split at h <;> (try contradiction)
    rename_i hp
    split at h <;> (try contradiction)
    rename_i he
    subst he
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .vpush (atomTy_sound ha) (placeTy_sound hp)
  | .vpop p, Γ, exp, r, τ, Γ', h => by
    simp only [infer] at h
    split at h <;> (try contradiction)
    rename_i hp
    split at h <;> (try contradiction)
    rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .vpop (placeTy_sound hp) hc
  | .caseRef .., _, _, _, _, _, h | .lam .., _, _, _, _, _, h | .apply .., _, _, _, _, _, h
  | .lendClo .., _, _, _, _, _, h | .lendCall .., _, _, _, _, _, h | .perform .., _, _, _, _, _, h
  | .handle .., _, _, _, _, _, h | .handleAbort .., _, _, _, _, _, h | .handleR .., _, _, _, _, _, h
  | .par .., _, _, _, _, _, h | .region .., _, _, _, _, _, h | .ralloc .., _, _, _, _, _, h
  | .rget .., _, _, _, _, _, h | .rset .., _, _, _, _, _, h | .rlnew .., _, _, _, _, _, h
  | .rpush .., _, _, _, _, _, h | .rnth .., _, _, _, _, _, h | .rlen .., _, _, _, _, _, h
  | .lendSlice .., _, _, _, _, _, h | .gen .., _, _, _, _, _, h | .scope .., _, _, _, _, _, h
  | .handleV .., _, _, _, _, _, h | .resume .., _, _, _, _, _, h | .lendIdx .., _, _, _, _, _, h => by
    simp [infer] at h

/-- A function the checker takes: its parameters named apart, neither a closure's code nor one that
returns a borrow, and its body of its result type, performing what its row names. -/
def fnOk (F : List Fn) (O : List Op) (d : Fn) : Bool :=
  decide ((d.owns.map Prod.fst ++ d.refs.map Prod.fst).Nodup) &&
    match d.cap, d.retp with
    | none, none =>
      match infer F O (fnCtx d) d.body (some d.ret) d.row with
      | some (τ, _) => decide (τ = d.ret)
      | none => false
    | _, _ => false

theorem fnOk_sound : fnOk F O d = true → FnOk F O d := by
  intro h
  simp only [fnOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hn, h⟩ := h
  unfold FnOk
  refine ⟨hn, ?_⟩
  split at h <;> (try contradiction)
  rename_i hc hr
  simp only [hc, hr]
  split at h <;> (try contradiction)
  rename_i hb
  simp only [decide_eq_true_eq] at h
  subst h
  exact ⟨_, infer_sound hb⟩

def fnsOk (F : List Fn) (O : List Op) : Bool := F.all (fnOk F O)

theorem fnsOk_sound : fnsOk F O = true → FnsOk F O := by
  intro h d hd
  simp only [fnsOk, List.all_eq_true] at h
  exact fnOk_sound (h d hd)

/-- A program the checker takes — its functions, and its main expression, which may fail — never
gets stuck: as `program_ok`, given no more than that the checker answered. -/
theorem certified (hF : fnsOk F O = true) (he : infer F O [] e none [.fail] = some (τ, Γ')) (n : Nat) :
    match eval F O n [.abort .fail 0] .empty [] e with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.ended, _) => True
    | (.val v, σ') => ∃ L, VT F ⟨[], Wstar F O⟩ σ' τ v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok (fnsOk_sound hF) (infer_sound he) n

end FlyCore.Ownership.Check
