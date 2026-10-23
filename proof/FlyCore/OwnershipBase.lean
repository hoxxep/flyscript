import FlyCore.Ownership

/-!
# Ownership: the shape of the store

What a well-typed program keeps true of the store: each location a variable stands for holds a
value of the variable's type, and the cells that value owns — the location itself and the cells of
its boxes — form a tree, its footprint. Footprints of what may be changed are disjoint; footprints
of what is only read may overlap each other, but nothing that may be changed. A `mut` borrow of a
closure may change what the closure captured but only reads the closure's own cell, so nothing puts
another closure in its place while the borrow lives.
-/

namespace FlyCore.Ownership

/-- The code `f` is a closure's, called as `k`, taking an `A` and giving a `B`, performing only
what `r` names, having captured plain data of type `τc`. -/
def CloOk (F : List Fn) (f : Nat) (τc : Ty) (k : Kind) (A B : Ty) (r : Row) : Prop :=
  ∃ d xc pn, F[f]? = some d ∧ d.cap = some (xc, τc, k) ∧ d.owns = [(pn, A)] ∧ d.refs = [] ∧
    d.retp = none ∧ d.ret = B ∧ d.row = r ∧ τc.data = true

/-- A closure's code says its type. -/
theorem CloOk.det : CloOk F f τc k A B r → CloOk F f τc' k' A' B' r' →
    τc = τc' ∧ k = k' ∧ A = A' ∧ B = B' ∧ r = r' := by
  rintro ⟨d, xc, pn, hd, hcap, hown, -, -, hret, hrow, -⟩ ⟨d', xc', pn', hd', hcap', hown', -, -, hret', hrow', -⟩
  rw [hd] at hd'
  cases hd'
  rw [hcap] at hcap'
  rw [hown] at hown'
  simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hcap' hown'
  exact ⟨hcap'.2.1, hcap'.2.2, hown'.2, hret.symm.trans hret', hrow.symm.trans hrow'⟩

/-- `a` holds a value of type `τ`, whose cells — `a` and every cell of its boxes — are `L`. -/
inductive LT (F : List Fn) (σ : Store) : Nat → Ty → List Nat → Prop
  | int : σ.mem a = some (.int n) → LT F σ a .int [a]
  | box : σ.mem a = some (.ptr b) → LT F σ b τ R → a ∉ R → LT F σ a (.box τ) (a :: R)
  | clo : σ.mem a = some (.clo f c τc) → CloOk F f τc k A B r → LT F σ c τc R → a ∉ R →
      LT F σ a (.fn k A B r) (a :: R)

/-- A value of type `τ`, and the cells it owns. -/
inductive VT (F : List Fn) (σ : Store) : Ty → Val → List Nat → Prop
  | int : VT F σ .int (.int n) []
  | box : LT F σ b τ R → VT F σ (.box τ) (.ptr b) R
  | clo : CloOk F f τc k A B r → LT F σ c τc R → VT F σ (.fn k A B r) (.clo f c τc) R

def Disj (A B : List Nat) : Prop := ∀ x ∈ A, x ∉ B

/-- Every allocated cell is below `next`. -/
def WF (σ : Store) : Prop := ∀ l, σ.mem l ≠ none → l < σ.next

/-- Two stores agree on `L`. -/
def Agree (σ σ' : Store) (L : List Nat) : Prop := ∀ l ∈ L, σ'.mem l = σ.mem l

theorem Disj.symm : Disj A B → Disj B A := fun h x hb ha => h x ha hb

theorem Disj.mono_left : Disj A B → (∀ x ∈ C, x ∈ A) → Disj C B := fun h hc x hx => h x (hc x hx)

theorem Disj.mono_right : Disj A B → (∀ x ∈ C, x ∈ B) → Disj A C :=
  fun h hc x hx hcx => h x hx (hc x hcx)

theorem disj_nil_left : Disj [] B := fun _ h => by simp at h

theorem disj_nil_right : Disj A [] := fun _ _ h => by simp at h

theorem disj_append_left : Disj (A ++ B) C ↔ Disj A C ∧ Disj B C := by
  constructor
  · intro h
    exact ⟨fun x hx => h x (List.mem_append.mpr (.inl hx)), fun x hx => h x (List.mem_append.mpr (.inr hx))⟩
  · intro ⟨h1, h2⟩ x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h1 x hx
    · exact h2 x hx

theorem disj_append_right : Disj A (B ++ C) ↔ Disj A B ∧ Disj A C := by
  constructor
  · intro h
    exact ⟨fun x hx hb => h x hx (List.mem_append.mpr (.inl hb)),
      fun x hx hc => h x hx (List.mem_append.mpr (.inr hc))⟩
  · intro ⟨h1, h2⟩ x hx hbc
    rcases List.mem_append.mp hbc with hb | hc
    · exact h1 x hx hb
    · exact h2 x hx hc

theorem disj_cons_left : Disj (a :: A) B ↔ a ∉ B ∧ Disj A B := by
  constructor
  · intro h
    exact ⟨h a (List.mem_cons_self ..), fun x hx => h x (List.mem_cons_of_mem _ hx)⟩
  · intro ⟨h1, h2⟩ x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h1
    · exact h2 x hx

theorem nodup_append_disj : (A ++ B).Nodup ↔ A.Nodup ∧ B.Nodup ∧ Disj A B := by
  rw [List.nodup_append]
  constructor
  · intro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun x hx hb => h3 x hx x hb rfl⟩
  · intro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun x hx y hy hxy => h3 x hx (hxy ▸ hy)⟩

/-! ## Trees -/

theorem LT.head : LT F σ a τ L → a ∈ L := by
  intro h
  cases h <;> simp

theorem LT.cons : LT F σ a τ L → ∃ R, L = a :: R := by
  intro h
  cases h <;> exact ⟨_, rfl⟩

theorem LT.alloc : LT F σ a τ L → ∀ l ∈ L, σ.mem l ≠ none := by
  intro h
  induction h with
  | int ha => intro l hl; simp at hl; subst hl; simp [ha]
  | box ha _ _ ih | clo ha _ _ _ ih =>
    intro l hl
    rcases List.mem_cons.mp hl with rfl | hl
    · simp [ha]
    · exact ih l hl

theorem LT.nodup : LT F σ a τ L → L.Nodup := by
  intro h
  induction h with
  | int => simp
  | box _ _ hn ih | clo _ _ _ hn ih => exact List.nodup_cons.mpr ⟨hn, ih⟩

theorem LT.frame : LT F σ a τ L → Agree σ σ' L → LT F σ' a τ L := by
  intro h
  induction h with
  | int ha =>
    intro hag
    exact .int (by rw [hag _ (List.mem_singleton_self _)]; exact ha)
  | box ha _ hn ih =>
    intro hag
    refine .box (by rw [hag _ (List.mem_cons_self ..)]; exact ha) (ih fun l hl => hag l (List.mem_cons_of_mem _ hl)) hn
  | clo ha hc _ hn ih =>
    intro hag
    exact .clo (by rw [hag _ (List.mem_cons_self ..)]; exact ha) hc (ih fun l hl => hag l (List.mem_cons_of_mem _ hl)) hn

theorem LT.det : LT F σ a τ L → LT F σ a τ L' → L = L' := by
  intro h
  induction h generalizing L' with
  | int => intro h'; cases h'; rfl
  | box ha _ _ ih =>
    intro h'
    cases h' with
    | box ha' hb' _ =>
      rw [ha] at ha'
      cases ha'
      rw [ih hb']
  | clo ha _ _ _ ih =>
    intro h'
    cases h' with
    | clo ha' _ hb' _ =>
      rw [ha] at ha'
      cases ha'
      rw [ih hb']

/-- What a location holds says its type, too. -/
theorem LT.det_ty : LT F σ a τ L → LT F σ a τ' L' → τ = τ' ∧ L = L' := by
  intro h
  induction h generalizing τ' L' with
  | int ha => intro h'; cases h' with
    | int => exact ⟨rfl, rfl⟩
    | box ha' => rw [ha] at ha'; cases ha'
    | clo ha' => rw [ha] at ha'; cases ha'
  | box ha _ _ ih =>
    intro h'
    cases h' with
    | int ha' => rw [ha] at ha'; cases ha'
    | box ha' hb' _ =>
      rw [ha] at ha'
      cases ha'
      obtain ⟨rfl, rfl⟩ := ih hb'
      exact ⟨rfl, rfl⟩
    | clo ha' => rw [ha] at ha'; cases ha'
  | clo ha hc _ _ ih =>
    intro h'
    cases h' with
    | int ha' => rw [ha] at ha'; cases ha'
    | box ha' => rw [ha] at ha'; cases ha'
    | clo ha' hc' hb' _ =>
      rw [ha] at ha'
      cases ha'
      obtain ⟨-, rfl, rfl, rfl, rfl⟩ := hc.det hc'
      obtain ⟨-, rfl⟩ := ih hb'
      exact ⟨rfl, rfl⟩

theorem VT.alloc : VT F σ τ v L → ∀ l ∈ L, σ.mem l ≠ none := by
  intro h
  cases h with
  | int => simp
  | box h | clo _ h => exact h.alloc

theorem VT.nodup : VT F σ τ v L → L.Nodup := by
  intro h
  cases h with
  | int => simp
  | box h | clo _ h => exact h.nodup

theorem VT.frame : VT F σ τ v L → Agree σ σ' L → VT F σ' τ v L := by
  intro h hag
  cases h with
  | int => exact .int
  | box h => exact .box (h.frame hag)
  | clo hc h => exact .clo hc (h.frame hag)

theorem agree_set : l ∉ L → Agree σ (σ.set l v) L := by
  intro h x hx
  simp only [Store.set]
  split
  · subst_vars; exact absurd hx h
  · rfl

theorem agree_alloc (hwf : WF σ) (hL : ∀ l ∈ L, σ.mem l ≠ none) : Agree σ (σ.alloc v).2 L := by
  intro x hx
  simp only [Store.alloc]
  split
  · subst_vars; exact absurd (hwf _ (hL _ hx)) (Nat.lt_irrefl _)
  · rfl

theorem WF.set (hwf : WF σ) (hl : l < σ.next) : WF (σ.set l v) := by
  intro x hx
  simp only [Store.set] at hx ⊢
  split at hx
  · subst_vars; exact hl
  · exact hwf x hx

theorem WF.set_none (hwf : WF σ) : WF (σ.set l none) := by
  intro x hx
  simp only [Store.set] at hx ⊢
  split at hx
  · simp at hx
  · exact hwf x hx

theorem WF.alloc (hwf : WF σ) : WF (σ.alloc v).2 := by
  intro x hx
  simp only [Store.alloc] at hx ⊢
  split at hx
  · subst_vars; exact Nat.lt_succ_self _
  · exact Nat.lt_succ_of_lt (hwf x hx)

/-- What a location holds: a value of its type, owning the rest of its footprint. -/
theorem LT.contents : LT F σ b τ R → ∃ w R', σ.mem b = some w ∧ VT F σ τ w R' ∧ R = b :: R' ∧ b ∉ R' := by
  intro h
  cases h with
  | int ha => exact ⟨_, [], ha, .int, rfl, by simp⟩
  | box ha hb hn => exact ⟨_, _, ha, .box hb, rfl, hn⟩
  | clo ha hc hb hn => exact ⟨_, _, ha, .clo hc hb, rfl, hn⟩

theorem LT.of_contents : σ.mem b = some w → VT F σ τ w R' → b ∉ R' → LT F σ b τ (b :: R') := by
  intro ha hv hn
  cases hv with
  | int => exact .int ha
  | box hb => exact .box ha hb hn
  | clo hc hb => exact .clo ha hc hb hn

/-! ## Dropping -/

/-- Dropping plain data frees exactly the cells it owns. -/
theorem dropData_ok : ∀ (τ : Ty) (σ : Store) v L, VT F σ τ v L → τ.data = true →
    ∃ σ', dropData σ τ v = some σ' ∧ σ'.next = σ.next ∧ (∀ l ∈ L, σ'.mem l = none) ∧
      ∀ l, l ∉ L → σ'.mem l = σ.mem l := by
  intro τ
  induction τ with
  | int =>
    intro σ v L h _
    cases h
    exact ⟨σ, by simp [dropData], rfl, by simp, fun _ _ => rfl⟩
  | box τ ih =>
    intro σ v L h hd
    cases h with
    | @box b _ _ hb =>
      obtain ⟨w, R', hw, hv, rfl, hn⟩ := hb.contents
      obtain ⟨σ1, hdr, hnext, hfree, hkeep⟩ := ih σ w R' hv (by simpa [Ty.data] using hd)
      refine ⟨σ1.set b none, by simp [dropData, hw, hdr], by simp [Store.set, hnext], ?_, ?_⟩
      · intro l hl
        simp only [Store.set]
        split
        · rfl
        · rcases List.mem_cons.mp hl with rfl | hl
          · contradiction
          · exact hfree l hl
      · intro l hl
        simp only [Store.set]
        split
        · subst_vars; simp at hl
        · exact hkeep l (fun h => hl (List.mem_cons_of_mem _ h))
  | fn => intro _ _ _ _ hd; simp [Ty.data] at hd

/-- Dropping a value frees exactly the cells it owns. -/
theorem drop_ok : ∀ (τ : Ty) (σ : Store) v L, VT F σ τ v L →
    ∃ σ', drop σ τ v = some σ' ∧ σ'.next = σ.next ∧ (∀ l ∈ L, σ'.mem l = none) ∧
      ∀ l, l ∉ L → σ'.mem l = σ.mem l := by
  intro τ
  induction τ with
  | int =>
    intro σ v L h
    cases h
    exact ⟨σ, by simp [drop], rfl, by simp, fun _ _ => rfl⟩
  | box τ ih =>
    intro σ v L h
    cases h with
    | @box b _ _ hb =>
      obtain ⟨w, R', hw, hv, rfl, hn⟩ := hb.contents
      obtain ⟨σ1, hd, hnext, hfree, hkeep⟩ := ih σ w R' hv
      refine ⟨σ1.set b none, by simp [drop, hw, hd], by simp [Store.set, hnext], ?_, ?_⟩
      · intro l hl
        simp only [Store.set]
        split
        · rfl
        · rcases List.mem_cons.mp hl with rfl | hl
          · contradiction
          · exact hfree l hl
      · intro l hl
        simp only [Store.set]
        split
        · subst_vars; simp at hl
        · exact hkeep l (fun h => hl (List.mem_cons_of_mem _ h))
  | fn =>
    intro σ v L h
    cases h with
    | @clo f τc _ _ _ _ c _ hc hb =>
      obtain ⟨w, R', hw, hv, rfl, hn⟩ := hb.contents
      obtain ⟨-, -, -, -, -, -, -, -, -, -, hdat⟩ := hc
      obtain ⟨σ1, hdr, hnext, hfree, hkeep⟩ := dropData_ok τc σ w R' hv hdat
      refine ⟨σ1.set c none, by simp [drop, hw, hdr], by simp [Store.set, hnext], ?_, ?_⟩
      · intro l hl
        simp only [Store.set]
        split
        · rfl
        · rcases List.mem_cons.mp hl with rfl | hl
          · contradiction
          · exact hfree l hl
      · intro l hl
        simp only [Store.set]
        split
        · subst_vars; simp at hl
        · exact hkeep l (fun h => hl (List.mem_cons_of_mem _ h))

/-- Dropping a variable's cell frees its footprint: the cell, and what a live value in it owns. -/
theorem dropCell_live : LT F σ c τ L →
    ∃ σ', dropCell σ τ c = some σ' ∧ σ'.next = σ.next ∧ (∀ l ∈ L, σ'.mem l = none) ∧
      ∀ l, l ∉ L → σ'.mem l = σ.mem l := by
  intro h
  obtain ⟨w, R', hw, hv, rfl, hn⟩ := h.contents
  obtain ⟨σ1, hd, hnext, hfree, hkeep⟩ := drop_ok τ σ w R' hv
  refine ⟨σ1.set c none, ?_, by simp [Store.set, hnext], ?_, ?_⟩
  · cases hv <;> simp [dropCell, hw, hd]
  · intro l hl
    simp only [Store.set]
    split
    · rfl
    · rcases List.mem_cons.mp hl with rfl | hl
      · contradiction
      · exact hfree l hl
  · intro l hl
    simp only [Store.set]
    split
    · subst_vars; simp at hl
    · exact hkeep l (fun h => hl (List.mem_cons_of_mem _ h))

theorem dropCell_moved : σ.mem c = some .moved →
    ∃ σ', dropCell σ τ c = some σ' ∧ σ'.next = σ.next ∧ σ'.mem c = none ∧
      ∀ l, l ≠ c → σ'.mem l = σ.mem l := by
  intro h
  refine ⟨σ.set c none, by simp [dropCell, h], rfl, by simp [Store.set], ?_⟩
  intro l hl
  simp [Store.set, hl]

/-! ## Paths: how a place reaches into a variable's tree -/

/-- Following boxes from `a`, which holds a `τa`, reaches `l`, which holds a `τ`; `P` are the cells
passed on the way. -/
inductive Path (σ : Store) : Nat → Ty → List Nat → Nat → Ty → Prop
  | here : Path σ a τ [] a τ
  | step : σ.mem a = some (.ptr b) → Path σ b τ' P l τ → Path σ a (.box τ') (a :: P) l τ
  | clo : σ.mem a = some (.clo f c τc) → Path σ c τc P l τ → Path σ a (.fn k A B r) (a :: P) l τ

theorem Path.snoc' : Path σ a τa P l τl → τl = .box τ → σ.mem l = some (.ptr b) →
    Path σ a τa (P ++ [l]) b τ := by
  intro h
  induction h with
  | here => intro he hl; subst he; exact .step hl .here
  | step ha _ ih => intro he hl; exact .step ha (ih he hl)
  | clo ha _ ih => intro he hl; exact .clo ha (ih he hl)

theorem Path.snoc : Path σ a τa P l (.box τ) → σ.mem l = some (.ptr b) → Path σ a τa (P ++ [l]) b τ :=
  fun h => h.snoc' rfl

/-- Two paths, the second from where the first ends, are one. -/
theorem Path.trans : Path σ a τa P l τl → Path σ l τl P' b τ → Path σ a τa (P ++ P') b τ := by
  intro h h'
  induction h with
  | here => exact h'
  | step ha _ ih => exact .step ha (ih h')
  | clo ha _ ih => exact .clo ha (ih h')

/-- A path stays where its cells do. -/
theorem Path.frame : Path σ a τa P l τ → Agree σ σ' P → Path σ' a τa P l τ := by
  intro h hag
  induction h with
  | here => exact .here
  | step ha _ ih =>
    exact .step (by rw [hag _ (List.mem_cons_self ..)]; exact ha)
      (ih fun x hx => hag x (List.mem_cons_of_mem _ hx))
  | clo ha _ ih =>
    exact .clo (by rw [hag _ (List.mem_cons_self ..)]; exact ha)
      (ih fun x hx => hag x (List.mem_cons_of_mem _ hx))

/-- A tree is the cells on a path into it, then the tree where the path ends. -/
theorem path_split : Path σ a τa P l τ → LT F σ a τa L → ∃ R, LT F σ l τ R ∧ L = P ++ R := by
  intro hp
  induction hp generalizing L with
  | here => intro h; exact ⟨L, h, rfl⟩
  | step ha _ ih =>
    intro h
    cases h with
    | box ha' hb hn =>
      rw [ha] at ha'
      cases ha'
      obtain ⟨R, hR, rfl⟩ := ih hb
      exact ⟨R, hR, rfl⟩
  | clo ha _ ih =>
    intro h
    cases h with
    | clo ha' _ hb hn =>
      rw [ha] at ha'
      cases ha'
      obtain ⟨R, hR, rfl⟩ := ih hb
      exact ⟨R, hR, rfl⟩

/-- Replacing the tree where a path ends keeps a tree: the cells on the way are unchanged, and the
new tree shares none of them. -/
theorem path_join : Path σ a τa P l τ → LT F σ a τa (P ++ R) → Agree σ σ' P → LT F σ' l τ R' →
    Disj P R' → LT F σ' a τa (P ++ R') ∧ Path σ' a τa P l τ := by
  intro hp
  induction hp with
  | here => intro _ _ h _; exact ⟨h, .here⟩
  | step ha _ ih =>
    intro h hag h' hd
    cases h with
    | box ha' hb hn =>
      rw [ha] at ha'
      cases ha'
      have hag' : Agree σ σ' _ := fun x hx => hag x (List.mem_cons_of_mem _ hx)
      have hd' := (disj_cons_left.mp hd).2
      obtain ⟨hlt, hpath⟩ := ih hb hag' h' hd'
      have hnP : _ ∉ _ := fun hx => hn (List.mem_append.mpr (.inl hx))
      have hnR := (disj_cons_left.mp hd).1
      refine ⟨.box (by rw [hag _ (List.mem_cons_self ..)]; exact ha) hlt ?_, .step (by rw [hag _ (List.mem_cons_self ..)]; exact ha) hpath⟩
      intro hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hnP hx
      · exact hnR hx
  | clo ha _ ih =>
    intro h hag h' hd
    cases h with
    | clo ha' hc hb hn =>
      rw [ha] at ha'
      cases ha'
      have hag' : Agree σ σ' _ := fun x hx => hag x (List.mem_cons_of_mem _ hx)
      have hd' := (disj_cons_left.mp hd).2
      obtain ⟨hlt, hpath⟩ := ih hb hag' h' hd'
      have hnP : _ ∉ _ := fun hx => hn (List.mem_append.mpr (.inl hx))
      have hnR := (disj_cons_left.mp hd).1
      refine ⟨.clo (by rw [hag _ (List.mem_cons_self ..)]; exact ha) hc hlt ?_, .clo (by rw [hag _ (List.mem_cons_self ..)]; exact ha) hpath⟩
      intro hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hnP hx
      · exact hnR hx

/-! ## The variables of an activation -/

/-- A slot whose footprint is exclusive: an owned variable or a `mut` borrow. -/
def Slot.excl : Slot → Bool
  | .own _ _ => true
  | .ref .mut _ => true
  | .ref .ro _ => false
  | .lent _ => false

/-- The footprint a slot has: what an owned live variable or a borrow holds, owning the rest. A
variable perhaps moved holds the mark a move leaves, its footprint its cell alone, or still its
value: which, only running the program tells, and dropping it at the end of its scope looks. -/
def SlotOk (F : List Fn) (σ : Store) : Slot → Nat → List Nat → Prop
  | .own τ true, a, L => LT F σ a τ L
  | .own τ false, a, L => (σ.mem a = some .moved ∧ L = [a]) ∨ LT F σ a τ L
  | .ref _ τ, a, L => LT F σ a τ L
  | .lent _, _, L => L = []

/-- The part of a slot's footprint that may be changed, and the part that is only read: a `mut`
borrow of a closure only reads the closure's cell, the head of its footprint. -/
def exclPart (s : Slot) (L : List Nat) : List Nat := if s.excl then (if s.shell then L.tail else L) else []
def sharedPart (s : Slot) (L : List Nat) : List Nat := if s.excl then (if s.shell then L.take 1 else []) else L

/-- Adds a footprint to the exclusive ones and to the shared ones, as the slot says. -/
def addE (s : Slot) (L E : List Nat) : List Nat := exclPart s L ++ E
def addS (s : Slot) (L S : List Nat) : List Nat := sharedPart s L ++ S

/-- The footprints of an activation's variables, in order: of those that may be changed — owned
variables and `mut` borrows — and of those that may only be read, `readonly` borrows. -/
inductive Foot (F : List Fn) (σ : Store) : Ctx → Env → List Nat → List Nat → Prop
  | nil : Foot F σ [] [] [] []
  | cons : SlotOk F σ s a L → Foot F σ Γ env E S →
      Foot F σ ((x, s) :: Γ) ((x, a) :: env) (addE s L E) (addS s L S)

/-- The invariant of an activation: its variables' footprints, those that may be changed disjoint
from each other and from those that may be read. -/
structure Inv (F : List Fn) (σ : Store) (Γ : Ctx) (env : Env) (E S : List Nat) : Prop where
  foot : Foot F σ Γ env E S
  nodup : E.Nodup
  disj : Disj S E
  keys : (Γ.map Prod.fst).Nodup

theorem LT.not_moved : LT F σ a τ L → σ.mem a ≠ some .moved := by
  intro h
  cases h <;> simp_all

theorem SlotOk.alloc : SlotOk F σ s a L → ∀ l ∈ L, σ.mem l ≠ none := by
  intro h
  rcases s with ⟨τ, live⟩ | ⟨m, τ⟩ | τ
  · cases live
    · rcases h with ⟨ha, rfl⟩ | h
      · intro l hl; simp at hl; subst hl; simp [ha]
      · exact LT.alloc h
    · exact LT.alloc h
  · exact LT.alloc h
  · simp only [SlotOk] at h; subst h; simp

theorem SlotOk.frame : SlotOk F σ s a L → Agree σ σ' L → SlotOk F σ' s a L := by
  intro h hag
  rcases s with ⟨τ, live⟩ | ⟨m, τ⟩ | τ
  · cases live
    · rcases h with ⟨ha, rfl⟩ | h
      · exact .inl ⟨by rw [hag _ (by simp)]; exact ha, rfl⟩
      · exact .inr (LT.frame h hag)
    · exact LT.frame h hag
  · exact LT.frame h hag
  · exact h

theorem SlotOk.nodup : SlotOk F σ s a L → L.Nodup := by
  intro h
  rcases s with ⟨τ, live⟩ | ⟨m, τ⟩ | τ
  · cases live
    · rcases h with ⟨_, rfl⟩ | h
      · simp
      · exact LT.nodup h
    · exact LT.nodup h
  · exact LT.nodup h
  · simp only [SlotOk] at h; subst h; simp

theorem SlotOk.det : SlotOk F σ s a L → SlotOk F σ s a L' → L = L' := by
  intro h h'
  rcases s with ⟨τ, live⟩ | ⟨m, τ⟩ | τ
  · cases live
    · rcases h with ⟨ha, rfl⟩ | h <;> rcases h' with ⟨ha', rfl⟩ | h'
      · rfl
      · exact absurd ha h'.not_moved
      · exact absurd ha' h.not_moved
      · exact LT.det h h'
    · exact LT.det h h'
  · exact LT.det h h'
  · simp only [SlotOk] at h h'; rw [h, h']

theorem mem_addE : l ∈ addE s L E ↔ l ∈ exclPart s L ∨ l ∈ E := by
  simp [addE]

theorem mem_addS : l ∈ addS s L S ↔ l ∈ sharedPart s L ∨ l ∈ S := by
  simp [addS]

theorem exclPart_sub : l ∈ exclPart s L → l ∈ L := by
  unfold exclPart; split
  · split
    · exact List.mem_of_mem_tail
    · exact id
  · simp

theorem sharedPart_sub : l ∈ sharedPart s L → l ∈ L := by
  unfold sharedPart; split
  · split
    · exact List.mem_of_mem_take
    · simp
  · exact id

/-- Every cell of a footprint is in one part or the other. -/
theorem mem_parts : l ∈ L → l ∈ exclPart s L ∨ l ∈ sharedPart s L := by
  intro h
  unfold exclPart sharedPart
  split
  · split
    · cases L with
      | nil => simp at h
      | cons a L => rcases List.mem_cons.mp h with rfl | h <;> simp_all
    · exact .inl h
  · exact .inr h

theorem parts_perm {L : List Nat} {s : Slot} : L.Perm (exclPart s L ++ sharedPart s L) := by
  unfold exclPart sharedPart
  split
  · split
    · cases L with
      | nil => simp
      | cons a L => simpa using (List.perm_append_singleton a L).symm
    · simp
  · simp

/-- A slot that is not a closure borrowed `mut`: all of its footprint changeable, or all only read. -/
theorem exclPart_plain (hs : s.shell = false) : exclPart s L = if s.excl then L else [] := by
  simp [exclPart, hs]

theorem sharedPart_plain (hs : s.shell = false) : sharedPart s L = if s.excl then [] else L := by
  simp [sharedPart, hs]

theorem Slot.shell_ref : (Slot.ref m τ).shell = (m == .mut && τ.isFn) := by
  cases m <;> cases τ <;> rfl

theorem Slot.shell_own : (Slot.own τ l).shell = false := rfl

theorem Slot.shell_lent : (Slot.lent τ).shell = false := rfl

theorem Slot.shell_excl {s : Slot} : s.shell = true → s.excl = true := by
  intro h; match s, h with
  | .ref .mut (.fn _ _ _ _), _ => rfl

/-- A footprint without duplicates splits into disjoint parts. -/
theorem parts_disj : L.Nodup → Disj (exclPart s L) (sharedPart s L) := by
  intro hn x hx hy
  unfold exclPart at hx; unfold sharedPart at hy
  by_cases he : s.excl = true <;> by_cases hs : s.shell = true <;> simp only [he, hs, ↓reduceIte] at hx hy
  · cases L with
    | nil => simp at hx
    | cons a L =>
      simp only [List.tail_cons, List.take_succ_cons, List.take_zero, List.mem_singleton] at hx hy
      subst hy
      exact (List.nodup_cons.mp hn).1 hx
  all_goals simp_all

theorem parts_nodup : L.Nodup → (exclPart s L).Nodup ∧ (sharedPart s L).Nodup := by
  intro hn
  unfold exclPart sharedPart
  split
  · split
    · exact ⟨hn.sublist (List.tail_sublist _), hn.sublist (List.take_sublist _ _)⟩
    · exact ⟨hn, by simp⟩
  · exact ⟨by simp, hn⟩

theorem Foot.alloc : Foot F σ Γ env E S → ∀ l, l ∈ E ∨ l ∈ S → σ.mem l ≠ none := by
  intro h
  induction h with
  | nil => intro l h; simp at h
  | cons hs _ ih =>
    intro l hl
    rcases hl with hl | hl
    · rcases mem_addE.mp hl with hl | hl
      · exact hs.alloc l (exclPart_sub hl)
      · exact ih l (.inl hl)
    · rcases mem_addS.mp hl with hl | hl
      · exact hs.alloc l (sharedPart_sub hl)
      · exact ih l (.inr hl)

theorem Foot.frame : Foot F σ Γ env E S → Agree σ σ' (E ++ S) → Foot F σ' Γ env E S := by
  intro h
  induction h with
  | nil => intro _; exact .nil
  | @cons s a L Γ env E S x hs _ ih =>
    intro hag
    have hL : Agree σ σ' L := by
      intro l hl
      apply hag l
      rcases mem_parts (s := s) hl with h | h
      · exact List.mem_append.mpr (.inl (mem_addE.mpr (.inl h)))
      · exact List.mem_append.mpr (.inr (mem_addS.mpr (.inl h)))
    exact .cons (hs.frame hL) (ih fun l hl => hag l (by
      rcases List.mem_append.mp hl with hl | hl
      · exact List.mem_append.mpr (.inl (mem_addE.mpr (.inr hl)))
      · exact List.mem_append.mpr (.inr (mem_addS.mpr (.inr hl)))))

end FlyCore.Ownership
