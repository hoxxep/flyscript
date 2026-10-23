import FlyCore.Ownership

/-!
# Ownership: the shape of the store

What a well-typed program keeps true of the store: each location a variable stands for holds a
value of the variable's type, and the cells that value owns — the location itself and the cells of
its boxes — form a tree, its footprint. Footprints of what may be changed are disjoint; footprints
of what is only read may overlap each other, but nothing that may be changed.
-/

namespace FlyCore.Ownership

/-- `a` holds a value of type `τ`, whose cells — `a` and every cell of its boxes — are `L`. -/
inductive LT (σ : Store) : Nat → Ty → List Nat → Prop
  | int : σ.mem a = some (.int n) → LT σ a .int [a]
  | box : σ.mem a = some (.ptr b) → LT σ b τ R → a ∉ R → LT σ a (.box τ) (a :: R)

/-- A value of type `τ`, and the cells it owns. -/
inductive VT (σ : Store) : Ty → Val → List Nat → Prop
  | int : VT σ .int (.int n) []
  | box : LT σ b τ R → VT σ (.box τ) (.ptr b) R

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

theorem LT.head : LT σ a τ L → a ∈ L := by
  intro h
  cases h <;> simp

theorem LT.alloc : LT σ a τ L → ∀ l ∈ L, σ.mem l ≠ none := by
  intro h
  induction h with
  | int ha => intro l hl; simp at hl; subst hl; simp [ha]
  | box ha _ _ ih =>
    intro l hl
    rcases List.mem_cons.mp hl with rfl | hl
    · simp [ha]
    · exact ih l hl

theorem LT.nodup : LT σ a τ L → L.Nodup := by
  intro h
  induction h with
  | int => simp
  | box _ _ hn ih => exact List.nodup_cons.mpr ⟨hn, ih⟩

theorem LT.frame : LT σ a τ L → Agree σ σ' L → LT σ' a τ L := by
  intro h
  induction h with
  | int ha =>
    intro hag
    exact .int (by rw [hag _ (List.mem_singleton_self _)]; exact ha)
  | box ha _ hn ih =>
    intro hag
    refine .box (by rw [hag _ (List.mem_cons_self ..)]; exact ha) (ih fun l hl => hag l (List.mem_cons_of_mem _ hl)) hn

theorem LT.det : LT σ a τ L → LT σ a τ L' → L = L' := by
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

/-- What a location holds says its type, too. -/
theorem LT.det_ty : LT σ a τ L → LT σ a τ' L' → τ = τ' ∧ L = L' := by
  intro h
  induction h generalizing τ' L' with
  | int ha => intro h'; cases h' with
    | int => exact ⟨rfl, rfl⟩
    | box ha' => rw [ha] at ha'; cases ha'
  | box ha _ _ ih =>
    intro h'
    cases h' with
    | int ha' => rw [ha] at ha'; cases ha'
    | box ha' hb' _ =>
      rw [ha] at ha'
      cases ha'
      obtain ⟨rfl, rfl⟩ := ih hb'
      exact ⟨rfl, rfl⟩

theorem VT.alloc : VT σ τ v L → ∀ l ∈ L, σ.mem l ≠ none := by
  intro h
  cases h with
  | int => simp
  | box h => exact h.alloc

theorem VT.nodup : VT σ τ v L → L.Nodup := by
  intro h
  cases h with
  | int => simp
  | box h => exact h.nodup

theorem VT.frame : VT σ τ v L → Agree σ σ' L → VT σ' τ v L := by
  intro h hag
  cases h with
  | int => exact .int
  | box h => exact .box (h.frame hag)

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
theorem LT.contents : LT σ b τ R → ∃ w R', σ.mem b = some w ∧ VT σ τ w R' ∧ R = b :: R' ∧ b ∉ R' := by
  intro h
  cases h with
  | int ha => exact ⟨_, [], ha, .int, rfl, by simp⟩
  | box ha hb hn => exact ⟨_, _, ha, .box hb, rfl, hn⟩

theorem LT.of_contents : σ.mem b = some w → VT σ τ w R' → b ∉ R' → LT σ b τ (b :: R') := by
  intro ha hv hn
  cases hv with
  | int => exact .int ha
  | box hb => exact .box ha hb hn

/-! ## Dropping -/

/-- Dropping a value frees exactly the cells it owns. -/
theorem drop_ok : ∀ (τ : Ty) (σ : Store) v L, VT σ τ v L →
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

/-- Dropping a variable's cell frees its footprint: the cell, and what a live value in it owns. -/
theorem dropCell_live : LT σ c τ L →
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

theorem Path.snoc' : Path σ a τa P l τl → τl = .box τ → σ.mem l = some (.ptr b) →
    Path σ a τa (P ++ [l]) b τ := by
  intro h
  induction h with
  | here => intro he hl; subst he; exact .step hl .here
  | step ha _ ih => intro he hl; exact .step ha (ih he hl)

theorem Path.snoc : Path σ a τa P l (.box τ) → σ.mem l = some (.ptr b) → Path σ a τa (P ++ [l]) b τ :=
  fun h => h.snoc' rfl

/-- Two paths, the second from where the first ends, are one. -/
theorem Path.trans : Path σ a τa P l τl → Path σ l τl P' b τ → Path σ a τa (P ++ P') b τ := by
  intro h h'
  induction h with
  | here => exact h'
  | step ha _ ih => exact .step ha (ih h')

/-- A path stays where its cells do. -/
theorem Path.frame : Path σ a τa P l τ → Agree σ σ' P → Path σ' a τa P l τ := by
  intro h hag
  induction h with
  | here => exact .here
  | step ha _ ih =>
    exact .step (by rw [hag _ (List.mem_cons_self ..)]; exact ha)
      (ih fun x hx => hag x (List.mem_cons_of_mem _ hx))

/-- A tree is the cells on a path into it, then the tree where the path ends. -/
theorem path_split : Path σ a τa P l τ → LT σ a τa L → ∃ R, LT σ l τ R ∧ L = P ++ R := by
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

/-- Replacing the tree where a path ends keeps a tree: the cells on the way are unchanged, and the
new tree shares none of them. -/
theorem path_join : Path σ a τa P l τ → LT σ a τa (P ++ R) → Agree σ σ' P → LT σ' l τ R' →
    Disj P R' → LT σ' a τa (P ++ R') ∧ Path σ' a τa P l τ := by
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
def SlotOk (σ : Store) : Slot → Nat → List Nat → Prop
  | .own τ true, a, L => LT σ a τ L
  | .own τ false, a, L => (σ.mem a = some .moved ∧ L = [a]) ∨ LT σ a τ L
  | .ref _ τ, a, L => LT σ a τ L
  | .lent _, _, L => L = []

/-- Adds a footprint to the exclusive ones or to the shared ones, as the slot says. -/
def addE (s : Slot) (L E : List Nat) : List Nat := if s.excl then L ++ E else E
def addS (s : Slot) (L S : List Nat) : List Nat := if s.excl then S else L ++ S

/-- The footprints of an activation's variables, in order: of those that may be changed — owned
variables and `mut` borrows — and of those that may only be read, `readonly` borrows. -/
inductive Foot (σ : Store) : Ctx → Env → List Nat → List Nat → Prop
  | nil : Foot σ [] [] [] []
  | cons : SlotOk σ s a L → Foot σ Γ env E S →
      Foot σ ((x, s) :: Γ) ((x, a) :: env) (addE s L E) (addS s L S)

/-- The invariant of an activation: its variables' footprints, those that may be changed disjoint
from each other and from those that may be read. -/
structure Inv (σ : Store) (Γ : Ctx) (env : Env) (E S : List Nat) : Prop where
  foot : Foot σ Γ env E S
  nodup : E.Nodup
  disj : Disj S E
  keys : (Γ.map Prod.fst).Nodup

theorem LT.not_moved : LT σ a τ L → σ.mem a ≠ some .moved := by
  intro h
  cases h <;> simp_all

theorem SlotOk.alloc : SlotOk σ s a L → ∀ l ∈ L, σ.mem l ≠ none := by
  intro h
  rcases s with ⟨τ, live⟩ | ⟨m, τ⟩ | τ
  · cases live
    · rcases h with ⟨ha, rfl⟩ | h
      · intro l hl; simp at hl; subst hl; simp [ha]
      · exact LT.alloc h
    · exact LT.alloc h
  · exact LT.alloc h
  · simp only [SlotOk] at h; subst h; simp

theorem SlotOk.frame : SlotOk σ s a L → Agree σ σ' L → SlotOk σ' s a L := by
  intro h hag
  rcases s with ⟨τ, live⟩ | ⟨m, τ⟩ | τ
  · cases live
    · rcases h with ⟨ha, rfl⟩ | h
      · exact .inl ⟨by rw [hag _ (by simp)]; exact ha, rfl⟩
      · exact .inr (LT.frame h hag)
    · exact LT.frame h hag
  · exact LT.frame h hag
  · exact h

theorem SlotOk.nodup : SlotOk σ s a L → L.Nodup := by
  intro h
  rcases s with ⟨τ, live⟩ | ⟨m, τ⟩ | τ
  · cases live
    · rcases h with ⟨_, rfl⟩ | h
      · simp
      · exact LT.nodup h
    · exact LT.nodup h
  · exact LT.nodup h
  · simp only [SlotOk] at h; subst h; simp

theorem SlotOk.det : SlotOk σ s a L → SlotOk σ s a L' → L = L' := by
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

theorem mem_addE : l ∈ addE s L E ↔ (s.excl ∧ l ∈ L) ∨ l ∈ E := by
  unfold addE; split <;> simp_all

theorem mem_addS : l ∈ addS s L S ↔ (s.excl = false ∧ l ∈ L) ∨ l ∈ S := by
  unfold addS; split <;> simp_all

theorem Foot.alloc : Foot σ Γ env E S → ∀ l, l ∈ E ∨ l ∈ S → σ.mem l ≠ none := by
  intro h
  induction h with
  | nil => intro l h; simp at h
  | cons hs _ ih =>
    intro l hl
    rcases hl with hl | hl
    · rcases mem_addE.mp hl with ⟨_, hl⟩ | hl
      · exact hs.alloc l hl
      · exact ih l (.inl hl)
    · rcases mem_addS.mp hl with ⟨_, hl⟩ | hl
      · exact hs.alloc l hl
      · exact ih l (.inr hl)

theorem Foot.frame : Foot σ Γ env E S → Agree σ σ' (E ++ S) → Foot σ' Γ env E S := by
  intro h
  induction h with
  | nil => intro _; exact .nil
  | @cons s a L Γ env E S x hs _ ih =>
    intro hag
    have hL : Agree σ σ' L := by
      intro l hl
      apply hag l
      cases he : s.excl
      · exact List.mem_append.mpr (.inr (mem_addS.mpr (.inl ⟨he, hl⟩)))
      · exact List.mem_append.mpr (.inl (mem_addE.mpr (.inl ⟨he, hl⟩)))
    exact .cons (hs.frame hL) (ih fun l hl => hag l (by
      rcases List.mem_append.mp hl with hl | hl
      · exact List.mem_append.mpr (.inl (mem_addE.mpr (.inr hl)))
      · exact List.mem_append.mpr (.inr (mem_addS.mpr (.inr hl)))))

end FlyCore.Ownership
