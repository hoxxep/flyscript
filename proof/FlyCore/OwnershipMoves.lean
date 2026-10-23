import FlyCore.OwnershipPlaces

/-!
# Ownership: what a step may do to the store

`Moves σ E σ' E' L`: going from `σ` to `σ'`, an activation whose exclusive footprint was `E` and is
now `E'` changed nothing outside `E`, took every new cell from above `σ.next`, and left allocated
exactly what was allocated outside `E`, its new footprint, and `L`: the cells of the value it
gives. Steps compose; at the top, with no variables, it says that nothing is left allocated but the
result.
-/

namespace FlyCore.Ownership

/-- Proves `x ∈ … ↔ x ∈ …` between lists built by `++`, `::` and `[a]`, where both sides name the
same cells: each side is a disjunction of the same atoms. -/
macro "mem_iff" : tactic => `(tactic| (
  simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
    false_or, or_assoc] <;>
  constructor <;> intro h <;> (repeat' (refine Or.elim h (fun h => ?_) (fun h => ?_))) <;> simp [h]))

structure Moves (σ : Store) (E : List Nat) (σ' : Store) (E' L : List Nat) : Prop where
  within : ∀ l, l ∈ L ∨ l ∈ E' → l ∈ E ∨ σ.next ≤ l
  next : σ.next ≤ σ'.next
  wf : WF σ'
  frame : ∀ l, l < σ.next → l ∉ E → σ'.mem l = σ.mem l
  alloc : ∀ l, σ'.mem l ≠ none ↔ (σ.mem l ≠ none ∧ l ∉ E) ∨ l ∈ E' ∨ l ∈ L
  rt : RtExt σ σ'
  /-- A region gains cells only through an arena the step may change, or one it made. -/
  fresh : ∀ l a x, σ'.rt l = some (a, x) → σ.rt l = none → a ∈ E ∨ σ.next ≤ a

theorem Moves.refl (hwf : WF σ) (hE : ∀ l ∈ E, σ.mem l ≠ none) : Moves σ E σ E [] where
  rt := RtExt.refl
  fresh := fun _ _ _ h h0 => by rw [h0] at h; cases h
  within := by intro l h; simp at h; exact .inl h
  next := Nat.le_refl _
  wf := hwf
  frame := fun _ _ _ => rfl
  alloc := by
    intro l
    constructor
    · intro h
      by_cases hl : l ∈ E
      · exact .inr (.inl hl)
      · exact .inl ⟨h, hl⟩
    · intro h
      rcases h with ⟨h, _⟩ | h | h
      · exact h
      · exact hE l h
      · simp at h

/-- Two steps, the first giving cells `L₁` that the second, which cannot reach them, leaves alone.
-/
theorem Moves.trans (h₁ : Moves σ E σ₁ E₁ L₁) (h₂ : Moves σ₁ E₁ σ₂ E₂ L₂) (hd : Disj L₁ E₁)
    (hwf : WF σ) : Moves σ E σ₂ E₂ (L₁ ++ L₂) where
  rt := h₁.rt.trans h₂.rt
  fresh := by
    intro l a x h h0
    cases h1 : σ₁.rt l with
    | none =>
      rcases h₂.fresh l a x h h1 with ha | ha
      · rcases h₁.within a (.inr ha) with h' | h'
        · exact .inl h'
        · exact .inr h'
      · exact .inr (Nat.le_trans h₁.next ha)
    | some y =>
      have := h₂.rt l y h1
      rw [h] at this
      cases this
      exact h₁.fresh l a x h1 h0
  within := by
    intro l h
    rcases h with h | h
    · rcases List.mem_append.mp h with h | h
      · exact h₁.within l (.inl h)
      · rcases h₂.within l (.inl h) with h | h
        · exact h₁.within l (.inr h)
        · exact .inr (Nat.le_trans h₁.next h)
    · rcases h₂.within l (.inr h) with h | h
      · exact h₁.within l (.inr h)
      · exact .inr (Nat.le_trans h₁.next h)
  next := Nat.le_trans h₁.next h₂.next
  wf := h₂.wf
  frame := by
    intro l hl hE
    have hE₁ : l ∉ E₁ := by
      intro h
      rcases h₁.within l (.inr h) with h | h
      · exact hE h
      · exact absurd hl (Nat.not_lt.mpr h)
    rw [h₂.frame l (Nat.lt_of_lt_of_le hl h₁.next) hE₁, h₁.frame l hl hE]
  alloc := by
    intro l
    rw [h₂.alloc, h₁.alloc]
    constructor
    · intro h
      rcases h with ⟨h, hE₁⟩ | h | h
      · rcases h with ⟨h, hE⟩ | h | h
        · exact .inl ⟨h, hE⟩
        · exact absurd h hE₁
        · exact .inr (.inr (List.mem_append.mpr (.inl h)))
      · exact .inr (.inl h)
      · exact .inr (.inr (List.mem_append.mpr (.inr h)))
    · intro h
      rcases h with ⟨h, hE⟩ | h | h
      · refine .inl ⟨.inl ⟨h, hE⟩, fun hE₁ => ?_⟩
        rcases h₁.within l (.inr hE₁) with h' | h'
        · exact hE h'
        · exact absurd (hwf l h) (Nat.not_lt.mpr h')
      · exact .inr (.inl h)
      · rcases List.mem_append.mp h with h | h
        · exact .inl ⟨.inr (.inr h), hd l h⟩
        · exact .inr (.inr h)

/-- Allocating a cell: new, and given as the value's. -/
theorem Moves.allocate (hwf : WF σ) (hE : ∀ l ∈ E, σ.mem l ≠ none) :
    Moves σ E (σ.alloc v).2 E [σ.next] where
  rt := fun _ _ h => h
  fresh := fun _ _ _ h h0 => by simp only [Store.alloc_rt] at h; rw [h0] at h; cases h
  within := by
    intro l h
    rcases h with h | h
    · simp at h; exact .inr (Nat.le_of_eq h.symm)
    · exact .inl h
  next := Nat.le_succ _
  wf := hwf.alloc
  frame := by
    intro l hl _
    simp [Store.alloc, Nat.ne_of_lt hl]
  alloc := by
    intro l
    simp only [Store.alloc, List.mem_singleton]
    constructor
    · intro h
      split at h
      · exact .inr (.inr (by assumption))
      · by_cases hl : l ∈ E
        · exact .inr (.inl hl)
        · exact .inl ⟨h, hl⟩
    · intro h
      split
      · simp
      · rcases h with ⟨h, _⟩ | h | h
        · exact h
        · exact hE l h
        · contradiction

/-- Changing what a cell of the footprint holds, to something. -/
theorem Moves.set (hwf : WF σ) (hE : ∀ l ∈ E, σ.mem l ≠ none) (hl : l ∈ E) :
    Moves σ E (σ.set l (some v)) E [] where
  rt := fun _ _ h => h
  fresh := fun _ _ _ h h0 => by simp only [Store.set_rt] at h; rw [h0] at h; cases h
  within := by intro x h; simp at h; exact .inl h
  next := Nat.le_refl _
  wf := hwf.set (hwf l (hE l hl))
  frame := by
    intro x _ hx
    have hne : x ≠ l := fun h => hx (h ▸ hl)
    simp [Store.set, hne]
  alloc := by
    intro x
    simp only [Store.set]
    constructor
    · intro h
      by_cases hx : x ∈ E
      · exact .inr (.inl hx)
      · refine .inl ⟨?_, hx⟩
        split at h
        · subst_vars; exact absurd hl hx
        · exact h
    · intro h
      split
      · simp
      · rcases h with ⟨h, _⟩ | h | h
        · exact h
        · exact hE x h
        · simp at h

/-- Freeing cells `D` of the footprint, which is then `E'`. -/
theorem Moves.free (hwf : WF σ') (hnext : σ'.next = σ.next) (hE : ∀ l ∈ E, σ.mem l ≠ none)
    (hsplit : ∀ l, l ∈ E ↔ l ∈ E' ∨ l ∈ D) (hD : ∀ l ∈ D, σ'.mem l = none)
    (hkeep : ∀ l, l ∉ D → σ'.mem l = σ.mem l) (hdisj : Disj E' D)
    (hrt : σ'.rt = σ.rt := by rt_tac) :
    Moves σ E σ' E' [] where
  rt := fun l x h => by rw [hrt]; exact h
  fresh := fun _ _ _ h h0 => by rw [hrt, h0] at h; cases h
  within := by
    intro l h
    simp at h
    exact .inl ((hsplit l).mpr (.inl h))
  next := Nat.le_of_eq hnext.symm
  wf := hwf
  frame := by
    intro l _ hl
    exact hkeep l (fun h => hl ((hsplit l).mpr (.inr h)))
  alloc := by
    intro l
    constructor
    · intro h
      by_cases hlD : l ∈ D
      · exact absurd (hD l hlD) h
      · rw [hkeep l hlD] at h
        by_cases hl : l ∈ E
        · rcases (hsplit l).mp hl with h' | h'
          · exact .inr (.inl h')
          · exact absurd h' hlD
        · exact .inl ⟨h, hl⟩
    · intro h
      rcases h with ⟨h, hl⟩ | h | h
      · rw [hkeep l (fun h => hl ((hsplit l).mpr (.inr h)))]; exact h
      · rw [hkeep l (hdisj l h)]; exact hE l ((hsplit l).mpr (.inl h))
      · simp at h

/-- What a step's footprint and value own may be regrouped: cells the value owned may become the
footprint's, as when a value is bound to a variable or stored in a place. -/
theorem Moves.relabel (h : Moves σ E σ' E' L) (hsplit : ∀ x, x ∈ E'' ∨ x ∈ L'' ↔ x ∈ E' ∨ x ∈ L) :
    Moves σ E σ' E'' L'' where
  rt := h.rt
  fresh := h.fresh
  within := fun l hl => h.within l ((hsplit l).mp (hl.symm)).symm
  next := h.next
  wf := h.wf
  frame := h.frame
  alloc := by
    intro l
    rw [h.alloc]
    constructor
    · rintro (h | h | h)
      · exact .inl h
      · exact .inr ((hsplit l).mpr (.inl h))
      · exact .inr ((hsplit l).mpr (.inr h))
    · rintro (h | h | h)
      · exact .inl h
      · exact .inr ((hsplit l).mp (.inl h))
      · exact .inr ((hsplit l).mp (.inr h))

end FlyCore.Ownership
