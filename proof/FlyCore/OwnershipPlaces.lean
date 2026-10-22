import FlyCore.OwnershipBase

/-!
# Ownership: places

A place the types accept denotes a location: one along a path into the tree of the variable it is
rooted at. A place that may be changed is rooted at a variable that may be changed — owned, or
borrowed `mut` — so the whole path, and the tree at its end, lie in the activation's exclusive
footprint.
-/

namespace FlyCore.Ownership

def Sub (A B : List Nat) : Prop := ∀ x ∈ A, x ∈ B

/-- Each variable the types know is bound in the environment, with the footprint its slot says,
among the exclusive footprints or the shared ones as its slot says. -/
theorem foot_lookup : Foot σ Γ env E S → lookup x Γ = some s →
    ∃ a L, lookup x env = some a ∧ SlotOk σ s a L ∧ Sub L (if s.excl then E else S) := by
  intro h
  induction h with
  | nil => simp [lookup]
  | @cons t a L Γ env E S y ht _ ih =>
    intro hx
    by_cases hy : x = y
    · simp only [lookup, hy, ↓reduceIte, Option.some.injEq] at hx ⊢
      subst hx
      refine ⟨a, L, rfl, ht, fun z hz => ?_⟩
      cases he : t.excl <;> simp [he, addE, addS, hz]
    · simp only [lookup, hy, ↓reduceIte] at hx ⊢
      obtain ⟨a', L', ha, hs, hsub⟩ := ih hx
      refine ⟨a', L', ha, hs, fun z hz => ?_⟩
      have := hsub z hz
      cases he : s.excl <;> simp only [he] at this ⊢
      · exact mem_addS.mpr (.inr this)
      · exact mem_addE.mpr (.inr this)

/-- A typed place: where it is, on a path into the tree of its root, and, if it may be changed, in
the exclusive footprint. -/
theorem place_ok : PlaceTy Γ p τ w r → Foot σ Γ env E S →
    ∃ a τr Lr P l s, lookup r env = some a ∧ LT σ a τr Lr ∧ Path σ a τr P l τ ∧
      resolve σ env p = some l ∧ (Sub Lr E ∨ Sub Lr S) ∧ (w = true → Sub Lr E) ∧
      lookup r Γ = some s ∧ SlotOk σ s a Lr ∧ (w = true → s.excl = true) ∧
      ∀ σ' L', LT σ' a τr L' → SlotOk σ' s a L' := by
  intro hp hf
  induction hp with
  | own hx =>
    obtain ⟨a, L, ha, hL, hsub⟩ := foot_lookup hf hx
    simp [Slot.excl] at hsub
    exact ⟨a, _, L, [], a, _, ha, hL, .here, ha, .inl hsub, fun _ => hsub, hx, hL, fun _ => rfl,
      fun _ _ h => h⟩
  | @ref x m τ hx =>
    obtain ⟨a, L, ha, hL, hsub⟩ := foot_lookup hf hx
    cases m
    · simp [Slot.excl] at hsub
      exact ⟨a, τ, L, [], a, _, ha, hL, .here, ha, .inr hsub, fun h => by simp at h, hx, hL,
        fun h => by simp at h, fun _ _ h => h⟩
    · simp [Slot.excl] at hsub
      exact ⟨a, τ, L, [], a, _, ha, hL, .here, ha, .inl hsub, fun _ => hsub, hx, hL, fun _ => rfl,
        fun _ _ h => h⟩
  | deref _ ih =>
    obtain ⟨a, τr, Lr, P, l, s, ha, hLr, hpath, hres, hsub, hw, hs, hso, hex, hlt⟩ := ih
    obtain ⟨R, hR, rfl⟩ := path_split hpath hLr
    cases hR with
    | box hl hb _ =>
      exact ⟨a, τr, _, P ++ [l], _, s, ha, hLr, hpath.snoc hl, by simp [resolve, hres, hl], hsub, hw, hs,
        hso, hex, hlt⟩


/-! ## Changing one variable -/

theorem setSlot_keys (Γ : Ctx) : (setSlot Γ x s).map Prod.fst = Γ.map Prod.fst := by
  induction Γ with
  | nil => rfl
  | cons p Γ ih =>
    obtain ⟨y, t⟩ := p
    simp only [setSlot, List.map_cons] at ih ⊢
    split <;> simp [ih]

theorem setSlot_absent (Γ : Ctx) : x ∉ Γ.map Prod.fst → setSlot Γ x s = Γ := by
  induction Γ with
  | nil => intro; rfl
  | cons p Γ ih =>
    obtain ⟨y, t⟩ := p
    intro h
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [setSlot, List.map_cons] at ih ⊢
    simp only [Ne.symm h.1, ↓reduceIte]
    exact congrArg _ (ih h.2)

theorem setSlot_head (Γ : Ctx) : x ∉ Γ.map Prod.fst → setSlot ((x, t) :: Γ) x s = (x, s) :: Γ := by
  intro h
  have := setSlot_absent (s := s) Γ h
  simp only [setSlot, List.map_cons, ↓reduceIte] at this ⊢
  rw [this]

theorem setSlot_tail (Γ : Ctx) : y ≠ x → setSlot ((y, t) :: Γ) x s = (y, t) :: setSlot Γ x s := by
  intro h
  simp [setSlot, h]

/-- An exclusive variable's footprint is one segment of the exclusive footprints. It may be
replaced, as the variable changes, in a store that changed nothing else, and the rest stands. -/
theorem foot_update : Foot σ Γ env E S → (Γ.map Prod.fst).Nodup → lookup x Γ = some s →
    s.excl = true →
    ∃ a L E₁ E₂, lookup x env = some a ∧ SlotOk σ s a L ∧ E = E₁ ++ L ++ E₂ ∧
      ∀ σ' s' L', s'.excl = true → Agree σ σ' (E₁ ++ E₂ ++ S) → SlotOk σ' s' a L' →
        Foot σ' (setSlot Γ x s') env (E₁ ++ L' ++ E₂) S := by
  intro h
  induction h with
  | nil => simp [lookup]
  | @cons t a L Γ env E S y ht hrest ih =>
    intro hk hx hex
    simp only [List.map_cons] at hk
    have hy' := (List.nodup_cons.mp hk).1
    have hk' := (List.nodup_cons.mp hk).2
    by_cases hy : x = y
    · subst hy
      simp only [lookup, ↓reduceIte, Option.some.injEq] at hx
      subst hx
      refine ⟨a, L, [], E, by simp [lookup], ht, by simp [addE, hex], ?_⟩
      intro σ' s' L' hex' hag hs'
      have hS : addS t L S = S := by simp [addS, hex]
      rw [hS] at hag
      have hrest' := hrest.frame (σ' := σ') (fun l hl => hag l (by simpa using hl))
      rw [setSlot_head Γ hy']
      have := Foot.cons (x := x) hs' hrest'
      simpa [addE, addS, hex, hex'] using this
    · simp only [lookup, hy, ↓reduceIte] at hx
      obtain ⟨a', L', E₁, E₂, ha, hs, hE, hupd⟩ := ih hk' hx hex
      refine ⟨a', L', addE t L E₁, E₂, by simp [lookup, hy, ha], hs, ?_, ?_⟩
      · subst hE; cases he : t.excl <;> simp [addE, he]
      · intro σ' s' L'' hex' hag hs'
        have hL : Agree σ σ' L := by
          intro l hl
          apply hag l
          cases he : t.excl
          · exact List.mem_append.mpr (.inr (mem_addS.mpr (.inl ⟨he, hl⟩)))
          · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inl (mem_addE.mpr (.inl ⟨he, hl⟩)))))
        have hrest' := hupd σ' s' L'' hex' (fun l hl => hag l (by
          simp only [List.mem_append] at hl ⊢
          rcases hl with (hl | hl) | hl
          · exact .inl (.inl (mem_addE.mpr (.inr hl)))
          · exact .inl (.inr hl)
          · exact .inr (mem_addS.mpr (.inr hl)))) hs'
        rw [setSlot_tail Γ (Ne.symm hy)]
        have := Foot.cons (x := y) (ht.frame hL) hrest'
        cases he : t.excl <;> simpa [addE, addS, he] using this

theorem setSlot_same (Γ : Ctx) : (Γ.map Prod.fst).Nodup → lookup x Γ = some s → setSlot Γ x s = Γ := by
  induction Γ with
  | nil => simp [lookup]
  | cons p Γ ih =>
    obtain ⟨y, t⟩ := p
    intro hk hx
    simp only [List.map_cons] at hk
    by_cases hy : x = y
    · subst hy
      simp only [lookup, ↓reduceIte, Option.some.injEq] at hx
      subst hx
      rw [setSlot_head Γ (List.nodup_cons.mp hk).1]
    · simp only [lookup, hy, ↓reduceIte] at hx
      rw [setSlot_tail Γ (Ne.symm hy), ih (List.nodup_cons.mp hk).2 hx]

theorem lookup_none_keys : lookup x Γ = none → x ∉ Γ.map Prod.fst := by
  induction Γ with
  | nil => simp
  | cons p Γ ih =>
    obtain ⟨y, t⟩ := p
    intro h
    simp only [lookup] at h
    split at h
    · simp at h
    · simp only [List.map_cons, List.mem_cons, not_or]
      exact ⟨by assumption, ih h⟩

mutual
theorem typed_keys : Typed F Γ e τ Γ' → Γ'.map Prod.fst = Γ.map Prod.fst
  | .lit => rfl
  | .read _ => rfl
  | .move _ => setSlot_keys _
  | .add ha hb => (typed_keys hb).trans (typed_keys ha)
  | .new ha => typed_keys ha
  | .let_ _ ha hb => by
    have := typed_keys hb
    simp only [List.map_cons, List.cons.injEq] at this
    exact this.2.trans (typed_keys ha)
  | .write ha _ => typed_keys ha
  | .assign ha _ => typed_keys ha
  | .call _ hargs _ _ => args_keys hargs
  | .seq ha hb => (typed_keys hb).trans (typed_keys ha)
theorem args_keys : Args F Γ as τs Γ' → Γ'.map Prod.fst = Γ.map Prod.fst
  | .nil => rfl
  | .cons ha hrest => (args_keys hrest).trans (typed_keys ha)
end

theorem lookup_det {α : Type} {x : Var} {a b : α} {env : List (Var × α)} : lookup x env = some a → lookup x env = some b → a = b := by
  intro h1 h2; rw [h1] at h2; exact Option.some.inj h2

/-- At a place that may be changed, what the location holds may be replaced: the rest of the
activation stands, the variable the place is rooted at now owning the new tree. -/
theorem replace_at (hI : Inv σ Γ env E S) (hp : PlaceTy Γ p τ true r) :
    ∃ l R P E₁ E₂, resolve σ env p = some l ∧ LT σ l τ R ∧ E = E₁ ++ (P ++ R) ++ E₂ ∧
      ∀ σ' R', Agree σ σ' (E₁ ++ P ++ E₂ ++ S) → LT σ' l τ R' → Disj R' (E₁ ++ P ++ E₂) →
        Disj R' S → Inv σ' Γ env (E₁ ++ (P ++ R') ++ E₂) S := by
  obtain ⟨a, τr, Lr, P, l, s, ha, hLr, hpath, hres, -, -, hs, hso, hex, hlt⟩ := place_ok hp hI.foot
  obtain ⟨R, hR, rfl⟩ := path_split hpath hLr
  obtain ⟨a', L', E₁, E₂, ha', hso', hE, hupd⟩ := foot_update hI.foot hI.keys hs (hex rfl)
  cases lookup_det ha ha'
  cases hso.det hso'
  refine ⟨l, R, P, E₁, E₂, hres, hR, hE, ?_⟩
  intro σ' R' hag hR' hd hdS
  have hnd := hE ▸ hI.nodup
  rw [nodup_append_disj, nodup_append_disj] at hnd
  have hPR := hLr.nodup
  rw [nodup_append_disj] at hPR
  have hagP : Agree σ σ' P := fun x hx => hag x (by simp [hx])
  have hdP : Disj P R' := fun x hx hx' => hd x hx' (by simp [hx])
  obtain ⟨hlt', -⟩ := path_join hpath hLr hagP hR' hdP
  have hfoot := hupd σ' s (P ++ R') (hex rfl) (fun x hx => hag x (by
    simp only [List.mem_append] at hx ⊢
    rcases hx with (hx | hx) | hx
    · exact .inl (.inl (.inl hx))
    · exact .inl (.inr hx)
    · exact .inr hx)) (hlt σ' _ hlt')
  rw [setSlot_same Γ hI.keys hs] at hfoot
  refine ⟨hfoot, ?_, ?_, hI.keys⟩
  · rw [nodup_append_disj, nodup_append_disj, nodup_append_disj]
    obtain ⟨⟨h1, -, h1PR⟩, h2, h12⟩ := hnd
    refine ⟨⟨h1, ⟨hPR.1, hR'.nodup, hdP⟩, ?_⟩, h2, ?_⟩
    · intro x hx hx'
      rcases List.mem_append.mp hx' with hx' | hx'
      · exact h1PR x hx (List.mem_append.mpr (.inl hx'))
      · exact hd x hx' (by simp [hx])
    · intro x hx hx'
      rcases List.mem_append.mp hx with hx | hx
      · exact h12 x (List.mem_append.mpr (.inl hx)) hx'
      · rcases List.mem_append.mp hx with hx | hx
        · exact h12 x (List.mem_append.mpr (.inr (List.mem_append.mpr (.inl hx)))) hx'
        · exact hd x hx (by simp [hx'])
  · intro x hxS hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact hI.disj x hxS (hE ▸ by simp [hx])
      · rcases List.mem_append.mp hx with hx | hx
        · exact hI.disj x hxS (hE ▸ by simp [hx])
        · exact hdS x hx hxS
    · exact hI.disj x hxS (hE ▸ by simp [hx])

end FlyCore.Ownership
