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
its parts among the exclusive footprints and the shared ones as its slot says. -/
theorem foot_lookup : Foot F σ Γ env E S → lookup x Γ = some s →
    ∃ a L, lookup x env = some a ∧ SlotOk F σ s a L ∧ Sub (exclPart s L) E ∧ Sub (sharedPart s L) S := by
  intro h
  induction h with
  | nil => simp [lookup]
  | @cons t a L Γ env E S y ht _ ih =>
    intro hx
    by_cases hy : x = y
    · simp only [lookup, hy, ↓reduceIte, Option.some.injEq] at hx ⊢
      subst hx
      exact ⟨a, L, rfl, ht, fun z hz => mem_addE.mpr (.inl hz), fun z hz => mem_addS.mpr (.inl hz)⟩
    · simp only [lookup, hy, ↓reduceIte] at hx ⊢
      obtain ⟨a', L', ha, hs, hE, hS⟩ := ih hx
      exact ⟨a', L', ha, hs, fun z hz => mem_addE.mpr (.inr (hE z hz)), fun z hz => mem_addS.mpr (.inr (hS z hz))⟩

theorem exclPart_of_noshell (he : s.excl = true) (hs : s.shell = false) : exclPart s L = L := by
  simp [exclPart, he, hs]

theorem sharedPart_of_ro (he : s.excl = false) : sharedPart s L = L := by
  simp [sharedPart, he]

/-- A closure borrowed `mut` holds a closure. -/
theorem SlotOk.shell_fn (h : SlotOk F σ s a L) (hL : LT F σ a τ L) (hs : s.shell = true) : τ.isFn = true := by
  match s, hs, h with
  | .ref .mut (.fn _ _ _ _), _, h => rw [← (LT.det_ty h hL).1]; rfl

/-- A typed place: where it is, on a path into the tree of its root, and, if it may be changed, in
the exclusive footprint — but for a closure borrowed `mut`, which is the place itself, its cell only
read. -/
theorem place_ok : PlaceTy Γ p τ w r → Foot F σ Γ env E S →
    ∃ a τr Lr P l s, lookup r env = some a ∧ LT F σ a τr Lr ∧ Path F σ a τr P l τ ∧
      resolve σ env p = some l ∧ (Sub (exclPart s Lr) E ∧ Sub (sharedPart s Lr) S) ∧
      (w = true → s.shell = false → Sub Lr E) ∧
      lookup r Γ = some s ∧ SlotOk F σ s a Lr ∧ (w = true → s.excl = true) ∧
      (∀ σ' L', LT F σ' a τr L' → SlotOk F σ' s a L') ∧ (s.shell = true → P = [] ∧ τ = τr) := by
  intro hp hf
  induction hp with
  | own hx =>
    obtain ⟨a, L, ha, hL, hE, hS⟩ := foot_lookup hf hx
    exact ⟨a, _, L, [], a, _, ha, hL, .here, ha, ⟨hE, hS⟩,
      fun _ _ => by simpa [exclPart, Slot.excl, Slot.shell] using hE, hx, hL, fun _ => rfl,
      fun _ _ h => h, fun h => by simp [Slot.shell] at h⟩
  | @ref x m τ hx =>
    obtain ⟨a, L, ha, hL, hE, hS⟩ := foot_lookup hf hx
    refine ⟨a, τ, L, [], a, _, ha, hL, .here, ha, ⟨hE, hS⟩, ?_, hx, hL, ?_, fun _ _ h => h, fun _ => ⟨rfl, rfl⟩⟩
    · intro hw hsh
      cases m
      · simp at hw
      · simpa [exclPart, Slot.excl, hsh] using hE
    · intro hw; cases m
      · simp at hw
      · rfl
  | deref hq ih =>
    obtain ⟨a, τr, Lr, P, l, s, ha, hLr, hpath, hres, hsub, hw, hs, hso, hex, hlt, hsh⟩ := ih
    obtain ⟨R, hR, -⟩ := path_split hpath hLr
    cases hR with
    | box hl hb _ =>
      refine ⟨a, τr, Lr, P ++ [l], _, s, ha, hLr, hpath.snoc hl, by simp [resolve, hres, hl], hsub, hw, hs,
        hso, hex, hlt, fun h => ?_⟩
      -- A closure's cell holds no box to follow.
      obtain ⟨-, rfl⟩ := hsh h
      match s, h, hso with
      | .ref .mut (.fn _ _ _ _), _, hso => exact absurd (LT.det_ty hLr hso).1 (by simp)
  | fst hq ih =>
    obtain ⟨a, τr, Lr, P, l, s, ha, hLr, hpath, hres, hsub, hw, hs, hso, hex, hlt, hsh⟩ := ih
    obtain ⟨R, hR, -⟩ := path_split hpath hLr
    cases hR with
    | pair hl h1 h2 _ _ =>
      refine ⟨a, τr, Lr, _, _, s, ha, hLr, hpath.snocFst' rfl hl h2, by simp [resolve, hres, hl], hsub, hw, hs,
        hso, hex, hlt, fun h => ?_⟩
      obtain ⟨-, rfl⟩ := hsh h
      match s, h, hso with
      | .ref .mut (.fn _ _ _ _), _, hso => exact absurd (LT.det_ty hLr hso).1 (by simp)
  | snd hq ih =>
    obtain ⟨a, τr, Lr, P, l, s, ha, hLr, hpath, hres, hsub, hw, hs, hso, hex, hlt, hsh⟩ := ih
    obtain ⟨R, hR, -⟩ := path_split hpath hLr
    cases hR with
    | pair hl h1 h2 _ _ =>
      refine ⟨a, τr, Lr, _, _, s, ha, hLr, hpath.snocSnd' rfl hl h1, by simp [resolve, hres, hl], hsub, hw, hs,
        hso, hex, hlt, fun h => ?_⟩
      obtain ⟨-, rfl⟩ := hsh h
      match s, h, hso with
      | .ref .mut (.fn _ _ _ _), _, hso => exact absurd (LT.det_ty hLr hso).1 (by simp)


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
theorem foot_update : Foot F σ Γ env E S → (Γ.map Prod.fst).Nodup → lookup x Γ = some s →
    s.excl = true → s.shell = false →
    ∃ a L E₁ E₂, lookup x env = some a ∧ SlotOk F σ s a L ∧ E = E₁ ++ L ++ E₂ ∧
      ∀ σ' s' L', s'.excl = true → s'.shell = false → Agree σ σ' (E₁ ++ E₂ ++ S) → SlotOk F σ' s' a L' →
        Foot F σ' (setSlot Γ x s') env (E₁ ++ L' ++ E₂) S := by
  intro h
  induction h with
  | nil => simp [lookup]
  | @cons t a L Γ env E S y ht hrest ih =>
    intro hk hx hex hsh
    simp only [List.map_cons] at hk
    have hy' := (List.nodup_cons.mp hk).1
    have hk' := (List.nodup_cons.mp hk).2
    by_cases hy : x = y
    · subst hy
      simp only [lookup, ↓reduceIte, Option.some.injEq] at hx
      subst hx
      refine ⟨a, L, [], E, by simp [lookup], ht, by simp [addE, exclPart, hex, hsh], ?_⟩
      intro σ' s' L' hex' hsh' hag hs'
      have hS : addS t L S = S := by simp [addS, sharedPart, hex, hsh]
      rw [hS] at hag
      have hrest' := hrest.frame (σ' := σ') (fun l hl => hag l (by simpa using hl))
      rw [setSlot_head Γ hy']
      have := Foot.cons (x := x) hs' hrest'
      simpa [addE, addS, exclPart, sharedPart, hex, hsh, hex', hsh'] using this
    · simp only [lookup, hy, ↓reduceIte] at hx
      obtain ⟨a', L', E₁, E₂, ha, hs, hE, hupd⟩ := ih hk' hx hex hsh
      refine ⟨a', L', addE t L E₁, E₂, by simp [lookup, hy, ha], hs, by subst hE; simp [addE], ?_⟩
      intro σ' s' L'' hex' hsh' hag hs'
      have hL : Agree σ σ' L := by
        intro l hl
        apply hag l
        rcases mem_parts (s := t) hl with h | h
        · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inl (mem_addE.mpr (.inl h)))))
        · exact List.mem_append.mpr (.inr (mem_addS.mpr (.inl h)))
      have hrest' := hupd σ' s' L'' hex' hsh' (fun l hl => hag l (by
        simp only [List.mem_append] at hl ⊢
        rcases hl with (hl | hl) | hl
        · exact .inl (.inl (mem_addE.mpr (.inr hl)))
        · exact .inl (.inr hl)
        · exact .inr (mem_addS.mpr (.inr hl)))) hs'
      rw [setSlot_tail Γ (Ne.symm hy)]
      have := Foot.cons (x := y) (ht.frame hL) hrest'
      simpa [addE, addS] using this

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

theorem Weaker.keys : Weaker Γ' Γ → Γ'.map Prod.fst = Γ.map Prod.fst
  | .nil => rfl
  | .cons _ h => by simp [h.keys]

theorem freeze_keys : (freeze Γ ys).map Prod.fst = Γ.map Prod.fst := by
  induction Γ with
  | nil => rfl
  | cons p Γ ih =>
    obtain ⟨y, s⟩ := p
    simp only [freeze, List.map_cons] at ih ⊢
    split <;> simp [ih]

theorem thaw_cons : thaw ((x, s) :: Γ) ys ((y, s') :: Γb) = (if x ∈ ys then (x, s) else (y, s')) :: thaw Γ ys Γb := by
  simp [thaw]

theorem hide_keys : (hide Γ y).map Prod.fst = Γ.map Prod.fst := by
  induction Γ with
  | nil => rfl
  | cons p Γ ih =>
    obtain ⟨z, s⟩ := p
    simp only [hide, List.map_cons] at ih ⊢
    split <;> simp [ih]

theorem lendCtx_keys : (lendCtx m Γ y).map Prod.fst = Γ.map Prod.fst := by
  cases m
  · exact freeze_keys
  · exact hide_keys

theorem thaw_keys : ∀ {Γ Γb : Ctx}, Γb.map Prod.fst = Γ.map Prod.fst → (thaw Γ ys Γb).map Prod.fst = Γ.map Prod.fst
  | [], _, h => by simp [thaw]
  | _ :: _, [], h => by simp at h
  | p :: Γ, q :: Γb, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [thaw, List.zipWith_cons_cons, List.map_cons, List.cons.injEq]
    refine ⟨by split <;> simp [h.1], thaw_keys h.2⟩

theorem hideAll_keys : ∀ {Γ : Ctx} {ys : List Var}, (hideAll Γ ys).map Prod.fst = Γ.map Prod.fst
  | _, [] => rfl
  | Γ, y :: ys => (hideAll_keys (Γ := hide Γ y) (ys := ys)).trans hide_keys

theorem unhideAll_keys : ∀ {Γ Γb : Ctx} {ys : List Var}, Γb.map Prod.fst = Γ.map Prod.fst →
    (unhideAll Γ ys Γb).map Prod.fst = Γ.map Prod.fst
  | _, _, [], h => h
  | Γ, _, y :: ys, h => thaw_keys ((unhideAll_keys (Γ := hide Γ y) (ys := ys) (h.trans hide_keys.symm)).trans hide_keys)

theorem lendCtxs_keys : (lendCtxs m Γ ys).map Prod.fst = Γ.map Prod.fst := by
  cases m
  · exact freeze_keys
  · exact hideAll_keys

theorem unlend_keys (h : Γb.map Prod.fst = Γ.map Prod.fst) : (unlend m Γ ys Γb).map Prod.fst = Γ.map Prod.fst := by
  cases m
  · exact thaw_keys h
  · exact unhideAll_keys h

theorem atom_keys : AtomTy Γ a τ Γ' → Γ'.map Prod.fst = Γ.map Prod.fst
  | .lit => rfl
  | .read _ => rfl
  | .move _ => setSlot_keys _

theorem atoms_keys : AtomsTy Γ as τs Γ' → Γ'.map Prod.fst = Γ.map Prod.fst
  | .nil => rfl
  | .cons ha hrest => (atoms_keys hrest).trans (atom_keys ha)

theorem typed_keys : Typed F O Γ e τ Γ' r → Γ'.map Prod.fst = Γ.map Prod.fst
  | .atom ha => atom_keys ha
  | .add ha hb => (atom_keys hb).trans (atom_keys ha)
  | .new ha => atom_keys ha
  | .pair ha hb => (atom_keys hb).trans (atom_keys ha)
  | .inj ha => atom_keys ha
  | .case _ _ h₁ _ w₁ _ => by
    have := typed_keys h₁
    simp only [List.map_cons, List.cons.injEq] at this
    exact w₁.keys.trans (this.2.trans (setSlot_keys _))
  | .caseRef _ _ _ _ h₁ _ w₁ _ => by
    have := typed_keys h₁
    simp only [List.map_cons, List.cons.injEq] at this
    exact thaw_keys (w₁.keys.trans (this.2.trans lendCtx_keys))
  | .let_ _ ha hb => by
    have := typed_keys hb
    simp only [List.map_cons, List.cons.injEq] at this
    exact this.2.trans (typed_keys ha)
  | .write ha _ => atom_keys ha
  | .assign ha _ _ => atom_keys ha
  | .call _ _ _ _ hargs _ _ => atoms_keys hargs
  | .lam _ _ _ _ _ ha => atom_keys ha
  | .lendClo _ _ _ _ _ _ _ _ hb => by
    have := typed_keys hb
    simp only [List.map_cons, List.cons.injEq] at this
    exact thaw_keys (this.2.trans freeze_keys)
  | .lendCloMut _ _ _ _ _ _ _ _ hb => by
    have := typed_keys hb
    simp only [List.map_cons, List.cons.injEq] at this
    exact thaw_keys (this.2.trans hide_keys)
  | .applyOnce _ _ ha => (atom_keys ha).trans (setSlot_keys _)
  | .applyBorrow _ ha _ _ _ => atom_keys ha
  | .lendCall (m := m) _ _ _ _ hargs _ _ _ _ _ hb => by
    have := typed_keys hb
    simp only [List.map_cons, List.cons.injEq] at this
    exact (unlend_keys (m := m) (this.2.trans lendCtxs_keys)).trans (atoms_keys hargs)
  | .ite hc ha _ wa _ => wa.keys.trans ((typed_keys ha).trans (atom_keys hc))
  | .throw_ ha _ => atom_keys ha
  | .try_ _ hb hh => by
    have := typed_keys hh
    simp only [List.map_cons, List.cons.injEq] at this
    exact this.2.trans (typed_keys hb)
  | .while_ _ _ => rfl
  | .defer hb _ => typed_keys hb
  | .lend _ _ _ _ hb => by
    have := typed_keys hb
    simp only [List.map_cons, List.cons.injEq] at this
    exact thaw_keys (this.2.trans lendCtx_keys)
  | .perform _ _ hargs _ _ => atoms_keys hargs
  | .handle _ _ _ _ _ _ _ hb =>
    unhideAll_keys ((thaw_keys ((typed_keys hb).trans freeze_keys)).trans hideAll_keys)
  | .handleAbort _ _ _ _ hb hh => by
    have := typed_keys hh
    simp only [List.map_cons, List.cons.injEq] at this
    exact this.2.trans (typed_keys hb)

theorem lookup_det {α : Type} {x : Var} {a b : α} {env : List (Var × α)} : lookup x env = some a → lookup x env = some b → a = b := by
  intro h1 h2; rw [h1] at h2; exact Option.some.inj h2

/-- At a place that may be changed, what the location holds may be replaced: the rest of the
activation stands, the variable the place is rooted at now owning the new tree. -/
theorem replace_at (hI : Inv F σ Γ env E S) (hp : PlaceTy Γ p τ true r)
    (hτ : τ.isFn = false ∨ ∀ s, lookup r Γ = some s → s.shell = false) :
    ∃ l R P E₁ E₂, resolve σ env p = some l ∧ LT F σ l τ R ∧ E.Perm (E₁ ++ (P ++ R) ++ E₂) ∧
      ∀ σ' R', Agree σ σ' (E₁ ++ P ++ E₂ ++ S) → LT F σ' l τ R' → Disj R' (E₁ ++ P ++ E₂) →
        Disj R' S → ∃ E', Inv F σ' Γ env E' S ∧ E'.Perm (E₁ ++ (P ++ R') ++ E₂) := by
  obtain ⟨a, τr, Lr, P, l, s, ha, hLr, hpath, hres, -, -, hs, hso, hex, hlt, hshp⟩ := place_ok hp hI.foot
  have hsh : ∀ s', lookup r Γ = some s' → s'.shell = false := by
    rcases hτ with hτ | h
    · intro s' hs'
      obtain rfl := lookup_det hs hs'
      cases h : s.shell
      · rfl
      · obtain ⟨-, rfl⟩ := hshp h; rw [hso.shell_fn hLr h] at hτ; cases hτ
    · exact h
  obtain ⟨R, hR, hLrp⟩ := path_split hpath hLr
  obtain ⟨a', L', E₁, E₂, ha', hso', hE, hupd⟩ := foot_update hI.foot hI.keys hs (hex rfl) (hsh s hs)
  cases lookup_det ha ha'
  cases hso.det hso'
  have hEp : E.Perm (E₁ ++ (P ++ R) ++ E₂) := by
    rw [hE]; exact (hLrp.append_left E₁).append_right E₂
  refine ⟨l, R, P, E₁, E₂, hres, hR, hEp, ?_⟩
  intro σ' R' hag hR' hd hdS
  have hnd := hEp.nodup_iff.mp hI.nodup
  have hPn : P.Nodup := (nodup_append_disj.mp (hLrp.nodup_iff.mp hLr.nodup)).1
  have hagP : Agree σ σ' P := fun x hx => hag x (by simp [hx])
  have hdP : Disj P R' := fun x hx hx' => hd x hx' (by simp [hx])
  obtain ⟨L'', hlt', hL''p, -⟩ := path_join hpath hPn hagP hR' hdP
  have hfoot := hupd σ' s L'' (hex rfl) (hsh s hs) (fun x hx => hag x (by
    simp only [List.mem_append] at hx ⊢
    rcases hx with (hx | hx) | hx
    · exact .inl (.inl (.inl hx))
    · exact .inl (.inr hx)
    · exact .inr hx)) (hlt σ' _ hlt')
  rw [setSlot_same Γ hI.keys hs] at hfoot
  have hE' : (E₁ ++ L'' ++ E₂).Perm (E₁ ++ (P ++ R') ++ E₂) := (hL''p.append_left E₁).append_right E₂
  refine ⟨_, ⟨hfoot, hE'.nodup_iff.mpr ?_, ?_, hI.keys⟩, hE'⟩
  · simp only [List.nodup_append, List.mem_append] at hnd ⊢
    obtain ⟨⟨h1, ⟨hP, -, -⟩, h1PR⟩, h2, h12⟩ := hnd
    refine ⟨⟨h1, ⟨hP, hR'.nodup, fun x hx y hy e => hdP x hx (e ▸ hy)⟩, ?_⟩, h2, ?_⟩
    · intro x hx y hy e
      subst e
      rcases hy with hy | hy
      · exact h1PR x hx x (.inl hy) rfl
      · exact hd x hy (by simp [hx])
    · intro x hx y hy e
      subst e
      rcases hx with hx | hx | hx
      · exact h12 x (.inl hx) x hy rfl
      · exact h12 x (.inr (.inl hx)) x hy rfl
      · exact hd x hx (by simp [hy])
  · intro x hxS hx
    rcases List.mem_append.mp (hE'.mem_iff.mp hx) with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact hI.disj x hxS (hEp.mem_iff.mpr (by simp [hx]))
      · rcases List.mem_append.mp hx with hx | hx
        · exact hI.disj x hxS (hEp.mem_iff.mpr (by simp [hx]))
        · exact hdS x hx hxS
    · exact hI.disj x hxS (hEp.mem_iff.mpr (by simp [hx]))

end FlyCore.Ownership
