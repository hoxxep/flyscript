import FlyCore.OwnershipJoin

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
theorem foot_lookup : Foot F ι σ Γ env E S → lookup x Γ = some s →
    ∃ a L, lookup x env = some a ∧ SlotOk F ι σ s a L ∧ Sub (exclPart s L) E ∧ Sub (sharedPart s L) S := by
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
theorem SlotOk.shell_fn (h : SlotOk F ι σ s a L) (hL : LT F ι σ a τ L) (hs : s.shell = true)
    (hh : ∀ t A B, s ≠ .half t A B) : τ.isFn = true := by
  match s, hs, h with
  | .half t A B, _, _ => exact absurd rfl (hh t A B)
  | .ref .mut (.fn _ _ _ _), _, h =>
    cases hτ : τ.isHole
    · rw [(LT.det_fn h hL hτ).1]; rfl
    · exfalso
      cases τ <;> simp [Ty.isHole] at hτ
      cases hL
      cases h

/-- A typed place: where it is, on a path into the tree of its root, and, if it may be changed, in
the exclusive footprint — but for a closure borrowed `mut`, which is the place itself, its cell only
read. -/
theorem place_ok : PlaceTy Γ p τ w r → Foot F ι σ Γ env E S →
    ∃ a τr Lr P l s, lookup r env = some a ∧ LT F ι σ a τr Lr ∧ Path F ι σ a τr P l τ ∧
      resolve σ env p = some l ∧ (Sub (exclPart s Lr) E ∧ Sub (sharedPart s Lr) S) ∧
      (w = true → s.shell = false → Sub Lr E) ∧
      lookup r Γ = some s ∧ SlotOk F ι σ s a Lr ∧ (w = true → s.excl = true) ∧
      (∀ σ' L', LT F ι σ' a τr L' → SlotOk F ι σ' s a L') ∧
      (s.shell = true → (P = [] ∧ τ = τr) ∨ (τr.isFn = false ∧ ∃ P', P = a :: P')) ∧ τr = s.ty := by
  intro hp hf
  induction hp with
  | own hx =>
    obtain ⟨a, L, ha, hL, hE, hS⟩ := foot_lookup hf hx
    exact ⟨a, _, L, [], a, _, ha, hL, .here, ha, ⟨hE, hS⟩,
      fun _ _ => by simpa [exclPart, Slot.excl, Slot.shell] using hE, hx, hL, fun _ => rfl,
      fun _ _ h => h, fun h => by simp [Slot.shell] at h, rfl⟩
  | @ref x m τ hx =>
    obtain ⟨a, L, ha, hL, hE, hS⟩ := foot_lookup hf hx
    refine ⟨a, τ, L, [], a, _, ha, hL, .here, ha, ⟨hE, hS⟩, ?_, hx, hL, ?_, fun _ _ h => h, fun _ => .inl ⟨rfl, rfl⟩, rfl⟩
    · intro hw hsh
      cases m
      · simp at hw
      · simpa [exclPart, Slot.excl, hsh] using hE
    · intro hw; cases m
      · simp at hw
      · rfl
  | @half x t A B τ hx hτ =>
    subst hτ
    obtain ⟨a, L, ha, hL, hE, hS⟩ := foot_lookup hf hx
    exact ⟨a, .lent1 t A B, L, [], a, _, ha, hL, .here, ha, ⟨hE, hS⟩, fun _ hsh => by simp [Slot.shell] at hsh, hx, hL,
      fun _ => rfl, fun _ _ h => h, fun _ => .inl ⟨rfl, rfl⟩, rfl⟩
  | deref hq ih =>
    obtain ⟨a, τr, Lr, P, l, s, ha, hLr, hpath, hres, hsub, hw, hs, hso, hex, hlt, hsh, hty⟩ := ih
    obtain ⟨R, hR, -⟩ := path_split hpath hLr
    cases hR with
    | box hl hb _ =>
      refine ⟨a, τr, Lr, P ++ [l], _, s, ha, hLr, hpath.snoc hl, by simp [resolve, hres, hl], hsub, hw, hs,
        hso, hex, hlt, fun h => .inr ?_, hty⟩
      rcases hsh h with ⟨rfl, rfl⟩ | ⟨hfn, P', rfl⟩
      · cases hpath; exact ⟨rfl, [], rfl⟩
      · exact ⟨hfn, _, rfl⟩
  | fst hq ih =>
    obtain ⟨a, τr, Lr, P, l, s, ha, hLr, hpath, hres, hsub, hw, hs, hso, hex, hlt, hsh, hty⟩ := ih
    obtain ⟨R, hR, -⟩ := path_split hpath hLr
    cases hR with
    | pair hl h1 h2 _ _ =>
      refine ⟨a, τr, Lr, _, _, s, ha, hLr, hpath.snocFst' rfl hl h2, by simp [resolve, hres, hl], hsub, hw, hs,
        hso, hex, hlt, fun h => .inr ?_, hty⟩
      rcases hsh h with ⟨rfl, rfl⟩ | ⟨hfn, P', rfl⟩
      · cases hpath; exact ⟨rfl, _, rfl⟩
      · exact ⟨hfn, _, rfl⟩
  | snd hq ih =>
    obtain ⟨a, τr, Lr, P, l, s, ha, hLr, hpath, hres, hsub, hw, hs, hso, hex, hlt, hsh, hty⟩ := ih
    obtain ⟨R, hR, -⟩ := path_split hpath hLr
    cases hR with
    | pair hl h1 h2 _ _ =>
      refine ⟨a, τr, Lr, _, _, s, ha, hLr, hpath.snocSnd' rfl hl h1, by simp [resolve, hres, hl], hsub, hw, hs,
        hso, hex, hlt, fun h => .inr ?_, hty⟩
      rcases hsh h with ⟨rfl, rfl⟩ | ⟨hfn, P', rfl⟩
      · cases hpath; exact ⟨rfl, _, rfl⟩
      · exact ⟨hfn, _, rfl⟩


/-- A place has one type. -/
theorem PlaceTy.det : PlaceTy Γ p τ w y → PlaceTy Γ p τ' w' y' → τ = τ' := by
  intro h
  induction h generalizing τ' w' y' with
  | own hx => intro h'; cases h' with
    | own hx' => rw [hx] at hx'; cases hx'; rfl
    | ref hx' => rw [hx] at hx'; cases hx'
    | half hx' => rw [hx] at hx'; cases hx'
  | ref hx => intro h'; cases h' with
    | own hx' => rw [hx] at hx'; cases hx'
    | ref hx' => rw [hx] at hx'; cases hx'; rfl
    | half hx' => rw [hx] at hx'; cases hx'
  | half hx hτ => intro h'; cases h' with
    | own hx' => rw [hx] at hx'; cases hx'
    | ref hx' => rw [hx] at hx'; cases hx'
    | half hx' hτ' => rw [hx] at hx'; cases hx'; rw [hτ, hτ']
  | deref _ ih => intro h'; cases h' with | deref h' => exact Ty.box.inj (ih h')
  | fst _ ih => intro h'; cases h' with | fst h' => exact (Ty.pair.inj (ih h')).1
  | snd _ ih => intro h'; cases h' with | snd h' => exact (Ty.pair.inj (ih h')).2

theorem PlaceTy.root_eq : PlaceTy Γ p τ w y → y = p.root := by
  intro h
  induction h with
  | own => rfl
  | ref => rfl
  | half => rfl
  | deref _ ih => exact ih
  | fst _ ih => exact ih
  | snd _ ih => exact ih

/-- A typed place denotes a location holding a tree of its type. -/
theorem place_lt (hp : PlaceTy Γ p τ w y) (hf : Foot F ι σ Γ env E S) :
    ∃ l R, resolve σ env p = some l ∧ LT F ι σ l τ R := by
  obtain ⟨a, τr, Lr, P, l, -, -, hLr, hpath, hres, -⟩ := place_ok hp hf
  obtain ⟨R, hR, -⟩ := path_split hpath hLr
  exact ⟨l, R, hres, hR⟩

/-- The tree at a place reached from another lies in the tree there. -/
theorem place_within (hq : Place.Within q p) : PlaceTy Γ q τ w y → Foot F ι σ Γ env E S →
    resolve σ env q = some l → LT F ι σ l τ R →
    ∃ τp wp lp Rp, PlaceTy Γ p τp wp y ∧ resolve σ env p = some lp ∧ LT F ι σ lp τp Rp ∧ Sub R Rp := by
  induction hq generalizing τ w l R with
  | refl => intro ht _ hres hR; exact ⟨τ, w, l, R, ht, hres, hR, fun _ h => h⟩
  | deref _ ih =>
    intro ht hf hres hR
    cases ht with
    | deref ht0 =>
      obtain ⟨l0, R0, hres0, hR0⟩ := place_lt ht0 hf
      obtain ⟨τp, wp, lp, Rp, htp, hresp, hRp, hsub⟩ := ih ht0 hf hres0 hR0
      cases hR0 with
      | box hm hb _ =>
        simp only [resolve, hres0, hm, Option.some.injEq] at hres
        subst hres
        obtain rfl := hb.det hR
        exact ⟨τp, wp, lp, Rp, htp, hresp, hRp, fun z hz => hsub z (List.mem_cons_of_mem _ hz)⟩
  | fst _ ih =>
    intro ht hf hres hR
    cases ht with
    | fst ht0 =>
      obtain ⟨l0, R0, hres0, hR0⟩ := place_lt ht0 hf
      obtain ⟨τp, wp, lp, Rp, htp, hresp, hRp, hsub⟩ := ih ht0 hf hres0 hR0
      cases hR0 with
      | pair hm h1 _ _ _ =>
        simp only [resolve, hres0, hm, Option.some.injEq] at hres
        subst hres
        obtain rfl := h1.det hR
        exact ⟨τp, wp, lp, Rp, htp, hresp, hRp, fun z hz =>
          hsub z (List.mem_cons_of_mem _ (List.mem_append.mpr (.inl hz)))⟩
  | snd _ ih =>
    intro ht hf hres hR
    cases ht with
    | snd ht0 =>
      obtain ⟨l0, R0, hres0, hR0⟩ := place_lt ht0 hf
      obtain ⟨τp, wp, lp, Rp, htp, hresp, hRp, hsub⟩ := ih ht0 hf hres0 hR0
      cases hR0 with
      | pair hm _ h2 _ _ =>
        simp only [resolve, hres0, hm, Option.some.injEq] at hres
        subst hres
        obtain rfl := h2.det hR
        exact ⟨τp, wp, lp, Rp, htp, hresp, hRp, fun z hz =>
          hsub z (List.mem_cons_of_mem _ (List.mem_append.mpr (.inr hz)))⟩

/-- Places in different fields of a pair hold trees apart. -/
theorem place_apart (hap : Place.Apart p q) (hp : PlaceTy Γ p τ w y) (hq : PlaceTy Γ q τ' w' y')
    (hf : Foot F ι σ Γ env E S) (hres : resolve σ env p = some l) (hres' : resolve σ env q = some l')
    (hR : LT F ι σ l τ R) (hR' : LT F ι σ l' τ' R') : Disj R R' := by
  -- The pair's fields hold trees apart, and each place's tree lies in its field's.
  have key : ∀ {p q τ w y τ' w' y' l l' R R'} (r : Place), p.Within (.fst r) → q.Within (.snd r) →
      PlaceTy Γ p τ w y → PlaceTy Γ q τ' w' y' → resolve σ env p = some l → resolve σ env q = some l' →
      LT F ι σ l τ R → LT F ι σ l' τ' R' → Disj R R' := by
    intro p q τ w y τ' w' y' l l' R R' r h1 h2 hp hq hres hres' hR hR'
    obtain ⟨τ1, w1, l1, R1, ht1, hres1, hR1, hs1⟩ := place_within h1 hp hf hres hR
    obtain ⟨τ2, w2, l2, R2, ht2, hres2, hR2, hs2⟩ := place_within h2 hq hf hres' hR'
    cases ht1 with
    | fst ht0 =>
      cases ht2 with
      | snd ht0' =>
      obtain ⟨-, rfl⟩ := Ty.pair.inj (ht0.det ht0')
      obtain ⟨l0, R0, hres0, hR0⟩ := place_lt ht0 hf
      cases hR0 with
      | pair hm g1 g2 hd _ =>
        simp only [resolve, hres0, hm, Option.some.injEq] at hres1 hres2
        subst hres1 hres2
        obtain rfl := g1.det hR1
        obtain rfl := g2.det hR2
        exact fun z hz hz' => hd z (hs1 z hz) (hs2 z hz')
  obtain ⟨r, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := hap
  · exact key r h1 h2 hp hq hres hres' hR hR'
  · exact fun z hz hz' => key r h2 h1 hq hp hres' hres hR' hR z hz' hz


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
theorem foot_update : Foot F ι σ Γ env E S → (Γ.map Prod.fst).Nodup → lookup x Γ = some s →
    s.excl = true → s.shell = false →
    ∃ a L E₁ E₂, lookup x env = some a ∧ SlotOk F ι σ s a L ∧ E = E₁ ++ L ++ E₂ ∧
      ∀ σ' s' L', s'.excl = true → s'.shell = false → Agree σ σ' (E₁ ++ E₂ ++ S) → SlotOk F ι σ' s' a L' →
        Foot F ι σ' (setSlot Γ x s') env (E₁ ++ L' ++ E₂) S := by
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
      have hrest' := hrest.frame (σ' := σ') ((hag.mono fun l hl => by simpa using hl))
      rw [setSlot_head Γ hy']
      have := Foot.cons (x := x) hs' hrest'
      simpa [addE, addS, exclPart, sharedPart, hex, hsh, hex', hsh'] using this
    · simp only [lookup, hy, ↓reduceIte] at hx
      obtain ⟨a', L', E₁, E₂, ha, hs, hE, hupd⟩ := ih hk' hx hex hsh
      refine ⟨a', L', addE t L E₁, E₂, by simp [lookup, hy, ha], hs, by subst hE; simp [addE], ?_⟩
      intro σ' s' L'' hex' hsh' hag hs'
      have hL : Agree σ σ' L := hag.mono fun l hl => by
        rcases mem_parts (s := t) hl with h | h
        · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inl (mem_addE.mpr (.inl h)))))
        · exact List.mem_append.mpr (.inr (mem_addS.mpr (.inl h)))
      have hrest' := hupd σ' s' L'' hex' hsh' ((hag.mono fun l hl => by
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
  | .readRef _ => rfl
  | .move _ _ => setSlot_keys _

theorem atoms_keys : AtomsTy Γ as τs Γ' → Γ'.map Prod.fst = Γ.map Prod.fst
  | .nil => rfl
  | .cons ha hrest => (atoms_keys hrest).trans (atom_keys ha)

theorem typed_keys : Typed F O Γ e τ Γ' r → Γ'.map Prod.fst = Γ.map Prod.fst
  | .atom ha => atom_keys ha
  | .add ha hb => (atom_keys hb).trans (atom_keys ha)
  | .new ha => atom_keys ha
  | .pair ha hb => (atom_keys hb).trans (atom_keys ha)
  | .inj ha _ => atom_keys ha
  | .case _ _ _ h₁ _ w₁ _ => by
    have := typed_keys h₁
    simp only [List.map_cons, List.cons.injEq] at this
    exact w₁.keys.trans (this.2.trans (setSlot_keys _))
  | .caseRef _ _ _ _ _ h₁ _ w₁ _ => by
    have := typed_keys h₁
    simp only [List.map_cons, List.cons.injEq] at this
    exact thaw_keys (w₁.keys.trans (this.2.trans lendCtx_keys))
  | .let_ _ ha hb => by
    have := typed_keys hb
    simp only [List.map_cons, List.cons.injEq] at this
    exact this.2.trans (typed_keys ha)
  | .write ha _ => atom_keys ha
  | .assign ha _ _ => atom_keys ha
  | .rlnew _ _ _ => rfl
  | .rpush _ _ _ _ _ => rfl
  | .rnth _ _ _ _ _ => rfl
  | .rlen _ _ _ => rfl
  | .vnew _ => rfl
  | .vlen _ => rfl
  | .vpush ha _ => atom_keys ha
  | .vpop _ _ => rfl
  | .lendSlice _ _ _ _ hb => by
    have := typed_keys hb
    simp only [List.map_cons, List.cons.injEq] at this
    exact thaw_keys (this.2.trans freeze_keys)
  | .call _ _ _ _ hargs _ _ => atoms_keys hargs
  | .lam _ _ _ _ _ ha _ => atom_keys ha
  | .lendClo _ _ _ _ _ _ _ _ hb => by
    have := typed_keys hb
    simp only [List.map_cons, List.cons.injEq] at this
    exact thaw_keys (this.2.trans freeze_keys)
  | .gen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hargs _ hb _ => by
    have := typed_keys hb
    exact (thaw_keys (this.trans freeze_keys)).trans (atoms_keys hargs)
  | .lendCloMut _ _ _ _ _ _ _ _ _ hb => by
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
  | .lend _ _ _ _ _ hb => by
    have := typed_keys hb
    simp only [List.map_cons, List.cons.injEq] at this
    exact thaw_keys (this.2.trans lendCtx_keys)
  | .lendIdx _ _ _ _ _ _ hb => by
    have := typed_keys hb
    simp only [List.map_cons, List.cons.injEq] at this
    exact thaw_keys (this.2.trans lendCtx_keys)
  | .lendField _ _ _ _ _ _ hb => by
    have := typed_keys hb
    simp only [List.map_cons, List.cons.injEq] at this
    exact thaw_keys (this.2.trans (setSlot_keys _))
  | .perform _ _ hargs _ _ => atoms_keys hargs
  | .handle _ _ _ _ _ _ _ _ hb =>
    unhideAll_keys ((thaw_keys ((typed_keys hb).trans freeze_keys)).trans hideAll_keys)
  | .handleR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb =>
    unhideAll_keys ((thaw_keys ((typed_keys hb).trans freeze_keys)).trans hideAll_keys)
  | .handleAbort _ _ _ _ hb hh => by
    have := typed_keys hh
    simp only [List.map_cons, List.cons.injEq] at this
    exact this.2.trans (typed_keys hb)
  | .par _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hargs _ => atoms_keys hargs
  | .region _ _ hb => by
    have := typed_keys hb
    simpa [Ctx.shift, Function.comp_def] using this
  | .ralloc _ _ _ _ => rfl
  | .rget _ _ _ _ => rfl
  | .rset _ _ _ _ _ => rfl

theorem lookup_det {α : Type} {x : Var} {a b : α} {env : List (Var × α)} : lookup x env = some a → lookup x env = some b → a = b := by
  intro h1 h2; rw [h1] at h2; exact Option.some.inj h2

/-- A pair's tree, one field of it lent: the field's tree, and the pair's with a hole there; and the
pair's tree again, the field filled with what the borrow left, once it ends. -/
theorem split_field (t : Bool) (hL : LT F ι σ a (.pair A B) L) :
    ∃ b c Rt Ro, σ.mem a = some (.pair b c) ∧ LT F ι σ (if t then b else c) (if t then A else B) Rt ∧
      LT F ι σ a (Ty.lent1 t A B) (a :: Ro) ∧ L.Perm (a :: (Rt ++ Ro)) ∧ Disj Rt Ro ∧ a ∉ Rt ++ Ro ∧
      ∀ σ' Ro' Rx, σ'.mem a = σ.mem a → LT F ι σ' a (Ty.lent1 t A B) (a :: Ro') →
        LT F ι σ' (if t then b else c) (if t then A else B) Rx → Disj Rx Ro' → a ∉ Rx ++ Ro' →
        ∃ L', LT F ι σ' a (.pair A B) L' ∧ L'.Perm (a :: (Rx ++ Ro')) := by
  cases hL with
  | pair ha h1 h2 hd hn =>
    rename_i b c R₁ R₂
    cases t with
    | true =>
      have hlt : LT F ι σ a (Ty.lent1 true A B) (a :: R₂) := by
        have := LT.pair ha (.hole (τ := A)) h2 (by simp)
          (fun h => hn (List.mem_append.mpr (.inr (by simpa using h))))
        simpa [Ty.lent1] using this
      refine ⟨b, c, R₁, R₂, ha, h1, hlt, .refl _, hd, hn, ?_⟩
      intro σ' Ro' Rx hag hL' hx hd' hn'
      simp only [Ty.lent1, ↓reduceIte] at hL'
      cases hL' with
      | pair ha' g1 g2 _ _ =>
        rw [hag, ha] at ha'; cases ha'
        cases g1
        exact ⟨_, .pair (hag.trans ha) hx g2 (fun z h h' => hd' z h (by simpa using h')) (by simpa using hn'), by simp⟩
    | false =>
      have hlt : LT F ι σ a (Ty.lent1 false A B) (a :: R₁) := by
        have := LT.pair ha h1 (.hole (τ := B)) (by simp)
          (fun h => hn (List.mem_append.mpr (.inl (by simpa using h))))
        simpa [Ty.lent1] using this
      refine ⟨b, c, R₂, R₁, ha, h2, hlt, List.Perm.cons _ List.perm_append_comm, fun x hx hx' => hd x hx' hx,
        fun h => hn (List.perm_append_comm.mem_iff.mp h), ?_⟩
      intro σ' Ro' Rx hag hL' hx hd' hn'
      simp only [Ty.lent1, Bool.false_eq_true, ↓reduceIte] at hL'
      cases hL' with
      | pair ha' g1 g2 _ _ =>
        rw [hag, ha] at ha'; cases ha'
        cases g2
        simp only [List.append_nil] at hd' hn' ⊢
        exact ⟨_, .pair (hag.trans ha) g1 hx (fun z h h' => hd' z h' h)
          (fun h => hn' (List.perm_append_comm.mem_iff.mp h)), List.Perm.cons _ List.perm_append_comm⟩

/-- A slot that may change all but its first cell holds that cell first. -/
theorem SlotOk.head_of_shell (h : SlotOk F ι σ s a L) (hs : s.shell = true) : ∃ R, L = a :: R := by
  match s, hs, h with
  | .ref .mut (.fn _ _ _ _), _, h => exact LT.cons h rfl
  | .half _ _ _, _, h => exact LT.cons h Ty.lent1_isHole

/-- A variable that may change all but its first cell, changed: the rest of the activation stands,
the variable owning the new tree, its first cell as it was and only read. -/
theorem foot_update_sh : Foot F ι σ Γ env E S → (Γ.map Prod.fst).Nodup → lookup x Γ = some s →
    s.shell = true →
    ∃ a R E₁ E₂, lookup x env = some a ∧ SlotOk F ι σ s a (a :: R) ∧ E = E₁ ++ R ++ E₂ ∧ a ∈ S ∧
      ∀ σ' R', Agree σ σ' (E₁ ++ E₂ ++ S) → SlotOk F ι σ' s a (a :: R') →
        Foot F ι σ' Γ env (E₁ ++ R' ++ E₂) S := by
  intro h
  induction h with
  | nil => simp [lookup]
  | @cons t a L Γ env E S y ht hrest ih =>
    intro hk hx hsh
    simp only [List.map_cons] at hk
    have hk' := (List.nodup_cons.mp hk).2
    by_cases hy : x = y
    · subst hy
      simp only [lookup, ↓reduceIte, Option.some.injEq] at hx
      subst hx
      obtain ⟨R, rfl⟩ := ht.head_of_shell hsh
      have hex := Slot.shell_excl hsh
      refine ⟨a, R, [], E, by simp [lookup], ht, by simp [addE, exclPart, hex, hsh], by simp [addS, sharedPart, hex, hsh], ?_⟩
      intro σ' R' hag hs'
      have hrest' := hrest.frame (σ' := σ') ((hag.mono fun l hl => by
        simp only [List.nil_append, List.mem_append, addS, sharedPart, hex, hsh, ↓reduceIte, List.take_succ_cons,
          List.take_zero, List.cons_append, List.nil_append, List.mem_cons] at hl ⊢
        rcases hl with hl | hl
        · exact .inl hl
        · exact .inr (.inr hl)))
      have := Foot.cons (x := x) hs' hrest'
      simpa [addE, addS, exclPart, sharedPart, hex, hsh] using this
    · simp only [lookup, hy, ↓reduceIte] at hx
      obtain ⟨a', R, E₁, E₂, ha, hs, hE, haS, hupd⟩ := ih hk' hx hsh
      refine ⟨a', R, addE t L E₁, E₂, by simp [lookup, hy, ha], hs, by subst hE; simp [addE],
        mem_addS.mpr (.inr haS), ?_⟩
      intro σ' R' hag hs'
      have hL : Agree σ σ' L := hag.mono fun l hl => by
        rcases mem_parts (s := t) hl with h | h
        · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inl (mem_addE.mpr (.inl h)))))
        · exact List.mem_append.mpr (.inr (mem_addS.mpr (.inl h)))
      have hrest' := hupd σ' R' ((hag.mono fun l hl => by
        simp only [List.mem_append] at hl ⊢
        rcases hl with (hl | hl) | hl
        · exact .inl (.inl (mem_addE.mpr (.inr hl)))
        · exact .inl (.inr hl)
        · exact .inr (mem_addS.mpr (.inr hl)))) hs'
      have := Foot.cons (x := y) (ht.frame hL) hrest'
      simpa [addE, addS] using this

/-- At a place that may be changed, what the location holds may be replaced: the rest of the
activation stands, the variable the place is rooted at now owning the new tree. The place holds no
closure or no place lent, or is rooted at a variable that may change all it holds. -/
theorem replace_at (hI : Inv F ι σ Γ env E S) (hp : PlaceTy Γ p τ true r) (hc : τ.complete = true)
    (hτ : τ.isFn = false ∨ ∀ k A B r', lookup r Γ ≠ some (.ref .mut (.fn k A B r'))) :
    ∃ l R P E₁ E₂, resolve σ env p = some l ∧ LT F ι σ l τ R ∧ E.Perm (E₁ ++ (P ++ R) ++ E₂) ∧
      ∀ σ' R', Agree σ σ' (E₁ ++ P ++ E₂ ++ S) → LT F ι σ' l τ R' → Disj R' (E₁ ++ P ++ E₂) →
        Disj R' S → ∃ E', Inv F ι σ' Γ env E' S ∧ E'.Perm (E₁ ++ (P ++ R') ++ E₂) := by
  obtain ⟨a, τr, Lr, Pf, l, s, ha, hLr, hpath, hres, -, -, hs, hso, hex, hlt, hshp, hty⟩ := place_ok hp hI.foot
  obtain ⟨R, hR, hLrp⟩ := path_split hpath hLr
  -- The cells the root keeps, and how the root takes a new tree at the place.
  have key : ∃ P E₁ E₂, E.Perm (E₁ ++ (P ++ R) ++ E₂) ∧ (∀ z ∈ P, z ∈ Pf) ∧
      ∀ σ' R', Agree σ σ' (E₁ ++ P ++ E₂ ++ S) → LT F ι σ' l τ R' → Disj R' (E₁ ++ P ++ E₂) → Disj R' S →
        ∃ M, Foot F ι σ' Γ env (E₁ ++ M ++ E₂) S ∧ M.Perm (P ++ R') := by
    have hPn : Pf.Nodup := (nodup_append_disj.mp (hLrp.nodup_iff.mp hLr.nodup)).1
    cases hshb : s.shell
    · obtain ⟨a', L', E₁, E₂, ha', hso', hE, hupd⟩ := foot_update hI.foot hI.keys hs (hex rfl) hshb
      cases lookup_det ha ha'
      cases hso.det hso'
      refine ⟨Pf, E₁, E₂, by rw [hE]; exact (hLrp.append_left E₁).append_right E₂, fun _ h => h, ?_⟩
      intro σ' R' hag hR' hd hdS
      have hagP : Agree σ σ' Pf := (hag.mono fun x hx => by simp [hx])
      have hdP : Disj Pf R' := fun x hx hx' => hd x hx' (by simp [hx])
      obtain ⟨L'', hlt', hL''p, -⟩ := path_join hpath hPn hagP hR' hdP
      have hfoot := hupd σ' s L'' (hex rfl) hshb ((hag.mono fun x hx => by
        simp only [List.mem_append] at hx ⊢
        rcases hx with (hx | hx) | hx
        · exact .inl (.inl (.inl hx))
        · exact .inl (.inr hx)
        · exact .inr hx)) (hlt σ' _ hlt')
      rw [setSlot_same Γ hI.keys hs] at hfoot
      exact ⟨L'', hfoot, hL''p⟩
    · -- The place lies past the root's first cell, which stays as it was.
      have hpast : ∃ P', Pf = a :: P' := by
        rcases hshp hshb with ⟨rfl, rfl⟩ | ⟨-, P', hP'⟩
        · exfalso
          rw [hty] at hc
          match s, hshb, hs with
          | .half _ _ _, _, _ => simp [Slot.ty, Ty.lent1_complete] at hc
          | .ref .mut (.fn _ _ _ _), _, hs =>
            rcases hτ with hfn | h
            · rw [hty] at hfn; simp [Slot.ty, Ty.isFn] at hfn
            · exact h _ _ _ _ hs
        · exact ⟨P', hP'⟩
      obtain ⟨P', rfl⟩ := hpast
      obtain ⟨a', R0, E₁, E₂, ha', hso', hE, haS, hupd⟩ := foot_update_sh hI.foot hI.keys hs hshb
      cases lookup_det ha ha'
      have hLr0 : Lr = a :: R0 := hso.det hso'
      have hR0p : R0.Perm (P' ++ R) := by
        rw [hLr0] at hLrp; simpa using hLrp
      refine ⟨P', E₁, E₂, by rw [hE]; exact (hR0p.append_left E₁).append_right E₂,
        fun z hz => List.mem_cons_of_mem _ hz, ?_⟩
      intro σ' R' hag hR' hd hdS
      have hagP : Agree σ σ' (a :: P') := hag.mono fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · simp [haS]
        · simp [hx]
      have hdP : Disj (a :: P') R' := fun x hx hx' => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hdS x hx' haS
        · exact hd x hx' (by simp [hx])
      obtain ⟨L'', hlt', hL''p, -⟩ := path_join hpath hPn hagP hR' hdP
      have hτr : τr.isHole = false := by rw [hty]; match s, hshb with
        | .ref .mut (.fn _ _ _ _), _ => rfl
        | .half _ _ _, _ => exact Ty.lent1_isHole
      obtain ⟨R'', rfl⟩ := hlt'.cons hτr
      have hfoot := hupd σ' R'' ((hag.mono fun x hx => by
        simp only [List.mem_append] at hx ⊢
        rcases hx with (hx | hx) | hx
        · exact .inl (.inl (.inl hx))
        · exact .inl (.inr hx)
        · exact .inr hx)) (hlt σ' _ hlt')
      exact ⟨R'', hfoot, by simpa using hL''p⟩
  obtain ⟨P, E₁, E₂, hEp, hPf, hupd⟩ := key
  refine ⟨l, R, P, E₁, E₂, hres, hR, hEp, ?_⟩
  intro σ' R' hag hR' hd hdS
  have hnd := hEp.nodup_iff.mp hI.nodup
  have hdP : Disj P R' := fun x hx hx' => hd x hx' (by simp [hx])
  obtain ⟨M, hfoot, hMp⟩ := hupd σ' R' hag hR' hd hdS
  have hE' : (E₁ ++ M ++ E₂).Perm (E₁ ++ (P ++ R') ++ E₂) := (hMp.append_left E₁).append_right E₂
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
