import FlyCore.OwnershipTasks

/-!
# Ownership: regions

A region's arena is a variable of the code it runs, whose footprint is the arena's cell and every cell
allocated in the region; a reference into it owns nothing and names its cell by the tag the store
keeps, which says which region the cell is of. Reading through a reference finds the cell among the
arena's; allocating adds one; the region's end frees them all, and nothing the code around keeps can
refer to them, for its types are said of fewer regions.
-/

namespace FlyCore.Ownership

/-! ## Region data -/

theorem RD.toVT {v : Val} (h : RD (ι.drop k) σ τ v) (hd : τ.rdata = true) : VT F ι σ (τ.shiftBy k) v [] := by
  cases τ with
  | int => cases v <;> simp only [RD] at h; exact .int
  | rref c j τ' =>
    cases v <;> simp only [RD] at h
    obtain ⟨a, ha, ht⟩ := h
    simp only [Iota.drop_arenas, List.getElem?_drop] at ha
    exact .rref ⟨a, by rw [Nat.add_comm]; exact ha, ht⟩
  | _ => simp [Ty.rdata] at hd

theorem VT.toRD {v : Val} (h : VT F ι σ (τ.shiftBy k) v L) (hd : τ.rdata = true) : L = [] ∧ RD (ι.drop k) σ τ v := by
  cases τ with
  | int => simp only [Ty.shiftBy] at h; cases h; exact ⟨rfl, trivial⟩
  | rref c j τ' =>
    simp only [Ty.shiftBy] at h
    cases h with
    | rref hr =>
      obtain ⟨a, ha, ht⟩ := hr
      refine ⟨rfl, a, ?_, ht⟩
      simp only [Iota.drop_arenas, List.getElem?_drop]; rw [Nat.add_comm]; exact ha
  | _ => simp [Ty.rdata] at hd

/-- An arena in reach: its cell, and every cell of the region tagged with it, each holding data of it. -/
theorem arena_of (hR : lookup R Γ = some s) (hs : s = .own (.arena k) true ∨ ∃ m, s = .ref m (.arena k))
    (hI : Inv F ι σ Γ env E S) :
    ∃ c cs, lookup R env = some c ∧ ι.arenas[k]? = some c ∧ σ.mem c = some (.arena cs) ∧ (c :: cs).Nodup ∧
      (∀ l ∈ cs, ∃ τ v, σ.rt l = some (c, τ) ∧ σ.mem l = some v ∧ RD (ι.drop k) σ τ v) ∧
      (∀ l x, σ.rt l = some (c, x) → l ∈ cs) ∧ SlotOk F ι σ s c (c :: cs) := by
  obtain ⟨c, L, he, hsl, -, -⟩ := foot_lookup hI.foot hR
  have hlt : LT F ι σ c (.arena k) L := by
    rcases hs with rfl | ⟨m, rfl⟩ <;> exact hsl
  cases hlt with
  | arena hk ha hnd hn hcs hex =>
    exact ⟨c, _, he, hk, ha, List.nodup_cons.mpr ⟨hn, hnd⟩, hcs, hex, hsl⟩

/-! ## Reading -/

theorem rget_ok (hp : PlaceTy Γ p (.rref c k τ) w y) (hR : lookup R Γ = some s)
    (hs : s = .own (.arena k) true ∨ ∃ m, s = .ref m (.arena k)) (hd : τ.rdata = true) (hI : Inv F ι σ Γ env E S) (hwf : WF σ) :
    Post F ι O σ E S Γ env (τ.shiftBy k) r hs' (evalS F O n hs' σ env (.rget p)) := by
  obtain ⟨a, τr, Lr, P, l, s', ha, hLr, hpath, hres, -⟩ := place_ok hp hI.foot
  obtain ⟨Rb, hRb, -⟩ := path_split hpath hLr
  cases hRb with
  | @rref _ c _ _ _ hl hr =>
    obtain ⟨a', hk, ht⟩ := hr
    obtain ⟨c', cs, -, hk', -, -, hcs, hex, -⟩ := arena_of hR hs hI
    obtain rfl : a' = c' := Option.some.inj (hk.symm.trans hk')
    obtain ⟨τ', v, ht', hv, hrd⟩ := hcs c (hex c τ ht)
    rw [ht] at ht'
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj ht')
    simp only [evalS, hres, hl, hv]
    exact ⟨E, [], hI, hrd.toVT hd, disj_nil_left, disj_nil_left, Moves.refl hwf hI.alloc⟩

/-! ## Allocating -/

theorem Store.tag_mem {σ : Store} : (σ.tag l a τ).mem = σ.mem := by
  unfold Store.tag; split <;> rfl

theorem Store.tag_next {σ : Store} : (σ.tag l a τ).next = σ.next := by
  unfold Store.tag; split <;> rfl

theorem Store.tag_rt {σ : Store} (h : a < σ.next ∧ l < σ.next) :
    (σ.tag l a τ).rt = fun k => if k = l then some (a, τ) else σ.rt k := by
  unfold Store.tag; rw [dif_pos h]

/-- Tagging a cell, never tagged, as a cell of a region whose arena the step may change. -/
theorem Moves.tag (hwf : WF σ) (hE : ∀ l ∈ E, σ.mem l ≠ none) (ha : a ∈ E) (hl : l < σ.next)
    (hn : σ.rt l = none) : Moves σ E (σ.tag l a τ) E [] where
  within := by intro x h; simp at h; exact .inl h
  next := by rw [Store.tag_next]; exact Nat.le_refl _
  wf := by intro x hx; rw [Store.tag_mem] at hx; rw [Store.tag_next]; exact hwf x hx
  frame := by intro x _ _; rw [Store.tag_mem]
  alloc := by
    intro x
    rw [Store.tag_mem]
    constructor
    · intro h
      by_cases hx : x ∈ E
      · exact .inr (.inl hx)
      · exact .inl ⟨h, hx⟩
    · rintro (⟨h, _⟩ | h | h)
      · exact h
      · exact hE x h
      · simp at h
  rt := by
    intro x y hx
    rw [Store.tag_rt ⟨hwf a (hE a ha), hl⟩]
    simp only
    split
    · subst_vars; rw [hn] at hx; cases hx
    · exact hx
  fresh := by
    intro x b y hx h0
    rw [Store.tag_rt ⟨hwf a (hE a ha), hl⟩] at hx
    simp only at hx
    split at hx
    · cases hx; exact .inl ha
    · rw [h0] at hx; cases hx

theorem lookup_setSlot_self : ∀ {Γ : Ctx}, lookup x Γ = some s → lookup x (setSlot Γ x s') = some s'
  | [], h => by simp [lookup] at h
  | (y, t) :: Γ, h => by
    by_cases hxy : x = y
    · subst hxy; simp [setSlot, lookup]
    · simp only [lookup, hxy, ↓reduceIte] at h
      have ih := lookup_setSlot_self (s' := s') h
      simp only [setSlot, List.map_cons, lookup] at ih ⊢
      rw [if_neg (Ne.symm hxy), if_neg hxy]
      exact ih

/-- An atom that moves nothing leaves the store as it was. -/
theorem AtomTy.same_store (h : AtomTy Γ a τ Γ') (hΓ : Γ' = Γ) (hev : evalAtom σ env a = some (v, σ1)) : σ1 = σ := by
  cases h with
  | lit => simp [evalAtom] at hev; exact hev.2.symm
  | read hp =>
    simp only [evalAtom] at hev
    split at hev <;> try contradiction
    split at hev <;> simp at hev <;> exact hev.2.symm
  | readRef hp =>
    simp only [evalAtom] at hev
    split at hev <;> try contradiction
    split at hev <;> simp at hev <;> exact hev.2.symm
  | move hx hc =>
    have h1 := lookup_setSlot_self (s' := .own τ false) hx
    rw [hΓ, hx] at h1
    simp at h1

/-- A new cell of the region of arena `R`, holding `v`, data of the region of type `τ`: tagged as the
region's, the arena one cell more, and a reference to it the value. -/
theorem region_alloc (hR : lookup R Γ = some s) (hs : s = .own (.arena k) true ∨ s = .ref .mut (.arena k))
    (hrd : RD (ι.drop k) σ τ v) (hc1 : lookup R env = some c1) (hcm1 : σ.mem c1 = some (.arena cs))
    (hI : Inv F ι σ Γ env E S) (hwf : WF σ) :
    Post F ι O σ E S Γ env (.rref b k τ) r hs'
      (let (l, σ2) := σ.alloc v
       (.val (.rptr l), (σ2.set c1 (some (.arena (cs ++ [l])))).tag l c1 τ)) := by
  have hex' : s.excl = true ∧ s.shell = false := by rcases hs with rfl | rfl <;> simp [Slot.excl, Slot.shell, Ty.shell]
  obtain ⟨c0, LR, E₁a, E₂a, hc0, hsl, hE, hupd⟩ := foot_update hI.foot hI.keys hR hex'.1 hex'.2
  obtain ⟨c, cs', hc, hk, hcm, hnd, hcs, hexa, hsl'⟩ :=
    arena_of hR (by rcases hs with h | h; exact .inl h; exact .inr ⟨_, h⟩) hI
  obtain rfl : c = c1 := Option.some.inj (hc.symm.trans hc1)
  obtain rfl : cs = cs' := by rw [hcm1] at hcm; cases hcm; rfl
  have hcc : c0 = c := by rw [hc] at hc0; exact (Option.some.inj hc0).symm
  subst c0
  have hLT : ∀ {σ' : Store} {L : List Nat}, SlotOk F ι σ' s c L → LT F ι σ' c (.arena k) L := fun h => by
    rcases hs with rfl | rfl <;> exact h
  obtain rfl : LR = c :: cs := (hLT hsl).det (hLT hsl')
  -- Where the new cell is, and what changed.
  generalize hl : σ.next = l
  have hnd' := nodup_append_disj.mp (hE ▸ hI.nodup)
  have hcE : c ∈ E := by rw [hE]; simp
  have hfresh : ∀ x, σ.mem x ≠ none → x ≠ l := fun x hx e => by
    subst e; exact Nat.lt_irrefl _ (hl ▸ hwf x hx)
  have hlcs : l ∉ c :: cs := fun h => hfresh l (hI.alloc l (by
    rw [hE]; simp only [List.mem_append, List.mem_cons] at h ⊢; grind)) rfl
  have hrtl : σ.rt l = none := by
    cases h : σ.rt l with
    | none => rfl
    | some x => exact absurd (hl ▸ (σ.rtwf l x.1 x.2 h).2) (Nat.lt_irrefl _)
  let σ2 := (σ.alloc v).2
  let σ3 := σ2.set c (some (.arena (cs ++ [l])))
  have hσ2l : (σ.alloc v).1 = l := hl
  rw [show (σ.alloc v) = (l, σ2) from Prod.ext hσ2l rfl]
  have hcl : c ≠ l := fun e => hlcs (by simp [e])
  have hca : σ.mem c ≠ none := by rw [hcm]; simp
  have hcn : c < σ.next := hwf c hca
  have hm3 : ∀ x, σ3.mem x = if x = c then some (.arena (cs ++ [l])) else if x = l then some v else σ.mem x := by
    intro x
    simp only [σ3, σ2, Store.set, Store.alloc, hl]
  have hn3 : σ3.next = l + 1 := by simp only [σ3, σ2, Store.set, Store.alloc, hl]
  have hrt3 : σ3.rt = σ.rt := rfl
  have htag : c < σ3.next ∧ l < σ3.next := ⟨by omega, by omega⟩
  have hrt' : (σ3.tag l c τ).rt = fun x => if x = l then some (c, τ) else σ.rt x := Store.tag_rt htag
  have hmem' : (σ3.tag l c τ).mem = σ3.mem := Store.tag_mem
  -- The arena, one cell more.
  have hLT' : LT F ι (σ3.tag l c τ) c (.arena k) (c :: (cs ++ [l])) := by
    refine .arena hk (by rw [hmem', hm3]; simp) ?_ ?_ (fun x hx => ?_) (fun x y hx => ?_)
    · exact List.nodup_append.mpr ⟨(List.nodup_cons.mp hnd).2, by simp,
        fun x hx y hy e => by simp at hy; subst hy; subst e; exact hlcs (List.mem_cons_of_mem _ hx)⟩
    · intro h
      rcases List.mem_append.mp h with h | h
      · exact (List.nodup_cons.mp hnd).1 h
      · simp at h; exact hcl h
    · rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨τ', w, h1, h2, h3⟩ := hcs x hx
        have hxl : x ≠ l := fun e => hlcs (List.mem_cons_of_mem _ (e ▸ hx))
        have hxc : x ≠ c := fun e => (List.nodup_cons.mp hnd).1 (e ▸ hx)
        refine ⟨τ', w, by rw [hrt']; simp [hxl, h1], by rw [hmem', hm3]; simp [hxc, hxl, h2], h3.frame ?_⟩
        intro z y hz; rw [hrt']; simp only; split
        · subst_vars; rw [hrtl] at hz; cases hz
        · exact hz
      · simp at hx; subst hx
        refine ⟨τ, v, by rw [hrt']; simp, by rw [hmem', hm3]; simp [Ne.symm hcl], hrd.frame ?_⟩
        intro z y hz; rw [hrt']; simp only; split
        · subst_vars; rw [hrtl] at hz; cases hz
        · exact hz
    · rw [hrt'] at hx
      simp only at hx
      split at hx
      · subst_vars; simp
      · exact List.mem_append.mpr (.inl (hexa x y hx))
  -- The rest of the activation, as it was.
  have hout : ∀ x ∈ E₁a ++ E₂a ++ S, x ≠ c ∧ x ≠ l := by
    intro x hx
    refine ⟨fun e => ?_, fun e => ?_⟩
    · subst e
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_append.mp hx with hx | hx
        · exact hnd'.1 |> fun h => (nodup_append_disj.mp h).2.2 x hx (by simp)
        · exact hnd'.2.2 x (by simp) hx
      · exact hI.disj x hx hcE
    · subst e
      rcases List.mem_append.mp hx with hx | hx
      · exact hfresh x (hI.alloc x (by rw [hE]; rcases List.mem_append.mp hx with h | h <;> simp [h])) rfl
      · exact hfresh x (hI.allocS x hx) rfl
  have hag : Agree σ (σ3.tag l c τ) (E₁a ++ E₂a ++ S) := by
    refine ⟨fun x hx => ?_, fun z y hz => ?_, fun b hb z y hz => ?_⟩
    · rw [hmem', hm3, if_neg (hout x hx).1, if_neg (hout x hx).2]
    · rw [hrt']; simp only; split
      · subst_vars; rw [hrtl] at hz; cases hz
      · exact hz
    · rw [hrt'] at hz; simp only at hz
      split at hz
      · obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hz); exact absurd rfl (hout _ hb).1
      · exact hz
  have hfoot := hupd (σ3.tag l c τ) s (c :: (cs ++ [l])) hex'.1 hex'.2 hag (by rcases hs with rfl | rfl <;> exact hLT')
  rw [setSlot_same _ hI.keys hR] at hfoot
  have hnd2 : (E₁a ++ c :: (cs ++ [l]) ++ E₂a).Nodup := by
    have h0 : (E₁a ++ c :: cs ++ E₂a).Nodup := hE ▸ hI.nodup
    have hp : (E₁a ++ c :: (cs ++ [l]) ++ E₂a).Perm (l :: (E₁a ++ c :: cs ++ E₂a)) := by
      have : E₁a ++ c :: (cs ++ [l]) ++ E₂a = (E₁a ++ c :: cs) ++ l :: E₂a := by simp
      rw [this]; exact List.perm_middle
    refine hp.nodup_iff.mpr (List.nodup_cons.mpr ⟨fun h => ?_, h0⟩)
    exact hfresh l (hI.alloc l (hE ▸ h)) rfl
  refine ⟨E₁a ++ (c :: (cs ++ [l])) ++ E₂a, [], ⟨hfoot, hnd2, ?_, hI.keys⟩, .rref ⟨c, hk, by rw [hrt']; simp⟩,
    disj_nil_left, disj_nil_left, ?_⟩
  · intro x hx hx'
    rcases List.mem_append.mp hx' with hx' | hx'
    · rcases List.mem_append.mp hx' with hx' | hx'
      · exact hI.disj x hx (by rw [hE]; simp [hx'])
      · simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at hx'
        rcases hx' with rfl | hx' | rfl
        · exact hI.disj x hx hcE
        · exact hI.disj x hx (by rw [hE]; simp [hx'])
        · exact hfresh x (hI.allocS x hx) rfl
    · exact hI.disj x hx (by rw [hE]; simp [hx'])
  · have m1 := Moves.allocate (v := v) hwf hI.alloc
    have m2 := Moves.set (σ := σ2) (l := c) (v := .arena (cs ++ [l])) m1.wf
      (fun x hx => (m1.alloc x).mpr (.inr (.inl hx))) hcE
    have m3 := Moves.tag (σ := σ3) (a := c) (l := l) (τ := τ) m2.wf (fun x hx => (m2.alloc x).mpr (.inr (.inl hx))) hcE
      (by omega) (by rw [hrt3]; exact hrtl)
    have m12 := m1.trans m2 (fun x hx hx' => by
      simp at hx; subst hx; exact hfresh _ (hI.alloc _ hx') (by rw [hl])) hwf
    have m123 := m12.trans m3 (fun x hx hx' => by
      simp at hx; subst hx; exact hfresh _ (hI.alloc _ hx') (by rw [hl])) hwf
    exact m123.relabel fun x => by
      rw [hE]; simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, hl]; grind

theorem ralloc_ok (hR : lookup R Γ = some s) (hs : s = .own (.arena k) true ∨ s = .ref .mut (.arena k))
    (hd : τ.rdata = true) (ha : AtomTy Γ a (τ.shiftBy k) Γ) (hI : Inv F ι σ Γ env E S) (hwf : WF σ) :
    Post F ι O σ E S Γ env (.rref c k τ) r hs' (evalS F O n hs' σ env (.ralloc R c τ a)) := by
  obtain ⟨v, σ1, E₁, L₁, hev, -, hv₁, -, -, -⟩ := atom_ok ha hI hwf
  obtain rfl : σ = σ1 := (ha.same_store rfl hev).symm
  obtain ⟨rfl, hrd⟩ := hv₁.toRD hd
  obtain ⟨c1, cs, hc1, -, hcm1, -⟩ := arena_of hR (by rcases hs with h | h; exact .inl h; exact .inr ⟨_, h⟩) hI
  simp only [evalS, hc1, hcm1, hev]
  exact region_alloc hR hs hrd hc1 hcm1 hI hwf

/-! ## Changing a cell -/

/-- A cell of the region of arena `R`, tagged as holding a `τ`, given another `τ`: nothing else
changes, and the arena, which owns the cell, is still well formed. -/
theorem region_set (hR : lookup R Γ = some s) (hs : s = .own (.arena k) true ∨ s = .ref .mut (.arena k))
    (hk : ι.arenas[k]? = some a') (ht : σ.rt l = some (a', τ)) (hrd : RD (ι.drop k) σ τ v)
    (hI : Inv F ι σ Γ env E S) (hwf : WF σ) :
    Inv F ι (σ.set l (some v)) Γ env E S ∧ Moves σ E (σ.set l (some v)) E [] ∧ ∃ w, σ.mem l = some w := by
  have hex' : s.excl = true ∧ s.shell = false := by rcases hs with rfl | rfl <;> simp [Slot.excl, Slot.shell, Ty.shell]
  obtain ⟨c0, LR, E₁a, E₂a, hc0, hsl, hE, hupd⟩ := foot_update hI.foot hI.keys hR hex'.1 hex'.2
  obtain ⟨c, cs, hc, hk', hcm, hnd, hcs, hexa, hsl'⟩ :=
    arena_of hR (by rcases hs with h | h; exact .inl h; exact .inr ⟨_, h⟩) hI
  have hcc : c0 = c := by rw [hc] at hc0; exact (Option.some.inj hc0).symm
  subst c0
  have hac : a' = c := Option.some.inj (hk.symm.trans hk')
  subst a'
  have hLT : ∀ {σ' : Store} {L : List Nat}, SlotOk F ι σ' s c L → LT F ι σ' c (.arena k) L := fun h => by
    rcases hs with rfl | rfl <;> exact h
  obtain rfl : LR = c :: cs := (hLT hsl).det (hLT hsl')
  have hlcs : l ∈ cs := hexa l τ ht
  obtain ⟨τ', w0, ht', hw0, -⟩ := hcs l hlcs
  let σ' := σ.set l (some v)
  have hm' : ∀ x, σ'.mem x = if x = l then some v else σ.mem x := by intro x; simp only [σ', Store.set]
  have hrt' : σ'.rt = σ.rt := rfl
  have hlc : l ≠ c := fun e => (List.nodup_cons.mp hnd).1 (e ▸ hlcs)
  have hnd' := nodup_append_disj.mp (hE ▸ hI.nodup)
  have hlE : l ∈ E := by rw [hE]; simp [hlcs]
  have hout : ∀ x ∈ E₁a ++ E₂a ++ S, x ≠ l := by
    intro x hx e
    subst e
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact (nodup_append_disj.mp hnd'.1).2.2 x hx (by simp [hlcs])
      · exact hnd'.2.2 x (by simp [hlcs]) hx
    · exact hI.disj x hx hlE
  have hag : Agree σ σ' (E₁a ++ E₂a ++ S) := Agree.of (fun x hx => by rw [hm', if_neg (hout x hx)]) hrt'
  have hLT' : LT F ι σ' c (.arena k) (c :: cs) := by
    refine .arena hk' (by rw [hm', if_neg (Ne.symm hlc)]; exact hcm) (List.nodup_cons.mp hnd).2
      (List.nodup_cons.mp hnd).1 (fun x hx => ?_) (fun x y hx => hexa x y hx)
    by_cases hxl : x = l
    · subst hxl
      rw [ht] at ht'
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj ht')
      exact ⟨τ, v, ht, by rw [hm']; simp, hrd.frame (fun _ _ h => h)⟩
    · obtain ⟨τ'', w, h1, h2, h3⟩ := hcs x hx
      exact ⟨τ'', w, h1, by rw [hm', if_neg hxl]; exact h2, h3.frame (fun _ _ h => h)⟩
  have hfoot := hupd σ' s (c :: cs) hex'.1 hex'.2 hag (by rcases hs with rfl | rfl <;> exact hLT')
  rw [setSlot_same _ hI.keys hR, ← hE] at hfoot
  exact ⟨⟨hfoot, hI.nodup, hI.disj, hI.keys⟩, Moves.set hwf hI.alloc hlE, w0, hw0⟩

/-- `p.set(a)`: the cell `p` refers to is one of its region's, which the arena it is changed through
owns, so nothing else sees it change; what it holds next is data of the region as what it held was. -/
theorem rset_ok (hp : PlaceTy Γ p (.rref true k τ) w y) (hR : lookup R Γ = some s)
    (hs : s = .own (.arena k) true ∨ s = .ref .mut (.arena k)) (hd : τ.rdata = true)
    (ha : AtomTy Γ a (τ.shiftBy k) Γ) (hI : Inv F ι σ Γ env E S) (hwf : WF σ) :
    Post F ι O σ E S Γ env .int r hs' (evalS F O n hs' σ env (.rset R p a)) := by
  obtain ⟨v, σ1, E₁, L₁, hev, -, hv₁, -, -, -⟩ := atom_ok ha hI hwf
  obtain rfl : σ = σ1 := (ha.same_store rfl hev).symm
  obtain ⟨-, hrd⟩ := hv₁.toRD hd
  obtain ⟨a0, τr, Lr, P, q, s', -, hLr, hpath, hres, -⟩ := place_ok hp hI.foot
  obtain ⟨Rb, hRb, -⟩ := path_split hpath hLr
  cases hRb with
  | @rref _ l _ _ _ hql hr =>
  obtain ⟨a', hk, ht⟩ := hr
  obtain ⟨hI', hm', w0, hw0⟩ := region_set hR hs hk ht hrd hI hwf
  simp only [evalS, hev, hres, hql, hw0]
  exact ⟨E, [], hI', .int, disj_nil_left, disj_nil_left, hm'⟩


/-! ## A region's lists -/

/-- `RegionList.new()`: a new cell of the region, an empty list of it. -/
theorem rlnew_ok (hR : lookup R Γ = some s) (hs : s = .own (.arena k) true ∨ s = .ref .mut (.arena k))
    (hI : Inv F ι σ Γ env E S) (hwf : WF σ) :
    Post F ι O σ E S Γ env (.rref false k (.vec true τ)) r hs' (evalS F O n hs' σ env (.rlnew R τ)) := by
  obtain ⟨c1, cs, hc1, -, hcm1, -⟩ := arena_of hR (by rcases hs with h | h; exact .inl h; exact .inr ⟨_, h⟩) hI
  simp only [evalS, hc1, hcm1]
  exact region_alloc (v := .vec []) (τ := .vec true τ) hR hs (by simp [RD]) hc1 hcm1 hI hwf

/-- A list of a region a place holds a reference to: its cell holds its elements' cells, each a cell
of the region holding a `τ`. -/
theorem list_of (hp : PlaceTy Γ p (.rref c k (.vec true τ)) w y) (hR : lookup R Γ = some s)
    (hs : s = .own (.arena k) true ∨ ∃ m, s = .ref m (.arena k)) (hI : Inv F ι σ Γ env E S) :
    ∃ q lc ls a cs, resolve σ env p = some q ∧ σ.mem q = some (.rptr lc) ∧ σ.mem lc = some (.vec ls) ∧
      σ.rt lc = some (a, .vec true τ) ∧ ι.arenas[k]? = some a ∧ lookup R env = some a ∧ σ.mem a = some (.arena cs) ∧
      (∀ l ∈ ls, l ∈ cs ∧ σ.rt l = some (a, τ)) ∧
      (∀ l ∈ cs, ∃ τ v, σ.rt l = some (a, τ) ∧ σ.mem l = some v ∧ RD (ι.drop k) σ τ v) := by
  obtain ⟨a0, τr, Lr, P, q, s', -, hLr, hpath, hres, -⟩ := place_ok hp hI.foot
  obtain ⟨Rb, hRb, -⟩ := path_split hpath hLr
  cases hRb with
  | @rref _ lc _ _ _ hql hr =>
  obtain ⟨a', hk, ht⟩ := hr
  obtain ⟨c1, cs, hc1, hk', hcm, -, hcs, hexa, -⟩ := arena_of hR hs hI
  obtain rfl : a' = c1 := Option.some.inj (hk.symm.trans hk')
  obtain ⟨τ', w0, ht', hw0, hrd⟩ := hcs lc (hexa lc _ ht)
  rw [ht] at ht'
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj ht')
  cases w0 <;> simp only [RD] at hrd
  rename_i ls
  refine ⟨q, lc, ls, a', cs, hres, hql, hw0, ht, hk, hc1, hcm, fun l hl => ?_, hcs⟩
  obtain ⟨b, hb, htl⟩ := hrd l hl
  simp only [Iota.drop_arenas, List.getElem?_drop, Nat.add_zero] at hb
  obtain rfl : b = a' := Option.some.inj (hb.symm.trans hk)
  exact ⟨hexa l _ htl, htl⟩

/-- `p[z]` for a list: out of bounds, a panic; else a copy of the element, data of the region. -/
theorem rnth_ok (hp : PlaceTy Γ p (.rref c k (.vec true τ)) w y) (hz : PlaceTy Γ (.var z) .int wz yz)
    (hR : lookup R Γ = some s) (hs : s = .own (.arena k) true ∨ ∃ m, s = .ref m (.arena k))
    (hd : τ.rdata = true) (hI : Inv F ι σ Γ env E S) (hwf : WF σ) :
    Post F ι O σ E S Γ env (τ.shiftBy k) r hs' (evalS F O n hs' σ env (.rnth R p z)) := by
  obtain ⟨q, lc, ls, a, cs, hres, hq, hlc, -, -, -, -, hls, hcs⟩ := list_of hp hR hs hI
  obtain ⟨az, τz, Lz, Pz, lz, sz, -, hLz, hpathz, hresz, -⟩ := place_ok hz hI.foot
  obtain ⟨Rz, hRz, -⟩ := path_split hpathz hLz
  cases hRz with
  | int hk0 =>
  rename_i i
  have hlz : lookup z env = some lz := hresz
  simp only [evalS, hres, hlz, hq, hk0, hlc]
  split
  · cases hget : ls[i.toNat]? with
    | none => simp [Post]
    | some l =>
      have hl : l ∈ ls := List.mem_of_getElem? hget
      obtain ⟨hlcs, htl⟩ := hls l hl
      obtain ⟨τ', v, ht', hv, hrd⟩ := hcs l hlcs
      rw [htl] at ht'
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj ht')
      simp only [hv]
      exact ⟨E, [], hI, hrd.toVT hd, disj_nil_left, disj_nil_left, Moves.refl hwf hI.alloc⟩
  · simp [Post]

/-- `p.len()` for a list. -/
theorem rlen_ok (hp : PlaceTy Γ p (.rref c k (.vec true τ)) w y) (hR : lookup R Γ = some s)
    (hs : s = .own (.arena k) true ∨ ∃ m, s = .ref m (.arena k)) (hI : Inv F ι σ Γ env E S) (hwf : WF σ) :
    Post F ι O σ E S Γ env .int r hs' (evalS F O n hs' σ env (.rlen R p)) := by
  obtain ⟨q, lc, ls, -, -, hres, hq, hlc, -⟩ := list_of hp hR hs hI
  simp only [evalS, hres, hq, hlc]
  exact ⟨E, [], hI, .int, disj_nil_left, disj_nil_left, Moves.refl hwf hI.alloc⟩

/-- `p.push(a)` for a list: `a` in a new cell of the region, tagged as holding a `τ`, and the list's
cell given that cell at its end. -/
theorem rpush_ok (hp : PlaceTy Γ p (.rref c k (.vec true τ)) w y) (hR : lookup R Γ = some s)
    (hs : s = .own (.arena k) true ∨ s = .ref .mut (.arena k)) (hd : τ.rdata = true)
    (ha : AtomTy Γ a (τ.shiftBy k) Γ) (hI : Inv F ι σ Γ env E S) (hwf : WF σ) :
    Post F ι O σ E S Γ env .int r hs' (evalS F O n hs' σ env (.rpush R τ p a)) := by
  obtain ⟨v, σ1, E₁, L₁, hev, -, hv₁, -, -, -⟩ := atom_ok ha hI hwf
  obtain rfl : σ = σ1 := (ha.same_store rfl hev).symm
  obtain ⟨-, hrd⟩ := hv₁.toRD hd
  obtain ⟨q, lc, ls, a', cs, hres, hq, hlc, htlc, hk, hc1, hcm, hls, -⟩ :=
    list_of hp hR (by rcases hs with h | h; exact .inl h; exact .inr ⟨_, h⟩) hI
  simp only [evalS, hc1, hev, hcm, hres, hq, hlc]
  have h1 := region_alloc (b := false) (O := O) (r := r) (hs' := hs') hR hs hrd hc1 hcm hI hwf
  simp only at h1
  generalize hl : (σ.alloc v).1 = l at h1 ⊢
  generalize hσ3 : ((σ.alloc v).2.set a' (some (.arena (cs ++ [l])))).tag l a' τ = σ3 at h1 ⊢
  obtain ⟨E', L, hI3, hvl, -, -, hm3⟩ := h1
  cases hvl with
  | rref hrl =>
  have hrt3 := hm3.rt
  obtain ⟨hI4, hm4, -⟩ := region_set (v := .vec (ls ++ [l])) hR hs hk (hrt3 _ _ htlc) (by
    intro l' hl'
    rcases List.mem_append.mp hl' with h | h
    · obtain ⟨-, htl⟩ := hls l' h
      exact ⟨a', by simpa [List.getElem?_drop] using hk, hrt3 _ _ htl⟩
    · simp at h; subst h
      exact RefOk.drop_iff.mp (by simpa using hrl)) hI3 hm3.wf
  exact ⟨E', [], hI4, .int, disj_nil_left, disj_nil_left, by simpa using hm3.trans hm4 disj_nil_left hwf⟩

/-! ## A region's end -/

/-- A region's body ended: its arena and cells are freed. What is left — the variables around, a
value of a type said of them — refers to none of them. -/
theorem ret_regionK (hR : Ready O hs r) (hwf : WF σ0) (hag : Agree σf σ0 S) (hSa : ∀ l ∈ S, σ0.mem l ≠ none)
    (hSd : Disj S Ein)
    (hp : Post F (ι.push a) O σ0 Ein S ((R, .own (.arena 0) true) :: Ctx.shift Γ) ((R, a) :: env) (τ.shiftBy 1) r hs res) :
    Post F ι O σ0 Ein S Γ env τ r hs (ret F O n hs (.regionK a) res) := by
  -- What the body left: the arena with its cells, and the variables around.
  have key : ∀ σ1 E' L, Inv F (ι.push a) σ1 ((R, .own (.arena 0) true) :: Ctx.shift Γ) ((R, a) :: env) E' S →
      Disj L E' → Moves σ0 Ein σ1 E' L →
      ∃ cs E'', σ1.mem a = some (.arena cs) ∧ Inv F ι ((σ1.freeAll cs).set a none) Γ env E'' S ∧
        Agree σ1 ((σ1.freeAll cs).set a none) L ∧ Disj L E'' ∧ Moves σ0 Ein ((σ1.freeAll cs).set a none) E'' L := by
    intro σ1 E' L hI hdL hm
    obtain ⟨LR, E'', S'', hsl, hfoot, hE', hS'⟩ := hI.foot.uncons
    simp only [SlotOk] at hsl
    cases hsl with
    | arena hk ha hnd hn hcs hex =>
    rename_i cs
    simp only [addE, addS, exclPart, sharedPart, Slot.excl, Slot.shell, Ty.shell, ↓reduceIte, Bool.false_eq_true,
      List.nil_append] at hE' hS'
    subst hE' hS'
    have hnd' := nodup_append_disj.mp hI.nodup
    let σ2 := (σ1.freeAll cs).set a none
    have hm2 : ∀ x, σ2.mem x = if x = a then none else if x ∈ cs then none else σ1.mem x := by
      intro x; simp only [σ2, Store.set, Store.freeAll_mem]
    have hkeep : ∀ x, x ∉ a :: cs → σ2.mem x = σ1.mem x := fun x hx => by
      rw [hm2]; simp only [List.mem_cons, not_or] at hx; simp [hx.1, hx.2]
    have hfree : ∀ x ∈ a :: cs, σ2.mem x = none := fun x hx => by
      rw [hm2]; rcases List.mem_cons.mp hx with rfl | hx
      · simp
      · simp [hx]
    have hrt2 : σ2.rt = σ1.rt := by simp only [σ2, Store.set_rt, Store.freeAll_rt]
    have hn2 : σ2.next = σ1.next := by simp only [σ2, Store.set, Store.freeAll_next]
    have hag2 : Agree σ1 σ2 (E'' ++ S) := Agree.of (fun x hx => hkeep x fun h => by
      rcases List.mem_append.mp hx with hx | hx
      · exact hnd'.2.2 x h hx
      · exact hI.disj x hx (List.mem_append.mpr (.inl h))) hrt2
    have hkeysΓ : (Γ.map Prod.fst).Nodup := by
      have := (List.nodup_cons.mp hI.keys).2
      simpa [Ctx.shift, Function.comp_def] using this
    refine ⟨cs, E'', ha, ⟨hfoot.unshift.frame hag2, hnd'.2.1, fun x hx h => hI.disj x hx (List.mem_append.mpr (.inr h)),
      hkeysΓ⟩, Agree.of (fun x hx => hkeep x fun h => hdL x hx (List.mem_append.mpr (.inl h))) hrt2,
      fun x hx h => hdL x hx (List.mem_append.mpr (.inr h)), ?_⟩
    have m3 := hm.relabel (E'' := L ++ ((a :: cs) ++ E'')) (L'' := []) fun x => by
      simp only [List.mem_append, List.not_mem_nil, or_false]; grind
    have m4 := Moves.free (σ := σ1) (σ' := σ2) (E := L ++ ((a :: cs) ++ E'')) (E' := L ++ E'') (D := a :: cs)
      (WF.of_free hm.wf hn2 hfree hkeep) hn2 (fun x hx => (m3.alloc x).mpr (.inr (.inl hx)))
      (fun x => by simp only [List.mem_append, List.mem_cons]; grind) hfree hkeep (fun x hx hx' => by
        rcases List.mem_append.mp hx with hx | hx
        · exact hdL x hx (List.mem_append.mpr (.inl hx'))
        · exact hnd'.2.2 x hx' hx) hrt2
    exact (m3.trans m4 disj_nil_left hwf).relabel fun x => by
      simp only [List.mem_append, List.not_mem_nil, or_false, List.append_nil]; grind
  rcases res with ⟨res, σ1⟩
  cases res with
  | val v =>
    obtain ⟨E', L, hI, hv, hdL, hdLS, hm⟩ := hp
    obtain ⟨cs, E'', ha, hI2, hagL, hdL2, hm2⟩ := key σ1 E' L hI hdL hm
    simp only [ret, ha]
    exact ⟨E'', L, hI2, (VT.unshift hv).frame hagL, hdL2, hdLS, hm2⟩
  | abort j k =>
    obtain ⟨haim, E', hI, hm⟩ := hp
    obtain ⟨cs, E'', ha, hI2, -, -, hm2⟩ := key σ1 E' [] hI disj_nil_left hm
    simp only [ret, ha]
    exact ⟨haim, E'', hI2, hm2⟩
  | susp j ef vs ls K =>
    obtain ⟨op, X, hos, A, Lw, hc, hop, -, haim, hK, hls, hvs, hn, hdw, hdS, hm⟩ := hp
    have hK' := FramesOk.cons (A := A) (σf := σ1)
      (FrameOk.regionK (F := F) (O := O) (a := a) (ι := ι) (R := R) (Γ := Γ) (env := env) (τ := τ) (S := S) (r := r))
      (Weaker.refl _) (Agree.self) (fun _ h => by simp at h) List.nodup_nil disj_nil_left hK
      (fun _ h => by simp at h) (fun a ha => .inl ha)
    simp only [List.nil_append] at hK'
    simp only [ret]
    exact ⟨op, X, hos, A, Lw, hc, hop, hR.2, haim, hK', hls, hvs.rfree_iota op.owns_rfree, hn, hdw, hdS, hm⟩
  | stuck => simp [Post] at hp
  | timeout => simp [ret, Post]
  | panic => simp [ret, Post]

/-! ## Entering a region -/

/-- `region (R) { body }`: a new arena, innermost, its region empty; the body runs with the code
around a region further out; as it ends, the region is released. -/
theorem region_ok [WorldOk F O ι.w] (hE : EvalOk F O n) (hR : RetOk F O n) (hx : lookup R Γ = none)
    (hb : Typed F O ((R, .own (.arena 0) true) :: Ctx.shift Γ) body (τ.shiftBy 1)
      ((R, .own (.arena 0) true) :: Ctx.shift Γ') r)
    (hI : Inv F ι σ Γ env E S) (hwf : WF σ) (hRdy : Ready O hs r) :
    Post F ι O σ E S Γ' env τ r hs (evalS F O n hs σ env (.region R τ body)) := by
  simp only [evalS]
  generalize ha : (σ.alloc (.arena [])).1 = a
  have hna : σ.next = a := ha
  generalize hσ1 : (σ.alloc (.arena [])).2 = σ1
  have hm1 : ∀ x, σ1.mem x = if x = a then some (.arena []) else σ.mem x := by
    intro x; rw [← hσ1, ← hna]; simp [Store.alloc]
  have hrt1 : σ1.rt = σ.rt := by rw [← hσ1]; rfl
  have hwf1 : WF σ1 := by rw [← hσ1]; exact hwf.alloc
  have hfresh : ∀ x, σ.mem x ≠ none → x ≠ a := fun x hx e => by
    subst e; exact Nat.lt_irrefl _ (hna ▸ hwf x hx)
  have hag1 : Agree σ σ1 (E ++ S) := Agree.of (fun x hx => by
    rw [hm1, if_neg (hfresh x (by
      rcases List.mem_append.mp hx with h | h
      · exact hI.alloc x h
      · exact hI.allocS x h))]) hrt1
  -- The arena, empty.
  have hLa : LT F (ι.push a) σ1 a (.arena 0) [a] := by
    refine .arena (by simp) (by rw [hm1]; simp) List.nodup_nil (by simp) (fun l hl => by simp at hl) ?_
    intro l x hl
    rw [hrt1] at hl
    have := (σ.rtwf l a x hl).1
    rw [hna] at this
    exact absurd this (Nat.lt_irrefl _)
  have hxs : R ∉ (Ctx.shift Γ).map Prod.fst := by rw [Ctx.shift_keys]; exact lookup_none_keys hx
  have hI1 : Inv F (ι.push a) σ1 ((R, .own (.arena 0) true) :: Ctx.shift Γ) ((R, a) :: env) (a :: E) S := by
    have hf := Foot.cons (s := .own (.arena 0) true) (x := R) (a := a) hLa ((hI.shift (a := a)).foot.frame hag1)
    refine ⟨by simpa [addE, addS, exclPart, sharedPart, Slot.excl, Slot.shell, Ty.shell] using hf,
      List.nodup_cons.mpr ⟨fun h => hfresh a (hI.alloc a h) rfl, hI.nodup⟩, fun x hx hx' => ?_,
      List.nodup_cons.mpr ⟨hxs, by rw [Ctx.shift_keys]; exact hI.keys⟩⟩
    rcases List.mem_cons.mp hx' with rfl | hx'
    · exact hfresh x (hI.allocS x hx) rfl
    · exact hI.disj x hx hx'
  have hp := hE hs σ1 (ι.push a) _ _ _ _ _ _ _ _ hb hI1 hwf1 hRdy
  have hSa1 : ∀ l ∈ S, σ1.mem l ≠ none := fun l hl => by
    rw [hag1 l (List.mem_append.mpr (.inr hl))]; exact hI.allocS l hl
  have h2 := hR hs (ι.push a) ι σ1 (.regionK a) _ ⟨Γ', env, τ, S, r⟩ [] [] σ1 (a :: E) _
    (FrameOk.regionK (R := R)) hRdy (fun _ h => by simp at h) hwf1 Agree.self (fun _ h => by simp at h)
    List.nodup_nil disj_nil_left hSa1 (fun x hx hx' => by
      simp only [List.nil_append] at hx'
      rcases List.mem_cons.mp hx' with rfl | hx'
      · exact hfresh x (hI.allocS x hx) rfl
      · exact hI.disj x hx hx') hp
  refine post_after ?_ hwf (by simpa using h2)
  rw [← hσ1, ← hna]
  exact (Moves.allocate hwf hI.alloc).relabel fun x => by simp; exact Or.comm

end FlyCore.Ownership
