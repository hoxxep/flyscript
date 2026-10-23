import FlyCore.OwnershipRegions

/-!
# Ownership: vectors

A vector is a variable's cell holding its elements' cells, each the root of an element's tree. As it
grows it moves every element to a new cell and frees the old one, as a vector reallocating its
storage does, so a borrow of an element kept across a push would be left with a freed cell: the
types keep any from being kept, for a borrow of an element is one of the whole vector.
-/

namespace FlyCore.Ownership

theorem LT.alloc_lt (h : LT F ι σ a τ L) (hwf : WF σ) : ∀ x ∈ L, x < σ.next :=
  fun x hx => hwf x (h.alloc x hx)

/-- Moving each element to a fresh cell keeps each element's tree, rooted at its new cell. -/
theorem moveAll_ok {τ : Ty} (hc : τ.complete = true) : ∀ (cs : List Nat) (Rs : List (List Nat)) (σ : Store),
    WF σ → Rs.length = cs.length → (∀ i (h : i < cs.length) (h' : i < Rs.length), LT F ι σ cs[i] τ Rs[i]) →
    Rs.flatten.Nodup →
    ∃ (Rs' : List (List Nat)) (σ' : Store), σ.moveAll cs = some (List.range' σ.next cs.length, σ') ∧ Rs'.length = cs.length ∧
      (∀ i (h : i < (List.range' σ.next cs.length).length) (h' : i < Rs'.length),
        LT F ι σ' (List.range' σ.next cs.length)[i] τ Rs'[i]) ∧ Rs'.flatten.Nodup ∧
      (∀ x, x ∈ Rs'.flatten ↔ (x ∈ Rs.flatten ∧ x ∉ cs) ∨ x ∈ List.range' σ.next cs.length) ∧
      (∀ x ∈ cs, σ'.mem x = none) ∧ (∀ x, x ∉ cs → x < σ.next → σ'.mem x = σ.mem x) ∧
      σ'.next = σ.next + cs.length ∧ σ'.rt = σ.rt ∧ WF σ'
  | [], Rs, σ, hwf, hlen, _, _ => by
    obtain rfl : Rs = [] := List.eq_nil_of_length_eq_zero hlen
    exact ⟨[], σ, rfl, rfl, fun i h => by simp at h, List.nodup_nil, by simp, by simp,
      fun _ _ _ => rfl, rfl, rfl, hwf⟩
  | c :: cs, Rs, σ, hwf, hlen, hel, hnd => by
    cases Rs with
    | nil => simp at hlen
    | cons R Rs =>
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    have hnd' := List.nodup_append.mp (by simpa using hnd)
    have h0 := hel 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero] at h0
    have hRlt := h0.alloc_lt hwf
    obtain ⟨w, R', hw, hv, rfl, hn⟩ := h0.contents hc
    -- Each other element's head is in its tree, which is apart from this one's.
    have hhead : ∀ i (h : i < cs.length) (h' : i < Rs.length), cs[i] ∈ Rs[i] := fun i h h' =>
      (hel (i + 1) (by simp; omega) (by simp; omega)).head (Ty.complete_not_hole hc)
    have hcs_out : ∀ x ∈ cs, x ∉ c :: R' := fun x hx hx' => by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      exact hnd'.2.2 _ hx' _ (mem_flatten_of (hlen ▸ hi) (hhead i hi (hlen ▸ hi))) rfl
    have hc_cs : c ∉ cs := fun h => hcs_out c h (List.mem_cons_self ..)
    let σ1 := (σ.alloc w).2
    let σ2 := σ1.set c none
    have hm2 : ∀ x, σ2.mem x = if x = c then none else if x = σ.next then some w else σ.mem x := by
      intro x; simp only [σ2, σ1, Store.set, Store.alloc]
    have hcn : c < σ.next := hwf c (by rw [hw]; simp)
    have hwf2 : WF σ2 := (hwf.alloc).set_none
    have hn2 : σ2.next = σ.next + 1 := rfl
    have hel2 : ∀ i (h : i < cs.length) (h' : i < Rs.length), LT F ι σ2 cs[i] τ Rs[i] := fun i h h' => by
      have hi := hel (i + 1) (by simp; omega) (by simp; omega)
      simp only [List.getElem_cons_succ] at hi
      refine hi.frame (Agree.of (fun x hx => ?_) rfl)
      have hxc : x ≠ c := fun e => hnd'.2.2 c (List.mem_cons_self ..) x (mem_flatten_of h' hx) e.symm
      have hxn : x ≠ σ.next := fun e => Nat.lt_irrefl _ (e ▸ hi.alloc_lt hwf x hx)
      rw [hm2]; simp [hxc, hxn]
    obtain ⟨Rs'', σ3, hmv, hlen', hel', hnd'', hmem'', hfree, hkeep, hn3, hrt3, hwf3⟩ :=
      moveAll_ok hc cs Rs σ2 hwf2 hlen hel2 hnd'.2.1
    rw [hn2] at hmv hel' hmem'' hn3
    -- The moved element: its new cell holds what the old one did, and its tree is as it was.
    have hRsn : ∀ x ∈ Rs.flatten, x < σ.next := fun x hx => by
      obtain ⟨i, hi, hx⟩ := mem_flatten_idx.mp hx
      have := hel (i + 1) (by simp; omega) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      exact this.alloc_lt hwf x hx
    have hcs_lt : ∀ x ∈ cs, x < σ.next := fun x hx => by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      exact hRsn _ (mem_flatten_of (hlen ▸ hi) (hhead i hi (hlen ▸ hi)))
    have hR'n : ∀ x ∈ R', x < σ.next := fun x hx => hRlt x (List.mem_cons_of_mem _ hx)
    have hold3 : ∀ x, x ∉ cs → x ≠ c → x < σ.next → σ3.mem x = σ.mem x := fun x h1 h2 h3 => by
      rw [hkeep x h1 (by rw [hn2]; omega), hm2]; simp [h2, Nat.ne_of_lt h3]
    have hnew3 : σ3.mem σ.next = some w := by
      rw [hkeep σ.next (fun h => Nat.lt_irrefl _ (hcs_lt _ h)) (by rw [hn2]; omega), hm2]
      simp [Nat.ne_of_gt hcn]
    have hrt3' : σ3.rt = σ.rt := hrt3
    have hagR' : Agree σ σ3 R' := Agree.of (fun x hx =>
      hold3 x (fun h => hcs_out x h (List.mem_cons_of_mem _ hx)) (fun e => hn (e ▸ hx)) (hR'n x hx)) hrt3'
    have hnR' : σ.next ∉ R' := fun h => Nat.lt_irrefl _ (hR'n _ h)
    have hLT0 : LT F ι σ3 σ.next τ (σ.next :: R') := LT.of_contents hnew3 (hv.frame hagR') hnR'
    have hrange : List.range' σ.next (cs.length + 1) = σ.next :: List.range' (σ.next + 1) cs.length := by
      simp [List.range'_succ]
    refine ⟨(σ.next :: R') :: Rs'', σ3, ?_, by simp [hlen'], ?_, ?_, ?_, ?_, ?_, by rw [hn3]; simp; omega, hrt3', hwf3⟩
    · simp only [List.length_cons]
      rw [hrange]
      simp only [Store.moveAll, hw]
      rw [hmv]
      rfl
    · intro i h h'
      cases i with
      | zero => simp only [List.getElem_range', List.getElem_cons_zero]; simpa using hLT0
      | succ i =>
        have := hel' i (by simp at h ⊢; omega) (by simpa using h')
        simp only [List.getElem_range', List.getElem_cons_succ] at this ⊢
        rwa [show σ.next + 1 * (i + 1) = σ.next + 1 + 1 * i by omega]
    · simp only [List.flatten_cons]
      refine List.nodup_append.mpr ⟨List.nodup_cons.mpr ⟨hnR', (List.nodup_cons.mp h0.nodup).2⟩, hnd'', ?_⟩
      intro x hx y hy e
      subst e
      rcases (hmem'' x).mp hy with ⟨hx1, -⟩ | hx2
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact Nat.lt_irrefl _ (hRsn _ hx1)
        · exact hnd'.2.2 x (List.mem_cons_of_mem _ hx) x hx1 rfl
      · simp only [List.mem_range'_1] at hx2
        rcases List.mem_cons.mp hx with rfl | hx
        · omega
        · have := hR'n x hx; omega
    · intro x
      simp only [List.flatten_cons, List.mem_append, List.mem_cons, hmem'', List.mem_range'_1, List.length_cons]
      constructor
      · rintro ((rfl | hx) | (⟨hx1, hx2⟩ | hx3))
        · exact .inr ⟨Nat.le_refl _, by omega⟩
        · exact .inl ⟨.inl (.inr hx), fun h => by
            rcases h with rfl | h
            · exact hn hx
            · exact hcs_out x h (List.mem_cons_of_mem _ hx)⟩
        · exact .inl ⟨.inr hx1, fun h => by
            rcases h with rfl | h
            · exact hnd'.2.2 x (List.mem_cons_self ..) x hx1 rfl
            · exact hx2 h⟩
        · exact .inr ⟨by omega, by omega⟩
      · rintro (⟨(hx | hx) | hx, hx2⟩ | ⟨hx3, hx4⟩)
        · exact absurd (.inl hx) hx2
        · exact .inl (.inr hx)
        · exact .inr (.inl ⟨hx, fun h => hx2 (.inr h)⟩)
        · by_cases e : x = σ.next
          · exact .inl (.inl e)
          · exact .inr (.inr ⟨by omega, by omega⟩)
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [hkeep x hc_cs (by rw [hn2]; omega), hm2]; simp
      · exact hfree x hx
    · intro x hx hlt
      simp only [List.mem_cons, not_or] at hx
      exact hold3 x hx.2 hx.1 hlt


/-- A step that frees the cells `D` of those it may change, allocates the cells from `σ.next` on, and
changes no cell outside `E`. -/
theorem Moves.rewrite {D : List Nat} (hwf : WF σ) (hwf' : WF σ') (hn : σ.next ≤ σ'.next)
    (hframe : ∀ l, l < σ.next → l ∉ E → σ'.mem l = σ.mem l) (hD : ∀ l ∈ D, σ'.mem l = none)
    (hlive : ∀ l ∈ E, l ∉ D → σ'.mem l ≠ none) (hnew : ∀ l, σ.next ≤ l → l < σ'.next → σ'.mem l ≠ none)
    (hE' : ∀ l, l ∈ E' ↔ (l ∈ E ∧ l ∉ D) ∨ (σ.next ≤ l ∧ l < σ'.next)) (hrt : σ'.rt = σ.rt) :
    Moves σ E σ' E' [] where
  rt := fun l x h => by rw [hrt]; exact h
  fresh := fun _ _ _ h h0 => by rw [hrt, h0] at h; cases h
  within := by
    intro l hl
    simp only [List.not_mem_nil, false_or] at hl
    rcases (hE' l).mp hl with ⟨h, -⟩ | ⟨h, -⟩
    · exact .inl h
    · exact .inr h
  next := hn
  wf := hwf'
  frame := hframe
  alloc := by
    intro l
    simp only [List.not_mem_nil, or_false]
    constructor
    · intro h
      by_cases hlt : l < σ.next
      · by_cases hlE : l ∈ E
        · by_cases hlD : l ∈ D
          · exact absurd (hD l hlD) h
          · exact .inr ((hE' l).mpr (.inl ⟨hlE, hlD⟩))
        · exact .inl ⟨by rw [← hframe l hlt hlE]; exact h, hlE⟩
      · exact .inr ((hE' l).mpr (.inr ⟨Nat.le_of_not_lt hlt, hwf' l h⟩))
    · rintro (⟨h, hlE⟩ | h)
      · rw [hframe l (hwf l h) hlE]; exact h
      · rcases (hE' l).mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hlive l h1 h2
        · exact hnew l h1 h2

/-! ## Making, measuring and growing a vector -/

theorem vnew_ok (hc : τ.complete = true) (hI : Inv F ι σ Γ env E S) (hwf : WF σ) :
    Post F ι O σ E S Γ env (.vec true τ) r hs (evalS F O n hs σ env .vnew) := by
  simp only [evalS]
  exact ⟨E, [], hI, .vec (Rs := []) rfl (fun i h => by simp at h) List.nodup_nil hc, disj_nil_left, disj_nil_left,
    Moves.refl hwf hI.alloc⟩

theorem vlen_ok (hp : PlaceTy Γ p (.vec g τ) w y) (hI : Inv F ι σ Γ env E S) (hwf : WF σ) :
    Post F ι O σ E S Γ env .int r hs (evalS F O n hs σ env (.vlen p)) := by
  obtain ⟨a, τr, Lr, P, l, s', ha, hLr, hpath, hres, -⟩ := place_ok hp hI.foot
  obtain ⟨Rb, hRb, -⟩ := path_split hpath hLr
  cases hRb with
  | vec hl =>
    simp only [evalS, hres, hl]
    exact ⟨E, [], hI, .int, disj_nil_left, disj_nil_left, Moves.refl hwf hI.alloc⟩

/-- `p.push(a)`: the vector's elements move to new cells, the old ones freed, and `a` goes in one
more; the tree of the variable `p` is rooted at changes there alone. -/
theorem vpush_ok (ha : AtomTy Γ a τ Γ₁) (hp : PlaceTy Γ₁ p (.vec true τ) true y) (hI : Inv F ι σ Γ env E S) (hwf : WF σ) :
    Post F ι O σ E S Γ₁ env .int r hs (evalS F O n hs σ env (.vpush p a)) := by
  obtain ⟨v, σ1, E₁, L₁, hev, hI₁, hv₁, hd₁, hdS₁, hm₁⟩ := atom_ok ha hI hwf
  have hcτ : τ.complete = true := hv₁.complete
  obtain ⟨c, Rb, P, A, B, hres, hRb, hE, hupd⟩ := replace_at hI₁ hp (by simpa [Ty.complete] using hcτ) (.inl rfl)
  cases hRb with
  | vec hcm hlen hel hnd hcn =>
  rename_i cs Rs
  have hwf₁ := hm₁.wf
  obtain ⟨Rs', σ2, hmv, hlen', hel', hnd', hmem', hfree, hkeep, hn2, hrt2, hwf2⟩ :=
    moveAll_ok hcτ cs Rs σ1 hwf₁ hlen hel hnd
  simp only [evalS, hev, hres, hcm, hmv]
  -- Where everything is.
  have hndE := hE.nodup_iff.mp hI₁.nodup
  obtain ⟨hdR, -⟩ := seg3 hndE
  have hRE : ∀ x ∈ c :: Rs.flatten, x ∈ E₁ := fun x hx =>
    hE.mem_iff.mpr (mem_seg.mpr (.inl (List.mem_append.mpr (.inr hx))))
  have hAPB : ∀ x ∈ A ++ P ++ B, x ∈ E₁ := fun x hx => hE.mem_iff.mpr (by
    simp only [List.mem_append] at hx ⊢; rcases hx with (hx | hx) | hx <;> simp [hx])
  have hheads : ∀ x ∈ cs, x ∈ Rs.flatten := fun x hx => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    exact mem_flatten_of (hlen ▸ hi) ((hel i hi (hlen ▸ hi)).head (Ty.complete_not_hole hcτ))
  have hc_cs : c ∉ cs := fun h => hcn (hheads c h)
  have hlt1 : ∀ x ∈ E₁, x < σ1.next := fun x hx => hwf₁ x (hI₁.alloc x hx)
  have hltL : ∀ x ∈ L₁, x < σ1.next := fun x hx => hwf₁ x (hv₁.alloc x hx)
  have hltS : ∀ x ∈ S, x < σ1.next := fun x hx => hwf₁ x (hI₁.allocS x hx)
  have hcn1 : c < σ1.next := hlt1 c (hRE c (List.mem_cons_self ..))
  generalize hl : σ2.next = l at hn2
  have hl' : (σ2.alloc v).1 = l := hl
  rw [hl']
  generalize hσ4 : (σ2.alloc v).2.set c (some (.vec (List.range' σ1.next cs.length ++ [l]))) = σ4
  have hm4 : ∀ x, σ4.mem x = if x = c then some (.vec (List.range' σ1.next cs.length ++ [l]))
      else if x = l then some v else σ2.mem x := by
    intro x; rw [← hσ4, ← hl]; simp only [Store.set, Store.alloc]
  have hn4 : σ4.next = l + 1 := by rw [← hσ4, ← hl]; rfl
  have hrt4 : σ4.rt = σ1.rt := by rw [← hσ4]; exact hrt2
  have hwf4 : WF σ4 := by rw [← hσ4]; exact (hwf2.alloc).set (by show c < σ2.next + 1; omega)
  -- Cells older than the push, but the vector's and its elements' heads, are as they were.
  have hold : ∀ x, x < σ1.next → x ≠ c → x ∉ cs → σ4.mem x = σ1.mem x := fun x h1 h2 h3 => by
    rw [hm4, if_neg h2, if_neg (by omega), hkeep x h3 h1]
  have hrange : ∀ x, x ∈ List.range' σ1.next cs.length ↔ σ1.next ≤ x ∧ x < l := by
    intro x; simp only [List.mem_range'_1]; constructor <;> intro h <;> omega
  have hR'char : ∀ x, x ∈ Rs'.flatten ↔ (x ∈ Rs.flatten ∧ x ∉ cs) ∨ (σ1.next ≤ x ∧ x < l) := by
    intro x; rw [hmem', hrange]
  have hagL : Agree σ1 σ4 L₁ := Agree.of (fun x hx => hold x (hltL x hx)
    (fun e => hd₁ x hx (e ▸ hRE c (List.mem_cons_self ..))) (fun h => hd₁ x hx (hRE x (List.mem_cons_of_mem _ (hheads x h)))))
    hrt4
  have hlL : l ∉ L₁ := fun h => by have := hltL l h; omega
  -- The vector, one element more.
  have hLT : LT F ι σ4 c (.vec true τ) (c :: (Rs' ++ [l :: L₁]).flatten) := by
    refine .vec (cs := List.range' σ1.next cs.length ++ [l]) (by rw [hm4]; simp) (by simp [hlen']) (fun i h h' => ?_) ?_ ?_
    · simp only [List.length_append, List.length_range', List.length_singleton] at h
      by_cases hi : i < cs.length
      · have := hel' i (by simpa using hi) (by omega)
        rw [List.getElem_append_left (by simpa using hi), List.getElem_append_left (by omega)]
        refine this.frame (Agree.of (fun x hx => ?_) (by rw [hrt4, hrt2]))
        have hx' := (hR'char x).mp (mem_flatten_of (by omega) hx)
        have hxc : x ≠ c := fun e => by
          subst e; rcases hx' with ⟨h1, -⟩ | ⟨h1, -⟩
          · exact hcn h1
          · omega
        have hxl : x ≠ l := fun e => by
          subst e; rcases hx' with ⟨h1, -⟩ | ⟨-, h1⟩
          · have := hlt1 x (hRE x (List.mem_cons_of_mem _ h1)); omega
          · omega
        rw [hm4, if_neg hxc, if_neg hxl]
      · obtain rfl : i = cs.length := by omega
        rw [List.getElem_append_right (by simp), List.getElem_append_right (by omega)]
        simp only [List.length_range', Nat.sub_self, List.getElem_singleton, hlen']
        exact LT.of_contents (by rw [hm4]; simp [show l ≠ c by omega]) (hv₁.frame hagL) hlL
    · simp only [List.flatten_append, List.flatten_singleton]
      refine List.nodup_append.mpr ⟨hnd', List.nodup_cons.mpr ⟨hlL, hv₁.nodup⟩, ?_⟩
      intro x hx y hy e
      subst e
      rcases (hR'char x).mp hx with ⟨h1, -⟩ | ⟨h1, h2⟩
      · rcases List.mem_cons.mp hy with rfl | hy
        · have := hlt1 x (hRE x (List.mem_cons_of_mem _ h1)); omega
        · exact hd₁ x hy (hRE x (List.mem_cons_of_mem _ h1))
      · rcases List.mem_cons.mp hy with rfl | hy
        · omega
        · have := hltL x hy; omega
    · simp only [List.flatten_append, List.flatten_singleton, List.mem_append, List.mem_cons, not_or]
      refine ⟨fun h => ?_, ?_, fun h => hd₁ c h (hRE c (List.mem_cons_self ..))⟩
      · rcases (hR'char c).mp h with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hcn h1
        · omega
      · omega
  -- The rest of the activation, as it was.
  have hR'cells : ∀ x ∈ c :: (Rs' ++ [l :: L₁]).flatten,
      x = c ∨ (x ∈ Rs.flatten ∧ x ∉ cs) ∨ (σ1.next ≤ x ∧ x ≤ l) ∨ x ∈ L₁ := by
    intro x hx
    simp only [List.flatten_append, List.flatten_singleton, List.mem_append, List.mem_cons] at hx
    rcases hx with rfl | hx | rfl | hx
    · exact .inl rfl
    · rcases (hR'char x).mp hx with h | ⟨h1, h2⟩
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl ⟨h1, by omega⟩))
    · exact .inr (.inr (.inl ⟨by omega, Nat.le_refl _⟩))
    · exact .inr (.inr (.inr hx))
  have hdAPB : Disj (c :: (Rs' ++ [l :: L₁]).flatten) (A ++ P ++ B) := by
    intro x hx hx'
    rcases hR'cells x hx with rfl | ⟨h1, -⟩ | ⟨h1, -⟩ | h1
    · exact hdR _ (List.mem_cons_self ..) hx'
    · exact hdR x (List.mem_cons_of_mem _ h1) hx'
    · have := hlt1 x (hAPB x hx'); omega
    · exact hd₁ x h1 (hAPB x hx')
  have hdS : Disj (c :: (Rs' ++ [l :: L₁]).flatten) S := by
    intro x hx hx'
    rcases hR'cells x hx with rfl | ⟨h1, -⟩ | ⟨h1, -⟩ | h1
    · exact hI₁.disj _ hx' (hRE _ (List.mem_cons_self ..))
    · exact hI₁.disj x hx' (hRE x (List.mem_cons_of_mem _ h1))
    · have := hltS x hx'; omega
    · exact hdS₁ x h1 hx'
  have hag : Agree σ1 σ4 (A ++ P ++ B ++ S) := Agree.of (fun x hx => by
    have hxE : x ∉ c :: Rs.flatten := fun h => by
      rcases List.mem_append.mp hx with hx | hx
      · exact hdR x h hx
      · exact hI₁.disj x hx (hRE x h)
    have hxlt : x < σ1.next := by
      rcases List.mem_append.mp hx with hx | hx
      · exact hlt1 x (hAPB x hx)
      · exact hltS x hx
    exact hold x hxlt (fun e => hxE (e ▸ List.mem_cons_self ..)) (fun h => hxE (List.mem_cons_of_mem _ (hheads x h))))
    hrt4
  obtain ⟨E'', hI'', hE''⟩ := hupd σ4 _ hag hLT hdAPB hdS
  refine post_val hI'' .int disj_nil_left disj_nil_left ?_
  have mstep : Moves σ1 (E₁ ++ L₁) σ4 (A ++ (P ++ c :: (Rs' ++ [l :: L₁]).flatten) ++ B) [] := by
    refine Moves.rewrite (D := cs) hwf₁ hwf4 (by omega) (fun x hx hxE => ?_) (fun x hx => ?_) (fun x hx hxD => ?_)
      (fun x h1 h2 => ?_) (fun x => ?_) hrt4
    · exact hold x hx (fun e => hxE (List.mem_append.mpr (.inl (by rw [e]; exact hRE c (List.mem_cons_self ..)))))
        (fun h => hxE (List.mem_append.mpr (.inl (hRE x (List.mem_cons_of_mem _ (hheads x h))))))
    · have hxlt := hlt1 x (hRE x (List.mem_cons_of_mem _ (hheads x hx)))
      rw [hm4, if_neg (fun (e : x = c) => hc_cs (e ▸ hx)), if_neg (by omega)]
      exact hfree x hx
    · by_cases hxc : x = c
      · subst hxc; rw [hm4]; simp
      · have hxlt : x < σ1.next := by
          rcases List.mem_append.mp hx with hx | hx
          · exact hlt1 x hx
          · exact hltL x hx
        rw [hold x hxlt hxc hxD]
        rcases List.mem_append.mp hx with hx | hx
        · exact hI₁.alloc x hx
        · exact hv₁.alloc x hx
    · rw [hn4] at h2
      by_cases hxl : x = l
      · subst hxl; rw [hm4]; simp [show x ≠ c by omega]
      · have hx : x ∈ List.range' σ1.next cs.length := (hrange x).mpr ⟨h1, by omega⟩
        obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
        have := (hel' i hi (by simpa [hlen'] using hi)).head (Ty.complete_not_hole hcτ)
        have ha2 := (hel' i hi (by simpa [hlen'] using hi)).alloc _ this
        rw [hix] at ha2
        rw [hm4, if_neg (by omega), if_neg hxl]
        exact ha2
    · rw [hn4]
      have hE₁ : ∀ x, x ∈ E₁ ↔ x ∈ A ++ P ++ B ∨ x ∈ c :: Rs.flatten := fun x => by
        rw [hE.mem_iff, mem_seg]
        constructor
        · rintro (h | h)
          · rcases List.mem_append.mp h with hP | hR
            · exact .inl (by simp [hP])
            · exact .inr hR
          · rcases List.mem_append.mp h with hA | hB
            · exact .inl (by simp [hA])
            · exact .inl (by simp [hB])
        · rintro (h | h)
          · simp only [List.mem_append] at h
            rcases h with (hA | hP) | hB
            · exact .inr (by simp [hA])
            · exact .inl (by simp [hP])
            · exact .inr (by simp [hB])
          · exact .inl (List.mem_append.mpr (.inr h))
      simp only [List.mem_append, List.mem_cons, List.flatten_append, List.flatten_singleton] at hE₁ ⊢
      rw [hR'char]
      constructor
      · rintro ((hA | hP | rfl | (⟨h1, h2⟩ | ⟨h1, h2⟩) | rfl | hL) | hB)
        · exact .inl ⟨.inl ((hE₁ x).mpr (.inl (.inl (.inl hA)))), fun h => hdR x (List.mem_cons_of_mem _ (hheads x h)) (by simp [hA])⟩
        · exact .inl ⟨.inl ((hE₁ x).mpr (.inl (.inl (.inr hP)))), fun h => hdR x (List.mem_cons_of_mem _ (hheads x h)) (by simp [hP])⟩
        · exact .inl ⟨.inl ((hE₁ x).mpr (.inr (.inl rfl))), hc_cs⟩
        · exact .inl ⟨.inl ((hE₁ x).mpr (.inr (.inr h1))), h2⟩
        · exact .inr ⟨h1, by omega⟩
        · exact .inr ⟨by omega, by omega⟩
        · exact .inl ⟨.inr hL, fun h => hd₁ x hL (hRE x (List.mem_cons_of_mem _ (hheads x h)))⟩
        · exact .inl ⟨.inl ((hE₁ x).mpr (.inl (.inr hB))), fun h => hdR x (List.mem_cons_of_mem _ (hheads x h)) (by simp [hB])⟩
      · rintro (⟨hx | hx, hxD⟩ | ⟨h1, h2⟩)
        · rcases (hE₁ x).mp hx with ((hA | hP) | hB) | (rfl | hR)
          · exact .inl (.inl hA)
          · exact .inl (.inr (.inl hP))
          · exact .inr hB
          · exact .inl (.inr (.inr (.inl rfl)))
          · exact .inl (.inr (.inr (.inr (.inl (.inl ⟨hR, hxD⟩)))))
        · exact .inl (.inr (.inr (.inr (.inr (.inr hx)))))
        · by_cases hxl : x = l
          · exact .inl (.inr (.inr (.inr (.inr (.inl hxl)))))
          · exact .inl (.inr (.inr (.inr (.inl (.inr ⟨h1, by omega⟩)))))
  have := (hm₁.relabel (E'' := E₁ ++ L₁) (L'' := []) fun x => by mem_iff).trans mstep disj_nil_left hwf
  exact this.relabel fun x => by simp only [List.append_nil, hE''.mem_iff, List.not_mem_nil, or_false]



/-- `p.pop()`: an empty vector gives `#None`; otherwise its last element's tree moves out of the
vector into the value, `#Some` of it, and the vector keeps the rest. -/
theorem vpop_ok (hp : PlaceTy Γ p (.vec true τ) true y) (hcτ : τ.complete = true) (hI : Inv F ι σ Γ env E S)
    (hwf : WF σ) :
    Post F ι O σ E S Γ env (.sum .int τ) r hs (evalS F O n hs σ env (.vpop p)) := by
  obtain ⟨c, Rb, P, A, B, hres, hRb, hE, hupd⟩ := replace_at hI hp (by simpa [Ty.complete] using hcτ) (.inl rfl)
  cases hRb with
  | vec hcm hlen hel hnd hcn =>
  rename_i cs Rs
  simp only [evalS, hres, hcm]
  have hndE := hE.nodup_iff.mp hI.nodup
  obtain ⟨hdR, -⟩ := seg3 hndE
  have hRE : ∀ x ∈ c :: Rs.flatten, x ∈ E := fun x hx =>
    hE.mem_iff.mpr (mem_seg.mpr (.inl (List.mem_append.mpr (.inr hx))))
  cases hlast : cs.getLast? with
  | none =>
    simp only
    generalize hb : (σ.alloc (.int 0)).1 = b
    have hbn : b = σ.next := hb.symm
    generalize hσ1 : (σ.alloc (.int 0)).2 = σ1
    have hfresh : ∀ l, σ.mem l ≠ none → l ≠ b := fun l h e => by
      subst e; rw [hbn] at h; exact Nat.lt_irrefl _ (hwf _ h)
    have hold : ∀ l, σ.mem l ≠ none → σ1.mem l = σ.mem l := fun l h => by
      rw [← hσ1]; simp only [Store.alloc]; rw [if_neg (fun e => hfresh l h (by rw [hbn]; exact e))]
    have hbm : σ1.mem b = some (.int 0) := by rw [← hσ1, hbn]; simp [Store.alloc]
    have hag : Agree σ σ1 (E ++ S) := Agree.of' (fun l hl => by
      rcases List.mem_append.mp hl with h | h
      · exact hold l (hI.alloc l h)
      · exact hold l (hI.allocS l h)) (by rw [← hσ1]; rfl)
    refine ⟨E, [b], ⟨hI.foot.frame hag, hI.nodup, hI.disj, hI.keys⟩, .tag (.int hbm) rfl hcτ,
      fun l h1 h2 => ?_, fun l h1 h2 => ?_, ?_⟩
    · simp at h1; subst h1; exact hfresh _ (hI.alloc _ h2) rfl
    · simp at h1; subst h1; exact hfresh _ (hI.allocS _ h2) rfl
    · rw [← hσ1, hbn]; exact Moves.allocate hwf hI.alloc
  | some l =>
    simp only
    have hne : cs ≠ [] := by intro h; simp [h] at hlast
    have hRne : Rs ≠ [] := by intro h; simp [h] at hlen; exact hne (List.eq_nil_of_length_eq_zero hlen.symm)
    have hcs := List.dropLast_concat_getLast hne
    have hRs := List.dropLast_concat_getLast hRne
    have hl : cs.getLast hne = l := by rw [List.getLast?_eq_getLast hne] at hlast; exact Option.some.inj hlast
    have hk : cs.length - 1 < cs.length := by
      have : cs.length ≠ 0 := fun h => hne (List.eq_nil_of_length_eq_zero h)
      omega
    have hkR : cs.length - 1 < Rs.length := by rw [hlen]; exact hk
    have hlk : cs[cs.length - 1] = l := by rw [← hl, List.getLast_eq_getElem]
    have hRk : Rs[cs.length - 1]'hkR = Rs.getLast hRne := by
      rw [List.getLast_eq_getElem]; congr 1; omega
    have hLl : LT F ι σ l τ (Rs.getLast hRne) := by
      have := hel _ hk hkR; rw [hlk, hRk] at this; exact this
    have hflat : Rs.flatten = Rs.dropLast.flatten ++ Rs.getLast hRne := by
      have := congrArg List.flatten hRs
      simp only [List.flatten_append, List.flatten_singleton] at this
      exact this.symm
    rw [hflat] at hnd hcn hRE hdR
    have hnd2 := List.nodup_append.mp hnd
    generalize hσ' : σ.set c (some (.vec cs.dropLast)) = σ'
    have hm' : ∀ x, σ'.mem x = if x = c then some (.vec cs.dropLast) else σ.mem x := by
      intro x; rw [← hσ']; simp only [Store.set]
    have hrt' : σ'.rt = σ.rt := by rw [← hσ']; rfl
    have hcl : c ∉ Rs.getLast hRne := fun h => hcn (List.mem_append.mpr (.inr h))
    have hcD : c ∉ Rs.dropLast.flatten := fun h => hcn (List.mem_append.mpr (.inl h))
    have hagR : Agree σ σ' (Rs.getLast hRne) := Agree.of (fun x hx => by
      rw [hm', if_neg (fun (e : x = c) => hcl (e ▸ hx))]) hrt'
    have hLT' : LT F ι σ' c (.vec true τ) (c :: Rs.dropLast.flatten) := by
      refine .vec (cs := cs.dropLast) (by rw [hm']; simp) (by simp [hlen]) (fun j hj hj' => ?_) hnd2.1 hcD
      have hj1 : j < cs.length := by simp at hj; omega
      have := hel j hj1 (by rw [hlen]; exact hj1)
      rw [List.getElem_dropLast, List.getElem_dropLast]
      refine this.frame (Agree.of (fun x hx => ?_) hrt')
      have : x ∈ Rs.dropLast.flatten := mem_flatten_of (by simpa using hj') (by rw [List.getElem_dropLast]; exact hx)
      rw [hm', if_neg (fun (e : x = c) => hcD (e ▸ this))]
    have hout : ∀ x ∈ A ++ P ++ B ++ S, x ≠ c := fun x hx e => by
      subst e
      rcases List.mem_append.mp hx with hx | hx
      · exact hdR _ (List.mem_cons_self ..) hx
      · exact hI.disj _ hx (hRE _ (List.mem_cons_self ..))
    have hag : Agree σ σ' (A ++ P ++ B ++ S) := Agree.of (fun x hx => by rw [hm', if_neg (hout x hx)]) hrt'
    have hdAPB : Disj (c :: Rs.dropLast.flatten) (A ++ P ++ B) := fun x hx hx' =>
      hdR x (by rcases List.mem_cons.mp hx with rfl | hx <;> simp [*]) hx'
    have hdS : Disj (c :: Rs.dropLast.flatten) S := fun x hx hx' =>
      hI.disj x hx' (hRE x (by rcases List.mem_cons.mp hx with rfl | hx <;> simp [*]))
    obtain ⟨E'', hI'', hE''⟩ := hupd σ' _ hag hLT' hdAPB hdS
    have hRlast : ∀ x ∈ Rs.getLast hRne, x ∈ E := fun x hx => hRE x (by simp [hx])
    refine ⟨E'', Rs.getLast hRne, hI'', .tag (hLl.frame hagR) rfl hcτ, fun x h1 h2 => ?_,
      fun x h1 h2 => hI.disj x h2 (hRlast x h1), ?_⟩
    · rcases List.mem_append.mp (hE''.mem_iff.mp h2) with h2 | h2
      · rcases List.mem_append.mp h2 with h2 | h2
        · exact hdR x (by simp [h1]) (by simp [h2])
        · rcases List.mem_append.mp h2 with h2 | h2
          · exact hdR x (by simp [h1]) (by simp [h2])
          · rcases List.mem_cons.mp h2 with rfl | h2
            · exact hcl h1
            · exact hnd2.2.2 x h2 x h1 rfl
      · exact hdR x (by simp [h1]) (by simp [h2])
    · have m := Moves.set (v := .vec cs.dropLast) hwf hI.alloc (hRE c (List.mem_cons_self ..))
      rw [hσ'] at m
      exact m.relabel fun x => by
        simp only [hE''.mem_iff, hE.mem_iff, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
        grind

/-! ## Borrowing an element -/

theorem flatten_set_perm : ∀ {Rs : List (List Nat)} {i : Nat}, i < Rs.length → ∀ R : List Nat,
    (Rs.set i R).flatten.Perm (R ++ (Rs.set i []).flatten)
  | [], _, h, _ => by simp at h
  | R0 :: Rs, 0, _, R => by simp
  | R0 :: Rs, i + 1, h, R => by
    have ih := (flatten_set_perm (Rs := Rs) (i := i) (by simpa using h) R).count_eq
    refine List.perm_iff_count.mpr fun z => ?_
    have := ih z
    simp only [List.set_cons_succ, List.flatten_cons, List.count_append] at this ⊢
    omega

theorem flatten_perm_at {Rs : List (List Nat)} (hi : i < Rs.length) :
    Rs.flatten.Perm (Rs[i] ++ (Rs.set i []).flatten) := by
  have := flatten_set_perm hi Rs[i]
  rwa [List.set_getElem_self] at this

theorem mem_flatten_set {Rs : List (List Nat)} (hj : j < Rs.length) (hji : j ≠ i) (hz : z ∈ Rs[j]) :
    z ∈ (Rs.set i []).flatten :=
  mem_flatten_of (by simpa using hj) (by rw [List.getElem_set, if_neg (Ne.symm hji)]; exact hz)

/-- An element of a vector a path reaches: the root's tree is the element's, the path's cells, the
vector's cell and the other elements'; and given a new tree for the element, it is that and those. -/
theorem elem_reach (hp : Path F ι σ a τr P c (.vec g τ)) (hLr : LT F ι σ a τr Lr) (hcm : σ.mem c = some (.vec cs))
    (hi : i < cs.length) : ∃ Os, Reach F ι σ a τr (P ++ c :: Os) cs[i] τ := by
  obtain ⟨Rc, hRc, hperm⟩ := path_split hp hLr
  cases hRc with
  | vec hcm' hlen hel hnd hcn =>
  rename_i cs' Rs
  rw [hcm] at hcm'
  cases hcm'
  have hiR : i < Rs.length := hlen ▸ hi
  refine ⟨(Rs.set i []).flatten, ⟨fun {Lr'} hLr' => ?_, fun hn W hW σ' R' hag hR' hd => ?_⟩⟩
  · obtain rfl := hLr.det hLr'
    refine ⟨Rs[i], hel i hi hiR, hperm.trans ?_⟩
    have := flatten_perm_at hiR
    exact List.perm_iff_count.mpr fun z => by
      have h := this.count_eq z
      simp only [List.count_append, List.count_cons] at h ⊢
      omega
  · have hn' := List.nodup_append.mp hn
    have hOs : ((Rs.set i []).flatten).Nodup := (List.nodup_cons.mp hn'.2.1).2
    have hcOs : c ∉ (Rs.set i []).flatten := (List.nodup_cons.mp hn'.2.1).1
    have hagc : σ'.mem c = σ.mem c := hag c (by simp)
    have hLc : LT F (ι.inW W) σ' c (.vec g τ) (c :: (Rs.set i R').flatten) := by
      refine .vec (by rw [hagc]; exact hcm) (by simp [hlen]) (fun j hj hj' => ?_) ?_ ?_
      · rw [List.getElem_set]
        by_cases hji : i = j
        · subst hji; rw [if_pos rfl]; exact hR'
        · rw [if_neg hji]
          refine ((hel j hj (hlen ▸ hj)).mono hW).frame (hag.mono fun z hz => ?_)
          exact List.mem_append.mpr (.inr (List.mem_cons_of_mem _ (mem_flatten_set (hlen ▸ hj) (Ne.symm hji) hz)))
      · refine (flatten_set_perm hiR R').nodup_iff.mpr (List.nodup_append.mpr ⟨hR'.nodup, hOs, ?_⟩)
        intro x hx y hy e; subst e
        exact hd x (List.mem_append.mpr (.inr (List.mem_cons_of_mem _ hy))) hx
      · intro h
        rcases List.mem_append.mp ((flatten_set_perm hiR R').mem_iff.mp h) with h | h
        · exact hd c (by simp) h
        · exact hcOs h
    have hdP : Disj P (c :: (Rs.set i R').flatten) := by
      intro z hz hz'
      rcases List.mem_cons.mp hz' with rfl | hz'
      · exact hn'.2.2 z hz z (List.mem_cons_self ..) rfl
      · rcases List.mem_append.mp ((flatten_set_perm hiR R').mem_iff.mp hz') with h | h
        · exact hd z (List.mem_append.mpr (.inl hz)) h
        · exact hn'.2.2 z hz z (List.mem_cons_of_mem _ h) rfl
    obtain ⟨L', hL', hperm', -⟩ := path_join (hp.mono hW) hn'.1 (hag.mono fun z hz => List.mem_append.mpr (.inl hz)) hLc hdP
    refine ⟨L', hL', hperm'.trans ?_⟩
    have := flatten_set_perm hiR R'
    exact List.perm_iff_count.mpr fun z => by
      have h := this.count_eq z
      simp only [List.count_append, List.count_cons] at h ⊢
      omega


/-! ## Through a shell -/

/-- A variable that may be changed, out of reach for now: what it may change is the borrow's, and
what it only reads — the first cell of a closure or a slice borrowed `mut` — stays shared meanwhile;
it takes back a footprint that shares the same. -/
theorem Foot.hiddenX (h : Foot F ι σ Γ env E S) (hk : (Γ.map Prod.fst).Nodup) (he : Entry F ι σ Γ env y s a Ly)
    (hex : s.excl = true) :
    ∃ Eh, Foot F ι σ (hide Γ y) env Eh S ∧ E.Perm (exclPart s Ly ++ Eh) ∧
      ∀ W, ι.w.le W → ∀ σ' Γb Eb' Ly', Foot F (ι.inW W) σ' Γb env Eb' S → Weaker Γb (hide Γ y) → Agree σ σ' S →
        SlotOk F (ι.inW W) σ' s a Ly' → sharedPart s Ly' = sharedPart s Ly →
        ∃ E', Foot F (ι.inW W) σ' (thaw Γ [y] Γb) env E' S ∧ E'.Perm (exclPart s Ly' ++ Eb') := by
  induction h with
  | nil => exact absurd he.1 (by simp [lookup])
  | @cons s0 a0 L0 Γ env E S x hs hrest ih =>
    simp only [List.map_cons, List.nodup_cons] at hk
    obtain ⟨hx, hk⟩ := hk
    rcases (entry_cons hx).mp he with ⟨rfl, rfl, rfl, hL⟩ | ⟨hne, he'⟩
    · -- The variable lent is this one.
      obtain rfl := hL.det hs
      have hhide : hide ((y, s) :: Γ) y = (y, .lent s.ty s.shell) :: Γ := by
        simp only [hide, List.map_cons, ↓reduceIte, List.cons.injEq, true_and]
        exact hide_absent hx
      have hlent : ∀ {ι' σ'} {L : List Nat}, SlotOk F ι' σ' s a L →
          SlotOk F ι' σ' (.lent s.ty s.shell) a (sharedPart s L) := by
        intro ι' σ' L hL
        cases hsh : s.shell
        · simp [SlotOk, sharedPart, hex, hsh]
        · obtain ⟨R, rfl⟩ := hL.head_of_shell hsh
          exact ⟨by simp [sharedPart, hex, hsh], hL.alloc a (by simp)⟩
      have hro : ∀ {L}, sharedPart (.lent s.ty s.shell) L = L := sharedPart_of_ro rfl
      have hnoE : ∀ {L}, exclPart (.lent s.ty s.shell) L = [] := by simp [exclPart, Slot.excl]
      refine ⟨E, ?_, .of_eq rfl, ?_⟩
      · rw [hhide]
        have := Foot.cons (x := y) (hlent hs) hrest
        simpa only [addE, addS, hro, hnoE, List.nil_append] using this
      · intro W hW σ' Γb Eb' Ly' hb hw hag hs' hsheq
        rw [hhide] at hw
        obtain ⟨s', Γb', rfl, hle, hw'⟩ := Weaker.cons_inv hw
        cases hle
        obtain ⟨L', Et, St, hL', hft, rfl, hSt⟩ := hb.uncons
        obtain rfl : L' = sharedPart s Ly' := hL'.det (hlent hs')
        simp only [addS, hro, hsheq] at hSt
        obtain rfl := List.append_cancel_left hSt
        refine ⟨addE s Ly' Eb', ?_, .of_eq rfl⟩
        rw [thaw_cons]
        simp only [List.mem_singleton, ↓reduceIte]
        rw [thaw_absent hx (by rw [hw'.keys])]
        have := Foot.cons (x := y) hs' hft
        simpa only [addS, hsheq] using this
    · -- Another: as it was.
      obtain ⟨Eh, hfh, hp, hthaw⟩ := ih hk he'
      have hhide : hide ((x, s0) :: Γ) y = (x, s0) :: hide Γ y := by
        simp only [hide, List.map_cons, List.cons.injEq]
        simp [Ne.symm hne]
      refine ⟨addE s0 L0 Eh, by rw [hhide]; exact .cons hs hfh, ?_, ?_⟩
      · simp only [addE]; exact (hp.append_left _).trans perm_front
      · intro W hW σ' Γb Eb' Ly' hb hw hag hs' hsheq
        rw [hhide] at hw
        obtain ⟨s', Γb', rfl, hle, hw'⟩ := Weaker.cons_inv hw
        obtain ⟨L', Et, St, hL', hft, rfl, hSt⟩ := hb.uncons
        have hex' : s'.excl = s0.excl := hle.excl
        cases hx0 : s0.excl
        · -- Only read: the same slot, with the same tree.
          have hsame : s' = s0 := by
            cases hle with
            | refl => rfl
            | forget => simp [Slot.excl] at hx0
          subst hsame
          have hsh0 : s'.shell = false := by
            cases h : s'.shell
            · rfl
            · rw [Slot.shell_excl h] at hx0; cases hx0
          have hro : ∀ {L}, sharedPart s' L = L := by simp [sharedPart_plain hsh0, hx0]
          have hLL := ((hs.frame (hag.mono fun l hl => mem_addS.mpr (.inl (by rw [hro]; exact hl)))).mono hW).det hL'
          subst hLL
          simp only [addS, hro] at hSt
          have hSS := List.append_cancel_left hSt
          subst hSS
          obtain ⟨E', hf', hp'⟩ := hthaw W hW σ' Γb' Et Ly' hft hw' ((hag.mono fun l hl => mem_addS.mpr (.inr hl))) hs'
            hsheq
          refine ⟨E', ?_, by simpa [addE, exclPart, hx0] using hp'⟩
          rw [thaw_cons]
          simp only [List.mem_singleton, Ne.symm hne, ↓reduceIte]
          simpa [addE, exclPart, hx0] using Foot.cons (x := x) hL' hf'
        · have hsheq' := SlotOk.shared_eq (hs.mono hW) hL' hle.shell hx0 (hex'.trans hx0)
          simp only [addS, hsheq'] at hSt
          obtain rfl := List.append_cancel_left hSt
          obtain ⟨E', hf', hp'⟩ := hthaw W hW σ' Γb' Et Ly' hft hw' ((hag.mono fun l hl => mem_addS.mpr (.inr hl))) hs'
            hsheq
          refine ⟨addE s' L' E', ?_, ?_⟩
          · rw [thaw_cons]
            simp only [List.mem_singleton, Ne.symm hne, ↓reduceIte]
            have := Foot.cons (x := x) hL' hf'
            rwa [show ∀ X, addS s' L' X = addS s0 L0 X from fun X => by simp [addS, hsheq']] at this
          · simp only [addE]
            exact (hp'.append_left _).trans perm_front

/-- A `mut` borrow of a place past the first cell of a variable that may change all but that cell —
an element of a slice borrowed `mut`: the variable is out of reach while the borrow lives, its
first cell still shared; once it ends, the variable owns again its path to the place and what the
borrow left there. -/
theorem lend_mut_sh [WorldOk F O ι.w] (hE : EvalOk F O n) (hx : lookup x Γ = none) (ha : lookup y env = some a)
    (hsl : lookup y Γ = some s) (hLr : LT F ι σ a τr Lr) (hpath : Reach F ι σ a τr (a :: P) l τ)
    (hso : SlotOk F ι σ s a Lr) (hsx : s.excl = true) (hsh : s.shell = true) (haS : a ∈ S)
    (hslot : ∀ ι' σ' L', LT F ι' σ' a τr L' → SlotOk F ι' σ' s a L') (hτ : τ.shell = false)
    (hb : Typed F O ((x, .ref .mut τ) :: lendCtx .mut Γ y) body τb ((x, .ref .mut τ) :: Γb) r)
    (hI : Inv F ι σ Γ env E S) (hwf : WF σ) (hR : Ready O hs r) :
    Post F ι O σ E S (thaw Γ [y] Γb) env τb r hs (ret F O n hs .lendK (eval F O n hs σ ((x, l) :: env) body)) := by
  simp only [lendCtx] at hb
  obtain ⟨Rt, hRt, hLrp⟩ := hpath.split hLr
  obtain ⟨R0, rfl⟩ := hso.head_of_shell hsh
  have hR0p : R0.Perm (P ++ Rt) := by simpa using hLrp
  have hexcl : ∀ {R}, exclPart s (a :: R) = R := by simp [exclPart, hsx, hsh]
  have hshr : ∀ {R}, sharedPart s (a :: R) = [a] := by simp [sharedPart, hsx, hsh]
  have hxk : x ∉ (hide Γ y).map Prod.fst := by rw [hide_keys]; exact lookup_none_keys hx
  have hwb := typed_weaker hb (List.nodup_cons.mpr ⟨hxk, by rw [hide_keys]; exact hI.keys⟩)
  cases hwb with
  | cons _ hwb =>
  obtain ⟨Eh, hfh, hEh, hreb⟩ := hI.foot.hiddenX hI.keys ⟨hsl, ha, hso⟩ hsx
  rw [hexcl] at hEh
  have hxs : (Slot.ref .mut τ).shell = false := by simp [Slot.shell_ref, hτ]
  -- `E` is the borrowed tree, the rest of the activation and the path to the place.
  have hEp : E.Perm (Rt ++ Eh ++ P) := hEh.trans (by
    refine (hR0p.append_right Eh).trans ?_
    exact List.perm_iff_count.mpr fun z => by simp only [List.count_append]; omega)
  have hEn := hEp.nodup_iff.mp hI.nodup
  obtain ⟨hBn, hPn, hdBP⟩ := nodup_append_disj.mp hEn
  have hmemE : ∀ z, z ∈ E ↔ z ∈ Rt ++ Eh ++ P := fun z => hEp.mem_iff
  have hPE : ∀ z ∈ P, z ∈ E := fun z h => (hmemE z).mpr (List.mem_append.mpr (.inr h))
  have hBE : ∀ z ∈ Rt ++ Eh, z ∈ E := fun z h => (hmemE z).mpr (List.mem_append.mpr (.inl h))
  have hPa : ∀ z ∈ P, σ.mem z ≠ none := fun z h => hI.alloc z (hPE z h)
  have haP : a ∉ P := fun h => hI.disj a haS (hPE a h)
  have hIb : Inv F ι σ ((x, .ref .mut τ) :: hide Γ y) ((x, l) :: env) (Rt ++ Eh) S := by
    refine ⟨by simpa [addE, addS, Slot.excl, exclPart_plain hxs, sharedPart_plain hxs] using
        Foot.cons (s := .ref .mut τ) (x := x) hRt hfh, hBn, fun z hz h => hI.disj z hz (hBE z h),
      List.nodup_cons.mpr ⟨hxk, by rw [hide_keys]; exact hI.keys⟩⟩
  have hkb : Γb.map Prod.fst = Γ.map Prod.fst := by
    have := typed_keys hb
    simp only [List.map_cons, List.cons.injEq] at this
    rw [this.2]; exact hide_keys
  have hre : ∀ W, ι.w.le W → ∀ σ1 Eb', Agree σ σ1 (P ++ S) → Disj P Eb' →
      Inv F (ι.inW W) σ1 ((x, .ref .mut τ) :: Γb) ((x, l) :: env) Eb' S →
      ∃ E', Inv F (ι.inW W) σ1 (thaw Γ [y] Γb) env E' S ∧ ∀ z, z ∈ E' ↔ z ∈ Eb' ∨ z ∈ P := by
    intro W hW σ1 Eb' hag hdX hI'
    obtain ⟨R', Et, St, hR', hft, hEt, hSt⟩ := hI'.foot.uncons
    simp only [addE, addS, Slot.excl, ↓reduceIte, exclPart_plain hxs, sharedPart_plain hxs, List.nil_append] at hEt hSt
    subst hEt
    rw [← hSt] at hft
    have hagS : Agree σ σ1 S := hag.mono fun z hz => List.mem_append.mpr (.inr hz)
    have hagP : Agree σ σ1 (a :: P) := hag.mono fun z hz => by
      rcases List.mem_cons.mp hz with rfl | hz
      · exact List.mem_append.mpr (.inr haS)
      · exact List.mem_append.mpr (.inl hz)
    have haR : a ∉ R' := fun h => hI'.disj a haS (List.mem_append.mpr (.inl h))
    obtain ⟨L', hLT', hL'p⟩ := hpath.join (List.nodup_cons.mpr ⟨haP, hPn⟩) W hW σ1 _ hagP hR' (fun z hz h => by
      rcases List.mem_cons.mp hz with rfl | hz
      · exact haR h
      · exact hdX z hz (List.mem_append.mpr (.inl h)))
    have hso' := hslot _ σ1 _ hLT'
    obtain ⟨R1, rfl⟩ := hso'.head_of_shell hsh
    have hR1p : R1.Perm (P ++ R') := by simpa using hL'p
    obtain ⟨E', hf', hp'⟩ := hreb W hW σ1 Γb Et (a :: R1) hft hwb hagS hso' (by rw [hshr, hshr])
    rw [hexcl] at hp'
    have hp'' : E'.Perm ((R' ++ Et) ++ P) := hp'.trans (by
      refine (hR1p.append_right Et).trans ?_
      exact List.perm_iff_count.mpr fun z => by simp only [List.count_append]; omega)
    refine ⟨E', ⟨hf', hp''.nodup_iff.mpr (nodup_append_disj.mpr ⟨hI'.nodup, hPn, fun z h h' => hdX z h' h⟩),
      ?_, by rw [thaw_keys hkb]; exact hI.keys⟩, fun z => by rw [hp''.mem_iff, List.mem_append]⟩
    intro z hz hz'
    rcases List.mem_append.mp (hp''.mem_iff.mp hz') with h | h
    · exact hI'.disj z hz h
    · exact hI.disj z hz (hPE z h)
  refine post_relabel (E₁ := P ++ (Rt ++ Eh)) hwf hI.alloc (fun z => by
    rw [hmemE z]; simp only [List.mem_append]; grind) ?_
  exact ret_lendK (fun z hz => .inr hz) (fun z hz => hz) hre hR.2 hwf Agree.self hPa hPn
    (fun z hz h => hdBP z h hz) hI.allocS
    (fun z hz h => by
      rcases List.mem_append.mp h with h | h
      · exact hI.disj z hz (hPE z h)
      · exact hI.disj z hz (hBE z h))
    (hE _ _ _ _ _ _ _ _ _ _ _ hb hIb hwf hR)

/-- `{ const x = m p[z]; body }`: out of bounds, a panic; else a borrow of the element, the vector's
root only read, or out of reach, while it lives, as for a borrow of the vector. -/
theorem lendIdx_ok [WorldOk F O ι.w] {m : Mode} (hE : EvalOk F O n) (hx : lookup x Γ = none) (hp : PlaceTy Γ p (.vec g τ) w y)
    (hz : PlaceTy Γ (.var z) .int wz yz) (hm : m = .mut → w = true) (hmf : m = .mut → τ.shell = false)
    (hun : m = .mut → Unsplit Γ y)
    (hb : Typed F O ((x, .ref m τ) :: lendCtx m Γ y) body τb ((x, .ref m τ) :: Γb) r)
    (hI : Inv F ι σ Γ env E S) (hwf : WF σ) (hR : Ready O hs r) :
    Post F ι O σ E S (thaw Γ [y] Γb) env τb r hs (evalS F O n hs σ env (.lendIdx x m p z body)) := by
  obtain ⟨a, τr, Lr, P, c, s, ha, hLr, hpath, hres, hsub, hsubE, hsl, hso, hexw, hslot, hshp, hty⟩ := place_ok hp hI.foot
  obtain ⟨Rc, hRc, -⟩ := path_split hpath hLr
  cases hRc with
  | vec hcm =>
  rename_i cs _
  obtain ⟨az, τz, Lz, Pz, lz, sz, haz, hLz, hpathz, hresz, -⟩ := place_ok hz hI.foot
  obtain ⟨Rz, hRz, -⟩ := path_split hpathz hLz
  cases hRz with
  | int hk =>
  rename_i k
  have hlz : lookup z env = some lz := hresz
  simp only [evalS, hres, hlz, hcm, hk]
  split
  · split
    · rename_i l hl
      obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hl
      obtain ⟨Os, hreach⟩ := elem_reach hpath hLr hcm hi
      cases m with
      | ro => exact lend_ro_core hE hx ha hsl hLr hreach hso hp.root_live hb hI hwf hR
      | «mut» =>
        obtain rfl := hm rfl
        cases hsh : s.shell
        · exact lend_mut_core hE hx ha hsl hLr hreach hso (hsubE rfl hsh) (hexw rfl) hslot hsh (hmf rfl) hb hI hwf hR
        · -- A slice borrowed `mut`: the element lies past its cell, which stays shared.
          obtain ⟨R0, rfl⟩ := hso.head_of_shell hsh
          have haS : a ∈ S := hsub.2 a (by simp [sharedPart, hexw rfl, hsh])
          have hpa : ∃ P', P ++ c :: Os = a :: P' := by
            rcases hshp hsh with ⟨rfl, -⟩ | ⟨-, P', rfl⟩
            · cases hpath; exact ⟨Os, rfl⟩
            · exact ⟨P' ++ c :: Os, rfl⟩
          obtain ⟨P', hP'⟩ := hpa
          rw [hP'] at hreach
          exact lend_mut_sh hE hx ha hsl hLr hreach hso (hexw rfl) hsh haS hslot (hmf rfl) hb hI hwf hR
    · simp [Post]
  · simp [Post]


/-! ## A slice -/

theorem flatten_mid (Rs : List (List Nat)) (i m : Nat) :
    Rs.flatten = (Rs.take i).flatten ++ ((Rs.drop i).take m).flatten ++ ((Rs.drop i).drop m).flatten := by
  have h1 : Rs = Rs.take i ++ ((Rs.drop i).take m ++ (Rs.drop i).drop m) := by
    rw [List.take_append_drop, List.take_append_drop]
  have := congrArg List.flatten h1
  simp only [List.flatten_append, List.append_assoc] at this
  simpa [List.append_assoc] using this

/-- A run of `m` elements of a vector, from the `i`th, a path reaches: the root's tree is theirs, the
path's cells, the vector's cell and the other elements'; given new trees for them, it is those and
these. -/
theorem range_reach (hp : Path F ι σ a τr P c (.vec g τ)) (hLr : LT F ι σ a τr Lr) (hcm : σ.mem c = some (.vec cs))
    (him : i + m ≤ cs.length) :
    ∃ (Os : List Nat) (Rm : List (List Nat)), Lr.Perm (P ++ c :: Os ++ Rm.flatten) ∧ Rm.length = m ∧
      (∀ k (h : k < m) (h' : k < Rm.length), LT F ι σ (cs[i + k]'(by omega)) τ Rm[k]) ∧
      ∀ W, ι.w.le W → ∀ σ' (Rn : List (List Nat)), (P ++ c :: Os).Nodup → Agree σ σ' (P ++ c :: Os) →
        Rn.length = m →
        (∀ k (h : k < m) (h' : k < Rn.length), LT F (ι.inW W) σ' (cs[i + k]'(by omega)) τ Rn[k]) →
        Rn.flatten.Nodup → Disj (P ++ c :: Os) Rn.flatten →
        ∃ L', LT F (ι.inW W) σ' a τr L' ∧ L'.Perm (P ++ c :: Os ++ Rn.flatten) := by
  obtain ⟨Rc, hRc, hperm⟩ := path_split hp hLr
  cases hRc with
  | vec hcm' hlen hel hnd hcn =>
  rename_i cs' Rs
  rw [hcm] at hcm'
  cases hcm'
  have hRl : Rs.length = cs.length := hlen
  -- The run, and the elements before and after it.
  have hmid := flatten_mid Rs i m
  refine ⟨(Rs.take i).flatten ++ ((Rs.drop i).drop m).flatten, (Rs.drop i).take m, ?_, by simp; omega,
    fun k h h' => ?_, fun W hW σ' Rn hn hag hRn hel' hRnn hd => ?_⟩
  · refine hperm.trans ?_
    rw [hmid]
    exact List.perm_iff_count.mpr fun z => by simp only [List.count_append, List.count_cons]; omega
  · have e : ((Rs.drop i).take m)[k] = Rs[i + k]'(by omega) := by simp
    rw [e]
    exact hel (i + k) (by omega) (by omega)
  · -- The vector's cell, holding the same cells, the run's trees new.
    have hn' := List.nodup_append.mp hn
    have hcOs := List.nodup_cons.mp hn'.2.1
    have hagc : σ'.mem c = σ.mem c := hag c (by simp)
    have hOs : ∀ z ∈ (Rs.take i).flatten ++ ((Rs.drop i).drop m).flatten, z ∈ P ++ c :: ((Rs.take i).flatten ++ ((Rs.drop i).drop m).flatten) :=
      fun z hz => List.mem_append.mpr (.inr (List.mem_cons_of_mem _ hz))
    generalize hRs' : Rs.take i ++ Rn ++ (Rs.drop i).drop m = Rs'
    have hlen' : Rs'.length = cs.length := by subst hRs'; simp; omega
    have hflat : Rs'.flatten.Perm (Rn.flatten ++ ((Rs.take i).flatten ++ ((Rs.drop i).drop m).flatten)) := by
      subst hRs'
      simp only [List.flatten_append]
      exact List.perm_iff_count.mpr fun z => by simp only [List.count_append]; omega
    have hLc : LT F (ι.inW W) σ' c (.vec g τ) (c :: Rs'.flatten) := by
      refine .vec (by rw [hagc]; exact hcm) hlen' (fun k hk hk' => ?_) ?_ ?_
      · subst hRs'
        by_cases h1 : k < i
        · have e : (Rs.take i ++ Rn ++ (Rs.drop i).drop m)[k] = Rs[k]'(by omega) := by
            rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega)]; simp
          rw [e]
          refine ((hel k hk (by omega)).mono hW).frame (hag.mono fun z hz => ?_)
          refine hOs z (List.mem_append.mpr (.inl (mem_flatten_of (i := k) (by simp; omega) ?_)))
          simpa using hz
        · by_cases h2 : k < i + m
          · have e : (Rs.take i ++ Rn ++ (Rs.drop i).drop m)[k] = Rn[k - i]'(by omega) := by
              rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
              simp only [List.length_take]; congr 1; omega
            rw [e]
            have := hel' (k - i) (by omega) (by omega)
            have ec : cs[i + (k - i)]'(by omega) = cs[k] := by congr 1; omega
            rwa [ec] at this
          · have e : (Rs.take i ++ Rn ++ (Rs.drop i).drop m)[k] = Rs[k]'(by omega) := by
              rw [List.getElem_append_right (by simp; omega)]
              simp only [List.getElem_drop, List.length_append, List.length_take]
              congr 1; omega
            rw [e]
            refine ((hel k hk (by omega)).mono hW).frame (hag.mono fun z hz => ?_)
            refine hOs z (List.mem_append.mpr (.inr (mem_flatten_of (i := k - i - m) (by simp; omega) ?_)))
            have e2 : ((Rs.drop i).drop m)[k - i - m]'(by simp; omega) = Rs[k]'(by omega) := by
              simp only [List.getElem_drop]; congr 1; omega
            rw [e2]; exact hz
      · refine hflat.nodup_iff.mpr (List.nodup_append.mpr ⟨hRnn, hcOs.2, ?_⟩)
        intro x hx y hy e; subst e
        exact hd x (List.mem_append.mpr (.inr (List.mem_cons_of_mem _ hy))) hx
      · intro h
        rcases List.mem_append.mp (hflat.mem_iff.mp h) with h | h
        · exact hd c (by simp) h
        · exact hcOs.1 h
    have hdP : Disj P (c :: Rs'.flatten) := by
      intro z hz hz'
      rcases List.mem_cons.mp hz' with rfl | hz'
      · exact hn'.2.2 z hz z (List.mem_cons_self ..) rfl
      · rcases List.mem_append.mp (hflat.mem_iff.mp hz') with h | h
        · exact hd z (List.mem_append.mpr (.inl hz)) h
        · exact hn'.2.2 z hz z (List.mem_cons_of_mem _ h) rfl
    obtain ⟨L', hL', hperm', -⟩ := path_join (hp.mono hW) hn'.1 (hag.mono fun z hz => List.mem_append.mpr (.inl hz)) hLc hdP
    refine ⟨L', hL', hperm'.trans ?_⟩
    exact List.perm_iff_count.mpr fun z => by
      have h := hflat.count_eq z
      simp only [List.count_append, List.count_cons] at h ⊢
      omega

/-- `{ const x = p[lo..hi]; body }`: out of bounds, a panic; else a vector of its own, whose cell is
the frame's, of the elements from `lo` up to `hi`, the vector's root only read while it lives. -/
theorem lendSlice_ok [WorldOk F O ι.w] (hE : EvalOk F O n) (hx : lookup x Γ = none) (hp : PlaceTy Γ p (.vec g τ) w y)
    (hlo : PlaceTy Γ (.var lo) .int w1 y1) (hhi : PlaceTy Γ (.var hi) .int w2 y2)
    (hb : Typed F O ((x, .ref .ro (.vec false τ)) :: freeze Γ [y]) body τb ((x, .ref .ro (.vec false τ)) :: Γb) r)
    (hI : Inv F ι σ Γ env E S) (hwf : WF σ) (hR : Ready O hs r) :
    Post F ι O σ E S (thaw Γ [y] Γb) env τb r hs (evalS F O n hs σ env (.lendSlice x .ro p lo hi body)) := by
  obtain ⟨a0, τr, Lr, P, c, s, ha0, hLr, hpath, hres, -, -, hsl, hso, -, -⟩ := place_ok hp hI.foot
  obtain ⟨Rc, hRc, hLrPR⟩ := path_split hpath hLr
  have hRc' := hRc
  cases hRc' with
  | vec hcm hlen hel hnd hcn =>
  rename_i cs Rs
  have intOf : ∀ {v w' yv}, PlaceTy Γ (.var v) .int w' yv → ∃ l k, lookup v env = some l ∧ σ.mem l = some (.int k) := by
    intro v w' yv hv
    obtain ⟨az, τz, Lz, Pz, lz, sz, -, hLz, hpathz, hresz, -⟩ := place_ok hv hI.foot
    obtain ⟨Rz, hRz, -⟩ := path_split hpathz hLz
    cases hRz with
    | int hk => exact ⟨lz, _, hresz, hk⟩
  obtain ⟨l1, i, hl1, hi⟩ := intOf hlo
  obtain ⟨l2, j, hl2, hj⟩ := intOf hhi
  simp only [evalS, hres, hl1, hl2, hcm, hi, hj]
  split
  case isFalse => simp [Post]
  rename_i hbd
  obtain ⟨hi0, hij, hjn⟩ := hbd
  generalize hsub : (cs.drop i.toNat).take (j.toNat - i.toNat) = sub
  generalize hRsub : (Rs.drop i.toNat).take (j.toNat - i.toNat) = Rsub
  have hmid := flatten_mid Rs i.toNat (j.toNat - i.toNat)
  rw [hRsub] at hmid
  have hRt : ∀ z ∈ Rsub.flatten, z ∈ Rs.flatten := fun z hz => by rw [hmid]; simp [hz]
  have hRsubn : Rsub.flatten.Nodup := by
    rw [hmid] at hnd
    exact (List.nodup_append.mp (List.nodup_append.mp hnd).1).2.1
  -- The slice's cells: the frozen vector's, but its own cell, new.
  have hxk : x ∉ (freeze Γ [y]).map Prod.fst := by rw [freeze_keys]; exact lookup_none_keys hx
  have hwb := typed_weaker hb (List.nodup_cons.mpr ⟨hxk, by rw [freeze_keys]; exact hI.keys⟩)
  cases hwb with
  | cons _ hwb =>
  obtain ⟨Eb, Sb, Fz, hfb, hEp, hS, hent, hthaw⟩ := hI.foot.handle (ys := [y]) hI.keys (by
    intro y' hy' τ'; simp only [List.mem_singleton] at hy'; subst hy'; exact hp.root_live τ')
  obtain ⟨hEbn, hFzn, hdEF⟩ := nodup_append_disj.mp (hEp.nodup_iff.mp hI.nodup)
  have hEb : ∀ l ∈ Eb, l ∈ E := fun l h => hEp.mem_iff.mpr (List.mem_append.mpr (.inl h))
  have hFz : ∀ l ∈ Fz, l ∈ E := fun l h => hEp.mem_iff.mpr (List.mem_append.mpr (.inr h))
  have hRin : ∀ l ∈ Rsub.flatten, l ∈ Fz ∨ l ∈ S := fun l hl =>
    hent y s a0 Lr ⟨hsl, ha0, hso⟩ (List.mem_singleton_self _) l
      (hLrPR.mem_iff.mpr (List.mem_append.mpr (.inr (List.mem_cons_of_mem _ (hRt l hl)))))
  have hold : ∀ z, σ.mem z ≠ none → (σ.alloc (.vec sub)).2.mem z = σ.mem z := fun z hz => by
    simp only [Store.alloc]; rw [if_neg (fun e => Nat.lt_irrefl _ (e ▸ hwf z hz))]
  have hRta : ∀ z ∈ Rsub.flatten, σ.mem z ≠ none := fun z hz => hRc.alloc z (List.mem_cons_of_mem _ (hRt z hz))
  have hna : ∀ z, σ.mem z ≠ none → z ≠ σ.next := fun z hz e => Nat.lt_irrefl _ (e ▸ hwf z hz)
  have haRt : σ.next ∉ Rsub.flatten := fun h => hna _ (hRta _ h) rfl
  have hk : i.toNat ≤ cs.length ∧ j.toNat ≤ cs.length ∧ i.toNat ≤ j.toNat := by omega
  have hLa : LT F ι (σ.alloc (.vec sub)).2 σ.next (.vec false τ) (σ.next :: Rsub.flatten) := by
    refine .vec (cs := sub) (by simp [Store.alloc]) (by rw [← hsub, ← hRsub]; simp [hlen]) (fun k hk1 hk2 => ?_)
      hRsubn haRt
    have hk1' : i.toNat + k < cs.length := by rw [← hsub] at hk1; simp at hk1; omega
    have e1 : sub[k] = cs[i.toNat + k] := by subst hsub; simp
    have e2 : Rsub[k] = Rs[i.toNat + k]'(by rw [hlen]; exact hk1') := by subst hRsub; simp
    rw [e1, e2]
    refine (hel _ hk1' (by rw [hlen]; exact hk1')).frame (Agree.of' fun z hz => hold z ?_)
    exact hRta z (by rw [← e2] at hz; exact mem_flatten_of hk2 hz)
  have hFza : ∀ z ∈ Fz, σ.mem z ≠ none := fun z hz => hI.alloc z (hFz z hz)
  have hSin : ∀ z ∈ (σ.next :: Rsub.flatten) ++ Sb, z ∈ (σ.next :: Fz) ∨ z ∈ S := fun z hz => by
    rcases List.mem_append.mp hz with h | h
    · rcases List.mem_cons.mp h with rfl | h
      · exact .inl (List.mem_cons_self ..)
      · rcases hRin z h with h | h
        · exact .inl (List.mem_cons_of_mem _ h)
        · exact .inr h
    · rcases List.mem_append.mp (hS.mem_iff.mp h) with h | h
      · exact .inl (List.mem_cons_of_mem _ h)
      · exact .inr h
  have hIb : Inv F ι (σ.alloc (.vec sub)).2 ((x, .ref .ro (.vec false τ)) :: freeze Γ [y])
      ((x, σ.next) :: env) Eb ((σ.next :: Rsub.flatten) ++ Sb) := by
    have hfoot := Foot.cons (s := .ref .ro (.vec false τ)) (x := x) (a := σ.next) hLa
      (hfb.frame <| Agree.of' fun z hz => hold z (hfb.alloc z (List.mem_append.mp hz)))
    refine ⟨by simpa [addE, addS, Slot.excl, exclPart, sharedPart, Slot.shell, Ty.shell, Bool.false_eq_true] using hfoot, hEbn, ?_,
      List.nodup_cons.mpr ⟨hxk, by rw [freeze_keys]; exact hI.keys⟩⟩
    intro z hz hz'
    rcases hSin z hz with h | h
    · rcases List.mem_cons.mp h with rfl | h
      · exact hna _ (hI.alloc _ (hEb _ hz')) rfl
      · exact hdEF z hz' h
    · exact hI.disj z h (hEb z hz')
  have hkb : Γb.map Prod.fst = Γ.map Prod.fst := by
    have := typed_keys hb
    simp only [List.map_cons, List.cons.injEq] at this
    rw [this.2, freeze_keys]
  have hre : ∀ W, ι.w.le W → ∀ σ1 Eb', Agree (σ.alloc (.vec sub)).2 σ1 ((σ.next :: Fz) ++ S) → Disj (σ.next :: Fz) Eb' →
      Inv F (ι.inW W) σ1 ((x, .ref .ro (.vec false τ)) :: Γb) ((x, σ.next) :: env) Eb' ((σ.next :: Rsub.flatten) ++ Sb) →
      ∃ E', Inv F (ι.inW W) σ1 (thaw Γ [y] Γb) env E' S ∧
        ∀ z, z ∈ E' ↔ z ∈ Eb' ∨ (z ∈ σ.next :: Fz ∧ z ≠ σ.next) := by
    intro W hW σ1 Eb' hag hdX hI'
    obtain ⟨L', Et, St, hL', hft, hEt, hSt⟩ := hI'.foot.uncons
    simp only [addE, addS, Slot.excl, Bool.false_eq_true, ↓reduceIte, exclPart, sharedPart, Slot.shell, Ty.shell] at hEt hSt
    have hagR : Agree (σ.alloc (.vec sub)).2 σ1 (σ.next :: Rsub.flatten) := (hag.mono fun z hz => by
      rcases List.mem_cons.mp hz with rfl | h
      · exact List.mem_append.mpr (.inl (List.mem_cons_self ..))
      · rcases hRin z h with h | h
        · exact List.mem_append.mpr (.inl (List.mem_cons_of_mem _ h))
        · exact List.mem_append.mpr (.inr h))
    have hRR := ((hLa.frame hagR).mono hW).det hL'
    subst hRR
    obtain rfl := List.append_cancel_left hSt
    subst hEt
    have hag0 : Agree σ σ1 (Fz ++ S) := Agree.ofPre (by rt_tac) hag
      (fun z hz => by simp only [List.mem_append, List.mem_cons] at hz ⊢; grind) (fun z hz => by
      rw [hag z (by simp only [List.mem_append, List.mem_cons] at hz ⊢; grind)]
      rcases List.mem_append.mp hz with h | h
      · exact hold z (hFza z h)
      · exact hold z (hI.allocS z h))
    obtain ⟨E', hf', hpe⟩ := hthaw W hW σ1 Γb Eb' hft hwb hag0
    refine ⟨E', ⟨hf', hpe.nodup_iff.mpr (nodup_append_disj.mpr ⟨hI'.nodup, hFzn,
        fun z h h' => hdX z (List.mem_cons_of_mem _ h') h⟩), ?_, by rw [thaw_keys hkb]; exact hI.keys⟩,
      fun z => ?_⟩
    · intro z hz hz'
      rcases List.mem_append.mp (hpe.mem_iff.mp hz') with h | h
      · exact hI'.disj z (List.mem_append.mpr (.inr (hS.mem_iff.mpr (List.mem_append.mpr (.inr hz))))) h
      · exact hI.disj z hz (hFz z h)
    · rw [hpe.mem_iff, List.mem_append]
      constructor
      · rintro (h | h)
        · exact .inl h
        · exact .inr ⟨List.mem_cons_of_mem _ h, fun e => hna z (hFza z h) e⟩
      · rintro (h | ⟨h, hne⟩)
        · exact .inl h
        · exact .inr ((List.mem_cons.mp h).resolve_left hne)
  have hSS : ∀ z ∈ S, z ∈ (σ.next :: Rsub.flatten) ++ Sb := fun z hz =>
    List.mem_append.mpr (.inr (hS.mem_iff.mpr (List.mem_append.mpr (.inr hz))))
  have hndF : (σ.next :: Fz).Nodup := List.nodup_cons.mpr ⟨fun h => hna _ (hFza _ h) rfl, hFzn⟩
  have hd : Disj (σ.next :: Fz) Eb := fun z hz hz' => by
    rcases List.mem_cons.mp hz with rfl | h
    · exact hna _ (hI.alloc _ (hEb _ hz')) rfl
    · exact hdEF z hz' h
  have hwf1 : WF (σ.alloc (.vec sub)).2 := hwf.alloc
  refine post_after (E₁ := (σ.next :: Fz) ++ Eb) ((Moves.allocate (v := .vec sub) hwf hI.alloc).relabel fun z => by
    rw [hEp.mem_iff]; simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      show (σ.alloc (Val.vec sub)).1 = σ.next from rfl]; grind) hwf ?_
  exact ret_cloK (σf := (σ.alloc (.vec sub)).2) hSin hSS (List.mem_cons_self ..) hre hR.2 hwf1 Agree.self
    (fun z hz => by
      rcases List.mem_cons.mp hz with rfl | h
      · simp [Store.alloc]
      · rw [hold z (hFza z h)]; exact hFza z h)
    hndF hd (fun z hz => by rw [hold z (hI.allocS z hz)]; exact hI.allocS z hz)
    (fun z hz h => by
      simp only [List.mem_append, List.mem_cons] at h
      rcases h with (rfl | h) | h
      · exact hna _ (hI.allocS _ hz) rfl
      · exact hI.disj z hz (hFz z h)
      · exact hI.disj z hz (hEb z h))
    (hE _ _ _ _ _ _ _ _ _ _ _ hb hIb hwf1 hR)


/-- `{ const x = mut p[lo..hi]; body }`: out of bounds, a panic; else a slice of its own, whose cell
is the frame's and only read, of the elements from `lo` up to `hi`, which the slice may change, the
vector's root out of reach while it lives; once it ends, the root owns again the vector and the
elements as the slice left them. -/
theorem lendSliceMut_ok [WorldOk F O ι.w] (hE : EvalOk F O n) (hx : lookup x Γ = none) (hp : PlaceTy Γ p (.vec g τ) true y)
    (hlo : PlaceTy Γ (.var lo) .int w1 y1) (hhi : PlaceTy Γ (.var hi) .int w2 y2)
    (hb : Typed F O ((x, .ref .mut (.vec false τ)) :: hide Γ y) body τb ((x, .ref .mut (.vec false τ)) :: Γb) r)
    (hI : Inv F ι σ Γ env E S) (hwf : WF σ) (hR : Ready O hs r) :
    Post F ι O σ E S (thaw Γ [y] Γb) env τb r hs (evalS F O n hs σ env (.lendSlice x .mut p lo hi body)) := by
  obtain ⟨a0, τr, Lr, P, c, s, ha0, hLr, hpath, hres, hsub, hsubE, hsl, hso, hexw, hslot, hshp, hty⟩ := place_ok hp hI.foot
  have hsx := hexw rfl
  obtain ⟨Rc, hRc, -⟩ := path_split hpath hLr
  cases hRc with
  | vec hcm hlen hel hnd hcn =>
  rename_i cs Rs
  have intOf : ∀ {v w' yv}, PlaceTy Γ (.var v) .int w' yv → ∃ l k, lookup v env = some l ∧ σ.mem l = some (.int k) := by
    intro v w' yv hv
    obtain ⟨az, τz, Lz, Pz, lz, sz, -, hLz, hpathz, hresz, -⟩ := place_ok hv hI.foot
    obtain ⟨Rz, hRz, -⟩ := path_split hpathz hLz
    cases hRz with
    | int hk => exact ⟨lz, _, hresz, hk⟩
  obtain ⟨l1, i, hl1, hi⟩ := intOf hlo
  obtain ⟨l2, j, hl2, hj⟩ := intOf hhi
  simp only [evalS, hres, hl1, hl2, hcm, hi, hj]
  split
  case isFalse => simp [Post]
  rename_i hbd
  obtain ⟨hi0, hij, hjn⟩ := hbd
  obtain ⟨Os, Rm, hLrp, hRml, hRmel, hjoin⟩ :=
    range_reach (i := i.toNat) (m := j.toNat - i.toNat) hpath hLr hcm (by omega)
  generalize hsubd : (cs.drop i.toNat).take (j.toNat - i.toNat) = sub
  -- The path's cells: those the slice's frame keeps, `Pk`, and the root's first cell, `Ph`, if the
  -- root is a shell, which stays shared.
  have hsplit : ∃ Ph Pk, P ++ c :: Os = Ph ++ Pk ∧ sharedPart s Lr = Ph ∧
      (exclPart s Lr).Perm (Pk ++ Rm.flatten) := by
    cases hsh : s.shell
    · refine ⟨[], P ++ c :: Os, rfl, by simp [sharedPart_plain hsh, hsx], ?_⟩
      rw [exclPart_plain hsh, if_pos hsx]; simpa using hLrp
    · obtain ⟨R0, rfl⟩ := hso.head_of_shell hsh
      have hpa : ∃ Pt, P ++ c :: Os = a0 :: Pt := by
        rcases hshp hsh with ⟨rfl, -⟩ | ⟨-, P', rfl⟩
        · cases hpath; exact ⟨Os, rfl⟩
        · exact ⟨P' ++ c :: Os, rfl⟩
      obtain ⟨Pt, hPt⟩ := hpa
      refine ⟨[a0], Pt, hPt, by simp [sharedPart, hsx, hsh], ?_⟩
      simp only [exclPart, hsx, hsh, ↓reduceIte, List.tail_cons]
      rw [hPt] at hLrp
      simpa using hLrp
  obtain ⟨Ph, Pk, hPP, hPh, hPk⟩ := hsplit
  have hPhS : ∀ z ∈ Ph, z ∈ S := fun z hz => hsub.2 z (hPh ▸ hz)
  have hPkE : ∀ z ∈ Pk, z ∈ E := fun z hz => hsub.1 z (hPk.mem_iff.mpr (List.mem_append.mpr (.inl hz)))
  have hRmE : ∀ z ∈ Rm.flatten, z ∈ E := fun z hz => hsub.1 z (hPk.mem_iff.mpr (List.mem_append.mpr (.inr hz)))
  -- The root out of reach.
  have hxk : x ∉ (hide Γ y).map Prod.fst := by rw [hide_keys]; exact lookup_none_keys hx
  have hwb := typed_weaker hb (List.nodup_cons.mpr ⟨hxk, by rw [hide_keys]; exact hI.keys⟩)
  cases hwb with
  | cons _ hwb =>
  obtain ⟨Eh, hfh, hEh, hreb⟩ := hI.foot.hiddenX hI.keys ⟨hsl, ha0, hso⟩ hsx
  have hEp : E.Perm (Rm.flatten ++ Eh ++ Pk) := hEh.trans (by
    refine (hPk.append_right Eh).trans ?_
    exact List.perm_iff_count.mpr fun z => by simp only [List.count_append]; omega)
  obtain ⟨hBn, hPkn, hdBP⟩ := nodup_append_disj.mp (hEp.nodup_iff.mp hI.nodup)
  obtain ⟨hRmn, hEhn, hdRE⟩ := nodup_append_disj.mp hBn
  have hEhE : ∀ z ∈ Eh, z ∈ E := fun z h => hEp.mem_iff.mpr (by simp [h])
  have hBE : ∀ z ∈ Rm.flatten ++ Eh, z ∈ E := fun z h => hEp.mem_iff.mpr (List.mem_append.mpr (.inl h))
  -- The slice's cell, new.
  have hold : ∀ z, σ.mem z ≠ none → (σ.alloc (.vec sub)).2.mem z = σ.mem z := fun z hz => by
    simp only [Store.alloc]; rw [if_neg (fun e => Nat.lt_irrefl _ (e ▸ hwf z hz))]
  have hna : ∀ z, σ.mem z ≠ none → z ≠ σ.next := fun z hz e => Nat.lt_irrefl _ (e ▸ hwf z hz)
  have hRma : ∀ z ∈ Rm.flatten, σ.mem z ≠ none := fun z hz => hI.alloc z (hRmE z hz)
  have hbRm : σ.next ∉ Rm.flatten := fun h => hna _ (hRma _ h) rfl
  have hLb : LT F ι (σ.alloc (.vec sub)).2 σ.next (.vec false τ) (σ.next :: Rm.flatten) := by
    refine .vec (cs := sub) (by simp [Store.alloc]) (by rw [← hsubd, hRml]; simp; omega) (fun k hk1 hk2 => ?_)
      hRmn hbRm
    have hk' : k < j.toNat - i.toNat := by rw [← hsubd] at hk1; simp at hk1; omega
    have e1 : sub[k] = cs[i.toNat + k]'(by omega) := by subst hsubd; simp
    rw [e1]
    exact (hRmel k hk' hk2).frame (Agree.of' fun z hz => hold z (hRma z (mem_flatten_of hk2 hz)))
  have hIb : Inv F ι (σ.alloc (.vec sub)).2 ((x, .ref .mut (.vec false τ)) :: hide Γ y) ((x, σ.next) :: env)
      (Rm.flatten ++ Eh) (σ.next :: S) := by
    have hfoot := Foot.cons (s := .ref .mut (.vec false τ)) (x := x) (a := σ.next) hLb
      (hfh.frame <| Agree.of' fun z hz => hold z (hfh.alloc z (List.mem_append.mp hz)))
    refine ⟨by simpa [addE, addS, exclPart, sharedPart, Slot.excl, Slot.shell, Ty.shell] using hfoot, hBn, ?_,
      List.nodup_cons.mpr ⟨hxk, by rw [hide_keys]; exact hI.keys⟩⟩
    intro z hz hz'
    rcases List.mem_cons.mp hz with rfl | h
    · exact hna _ (hI.alloc _ (hBE _ hz')) rfl
    · exact hI.disj z h (hBE z hz')
  have hkb : Γb.map Prod.fst = Γ.map Prod.fst := by
    have := typed_keys hb
    simp only [List.map_cons, List.cons.injEq] at this
    rw [this.2]; exact hide_keys
  have hPPa : ∀ z ∈ P ++ c :: Os, σ.mem z ≠ none := fun z hz =>
    hLr.alloc z (hLrp.mem_iff.mpr (List.mem_append.mpr (.inl hz)))
  have hPn : (P ++ c :: Os).Nodup := (nodup_append_disj.mp (hLrp.nodup_iff.mp hLr.nodup)).1
  have hre : ∀ W, ι.w.le W → ∀ σ2 Eb', Agree (σ.alloc (.vec sub)).2 σ2 ((σ.next :: Pk) ++ S) → Disj (σ.next :: Pk) Eb' →
      Inv F (ι.inW W) σ2 ((x, .ref .mut (.vec false τ)) :: Γb) ((x, σ.next) :: env) Eb' (σ.next :: S) →
      ∃ E', Inv F (ι.inW W) σ2 (thaw Γ [y] Γb) env E' S ∧ ∀ z, z ∈ E' ↔ z ∈ Eb' ∨ (z ∈ σ.next :: Pk ∧ z ≠ σ.next) := by
    intro W hW σ2 Eb' hag hdX hI'
    obtain ⟨L', Et, St, hL', hft, hEt, hSt⟩ := hI'.foot.uncons
    -- The slice's cell holds the cells it was made of: it was only read.
    have hb2 : σ2.mem σ.next = some (.vec sub) := by
      rw [hag _ (List.mem_append.mpr (.inl (List.mem_cons_self ..)))]; simp [Store.alloc]
    simp only [SlotOk] at hL'
    cases hL' with
    | vec hcm2 hlen2 hel2 hnd2 hn2 =>
    rename_i cs2 Rn
    rw [hb2] at hcm2
    cases hcm2
    simp only [addE, addS, exclPart, sharedPart, Slot.excl, Slot.shell, Ty.shell, ↓reduceIte, List.tail_cons,
      List.take_succ_cons, List.take_zero, List.singleton_append, List.cons.injEq, true_and] at hEt hSt
    subst hEt hSt
    have hagσ : ∀ L, (∀ z ∈ L, σ.mem z ≠ none) → (∀ z ∈ L, z ∈ σ.next :: Pk ∨ z ∈ S) → Agree σ σ2 L :=
      fun L hL hLX => (Agree.of' fun z hz => hold z (hL z hz)).trans (hag.mono fun z hz => by
        rcases hLX z hz with h | h
        · exact List.mem_append.mpr (.inl h)
        · exact List.mem_append.mpr (.inr h))
    have hagP : Agree σ σ2 (P ++ c :: Os) := hagσ _ hPPa (fun z hz => by
      rw [hPP] at hz
      rcases List.mem_append.mp hz with h | h
      · exact .inr (hPhS z h)
      · exact .inl (List.mem_cons_of_mem _ h))
    have hRnl : Rn.length = j.toNat - i.toNat := by rw [hlen2, ← hsubd]; simp; omega
    have hel3 : ∀ k (h : k < j.toNat - i.toNat) (h' : k < Rn.length),
        LT F (ι.inW W) σ2 (cs[i.toNat + k]'(by omega)) τ Rn[k] := by
      intro k h h'
      have hk2 : k < sub.length := by rw [← hsubd]; simp; omega
      have e1 : sub[k] = cs[i.toNat + k]'(by omega) := by subst hsubd; simp
      rw [← e1]; exact hel2 k hk2 h'
    have hdR : Disj (P ++ c :: Os) Rn.flatten := fun z hz h => by
      rw [hPP] at hz
      rcases List.mem_append.mp hz with hz | hz
      · exact hI'.disj z (List.mem_cons_of_mem _ (hPhS z hz)) (List.mem_append.mpr (.inl h))
      · exact hdX z (List.mem_cons_of_mem _ hz) (List.mem_append.mpr (.inl h))
    obtain ⟨L'', hL'', hL''p⟩ := hjoin W hW σ2 Rn hPn hagP hRnl hel3 hnd2 hdR
    have hso'' := hslot _ σ2 _ hL''
    have hsheq : sharedPart s L'' = sharedPart s Lr := SlotOk.shared_eq (hso.mono hW) hso'' rfl hsx hsx
    have hagS : Agree σ σ2 S := hagσ S hI.allocS (fun z hz => .inr hz)
    obtain ⟨E', hf', hp'⟩ := hreb W hW σ2 Γb Et L'' hft hwb hagS hso'' hsheq
    have hexL : (exclPart s L'').Perm (Pk ++ Rn.flatten) := by
      rw [hPP] at hL''p
      cases hsh : s.shell
      · have hPh0 : Ph = [] := by rw [← hPh]; simp [sharedPart_plain hsh, hsx]
        subst hPh0
        rw [exclPart_plain hsh, if_pos hsx]; simpa using hL''p
      · obtain ⟨R1, rfl⟩ := hso''.head_of_shell hsh
        have hPh1 : Ph = [a0] := by
          rw [← hPh]; obtain ⟨R0, rfl⟩ := hso.head_of_shell hsh; simp [sharedPart, hsx, hsh]
        subst hPh1
        simp only [exclPart, hsx, hsh, ↓reduceIte, List.tail_cons]
        simpa using hL''p
    have hp'' : E'.Perm ((Rn.flatten ++ Et) ++ Pk) := hp'.trans (by
      refine (hexL.append_right Et).trans ?_
      exact List.perm_iff_count.mpr fun z => by simp only [List.count_append]; omega)
    refine ⟨E', ⟨hf', hp''.nodup_iff.mpr (nodup_append_disj.mpr ⟨hI'.nodup, hPkn,
        fun z h h' => hdX z (List.mem_cons_of_mem _ h') h⟩), ?_, by rw [thaw_keys hkb]; exact hI.keys⟩,
      fun z => ?_⟩
    · intro z hz hz'
      rcases List.mem_append.mp (hp''.mem_iff.mp hz') with h | h
      · exact hI'.disj z (List.mem_cons_of_mem _ hz) h
      · exact hI.disj z hz (hPkE z h)
    · rw [hp''.mem_iff, List.mem_append]
      constructor
      · rintro (h | h)
        · exact .inl h
        · exact .inr ⟨List.mem_cons_of_mem _ h, fun e => hna z (hI.alloc z (hPkE z h)) e⟩
      · rintro (h | ⟨h, hne⟩)
        · exact .inl h
        · exact .inr ((List.mem_cons.mp h).resolve_left hne)
  have hSin : ∀ z ∈ σ.next :: S, z ∈ (σ.next :: Pk) ∨ z ∈ S := fun z hz => by
    rcases List.mem_cons.mp hz with rfl | h
    · exact .inl (List.mem_cons_self ..)
    · exact .inr h
  have hPka : ∀ z ∈ Pk, σ.mem z ≠ none := fun z h => hI.alloc z (hPkE z h)
  have hnd : (σ.next :: Pk).Nodup := List.nodup_cons.mpr ⟨fun h => hna _ (hPka _ h) rfl, hPkn⟩
  have hd : Disj (σ.next :: Pk) (Rm.flatten ++ Eh) := fun z hz hz' => by
    rcases List.mem_cons.mp hz with rfl | h
    · exact hna _ (hI.alloc _ (hBE _ hz')) rfl
    · exact hdBP z hz' h
  have hwf1 : WF (σ.alloc (.vec sub)).2 := hwf.alloc
  refine post_after (E₁ := (σ.next :: Pk) ++ (Rm.flatten ++ Eh))
    ((Moves.allocate (v := .vec sub) hwf hI.alloc).relabel fun z => by
      rw [hEp.mem_iff]; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        show (σ.alloc (Val.vec sub)).1 = σ.next from rfl]; grind) hwf ?_
  exact ret_cloK (σf := (σ.alloc (.vec sub)).2) hSin (fun z hz => List.mem_cons_of_mem _ hz)
    (List.mem_cons_self ..) hre hR.2 hwf1 Agree.self
    (fun z hz => by
      rcases List.mem_cons.mp hz with rfl | h
      · simp [Store.alloc]
      · rw [hold z (hPka z h)]; exact hPka z h)
    hnd hd (fun z hz => by rw [hold z (hI.allocS z hz)]; exact hI.allocS z hz)
    (fun z hz h => by
      simp only [List.mem_append, List.mem_cons] at h
      rcases h with (rfl | h) | h | h
      · exact hna _ (hI.allocS _ hz) rfl
      · exact hI.disj z hz (hPkE z h)
      · exact hI.disj z hz (hRmE z h)
      · exact hI.disj z hz (hEhE z h))
    (hE _ _ _ _ _ _ _ _ _ _ _ hb hIb hwf1 hR)


theorem lendSlice_any [WorldOk F O ι.w] {m : Mode} (hE : EvalOk F O n) (hx : lookup x Γ = none) (hp : PlaceTy Γ p (.vec g τ) w y)
    (hlo : PlaceTy Γ (.var lo) .int w1 y1) (hhi : PlaceTy Γ (.var hi) .int w2 y2) (hm : m = .mut → w = true)
    (hb : Typed F O ((x, .ref m (.vec false τ)) :: lendCtx m Γ y) body τb ((x, .ref m (.vec false τ)) :: Γb) r)
    (hI : Inv F ι σ Γ env E S) (hwf : WF σ) (hR : Ready O hs r) :
    Post F ι O σ E S (thaw Γ [y] Γb) env τb r hs (evalS F O n hs σ env (.lendSlice x m p lo hi body)) := by
  cases m with
  | ro => exact lendSlice_ok hE hx hp hlo hhi hb hI hwf hR
  | «mut» => obtain rfl := hm rfl; exact lendSliceMut_ok hE hx hp hlo hhi hb hI hwf hR

end FlyCore.Ownership
