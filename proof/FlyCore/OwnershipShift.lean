import FlyCore.OwnershipCall

/-!
# Ownership: regions, seen from one region further in

Entering a region puts its arena innermost: the types of the code around count one more region out,
and say the same of the same cells. A type no region is part of says the same of a value wherever
the code is, which is how values cross calls, handlers and tasks.
-/

namespace FlyCore.Ownership

theorem Ty.shiftBy_ite {t : Bool} {A B : Ty} : (if t then A else B).shiftBy n = if t then A.shiftBy n else B.shiftBy n := by
  cases t <;> rfl

theorem Ty.rfree_ite {t : Bool} {A B : Ty} (hA : A.rfree = true) (hB : B.rfree = true) :
    (if t then A else B).rfree = true := by
  cases t <;> simpa

theorem RefOk.shift_iff : RefOk (a :: ι) σ (k + 1) τ l ↔ RefOk ι σ k τ l := by
  simp [RefOk]

/-! ## What no region is part of -/

theorem LT.rfree_iota (h : LT F ι σ c τ L) (hr : τ.rfree = true) : LT F ι' σ c τ L := by
  induction h with
  | int ha => exact .int ha
  | box ha _ hn ih => exact .box ha (ih (by simpa [Ty.rfree] using hr)) hn
  | clo ha hc _ hn ih => exact .clo ha hc (ih hc.rfree) hn
  | pair ha _ _ hd hn ih1 ih2 =>
    simp only [Ty.rfree, Bool.and_eq_true] at hr
    exact .pair ha (ih1 hr.1) (ih2 hr.2) hd hn
  | tag ha _ hn ih =>
    simp only [Ty.rfree, Bool.and_eq_true] at hr
    exact .tag ha (ih (Ty.rfree_ite hr.1 hr.2)) hn
  | hole => exact .hole
  | rref => simp [Ty.rfree] at hr
  | arena => simp [Ty.rfree] at hr

theorem VT.rfree_iota (h : VT F ι σ τ v L) (hr : τ.rfree = true) : VT F ι' σ τ v L := by
  cases h with
  | int => exact .int
  | box h hc => exact .box (h.rfree_iota (by simpa [Ty.rfree] using hr)) hc
  | clo hc h hc' => exact .clo hc (h.rfree_iota hc.rfree) hc'
  | pair h1 h2 hd hA hB =>
    simp only [Ty.rfree, Bool.and_eq_true] at hr
    exact .pair (h1.rfree_iota hr.1) (h2.rfree_iota hr.2) hd hA hB
  | tag h hA hB =>
    simp only [Ty.rfree, Bool.and_eq_true] at hr
    exact .tag (h.rfree_iota (Ty.rfree_ite hr.1 hr.2)) hA hB
  | rref => simp [Ty.rfree] at hr

theorem Vals.rfree_iota (h : Vals F ι σ τs vs Ls) (hr : ∀ τ ∈ τs, τ.rfree = true) : Vals F ι' σ τs vs Ls := by
  induction h with
  | nil => exact .nil
  | cons hv _ ih =>
    exact .cons (hv.rfree_iota (hr _ (List.mem_cons_self ..))) (ih fun τ hτ => hr τ (List.mem_cons_of_mem _ hτ))

theorem Op.owns_rfree (op : Op) : ∀ τ ∈ op.owns, τ.rfree = true := by
  have := op.rfree
  simp only [Bool.and_eq_true, List.all_eq_true] at this
  exact this.1.1

theorem Op.refs_rfree (op : Op) : ∀ p ∈ op.refs, p.2.rfree = true := by
  have := op.rfree
  simp only [Bool.and_eq_true, List.all_eq_true] at this
  exact this.1.2

theorem Op.ret_rfree (op : Op) : op.ret.rfree = true := by
  have := op.rfree
  simp only [Bool.and_eq_true, List.all_eq_true] at this
  exact this.2

/-! ## One region further in -/

theorem LT.shift (h : LT F ι σ c τ L) : LT F (a :: ι) σ c (τ.shiftBy 1) L := by
  induction h with
  | int ha => exact .int ha
  | box ha _ hn ih => exact .box ha ih hn
  | clo ha hc hb hn _ => exact .clo ha hc (hb.rfree_iota hc.rfree) hn
  | pair ha _ _ hd hn ih1 ih2 => exact .pair ha ih1 ih2 hd hn
  | tag ha _ hn ih =>
    refine .tag ha ?_ hn
    rw [← Ty.shiftBy_ite]; exact ih
  | hole => exact .hole
  | rref ha hr => exact .rref ha (RefOk.shift_iff.mpr hr)
  | arena hk ha hnd hn hcs hex =>
    refine .arena (by simpa using hk) ha hnd hn (fun l hl => ?_) hex
    obtain ⟨τ, v, h1, h2, h3⟩ := hcs l hl
    exact ⟨τ, v, h1, h2, by simpa using h3⟩

theorem LT.unshift : ∀ {τ : Ty} {c : Nat} {L : List Nat}, LT F (a :: ι) σ c (τ.shiftBy 1) L → LT F ι σ c τ L
  | .int, _, _, h => by simp only [Ty.shiftBy] at h; cases h with | int ha => exact .int ha
  | .box τ, _, _, h => by
    simp only [Ty.shiftBy] at h
    cases h with | box ha hb hn => exact .box ha (LT.unshift hb) hn
  | .fn _ _ _ _, _, _, h => by
    simp only [Ty.shiftBy] at h
    cases h with | clo ha hc hb hn => exact .clo ha hc (hb.rfree_iota hc.rfree) hn
  | .pair A B, _, _, h => by
    simp only [Ty.shiftBy] at h
    cases h with | pair ha h1 h2 hd hn => exact .pair ha (LT.unshift h1) (LT.unshift h2) hd hn
  | .sum A B, _, _, h => by
    simp only [Ty.shiftBy] at h
    cases h with
    | tag ha hb hn =>
      rename_i t _ _
      refine .tag ha ?_ hn
      cases t
      · exact LT.unshift (τ := B) hb
      · exact LT.unshift (τ := A) hb
  | .hole τ, _, _, h => by simp only [Ty.shiftBy] at h; cases h; exact .hole
  | .rref c k τ, _, _, h => by
    simp only [Ty.shiftBy] at h
    cases h with | rref ha hr => exact .rref ha (RefOk.shift_iff.mp hr)
  | .arena k, _, _, h => by
    simp only [Ty.shiftBy] at h
    cases h with
    | arena hk ha hnd hn hcs hex =>
      refine .arena (by simpa using hk) ha hnd hn (fun l hl => ?_) hex
      obtain ⟨τ, v, h1, h2, h3⟩ := hcs l hl
      exact ⟨τ, v, h1, h2, by simpa using h3⟩

theorem Ty.complete_shift : ∀ {τ : Ty}, (τ.shiftBy n).complete = τ.complete
  | .int => rfl
  | .box τ => by simp [Ty.shiftBy, Ty.complete, Ty.complete_shift (τ := τ)]
  | .fn _ _ _ _ => rfl
  | .pair A B => by simp [Ty.shiftBy, Ty.complete, Ty.complete_shift (τ := A), Ty.complete_shift (τ := B)]
  | .sum A B => by simp [Ty.shiftBy, Ty.complete, Ty.complete_shift (τ := A), Ty.complete_shift (τ := B)]
  | .hole _ => rfl
  | .rref _ _ _ => rfl
  | .arena _ => rfl

theorem Ty.isHole_shift {τ : Ty} : (τ.shiftBy n).isHole = τ.isHole := by
  cases τ <;> rfl

theorem LT.unshift_ite {t : Bool} (h : LT F (a :: ι) σ c (if t then A.shiftBy 1 else B.shiftBy 1) L) :
    LT F ι σ c (if t then A else B) L := by
  cases t
  · exact LT.unshift (τ := B) h
  · exact LT.unshift (τ := A) h

theorem VT.shift (h : VT F ι σ τ v L) : VT F (a :: ι) σ (τ.shiftBy 1) v L := by
  cases h with
  | int => exact .int
  | box h hc => exact .box h.shift (by rw [Ty.complete_shift]; exact hc)
  | clo hc h hc' => exact .clo hc (h.rfree_iota hc.rfree) hc'
  | pair h1 h2 hd hA hB =>
    exact .pair h1.shift h2.shift hd (by rw [Ty.complete_shift]; exact hA) (by rw [Ty.complete_shift]; exact hB)
  | tag h hA hB =>
    exact .tag (by rw [← Ty.shiftBy_ite]; exact h.shift) (by rw [Ty.complete_shift]; exact hA)
      (by rw [Ty.complete_shift]; exact hB)
  | rref hr => exact .rref (RefOk.shift_iff.mpr hr)

theorem VT.unshift : ∀ {τ : Ty} {v : Val} {L : List Nat}, VT F (a :: ι) σ (τ.shiftBy 1) v L → VT F ι σ τ v L
  | .int, _, _, h => by simp only [Ty.shiftBy] at h; cases h; exact .int
  | .box τ, _, _, h => by
    simp only [Ty.shiftBy] at h
    cases h with | box hb hc => exact .box (LT.unshift hb) (by rwa [Ty.complete_shift] at hc)
  | .fn _ _ _ _, _, _, h => by
    simp only [Ty.shiftBy] at h
    cases h with | clo hc hb hc' => exact .clo hc (hb.rfree_iota hc.rfree) hc'
  | .pair A B, _, _, h => by
    simp only [Ty.shiftBy] at h
    cases h with
    | pair h1 h2 hd hA hB =>
      exact .pair (LT.unshift h1) (LT.unshift h2) hd (by rwa [Ty.complete_shift] at hA) (by rwa [Ty.complete_shift] at hB)
  | .sum A B, _, _, h => by
    simp only [Ty.shiftBy] at h
    cases h with
    | tag hb hA hB =>
      exact .tag (LT.unshift_ite hb) (by rwa [Ty.complete_shift] at hA) (by rwa [Ty.complete_shift] at hB)
  | .hole _, _, _, h => by simp only [Ty.shiftBy] at h; cases h
  | .rref c k τ, _, _, h => by
    simp only [Ty.shiftBy] at h
    cases h with | rref hr => exact .rref (RefOk.shift_iff.mp hr)
  | .arena _, _, _, h => by simp only [Ty.shiftBy] at h; cases h

theorem Slot.excl_shift {s : Slot} : (s.shiftBy n).excl = s.excl := by
  cases s with
  | own => rfl
  | ref m τ => cases m <;> rfl
  | lent => rfl
  | half => rfl

theorem Slot.shell_shift {s : Slot} : (s.shiftBy n).shell = s.shell := by
  cases s with
  | own => rfl
  | ref m τ => cases m <;> cases τ <;> rfl
  | lent => rfl
  | half => rfl

theorem exclPart_shift {s : Slot} : exclPart (s.shiftBy n) L = exclPart s L := by
  simp [exclPart, Slot.excl_shift, Slot.shell_shift]

theorem sharedPart_shift {s : Slot} : sharedPart (s.shiftBy n) L = sharedPart s L := by
  simp [sharedPart, Slot.excl_shift, Slot.shell_shift]

theorem Ty.lent1_shift {t : Bool} : (Ty.lent1 t A B).shiftBy n = Ty.lent1 t (A.shiftBy n) (B.shiftBy n) := by
  cases t <;> rfl

theorem SlotOk.shift (h : SlotOk F ι σ s c L) : SlotOk F (a :: ι) σ (s.shiftBy 1) c L := by
  cases s with
  | own τ live =>
    cases live with
    | true => exact LT.shift (τ := τ) h
    | false =>
      rcases h with h | ⟨h, hh⟩
      · exact .inl h
      · exact .inr ⟨h.shift, by rw [Ty.isHole_shift]; exact hh⟩
  | ref m τ => exact LT.shift (τ := τ) h
  | lent τ => exact h
  | half t A B =>
    simp only [Slot.shiftBy, SlotOk] at h ⊢
    rw [← Ty.lent1_shift]; exact h.shift

theorem SlotOk.unshift (h : SlotOk F (a :: ι) σ (s.shiftBy 1) c L) : SlotOk F ι σ s c L := by
  cases s with
  | own τ live =>
    cases live with
    | true => exact LT.unshift (τ := τ) h
    | false =>
      rcases h with h | ⟨h, hh⟩
      · exact .inl h
      · exact .inr ⟨LT.unshift h, by rw [Ty.isHole_shift] at hh; exact hh⟩
  | ref m τ => exact LT.unshift (τ := τ) h
  | lent τ => exact h
  | half t A B =>
    simp only [Slot.shiftBy, SlotOk] at h ⊢
    rw [← Ty.lent1_shift] at h; exact LT.unshift h

theorem Foot.shift (h : Foot F ι σ Γ env E S) : Foot F (a :: ι) σ (Ctx.shift Γ) env E S := by
  induction h with
  | nil => exact .nil
  | @cons s c L Γ env E S x hs _ ih =>
    have := Foot.cons (x := x) hs.shift ih
    simpa [Ctx.shift, addE, addS, exclPart_shift, sharedPart_shift] using this

theorem Foot.unshift : ∀ {Γ : Ctx} {env : Env} {E S : List Nat}, Foot F (a :: ι) σ (Ctx.shift Γ) env E S → Foot F ι σ Γ env E S
  | [], _, _, _, h => by simp only [Ctx.shift, List.map_nil] at h; cases h; exact .nil
  | (x, s) :: Γ, _, _, _, h => by
    simp only [Ctx.shift, List.map_cons] at h
    cases h with
    | cons hs hr =>
      have := Foot.cons (x := x) hs.unshift (Foot.unshift hr)
      simpa [addE, addS, exclPart_shift, sharedPart_shift] using this

theorem Ctx.shift_keys (Γ : Ctx) : (Ctx.shift Γ).map Prod.fst = Γ.map Prod.fst := by
  simp [Ctx.shift, Function.comp_def]

theorem Inv.shift (h : Inv F ι σ Γ env E S) : Inv F (a :: ι) σ (Ctx.shift Γ) env E S :=
  ⟨h.foot.shift, h.nodup, h.disj, by rw [Ctx.shift_keys]; exact h.keys⟩

theorem Inv.unshift (h : Inv F (a :: ι) σ (Ctx.shift Γ) env E S) : Inv F ι σ Γ env E S :=
  ⟨h.foot.unshift, h.nodup, h.disj, by rw [← Ctx.shift_keys]; exact h.keys⟩

end FlyCore.Ownership
