import FlyCore.OwnershipKont

/-!
# Ownership: dropping what holds continuations

Dropping a value frees the cells it owns at once, but a continuation it holds has cleanup to run: it
is left for `flush` to drop, unwinding it. What both together leave is `Dropped`: the value's
footprint freed, and every other cell as it was, those allocated meanwhile freed again.
-/

namespace FlyCore.Ownership

variable {F : List Fn} {O : List Op}

/-- The continuations `ks`, holding the cells `Y` between them, are as their types say. -/
def KontsOk (_F : List Fn) (_ι : Iota) (_σ : Store) (ks : List (List Kont)) (Y : List Nat) : Prop :=
  ks = [] ∧ Y = []

/-- What dropping the cells `D` left, where the store was `σ`. -/
abbrev Dropped (σ : Store) (D : List Nat) (σ' : Store) : Prop := Moves σ D σ' [] []

/-- How dropping continuations that own `D` ended: with them dropped, or out of fuel, or a panic in
their cleanup. -/
def FlushGives (x : Res × Store) (σ : Store) (D : List Nat) : Prop :=
  x.1 = .timeout ∨ x.1 = .panic ∨ ∃ v σ', x = (.val v, σ') ∧ Dropped σ D σ'

/-- `fl` drops continuations as their types say. -/
def FlushOk (F : List Fn) (ι : Iota) (fl : Flush) : Prop :=
  ∀ σ ks Y, WF σ → KontsOk F ι σ ks Y → FlushGives (fl ks σ) σ Y

theorem FlushGives.bind {P : Res × Store → Prop} (h : FlushGives x σ D)
    (hk : ∀ σ', Dropped σ D σ' → P (k σ')) (ht : ∀ σ', P (.timeout, σ')) (hp : ∀ σ', P (.panic, σ')) :
    P (andThen x k) := by
  rcases x with ⟨r, σ1⟩
  rcases h with h | h | ⟨v, σ', h, hd⟩
  · simp only at h; subst h; exact ht σ1
  · simp only at h; subst h; exact hp σ1
  · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact hk _ hd

/-- What dropping continuations leaves, said of what an expression gives after. -/
theorem FlushGives.post (h : FlushGives x σ D)
    (hk : ∀ σ', Dropped σ D σ' → Post F ι O σ0 E S Γ env τ r hs (k σ')) :
    Post F ι O σ0 E S Γ env τ r hs (andThen x k) :=
  h.bind (P := Post F ι O σ0 E S Γ env τ r hs) hk (fun _ => trivial) (fun _ => trivial)

theorem kontsK_nil : ∀ (k : Nat) (τ : Ty) (σ : Store) v L, VT F ι σ τ v L → kontsK k σ τ v = [] := by
  intro k
  induction k with
  | zero => intro τ σ v L h; cases h <;> simp [kontsK]
  | succ k ih =>
    intro τ σ v L h
    cases h with
    | int => simp [kontsK]
    | rref => simp [kontsK]
    | box hb hc =>
      obtain ⟨w, R', hw, hv, -, -⟩ := hb.contents hc
      simp [kontsK, hw, ih _ _ _ _ hv]
    | clo _ hb hc =>
      obtain ⟨w, R', hw, hv, -, -⟩ := hb.contents hc
      simp [kontsK, hw, ih _ _ _ _ hv]
    | tag hb hA hB =>
      obtain ⟨w, R', hw, hv, -, -⟩ := hb.contents (Ty.complete_ite hA hB)
      simp [kontsK, hw, ih _ _ _ _ hv]
    | pair h1 h2 _ hA hB =>
      obtain ⟨w, R₁', hw, hv1, -, -⟩ := h1.contents hA
      obtain ⟨u, R₂', hu, hv2, -, -⟩ := h2.contents hB
      simp [kontsK, hw, hu, ih _ _ _ _ hv1, ih _ _ _ _ hv2]
    | vec hlen hel _ hc =>
      simp only [kontsK, List.flatMap_eq_nil_iff]
      intro c hcs
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcs
      obtain ⟨w, R', hw, hv, -, -⟩ := (hel i hi (by omega)).contents hc
      simp [hw, ih _ _ _ _ hv]

/-- A value's continuations, as dropping it leaves them. -/
theorem konts_ok (h : VT F ι σ τ v L) : KontsOk F ι σ' (konts σ τ v) [] :=
  ⟨kontsK_nil _ _ _ _ _ h, rfl⟩

/-- Dropping a value, and then the continuations it held, frees what it owns. -/
theorem dropF (hfl : FlushOk F ι fl) (hwf : WF σ) (h : VT F ι σ τ v L) :
    ∃ σ', drop σ τ v = some σ' ∧ FlushGives (fl (konts σ τ v) σ') σ L := by
  obtain ⟨σ', hd, hnext, hfree, hkeep⟩ := drop_ok hwf τ v L h
  have hwf' := WF.of_free hwf hnext hfree hkeep
  have hm : Dropped σ L σ' := Moves.free (D := L) hwf' hnext h.alloc (fun x => by simp) hfree hkeep
    disj_nil_left
  refine ⟨σ', hd, ?_⟩
  rcases hfl σ' _ [] hwf' (konts_ok (σ' := σ') h) with h1 | h1 | ⟨w, σ'', h1, hm'⟩
  · exact .inl h1
  · exact .inr (.inl h1)
  · exact .inr (.inr ⟨w, σ'', h1, (hm.trans hm' disj_nil_left hwf).relabel fun x => by simp⟩)

theorem cellKonts_live (h : LT F ι σ c τ L) (hc : τ.complete = true) : cellKonts σ τ c = [] := by
  obtain ⟨w, R', hw, hv, -, -⟩ := h.contents hc
  have hk := kontsK_nil σ.next _ _ _ _ hv
  cases hv <;> simp_all [cellKonts, konts]

theorem cellKonts_own (hτ : τ.complete = true) (h : SlotOk F ι σ (.own τ live) c L) : cellKonts σ τ c = [] := by
  cases live with
  | true => exact cellKonts_live h hτ
  | false =>
    rcases h with ⟨hc, -⟩ | ⟨h, -⟩
    · simp [cellKonts, hc]
    · exact cellKonts_live h hτ

/-- Dropping an owned variable's cell, live or moved, and then the continuations it held, frees its
footprint. -/
theorem dropCellF (hfl : FlushOk F ι fl) (hwf : WF σ) (hτ : τ.complete = true)
    (h : SlotOk F ι σ (.own τ live) c L) :
    ∃ σ', dropCell σ τ c = some σ' ∧ FlushGives (fl (cellKonts σ τ c) σ') σ L := by
  obtain ⟨σ', hd, hnext, hfree, hkeep⟩ := dropCell_own hwf hτ h
  have hwf' := WF.of_free hwf hnext hfree hkeep
  have hL : ∀ l ∈ L, σ.mem l ≠ none := by
    cases live with
    | true => exact LT.alloc h
    | false =>
      rcases h with ⟨hc, rfl⟩ | ⟨h, -⟩
      · intro l hl; simp at hl; subst hl; simp [hc]
      · exact LT.alloc h
  have hm : Dropped σ L σ' := Moves.free (D := L) hwf' hnext hL (fun x => by simp) hfree hkeep
    disj_nil_left (dropCell_rt hd)
  refine ⟨σ', hd, ?_⟩
  rw [cellKonts_own hτ h]
  rcases hfl σ' [] [] hwf' ⟨rfl, rfl⟩ with h1 | h1 | ⟨w, σ'', h1, hm'⟩
  · exact .inl h1
  · exact .inr (.inl h1)
  · exact .inr (.inr ⟨w, σ'', h1, (hm.trans hm' disj_nil_left hwf).relabel fun x => by simp⟩)

theorem cellsKonts_nil : ∀ {Γo : Ctx} {σ : Store} {eo : Env} {Eo So} {owns : List (Var × Ty)},
    Foot F ι σ Γo eo Eo So → shape Γo = ownCtx owns → (∀ o ∈ owns, o.2.complete = true) →
    cellsKonts σ ((owns.map Prod.snd).zip (eo.map Prod.snd)) = []
  | [], σ, _, _, _, owns, h, hs, _ => by
    cases h
    cases owns with
    | nil => rfl
    | cons => simp [shape, ownCtx] at hs
  | (z, r) :: Γo, σ, _, _, _, owns, h, hs, hc => by
    cases h with
    | @cons _ c M _ eo E S _ hr hrest =>
    cases owns with
    | nil => simp [shape, ownCtx] at hs
    | cons o owns =>
    simp only [shape, ownCtx, List.map_cons, List.cons.injEq, Prod.mk.injEq] at hs
    obtain ⟨⟨-, hrs⟩, hs⟩ := hs
    cases r with
    | ref => simp [Slot.shape] at hrs
    | lent => simp [Slot.shape] at hrs
    | half => simp [Slot.shape] at hrs
    | own τ live =>
    simp only [Slot.shape, Slot.own.injEq] at hrs
    obtain ⟨rfl, -⟩ := hrs
    simp only [List.map_cons, List.zip_cons_cons, cellsKonts,
      cellKonts_own (hc _ (List.mem_cons_self ..)) hr, List.nil_append]
    exact cellsKonts_nil hrest hs fun o ho => hc o (List.mem_cons_of_mem _ ho)

/-- Dropping the callee's owned parameters, and then the continuations they held, frees their
footprints. -/
theorem dropCellsF (hfl : FlushOk F ι fl) (h : Foot F ι σ Γo eo Eo So) (hs : shape Γo = ownCtx owns)
    (hn : Eo.Nodup) (hwf : WF σ) (hc : ∀ o ∈ owns, o.2.complete = true) :
    So = [] ∧ ∃ σ', dropCells σ ((owns.map Prod.snd).zip (eo.map Prod.snd)) = some σ' ∧
      FlushGives (fl (cellsKonts σ ((owns.map Prod.snd).zip (eo.map Prod.snd))) σ') σ Eo := by
  obtain ⟨hSo, σ', hd, hnext, hfree, hkeep⟩ := dropCells_ok h hs hn hwf hc
  have hwf' := WF.of_free hwf hnext hfree hkeep
  have hm : Dropped σ Eo σ' := Moves.free (D := Eo) hwf' hnext (fun l hl => h.alloc l (.inl hl))
    (fun x => by simp) hfree hkeep disj_nil_left (dropCells_rt _ _ _ hd)
  refine ⟨hSo, σ', hd, ?_⟩
  rw [cellsKonts_nil h hs hc]
  rcases hfl σ' [] [] hwf' ⟨rfl, rfl⟩ with h1 | h1 | ⟨w, σ'', h1, hm'⟩
  · exact .inl h1
  · exact .inr (.inl h1)
  · exact .inr (.inr ⟨w, σ'', h1, (hm.trans hm' disj_nil_left hwf).relabel fun x => by simp⟩)

theorem flushR_ok : FlushOk F ι (flushR F O n) := by
  intro σ ks Y hwf ⟨hks, hY⟩
  subst hks hY
  cases n with
  | zero => exact .inl (by rw [flushR])
  | succ m => exact .inr (.inr ⟨.int 0, σ, by rw [flushR, flush], Moves.refl hwf (by simp)⟩)

/-- A step, and then the cells `D` of its footprint dropped. -/
theorem Moves.thenDrop (hm : Moves σ0 E σ1 (E₂ ++ D) L) (hd : Dropped σ1 D σ2)
    (hlive : ∀ l ∈ E₂ ++ L, σ1.mem l ≠ none) (hdisj : Disj (E₂ ++ L) D) (hwf : WF σ0) :
    Moves σ0 E σ2 E₂ L :=
  ((hm.relabel (E'' := (E₂ ++ L) ++ D) (L'' := []) fun x => by mem_iff).trans
    ((hd.widen hlive hdisj).congr_left fun x => Iff.rfl) disj_nil_left hwf).relabel fun x => by mem_iff

/-- An activation apart from the cells dropped stands. -/
theorem Inv.dropped (hI : Inv F ι σ1 Γ env E S) (hd : Dropped σ1 D σ2) (hwf : WF σ1) (hDE : Disj D E)
    (hDS : Disj D S) : Inv F ι σ2 Γ env E S :=
  ⟨hI.foot.frame (hd.keeps hwf (fun l hl => by
      rcases List.mem_append.mp hl with hl | hl
      · exact hI.alloc l hl
      · exact hI.allocS l hl)
    fun l hl h => by
      rcases List.mem_append.mp hl with hl | hl
      · exact hDE l h hl
      · exact hDS l h hl), hI.nodup, hI.disj, hI.keys⟩

theorem Dropped.keep (hd : Dropped σ D σ') (hwf : WF σ) : ∀ l, l ∉ D → σ'.mem l = σ.mem l := by
  intro l hl
  by_cases hn : l < σ.next
  · exact hd.frame l hn hl
  · have h0 : σ.mem l = none := by
      by_cases h : σ.mem l = none
      · exact h
      · exact absurd (hwf l h) hn
    rw [h0]
    by_cases h : σ'.mem l = none
    · exact h
    · rcases (hd.alloc l).mp h with ⟨h', -⟩ | h' | h'
      · exact absurd h0 h'
      · simp at h'
      · simp at h'

theorem Dropped.free (hd : Dropped σ D σ') : ∀ l ∈ D, σ'.mem l = none := by
  intro l hl
  by_cases h : σ'.mem l = none
  · exact h
  · rcases (hd.alloc l).mp h with ⟨-, h'⟩ | h' | h'
    · exact absurd hl h'
    · simp at h'
    · simp at h'

/-- Dropping no continuations: nothing, with fuel to spare. -/
theorem andThen_flushR_nil {P : Res × Store → Prop} (ht : P (.timeout, σ)) (hk : P (k σ)) :
    P (andThen (flushR F O n [] σ) k) := by
  cases n with
  | zero => rw [flushR]; exact ht
  | succ m => rw [flushR, flush]; exact hk

theorem post_flushR_nil (h : Post F ι O σ0 E S Γ env τ r hs (k σ)) :
    Post F ι O σ0 E S Γ env τ r hs (andThen (flushR F O n [] σ) k) :=
  andThen_flushR_nil (P := Post F ι O σ0 E S Γ env τ r hs) trivial h

@[simp] theorem konts_int : konts σ .int v = [] := by
  simp only [konts]; cases σ.next <;> cases v <;> simp [kontsK]

theorem flush_ok : FlushOk F ι (flush F O n) := by
  intro σ ks Y hwf ⟨hks, hY⟩
  subst hks hY
  exact .inr (.inr ⟨.int 0, σ, by rw [flush], Moves.refl hwf (by simp)⟩)

/-- `Moves.free`, for cells dropped with what they held. -/
theorem Moves.ofDropped (hd : Dropped σ D σ') (hE : ∀ l ∈ E, σ.mem l ≠ none)
    (hsplit : ∀ l, l ∈ E ↔ l ∈ E' ∨ l ∈ D) (hdisj : Disj E' D) : Moves σ E σ' E' [] :=
  ((hd.widen (X := E') (fun l hl => hE l ((hsplit l).mpr (.inl hl))) hdisj).congr_left fun x => by
    rw [hsplit, List.mem_append]).relabel fun x => by simp

end FlyCore.Ownership
