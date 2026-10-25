import FlyCore.OwnershipWorld

/-!
# Ownership: dropping what holds continuations

Dropping a value frees the cells it owns at once, but a continuation it holds has cleanup to run: it
is left for `flush` to drop, unwinding it. What both together leave is `Dropped`: the value's
footprint freed, and every other cell as it was, those allocated meanwhile freed again.
-/

namespace FlyCore.Ownership

variable {F : List Fn} {O : List Op}

/-- What dropping the cells `D` left, where the store was `σ`. -/
abbrev Dropped (σ : Store) (D : List Nat) (σ' : Store) : Prop := Moves σ D σ' [] []

/-- How dropping continuations that own `D` ended: with them dropped, or out of fuel, or a panic in
their cleanup. -/
def FlushGives (x : Res × Store) (σ : Store) (D : List Nat) : Prop :=
  x.1 = .timeout ∨ x.1 = .ended ∨ ∃ v σ', x = (.val v, σ') ∧ Dropped σ D σ'

/-- `fl` drops continuations as their types say, freeing what they own. -/
def FlushOk (F : List Fn) (ι : Iota) (fl : Flush) : Prop :=
  ∀ σ vs, WF σ → KontsOk F ι σ vs → FlushGives (fl vs σ) σ (vs.flatMap Val.foot)

theorem FlushGives.bind {P : Res × Store → Prop} (h : FlushGives x σ D)
    (hk : ∀ σ', Dropped σ D σ' → P (k σ')) (ht : ∀ σ', P (.timeout, σ')) (hp : ∀ σ', P (.ended, σ')) :
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

/-- Dropping a value's own cells, and then its continuations, which own the rest of its cells. -/
theorem FlushGives.after (hm : Moves σ L σ' Y []) (h : FlushGives x σ' Y) (hwf : WF σ) : FlushGives x σ L := by
  rcases h with h | h | ⟨w, σ'', h1, hm'⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨w, σ'', h1, (hm.trans hm' disj_nil_left hwf).relabel fun x => by simp⟩)

/-- A drop that frees `L` but `Y`, which it keeps. -/
theorem Moves.ofDrop {L Y : List Nat} (hwf : WF σ) (hnext : σ'.next = σ.next) (hL : ∀ l ∈ L, σ.mem l ≠ none)
    (hY : ∀ l ∈ Y, l ∈ L) (hfree : ∀ l ∈ L, l ∉ Y → σ'.mem l = none)
    (hkeep : ∀ l, l ∉ L ∨ l ∈ Y → σ'.mem l = σ.mem l) (hrt : σ'.rt = σ.rt) : Moves σ L σ' Y [] :=
  Moves.free (D := L.filter (· ∉ Y)) (WF.of_drop hwf hnext hfree hkeep) hnext hL
    (fun l => by
      simp only [List.mem_filter, decide_eq_true_eq]
      constructor
      · intro h; by_cases hy : l ∈ Y
        · exact .inl hy
        · exact .inr ⟨h, hy⟩
      · rintro (h | ⟨h, -⟩)
        · exact hY l h
        · exact h)
    (fun l hl => by simp only [List.mem_filter, decide_eq_true_eq] at hl; exact hfree l hl.1 hl.2)
    (fun l hl => hkeep l (by
      simp only [List.mem_filter, decide_eq_true_eq, not_and, Decidable.not_not] at hl
      by_cases h : l ∈ L
      · exact .inr (hl h)
      · exact .inl h))
    (fun l h1 h2 => by simp only [List.mem_filter, decide_eq_true_eq] at h2; exact h2.2 h1) hrt

/-- Dropping a value, and then the continuations it held, frees what it owns. -/
theorem dropF (hfl : FlushOk F ι fl) (hwf : WF σ) (h : VT F ι σ τ v L) :
    ∃ σ', drop σ τ v = some σ' ∧ FlushGives (fl (konts σ τ v) σ') σ L := by
  obtain ⟨σ', hd, hnext, hfree, hkeep⟩ := drop_ok hwf τ v L h
  obtain ⟨hk, hY⟩ := konts_ok h
  have hm := Moves.ofDrop hwf hnext h.alloc hY hfree hkeep (drop_rt hd)
  exact ⟨σ', hd, FlushGives.after hm (hfl σ' _ hm.wf (hk.frame (Agree.of (fun l hl => hkeep l (.inr hl))
    (drop_rt hd)))) hwf⟩

/-- Dropping an owned variable's cell, live or moved, and then the continuations it held, frees its
footprint. -/
theorem dropCellF (hfl : FlushOk F ι fl) (hwf : WF σ) (hτ : τ.complete = true)
    (h : SlotOk F ι σ (.own τ live) c L) :
    ∃ σ', dropCell σ τ c = some σ' ∧ FlushGives (fl (cellKonts σ τ c) σ') σ L := by
  obtain ⟨σ', hd, hnext, hfree, hkeep, hrt⟩ := dropCell_own hwf hτ h
  obtain ⟨hk, hY⟩ := cellKonts_ok hτ h
  have hL : ∀ l ∈ L, σ.mem l ≠ none := by
    cases live with
    | true => exact LT.alloc h
    | false =>
      rcases h with ⟨hc, rfl⟩ | ⟨h, -⟩
      · intro l hl; simp at hl; subst hl; simp [hc]
      · exact LT.alloc h
  have hm := Moves.ofDrop hwf hnext hL hY hfree hkeep hrt
  exact ⟨σ', hd, FlushGives.after hm (hfl σ' _ hm.wf (hk.frame (Agree.of (fun l hl => hkeep l (.inr hl)) hrt))) hwf⟩

/-- Dropping the callee's owned parameters, and then the continuations they held, frees their
footprints. -/
theorem dropCellsF (hfl : FlushOk F ι fl) (h : Foot F ι σ Γo eo Eo So) (hs : shape Γo = ownCtx owns)
    (hn : Eo.Nodup) (hwf : WF σ) (hc : ∀ o ∈ owns, o.2.complete = true) :
    So = [] ∧ ∃ σ', dropCells σ ((owns.map Prod.snd).zip (eo.map Prod.snd)) = some σ' ∧
      FlushGives (fl (cellsKonts σ ((owns.map Prod.snd).zip (eo.map Prod.snd))) σ') σ Eo := by
  obtain ⟨hSo, σ', hd, hnext, hfree, hkeep, hrt, hk, hY⟩ := dropCells_ok h hs hn hwf hc
  have hL : ∀ l ∈ Eo, σ.mem l ≠ none := fun l hl => h.alloc l (.inl hl)
  have hm := Moves.ofDrop hwf hnext hL hY hfree hkeep hrt
  exact ⟨hSo, σ', hd, FlushGives.after hm (hfl σ' _ hm.wf (hk.frame (Agree.of (fun l hl => hkeep l (.inr hl)) hrt)))
    hwf⟩


/-- The continuations values hold are found through cells they own, which another store that keeps
them, with as many cells, gives as well. -/
theorem kontsAll_frame (hn : σ'.next = σ.next) : ∀ {τs vs Ls}, Vals F ι σ τs vs Ls →
    (∀ l ∈ Ls.flatten, σ'.mem l = σ.mem l) → kontsAll σ' τs vs = kontsAll σ τs vs
  | _, _, _, .nil, _ => rfl
  | _, _, _, .cons hv hr, hag => by
    simp only [kontsAll, konts, hn]
    rw [kontsK_frame _ _ _ _ _ hv σ' fun l hl => hag l (by simp [hl]),
      kontsAll_frame hn hr fun l hl => hag l (by simp [hl])]

/-- Dropping values in turn frees what they own but their continuations, which are left as they were. -/
theorem dropAll_pure (hwf : WF σ) : ∀ {τs vs Ls}, Vals F ι σ τs vs Ls → Ls.flatten.Nodup →
    ∃ σ', dropAll σ τs vs = some σ' ∧ Moves σ Ls.flatten σ' ((kontsAll σ τs vs).flatMap Val.foot) [] ∧
      KontsOk F ι σ' (kontsAll σ τs vs) ∧ ∀ l ∈ (kontsAll σ τs vs).flatMap Val.foot, l ∈ Ls.flatten
  | _, _, _, .nil, _ => ⟨σ, rfl, by simpa [kontsAll] using Moves.refl hwf (E := []) (by simp),
      by simpa [kontsAll] using (KontsOk.nil : KontsOk F ι σ []), by simp [kontsAll]⟩
  | _, _, _, .cons (τ := τ) (v := v) (L := L) (τs := τs) (vs := vs) (Ls := Ls) hv hr, hn => by
    obtain ⟨σ1, hd, hnext, hfree, hkeep⟩ := drop_ok hwf τ v L hv
    obtain ⟨hk1, hY1⟩ := konts_ok hv
    have hm1 := Moves.ofDrop hwf hnext hv.alloc hY1 hfree hkeep (drop_rt hd)
    simp only [List.flatten_cons] at hn
    obtain ⟨-, hn2, hdLL⟩ := nodup_append_disj.mp hn
    have hkeepL : ∀ l ∈ Ls.flatten, σ1.mem l = σ.mem l := fun l hl => hkeep l (.inl fun h => hdLL l h hl)
    have hag1 : Agree σ σ1 Ls.flatten := Agree.of hkeepL (drop_rt hd)
    have hr1 := hr.frame hag1
    obtain ⟨σ2, hd2, hm2, hk2, hY2⟩ := dropAll_pure hm1.wf hr1 hn2
    have hka : kontsAll σ1 τs vs = kontsAll σ τs vs := kontsAll_frame hnext hr hkeepL
    rw [hka] at hm2 hk2 hY2
    have hY1a : ∀ l ∈ (konts σ τ v).flatMap Val.foot, σ1.mem l ≠ none := fun l hl => by
      rw [hkeep l (.inr hl)]; exact hv.alloc l (hY1 l hl)
    have hdY1 : Disj ((konts σ τ v).flatMap Val.foot) Ls.flatten := fun l h1 h2 => hdLL l (hY1 l h1) h2
    simp only [dropAll, hd, kontsAll, List.flatMap_append, List.flatten_cons]
    refine ⟨σ2, hd2, ?_, ?_, ?_⟩
    · have m1 := (hm1.widen (X := Ls.flatten) hr.alloc fun l h1 h2 => hdLL l h2 h1).relabel
        (E'' := (konts σ τ v).flatMap Val.foot ++ Ls.flatten) (L'' := []) fun x => by
          simp only [List.mem_append, List.not_mem_nil, or_false]; exact Or.comm
      have m2 := hm2.widen (X := (konts σ τ v).flatMap Val.foot) hY1a hdY1
      exact ((m1.trans m2 disj_nil_left hwf).congr_left fun x => by
        simp only [List.mem_append]; exact Or.comm).relabel fun x => by simp
    · have hk1' := (hk1.frame (Agree.of (fun l hl => hkeep l (.inr hl)) (drop_rt hd))).frame
        (hm2.keeps hm1.wf hY1a hdY1)
      exact hk1'.append hk2 fun l h1 h2 => hdLL l (hY1 l h1) (hY2 l h2)
    · intro l hl
      rcases List.mem_append.mp hl with h | h
      · exact List.mem_append.mpr (.inl (hY1 l h))
      · exact List.mem_append.mpr (.inr (hY2 l h))

/-- Dropping values in turn, and then the continuations they held, frees what they own. -/
theorem dropAllF (hfl : FlushOk F ι fl) (hwf : WF σ) (h : Vals F ι σ τs vs Ls) (hn : Ls.flatten.Nodup) :
    ∃ σ', dropAll σ τs vs = some σ' ∧ FlushGives (fl (kontsAll σ τs vs) σ') σ Ls.flatten :=
  let ⟨σ', hd, hm, hk, _⟩ := dropAll_pure hwf h hn
  ⟨σ', hd, FlushGives.after hm (hfl σ' _ hm.wf hk) hwf⟩

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


/-- `Moves.free`, for cells dropped with what they held. -/
theorem Moves.ofDropped (hd : Dropped σ D σ') (hE : ∀ l ∈ E, σ.mem l ≠ none)
    (hsplit : ∀ l, l ∈ E ↔ l ∈ E' ∨ l ∈ D) (hdisj : Disj E' D) : Moves σ E σ' E' [] :=
  ((hd.widen (X := E') (fun l hl => hE l ((hsplit l).mpr (.inl hl))) hdisj).congr_left fun x => by
    rw [hsplit, List.mem_append]).relabel fun x => by simp

/-- Values, each owning the cells `treeK` reads off the store. -/
theorem Vals.trees (hwf : WF σ) : Vals F ι σ τs vs Ls → vs.flatMap (Val.tree σ) = Ls.flatten
  | .nil => rfl
  | .cons hv hr => by
    simp only [List.flatMap_cons, List.flatten_cons, hv.tree_eq hwf, Vals.trees hwf hr]

end FlyCore.Ownership
