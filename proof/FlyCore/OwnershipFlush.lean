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
  x.1 = .timeout ∨ x.1 = .panic ∨ ∃ v σ', x = (.val v, σ') ∧ Dropped σ D σ'

/-- `fl` drops continuations as their types say, freeing what they own. -/
def FlushOk (F : List Fn) (ι : Iota) (fl : Flush) : Prop :=
  ∀ σ vs, WF σ → KontsOk F ι σ vs → FlushGives (fl vs σ) σ (vs.flatMap Val.foot)

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

theorem VT.foot_cross (h : VT F ι σ τ v L) (hc : τ.cross = true) : L = v.foot := by
  cases h <;> simp_all [Ty.cross, Val.foot]

/-- Values that may pass out of a fiber, each owning its continuation's cells. -/
theorem Vals.konts : Vals F ι σ τs vs Ls → (∀ τ ∈ τs, τ.cross = true) → Ls.flatten.Nodup →
    KontsOk F ι σ vs ∧ vs.flatMap Val.foot = Ls.flatten
  | .nil, _, _ => ⟨KontsOk.nil, rfl⟩
  | .cons hv hr, hc, hn => by
    have hc1 := hc _ (List.mem_cons_self ..)
    have hfoot := hv.foot_cross hc1
    simp only [List.flatten_cons] at hn
    obtain ⟨-, hn2, -⟩ := nodup_append_disj.mp hn
    obtain ⟨hk, he⟩ := Vals.konts hr (fun τ hτ => hc τ (List.mem_cons_of_mem _ hτ)) hn2
    refine ⟨⟨fun w hw => ?_, ?_⟩, ?_⟩
    · rcases List.mem_cons.mp hw with rfl | hw
      · exact ⟨_, hc1, hfoot ▸ hv⟩
      · exact hk.1 w hw
    · simp only [List.flatMap_cons, he, ← hfoot]; simpa using hn
    · simp only [List.flatMap_cons, he, ← hfoot, List.flatten_cons]

end FlyCore.Ownership
