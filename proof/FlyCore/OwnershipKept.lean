import FlyCore.OwnershipSound

/-!
# Ownership: dropping a kept continuation

A continuation kept as a value is dropped by unwinding its frames to a barrier of its own, under no
handler but that barrier: its cleanup runs, and its fiber's operation, should its cleanup perform it,
goes on at once (`capD`). Its frames are as the world says (`Φ`), so the unwinding frees what it owns.
-/

namespace FlyCore.Ownership

variable {F : List Fn} {O : List Op}

/-- An activation of no variables owns nothing. -/
theorem Inv.nil_E (h : Inv F ι σ [] [] E S) : E = [] ∧ S = [] := by
  cases h.foot; exact ⟨rfl, rfl⟩

/-- Cells dropped, and then those of some continuations. -/
theorem FlushGives.trans (hd : Dropped σ D σ1) (h : FlushGives x σ1 D') (hwf : WF σ)
    (hD' : ∀ l ∈ D', σ.mem l ≠ none) (hDD : Disj D' D) : FlushGives x σ (D ++ D') := by
  rcases h with h | h | ⟨w, σ2, h1, hm⟩
  · exact .inl h
  · exact .inr (.inl h)
  · refine .inr (.inr ⟨w, σ2, h1, ?_⟩)
    have h1 : Moves σ (D' ++ D) σ1 D' [] := (hd.widen hD' hDD).relabel fun x => by simp
    exact ((h1.trans hm disj_nil_left hwf).congr_left fun x => by
      simp only [List.mem_append]; exact Or.comm).relabel fun x => by simp

theorem Ty.cross_complete {τ : Ty} (h : τ.cross = true) : τ.complete = true := by
  cases τ <;> simp_all [Ty.cross, Ty.complete]

/-- Dropping values that may pass out of a fiber, a continuation unwound to a barrier of its own:
what each owns is freed. -/
theorem flush_ok [WorldOk F O ι.w] (hK : EvalKOk F O n) : FlushOk F ι (flush F O n) := by
  intro σ vs hwf hk
  induction vs generalizing σ with
  | nil => exact .inr (.inr ⟨.int 0, σ, by rw [flush], Moves.refl hwf (by simp)⟩)
  | cons v vs ih =>
    obtain ⟨hall, hnd⟩ := hk
    simp only [List.flatMap_cons] at hnd ⊢
    obtain ⟨hnv, hnr, hdvr⟩ := nodup_append_disj.mp hnd
    have hk' : KontsOk F ι σ vs := ⟨fun w hw => hall w (List.mem_cons_of_mem _ hw), hnr⟩
    have hra : ∀ l ∈ vs.flatMap Val.foot, σ.mem l ≠ none := fun l hl => by
      obtain ⟨w, hw, hl⟩ := List.mem_flatMap.mp hl
      obtain ⟨_, _, _, hvw⟩ := hk'.1 w hw
      exact hvw.alloc l hl
    obtain ⟨At, Bt, rt, hv⟩ := hall v (List.mem_cons_self ..)
    -- What follows the first value's drop: the rest dropped as they were.
    have rest : ∀ σ2, Dropped σ v.foot σ2 →
        FlushGives (flush F O n vs σ2) σ (v.foot ++ vs.flatMap Val.foot) := fun σ2 hd =>
      FlushGives.trans hd (ih σ2 hd.wf (hk'.frame (hd.keeps hwf hra fun l h1 h2 => hdvr l h2 h1))) hwf hra
        fun l h1 h2 => hdvr l h2 h1
    cases hv with
    | @kont X K _ _ _ hXn hXa hks =>
    obtain ⟨σs, hkok, hagS⟩ := hks
    obtain ⟨τh, e, g, fa, ff, B', s', K', op, ra, rf, A, X', rfl, hτ, hcv, hrow, hA, hK', hperm⟩ :=
      ((WorldOk.ok (F := F) (O := O) (W := ι.w)) σs _ _ X).mp hkok
    have hfr : FrameOk F O ⟨[], ι.w⟩ ⟨[], ι.w⟩ σs (.capD τh e g σ.fresh.1) ⟨[], [], τh, [], rf⟩
        ⟨[], [], .int, [], [.fail]⟩ [] [σ.fresh.1] :=
      .capD hcv.hop hcv.hrefs (Ty.cross_complete hcv.hτ) fun l hl => by
        rcases hrow.1 l hl with rfl | ⟨-, hne⟩
        · exact .inl ⟨e, rfl⟩
        · cases l with
          | fail => exact .inr (List.mem_singleton_self _)
          | eff e' => exact .inl ⟨e', rfl⟩
          | drop => exact absurd rfl hne
    have hFr := FramesOk.cons (A := σ.fresh.1 :: A) hfr (Weaker.refl _) Agree.self (fun _ h => by simp at h)
      List.nodup_nil disj_nil_left hK' (fun a h => by simp at h; simp [h])
      (fun a ha => .inl (List.mem_cons_of_mem _ ha))
    simp only [List.nil_append] at hFr
    have hwf1 : WF σ.fresh.2 := hwf
    have hX'X : ∀ l, l ∈ X' ↔ l ∈ X := fun l => hperm.mem_iff.symm
    have hagF : Agree σ σ.fresh.2 X := Agree.of (fun _ _ => rfl) Store.fresh_rt
    have hagS1 : Agree σs σ.fresh.2 (X' ++ []) :=
      (hagS.trans hagF).mono fun l hl => (hX'X l).mp (by simpa using hl)
    have hpost := hK (hsDie g σ.fresh.1) ⟨[], ι.w⟩ σs (.capD τh e g σ.fresh.1 :: K') ⟨[], [], .int, [], [.fail]⟩ X'
      [] (σ.fresh.1 :: A) σ.fresh.2 [] (.abort σ.fresh.1 0) op [] hFr
      ⟨.abort (by intro e h; cases h) (.abort (by intro e h; cases h) (.abort (by intro e h; cases h) .nil)),
        fun l hl => by simp at hl; subst hl; exact ⟨_, by simp [hsDie, find, Frame.handles]; rfl⟩⟩
      (fun a h => by
        rcases List.mem_cons.mp h with rfl | h
        · exact ⟨.drop, by simp [hsDie]⟩
        · obtain ⟨rfl, -⟩ := hA a h; exact ⟨.drop, by simp [hsDie]⟩) hwf1 hagS1
      (fun l hl => by
        have hl' := (hX'X l).mp (by simpa using hl)
        rw [← hagS l hl']; exact hXa l hl')
      (hperm.nodup_iff.mp hXn) rfl (fun _ hp => by simp at hp) (by simp [mutCells]) (by simp [mutCells, Disj])
      (by simp [Disj]) (.inr ⟨σ.fresh.1, 0, rfl, ⟨.drop, by simp [hsDie]⟩, rfl⟩)
    simp only [mutCells, List.flatMap_nil, List.append_nil] at hpost
    -- The fiber unwound: what it owned freed.
    have hdone : ∀ σ2, Moves σ.fresh.2 X' σ2 [] [] → Dropped σ (Val.kont (.capV τh e g fa ff B' s' :: K') X).foot σ2 :=
      fun σ2 hm => ((Moves.freshen (E := X') hwf (fun l hl => hXa l ((hX'X l).mp hl))).trans hm disj_nil_left
        hwf).congr_left fun x => by simp only [Val.foot]; exact hX'X x
    rw [flush]
    simp only [Store.fresh] at hpost hdone ⊢
    generalize evalK F O n (hsDie g σ.ids) { σ with ids := σ.ids + 1 } (.capD τh e g σ.ids :: K') (.abort σ.ids 0) = res
      at hpost ⊢
    rcases res with ⟨res, σ2⟩
    cases res with
    | val w =>
      obtain ⟨E', L, hI, hw, -, -, hm⟩ := hpost
      obtain ⟨rfl, -⟩ := hI.nil_E
      cases hw
      exact rest σ2 (hdone σ2 (by simpa using hm))
    | abort j k =>
      obtain ⟨-, E', hI, hm⟩ := hpost
      obtain ⟨rfl, -⟩ := hI.nil_E
      exact rest σ2 (hdone σ2 hm)
    | susp j ef ws ls K2 =>
      obtain ⟨-, -, -, -, -, hc, -⟩ := hpost
      rcases hc with hc | hc <;> simp [hsDie] at hc
    | stuck => simp [Post] at hpost
    | timeout => exact .inl rfl
    | panic => exact .inr (.inl rfl)

/-- Dropping with what fuel is left. -/
theorem flushR_ok [WorldOk F O ι.w] (hK : ∀ m, n = m + 1 → EvalKOk F O m) : FlushOk F ι (flushR F O n) := by
  cases n with
  | zero => intro σ _ _ _; exact .inl (by rw [flushR])
  | succ m =>
    intro σ vs hwf hk
    have := flush_ok (hK m rfl) σ vs hwf hk
    rwa [show flushR F O (m + 1) vs σ = flush F O m vs σ by rw [flushR]]

end FlyCore.Ownership
