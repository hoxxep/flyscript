import FlyCore.OwnershipCall

/-!
# Ownership: soundness

`eval_ok`: a well-typed expression, evaluated in a store that keeps its activation's invariant,
never gets stuck. It gives a value of its type owning cells of no variable's, the invariant still
holds, and the step is accounted for (`Moves`). `program_ok` is the consequence for a whole
program: never stuck, and when it ends nothing is allocated but the cells of its result.
-/

namespace FlyCore.Ownership

/-! ## Footprints split around one variable -/

theorem mem_seg {x : Nat} {E₁ L E₂ : List Nat} : x ∈ E₁ ++ L ++ E₂ ↔ x ∈ L ∨ x ∈ E₁ ++ E₂ := by
  simp only [List.mem_append]
  constructor
  · rintro ((h | h) | h)
    · exact .inr (.inl h)
    · exact .inl h
    · exact .inr (.inr h)
  · rintro (h | h | h)
    · exact .inl (.inr h)
    · exact .inl (.inl h)
    · exact .inr h

theorem seg_nodup {E₁ L E₂ : List Nat} : (E₁ ++ L ++ E₂).Nodup → L.Nodup ∧ Disj L (E₁ ++ E₂) ∧ (E₁ ++ E₂).Nodup := by
  intro h
  rw [nodup_append_disj, nodup_append_disj] at h
  obtain ⟨⟨h1, hL, h1L⟩, h2, h12⟩ := h
  refine ⟨hL, ?_, ?_⟩
  · intro x hx hx'
    rcases List.mem_append.mp hx' with hx' | hx'
    · exact h1L x hx' hx
    · exact h12 x (List.mem_append.mpr (.inr hx)) hx'
  · rw [nodup_append_disj]
    exact ⟨h1, h2, fun x hx hx' => h12 x (List.mem_append.mpr (.inl hx)) hx'⟩

theorem seg_replace {E₁ L E₂ : List Nat} : (E₁ ++ E₂).Nodup → L.Nodup → Disj L (E₁ ++ E₂) → (E₁ ++ L ++ E₂).Nodup := by
  intro h hL hd
  rw [nodup_append_disj] at h
  obtain ⟨h1, h2, h12⟩ := h
  rw [nodup_append_disj, nodup_append_disj]
  refine ⟨⟨h1, hL, fun x hx hx' => hd x hx' (List.mem_append.mpr (.inl hx))⟩, h2, ?_⟩
  intro x hx hx'
  rcases List.mem_append.mp hx with hx | hx
  · exact h12 x hx hx'
  · exact hd x hx (List.mem_append.mpr (.inr hx'))

theorem post_now (hI : Inv σ Γ env E S) (hwf : WF σ) (hv : VT σ τ v []) :
    Post σ E S Γ env τ (.val v, σ) :=
  ⟨E, [], hI, hv, disj_nil_left, disj_nil_left, Moves.refl hwf hI.alloc⟩

/-- A result carried on unchanged out of a sub-expression — a failure, or running out of fuel — is as
the sub-expression said, of any context weaker than the one it would have left. -/
theorem post_out {r : Res × Store} (h : Post σ E S Γ₁ env τ₁ r) (hv : ∀ v σ', r ≠ (.val v, σ'))
    (w : Weaker Γ' Γ₁) : Post σ E S Γ' env τ r := by
  rcases r with ⟨r, σ'⟩
  cases r with
  | val v => exact absurd rfl (hv v σ')
  | fail k => obtain ⟨E', hI, hm⟩ := h; exact ⟨E', hI.weaken w, hm⟩
  | stuck => exact h
  | timeout => trivial

/-- After a step that gave nothing of its own, what the next one gives is what the two give. -/
theorem post_after {r : Res × Store} (hm : Moves σ E σ1 E₁ []) (hwf : WF σ)
    (h : Post σ1 E₁ S Γ' env τ r) : Post σ E S Γ' env τ r := by
  rcases r with ⟨r, σ'⟩
  cases r with
  | val v =>
    obtain ⟨E', L, hI, hv, hd, hdS, hm'⟩ := h
    exact ⟨E', L, hI, hv, hd, hdS, (hm.trans hm' disj_nil_left hwf).relabel fun x => by simp⟩
  | fail k =>
    obtain ⟨E', hI, hm'⟩ := h
    exact ⟨E', hI, (hm.trans hm' disj_nil_left hwf).relabel fun x => by simp⟩
  | stuck => exact h
  | timeout => trivial

/-- One segment of a footprint, against the rest. -/
theorem seg3 {A P R B : List Nat} (h : (A ++ (P ++ R) ++ B).Nodup) :
    Disj R (A ++ P ++ B) ∧ (A ++ P ++ B).Nodup := by
  have hp : (A ++ (P ++ R) ++ B).Perm (R ++ (A ++ P ++ B)) :=
    List.perm_iff_count.mpr fun a => by simp only [List.count_append]; omega
  rw [hp.nodup_iff, nodup_append_disj] at h
  exact ⟨h.2.2, h.2.1⟩

/-! ## Scopes -/

/-- Binding a value to a new variable: a fresh cell holding it, whose tree is the variable's
footprint. -/
theorem bind_ok (hI₁ : Inv σ1 Γ₁ env E₁ S) (hv₁ : VT σ1 τx v L₁) (hd₁ : Disj L₁ E₁) (hdS₁ : Disj L₁ S)
    (hm₁ : Moves σ E σ1 E₁ L₁) (hwf : WF σ) (hx : x ∉ Γ₁.map Prod.fst) :
    Inv (σ1.alloc v).2 ((x, .own τx true) :: Γ₁) ((x, σ1.next) :: env) (σ1.next :: L₁ ++ E₁) S ∧
      Moves σ E (σ1.alloc v).2 (σ1.next :: L₁ ++ E₁) [] := by
  have hwf₁ := hm₁.wf
  have hL₁ := hv₁.alloc
  have hfresh : ∀ l, σ1.mem l ≠ none → l ≠ σ1.next := fun l hl h => by
    subst h; exact Nat.lt_irrefl _ (hwf₁ _ hl)
  have hag : Agree σ1 (σ1.alloc v).2 (L₁ ++ E₁ ++ S) := agree_alloc hwf₁ (by
    intro l hl
    simp only [List.mem_append] at hl
    rcases hl with (hl | hl) | hl
    · exact hL₁ l hl
    · exact hI₁.alloc l hl
    · exact hI₁.allocS l hl)
  have hcL : σ1.next ∉ L₁ := fun h => hfresh _ (hL₁ _ h) rfl
  have hcE : σ1.next ∉ E₁ := fun h => hfresh _ (hI₁.alloc _ h) rfl
  have hcS : σ1.next ∉ S := fun h => hfresh _ (hI₁.allocS _ h) rfl
  have hLt : LT (σ1.alloc v).2 σ1.next τx (σ1.next :: L₁) :=
    LT.of_contents (by simp [Store.alloc]) (hv₁.frame fun l hl => hag l (by simp [hl])) hcL
  refine ⟨⟨.cons (s := .own τx true) hLt (hI₁.foot.frame fun l hl => hag l (by
    simp only [List.mem_append] at hl ⊢; rcases hl with hl | hl <;> simp [hl])), ?_, ?_, ?_⟩, ?_⟩
  · refine List.nodup_cons.mpr ⟨by simp [hcL, hcE], ?_⟩
    exact nodup_append_disj.mpr ⟨hv₁.nodup, hI₁.nodup, hd₁⟩
  · intro l hl hl'
    simp only [List.mem_append, List.mem_cons] at hl'
    rcases hl' with (rfl | hl') | hl'
    · exact hcS hl
    · exact hdS₁ l hl' hl
    · exact hI₁.disj l hl hl'
  · exact List.nodup_cons.mpr ⟨hx, hI₁.keys⟩
  · exact (hm₁.relabel (E'' := L₁ ++ E₁) (L'' := []) fun x => by mem_iff).trans
      ((Moves.allocate hwf₁ (fun l hl => by
        rcases List.mem_append.mp hl with hl | hl
        · exact hL₁ l hl
        · exact hI₁.alloc l hl))) disj_nil_left hwf |>.relabel fun x => by mem_iff

/-- Dropping the variable a scope declared, live or perhaps moved, as the scope is left: its
footprint is freed, and the rest stands. -/
theorem drop_var (hI₃ : Inv σ3 ((x, .own τx live) :: Γ₂) ((x, c) :: env) E₃ S)
    (hL₃ : ∀ l ∈ L₃, σ3.mem l ≠ none) (hd₃ : Disj L₃ E₃) (hm : Moves σ E σ3 E₃ L₃) (hwf : WF σ) :
    ∃ σ4 E₂, dropCell σ3 τx c = some σ4 ∧ Inv σ4 Γ₂ env E₂ S ∧ Agree σ3 σ4 L₃ ∧ Disj L₃ E₂ ∧
      Moves σ E σ4 E₂ L₃ := by
  obtain ⟨Lx, E₂, S₂, hs, hfoot, hE₃, hS₃⟩ := hI₃.foot.uncons
  simp only [addE, addS, Slot.excl, ↓reduceIte] at hE₃ hS₃
  subst hE₃ hS₃
  obtain ⟨σ4, hdrop, hnext, hfree, hkeep⟩ := dropCell_own hs
  have hnd := nodup_append_disj.mp hI₃.nodup
  have hag4 : Agree σ3 σ4 (E₂ ++ S) := by
    intro l hl
    refine hkeep l fun h => ?_
    rcases List.mem_append.mp hl with hl | hl
    · exact hnd.2.2 l h hl
    · exact hI₃.disj l hl (List.mem_append.mpr (.inl h))
  have hm₄ := Moves.free (E := Lx ++ E₂ ++ L₃) (E' := E₂ ++ L₃) (D := Lx) (WF.of_free hm.wf hnext hfree hkeep)
    hnext
    (fun l hl => by
      rcases List.mem_append.mp hl with hl | hl
      · exact hI₃.alloc l hl
      · exact hL₃ l hl)
    (fun x => by mem_iff) hfree hkeep (by
      intro l hl hlx
      rcases List.mem_append.mp hl with hl | hl
      · exact hnd.2.2 l hlx hl
      · exact hd₃ l hl (List.mem_append.mpr (.inl hlx)))
  refine ⟨σ4, E₂, hdrop, ⟨hfoot.frame hag4, hnd.2.1, fun l hl hl' => hI₃.disj l hl
      (List.mem_append.mpr (.inr hl')), (List.nodup_cons.mp hI₃.keys).2⟩,
    fun l hl => hkeep l fun h => hd₃ l hl (List.mem_append.mpr (.inl h)),
    fun l hl hl' => hd₃ l hl (List.mem_append.mpr (.inr hl')), ?_⟩
  exact ((hm.relabel (E'' := Lx ++ E₂ ++ L₃) (L'' := []) fun x => by mem_iff).trans hm₄ disj_nil_left
    hwf).relabel fun x => by mem_iff

/-- Leaving a scope, with a value or a failure, drops its variable. -/
theorem leave_ok {r : Res × Store} (hm : Moves σ E σb Eb []) (hwf : WF σ)
    (h : Post σb Eb S ((x, .own τx live) :: Γ₂) ((x, c) :: env) τ r) :
    Post σ E S Γ₂ env τ (leave τx c r) := by
  rcases r with ⟨r, σ3⟩
  cases r with
  | val w =>
    obtain ⟨E₃, L₃, hI₃, hv₃, hd₃, hdS₃, hm₃⟩ := h
    obtain ⟨σ4, E₂, hdrop, hI₄, hag, hd, hm₄⟩ := drop_var hI₃ hv₃.alloc hd₃
      ((hm.trans hm₃ disj_nil_left hwf).relabel fun x => by simp) hwf
    simp only [leave, Res.done, ↓reduceIte, hdrop]
    exact ⟨E₂, L₃, hI₄, hv₃.frame hag, hd, hdS₃, hm₄⟩
  | fail k =>
    obtain ⟨E₃, hI₃, hm₃⟩ := h
    obtain ⟨σ4, E₂, hdrop, hI₄, -, -, hm₄⟩ := drop_var (L₃ := []) hI₃ (by simp) disj_nil_left
      ((hm.trans hm₃ disj_nil_left hwf).relabel fun x => by simp) hwf
    simp only [leave, Res.done, ↓reduceIte, hdrop]
    exact ⟨E₂, hI₄, hm₄⟩
  | stuck => exact h
  | timeout => simp [leave, Res.done, Post]

/-! ## Soundness -/

theorem eval_ok (F : List Fn) (hF : FnsOk F) : ∀ n σ Γ env E S e τ Γ',
    Typed F Γ e τ Γ' → Inv σ Γ env E S → WF σ → Post σ E S Γ' env τ (eval F n σ env e) := by
  intro n
  induction n with
  | zero => intros; simp [eval, Post]
  | succ n ih =>
    intro σ Γ env E S e τ Γ' ht hI hwf
    cases ht with
    | lit => simp only [eval]; exact post_now hI hwf .int
    | read hp =>
      obtain ⟨a, τr, Lr, P, l, s, ha, hLr, hpath, hres, -⟩ := place_ok hp hI.foot
      obtain ⟨R, hR, rfl⟩ := path_split hpath hLr
      cases hR with
      | int hl => simp only [eval, hres, hl]; exact post_now hI hwf .int
    | move hx =>
      obtain ⟨a, L, E₁, E₂, ha, hL, hE, hupd⟩ := foot_update hI.foot hI.keys hx rfl
      simp only [SlotOk] at hL
      cases hL with
      | @box _ b _ R hb hR hn =>
        simp only [eval, ha, hb]
        have hnd := seg_nodup (hE ▸ hI.nodup)
        have haE : a ∈ E := hE ▸ mem_seg.mpr (.inl (List.mem_cons_self ..))
        have haS : a ∉ S := fun h => hI.disj a h haE
        have ha12 : a ∉ E₁ ++ E₂ := hnd.2.1 a (List.mem_cons_self ..)
        have hag : Agree σ (σ.set a (some .moved)) (E₁ ++ E₂ ++ S) := agree_set (by
          intro h
          rcases List.mem_append.mp h with h | h
          · exact ha12 h
          · exact haS h)
        have hR' : Disj R (E₁ ++ E₂) := fun x hx => hnd.2.1 x (List.mem_cons_of_mem _ hx)
        refine ⟨E₁ ++ [a] ++ E₂, R, ⟨hupd _ (.own _ false) [a] (by rfl) hag (by simp [SlotOk, Store.set]),
          ?_, ?_, ?_⟩, .box (hR.frame (agree_set hn)), ?_, ?_, ?_⟩
        · exact seg_replace hnd.2.2 (by simp) (disj_cons_left.mpr ⟨ha12, disj_nil_left⟩)
        · exact hI.disj.mono_right fun x hx => hE ▸ (by
            rcases mem_seg.mp hx with hx | hx
            · simp at hx; subst hx; exact mem_seg.mpr (.inl (List.mem_cons_self ..))
            · exact mem_seg.mpr (.inr hx))
        · rw [setSlot_keys]; exact hI.keys
        · intro x hx hx'
          rcases mem_seg.mp hx' with hx' | hx'
          · simp at hx'; subst hx'; exact hn hx
          · exact hR' x hx hx'
        · exact fun x hx hxS => hI.disj x hxS (hE ▸ mem_seg.mpr (.inl (List.mem_cons_of_mem _ hx)))
        · exact (Moves.set hwf hI.alloc haE).relabel fun x => by rw [hE]; mem_iff
    | add ha hb =>
      simp only [eval]
      have h1 := ih _ _ _ _ _ _ _ _ ha hI hwf
      generalize eval F n σ env _ = r1 at h1 ⊢
      rcases r1 with ⟨r1, σ1⟩
      cases r1 with
      | val v =>
        obtain ⟨E₁, L₁, hI₁, hv₁, -, -, hm₁⟩ := h1
        cases hv₁ with
        | int =>
          dsimp only
          have h2 := ih _ _ _ _ _ _ _ _ hb hI₁ hm₁.wf
          generalize eval F n σ1 env _ = r2 at h2 ⊢
          rcases r2 with ⟨r2, σ2⟩
          cases r2 with
          | val w =>
            obtain ⟨E₂, L₂, hI₂, hv₂, -, -, hm₂⟩ := h2
            cases hv₂ with
            | int =>
              dsimp only
              exact ⟨E₂, [], hI₂, .int, disj_nil_left, disj_nil_left, (hm₁.trans hm₂ disj_nil_left hwf).relabel (by simp)⟩
          | fail k => exact post_after hm₁ hwf h2
          | stuck => simp [Post] at h2
          | timeout => simp [Post]
      | fail k => exact post_out h1 (by simp) (typed_weaker hb (by rw [typed_keys ha]; exact hI.keys))
      | stuck => simp [Post] at h1
      | timeout => simp [Post]
    | new ha =>
      simp only [eval]
      have h1 := ih _ _ _ _ _ _ _ _ ha hI hwf
      generalize eval F n σ env _ = r1 at h1 ⊢
      rcases r1 with ⟨r1, σ1⟩
      cases r1 with
      | val v =>
        dsimp only
        obtain ⟨E₁, L₁, hI₁, hv₁, hd₁, hdS₁, hm₁⟩ := h1
        have hL₁ := hv₁.alloc
        have hag : Agree σ1 (σ1.alloc v).2 (L₁ ++ E₁ ++ S) := agree_alloc hm₁.wf (by
          intro l hl
          rcases List.mem_append.mp hl with hl | hl
          · rcases List.mem_append.mp hl with hl | hl
            · exact hL₁ l hl
            · exact hI₁.alloc l hl
          · exact hI₁.allocS l hl)
        have hfresh : ∀ l ∈ L₁ ++ E₁ ++ S, l ≠ σ1.next := by
          intro l hl h
          subst h
          rcases List.mem_append.mp hl with hl | hl
          · rcases List.mem_append.mp hl with hl | hl
            · exact Nat.lt_irrefl _ (hm₁.wf _ (hL₁ _ hl))
            · exact Nat.lt_irrefl _ (hm₁.wf _ (hI₁.alloc _ hl))
          · exact Nat.lt_irrefl _ (hm₁.wf _ (hI₁.allocS _ hl))
        refine ⟨E₁, σ1.next :: L₁, ⟨hI₁.foot.frame fun l hl => hag l ?_, hI₁.nodup, hI₁.disj, hI₁.keys⟩,
          .box (LT.of_contents (by simp [Store.alloc]) (hv₁.frame fun l hl => hag l ?_) ?_), ?_, ?_, ?_⟩
        · rcases List.mem_append.mp hl with hl | hl
          · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr hl)))
          · exact List.mem_append.mpr (.inr hl)
        · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inl hl)))
        · exact fun h => hfresh _ (List.mem_append.mpr (.inl (List.mem_append.mpr (.inl h)))) rfl
        · refine disj_cons_left.mpr ⟨fun h => hfresh _ (List.mem_append.mpr (.inl (List.mem_append.mpr (.inr h)))) rfl, hd₁⟩
        · exact disj_cons_left.mpr ⟨fun h => hfresh _ (List.mem_append.mpr (.inr h)) rfl, hdS₁⟩
        · exact (hm₁.trans (Moves.allocate hm₁.wf hI₁.alloc) hd₁ hwf).relabel fun x => by mem_iff
      | fail k => exact post_out h1 (by simp) (Weaker.refl _)
      | stuck => simp [Post] at h1
      | timeout => simp [Post]
    | seq ha hb =>
      simp only [eval]
      have h1 := ih _ _ _ _ _ _ _ _ ha hI hwf
      generalize eval F n σ env _ = r1 at h1 ⊢
      rcases r1 with ⟨r1, σ1⟩
      cases r1 with
      | val v =>
        obtain ⟨E₁, L₁, hI₁, hv₁, -, -, hm₁⟩ := h1
        cases hv₁ with
        | int =>
          dsimp only
          have h2 := ih _ _ _ _ _ _ _ _ hb hI₁ hm₁.wf
          generalize eval F n σ1 env _ = r2 at h2 ⊢
          rcases r2 with ⟨r2, σ2⟩
          cases r2 with
          | val w =>
            obtain ⟨E₂, L₂, hI₂, hv₂, hd₂, hdS₂, hm₂⟩ := h2
            exact ⟨E₂, L₂, hI₂, hv₂, hd₂, hdS₂, (hm₁.trans hm₂ disj_nil_left hwf).relabel (by simp)⟩
          | fail k => exact post_after hm₁ hwf h2
          | stuck => simp [Post] at h2
          | timeout => simp [Post]
      | fail k => exact post_out h1 (by simp) (typed_weaker hb (by rw [typed_keys ha]; exact hI.keys))
      | stuck => simp [Post] at h1
      | timeout => simp [Post]
    | write ha hp =>
      simp only [eval]
      have h1 := ih _ _ _ _ _ _ _ _ ha hI hwf
      generalize eval F n σ env _ = r1 at h1 ⊢
      rcases r1 with ⟨r1, σ1⟩
      cases r1 with
      | val v =>
        obtain ⟨E₁, L₁, hI₁, hv₁, -, -, hm₁⟩ := h1
        cases hv₁ with
        | @int k =>
          obtain ⟨l, R, P, A, B, hres, hR, hE, hupd⟩ := replace_at hI₁ hp
          cases hR with
          | int hl =>
            simp only [hres, hl]
            have hnd := seg_nodup (hE ▸ hI₁.nodup)
            have hlE : l ∈ E₁ := hE ▸ mem_seg.mpr (.inl (by simp))
            have hlP : l ∉ P := by
              have := hnd.1; rw [nodup_append_disj] at this; exact fun h => this.2.2 l h (by simp)
            have hlAB : l ∉ A ++ B := hnd.2.1 l (by simp)
            have hlS : l ∉ S := fun h => hI₁.disj l h hlE
            have hout : l ∉ A ++ P ++ B ++ S := by
              simp only [List.mem_append, not_or] at hlAB ⊢
              exact ⟨⟨⟨hlAB.1, hlP⟩, hlAB.2⟩, hlS⟩
            refine ⟨E₁, [], ?_, .int, disj_nil_left, disj_nil_left,
              (hm₁.trans (Moves.set hm₁.wf hI₁.alloc hlE) disj_nil_left hwf).relabel (by simp)⟩
            have := hupd (σ1.set l (some (.int k))) [l] (agree_set hout) (.int (n := k) (by simp [Store.set])) (by
              intro x hx; simp at hx; subst hx
              simp only [List.mem_append, not_or] at hout ⊢; exact hout.1) (by
              intro x hx; simp at hx; subst hx; exact hlS)
            rwa [← hE] at this
      | fail k => exact post_out h1 (by simp) (Weaker.refl _)
      | stuck => simp [Post] at h1
      | timeout => simp [Post]
    | assign ha hp =>
      simp only [eval]
      have h1 := ih _ _ _ _ _ _ _ _ ha hI hwf
      generalize eval F n σ env _ = r1 at h1 ⊢
      rcases r1 with ⟨r1, σ1⟩
      cases r1 with
      | val v =>
        dsimp only
        obtain ⟨E₁, L₁, hI₁, hv₁, hd₁, hdS₁, hm₁⟩ := h1
        obtain ⟨l, R, P, A, B, hres, hR, hE, hupd⟩ := replace_at hI₁ hp
        obtain ⟨w, R', hw, hvw, rfl, hlR'⟩ := hR.contents
        obtain ⟨σ2, hdrop, hnext, hfree, hkeep⟩ := drop_ok _ σ1 w R' hvw
        simp only [hres, hw, hdrop]
        have hlE : l ∈ E₁ := hE ▸ mem_seg.mpr (.inl (by simp))
        have hR'E : ∀ x ∈ R', x ∈ E₁ := fun x hx => hE ▸ mem_seg.mpr (.inl (by simp [hx]))
        obtain ⟨hdR, -⟩ := seg3 (hE ▸ hI₁.nodup)
        have hlAPB : l ∉ A ++ P ++ B := hdR l (by simp)
        have hdR' : Disj R' (A ++ P ++ B) := fun x hx => hdR x (by simp [hx])
        have hlL : l ∉ L₁ := fun h => hd₁ l h hlE
        have hlS : l ∉ S := fun h => hI₁.disj l h hlE
        have hAPB : ∀ x ∈ A ++ P ++ B, x ∈ E₁ := fun x hx => hE ▸ (by
          simp only [List.mem_append] at hx ⊢; rcases hx with (hx | hx) | hx <;> simp [hx])
        let σ3 := σ2.set l (some v)
        have hkeep3 : ∀ x, x ≠ l → x ∉ R' → σ3.mem x = σ1.mem x := by
          intro x hx hxR; simp only [σ3, Store.set, hx, ite_false]; exact hkeep x hxR
        have hag : Agree σ1 σ3 (A ++ P ++ B ++ S) := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hkeep3 x (fun h => hlAPB (h ▸ hx)) (fun h => hdR' x h hx)
          · exact hkeep3 x (fun h => hlS (h ▸ hx)) (fun h => hI₁.disj x hx (hR'E x h))
        have hagL : Agree σ1 σ3 L₁ := fun x hx =>
          hkeep3 x (fun h => hlL (h ▸ hx)) (fun h => hd₁ x hx (hR'E x h))
        have hLt : LT σ3 l _ (l :: L₁) :=
          LT.of_contents (by simp [σ3, Store.set]) (hv₁.frame hagL) hlL
        have hwf2 : WF σ2 := by
          intro x hx
          by_cases hxR : x ∈ R'
          · exact absurd (hfree x hxR) hx
          · rw [hkeep x hxR] at hx; rw [hnext]; exact hm₁.wf x hx
        have hm₂ := Moves.free (E := E₁ ++ L₁) (E' := A ++ (P ++ [l]) ++ B ++ L₁) (D := R') hwf2 hnext
          (fun x hx => by
            rcases List.mem_append.mp hx with hx | hx
            · exact hI₁.alloc x hx
            · exact hv₁.alloc x hx)
          (fun x => by rw [hE]; mem_iff) hfree hkeep (by
            intro x hx hxR
            rcases List.mem_append.mp hx with hx | hx
            · simp only [List.mem_append, List.mem_singleton] at hx
              rcases hx with (hx | hx | hx) | hx
              · exact hdR' x hxR (by simp [hx])
              · exact hdR' x hxR (by simp [hx])
              · subst hx; exact hlR' hxR
              · exact hdR' x hxR (by simp [hx])
            · exact hd₁ x hx (hR'E x hxR))
        have hm₃ := Moves.set (v := v) hwf2 (fun x hx => (hm₂.alloc x).mpr (.inr (.inl hx)))
          (l := l) (by simp)
        refine ⟨A ++ (P ++ (l :: L₁)) ++ B, [], hupd σ3 _ hag hLt ?_ ?_, .int, disj_nil_left,
          disj_nil_left, ?_⟩
        · exact disj_cons_left.mpr ⟨hlAPB, fun x hx hx' => hd₁ x hx (hAPB x hx')⟩
        · exact disj_cons_left.mpr ⟨hlS, hdS₁⟩
        · have := (hm₁.relabel (E'' := E₁ ++ L₁) (L'' := []) fun x => by mem_iff).trans
            ((hm₂.trans hm₃ disj_nil_left hm₁.wf).relabel (E'' := A ++ (P ++ (l :: L₁)) ++ B) (L'' := [])
              fun x => by mem_iff) disj_nil_left hwf
          simpa using this
      | fail k => exact post_out h1 (by simp) (Weaker.refl _)
      | stuck => simp [Post] at h1
      | timeout => simp [Post]
    | let_ hx ha hb =>
      rename_i x a τx Γ₁ b live
      simp only [eval]
      have hk₁ : (Γ₁.map Prod.fst).Nodup := by rw [typed_keys ha]; exact hI.keys
      have hx₁ : x ∉ Γ₁.map Prod.fst := by rw [typed_keys ha]; exact lookup_none_keys hx
      have h1 := ih _ _ _ _ _ _ _ _ ha hI hwf
      generalize eval F n σ env _ = r1 at h1 ⊢
      rcases r1 with ⟨r1, σ1⟩
      cases r1 with
      | val v =>
        dsimp only
        obtain ⟨E₁, L₁, hI₁, hv₁, hd₁, hdS₁, hm₁⟩ := h1
        obtain ⟨hIb, hma⟩ := bind_ok hI₁ hv₁ hd₁ hdS₁ hm₁ hwf hx₁
        have h2 := ih _ _ _ _ _ _ _ _ hb hIb hma.wf
        rw [show (σ1.alloc v).1 = σ1.next from rfl]
        exact leave_ok hma hwf h2
      | fail k =>
        have w := typed_weaker hb (List.nodup_cons.mpr ⟨hx₁, hk₁⟩)
        cases w with
        | cons _ w => exact post_out h1 (by simp) w
      | stuck => simp [Post] at h1
      | timeout => simp [Post]
    | call hfd hargs hlends hexcl =>
      rename_i f d owned lent ys
      simp only [eval, hfd]
      have ha := args_ok ih hargs hI hwf
      generalize evalArgs (eval F n) σ env owned _ = ra at ha ⊢
      rcases ra with ⟨ra, σ1⟩
      cases ra with
      | inr r =>
        rcases ha with rfl | ⟨k, rfl, E', hI', hm'⟩
        · trivial
        · exact ⟨E', hI', hm'⟩
      | inl vs =>
        obtain ⟨E₁, Ls, hI₁, hvs, hLn, hdL, hdLS, hm₁⟩ := ha
        have hwf₁ := hm₁.wf
        obtain ⟨hs, hts, hys, hmap, hholes⟩ := lends_ok hlends hI₁.foot
        have hpw : hs.Pairwise Apart := by
          rw [← hys, Exclusive, List.pairwise_map] at hexcl; exact hexcl
        obtain ⟨hkeys, Γ'', hbody⟩ := hF d (List.mem_of_getElem? hfd)
        have hlen : vs.length = d.owns.length ∧ (hs.map Hole.loc).length = d.refs.length := by
          refine ⟨by rw [hvs.length]; simp, ?_⟩
          have := congrArg List.length hts
          simp only [List.length_map] at this ⊢
          exact this
        simp only [hmap, hlen, and_self, ↓reduceIte]
        obtain ⟨Eo, hfo, hEo, hEomem, hle, hwf₂, hold, hnew, hlenc⟩ :=
          allocAll_ok (names := d.owns.map Prod.fst) hvs (by simp) hwf₁ hLn
        rw [zip_fst_snd] at hfo
        generalize allocAll σ1 ((d.owns.map Prod.fst).zip vs) = al at hfo hEomem hle hwf₂ hold hnew hlenc ⊢
        obtain ⟨cells, σ2⟩ := al
        dsimp only at hfo hEomem hle hwf₂ hold hnew hlenc ⊢
        have hMin : ∀ l ∈ (mutCells (olds hs)), l ∈ E₁ := fun l hl => by
          obtain ⟨h, hh, hm, hl⟩ := mem_olds_mut.mp hl
          exact (hole_in hI₁ (hholes h hh) l (List.mem_append.mpr (.inr hl))).1 hm
        have hXE : ∀ l ∈ (E₁.filter fun l => l ∉ mutCells (olds hs)), l ∈ E₁ := fun l hl => (mem_keep.mp hl).1
        have hEoin : ∀ l ∈ Eo, l ∈ Ls.flatten ∨ σ1.next ≤ l := fun l hl => by
          rcases (hEomem l).mp hl with h | h
          · exact .inl h
          · exact .inr h.1
        have hIc := callee_inv (d := d) hI₁ hholes hpw hts.symm hkeys hfo hEo hEoin hdL hdLS hwf₁ hold
        -- Cells the caller had before the call: allocated, below `σ1.next`, none of the callee's.
        have hlow : ∀ l, σ1.mem l ≠ none → σ2.mem l ≠ none := fun l h => by rw [hold l (hwf₁ l h)]; exact h
        have hapartE : ∀ {Y : List Nat}, (∀ l ∈ Y, σ1.mem l ≠ none) → Disj Y Ls.flatten → Disj Y (mutCells (olds hs)) →
            Disj Y (Eo ++ (mutCells (olds hs))) := by
          intro Y hY hYL hYM l hl hl'
          rcases List.mem_append.mp hl' with hl' | hl'
          · rcases hEoin l hl' with h | h
            · exact hYL l hl h
            · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hwf₁ l (hY l hl)) h)
          · exact hYM l hl hl'
        have hXa : ∀ l ∈ (E₁.filter fun l => l ∉ mutCells (olds hs)), σ1.mem l ≠ none := fun l hl => hI₁.alloc l (hXE l hl)
        have hXc : Disj (E₁.filter fun l => l ∉ mutCells (olds hs)) (Eo ++ (mutCells (olds hs))) := hapartE hXa (fun l hl h => hdL l h (hXE l hl))
          (fun l hl => (mem_keep.mp hl).2)
        have hSc : Disj S (Eo ++ (mutCells (olds hs))) := hapartE hI₁.allocS (fun l hl h => hdLS l h hl)
          (fun l hl h => hI₁.disj l hl (hMin l h))
        -- What the call leaves, with a value or a failure: the callee's owned parameters dropped, and
        -- the caller's variables as they were, but for the trees it lent `mut`.
        have key : ∀ σ3 Ec' Lw, Inv σ3 Γ'' (cells ++ (d.refs.map Prod.fst).zip (hs.map Hole.loc)) Ec'
            (roCells (olds hs)) → Disj Lw Ec' → Moves σ2 (Eo ++ mutCells (olds hs)) σ3 Ec' Lw →
            ∃ σ4 E'', dropCells σ3 ((d.owns.map Prod.snd).zip (cells.map Prod.snd)) = some σ4 ∧
              Inv σ4 Γ' env E'' S ∧ Agree σ3 σ4 Lw ∧ Disj Lw E'' ∧ Disj Lw S ∧ Moves σ E σ4 E'' Lw := by
          intro σ3 Ec' Lw hI₃ hdw hm₃
          -- The callee's variables when it ends: its owned parameters, then its borrows, as they were.
          have hsh := (typed_shape hbody hIc.keys).trans (shape_fnCtx d)
          obtain ⟨Γa, rfl, hΓa⟩ := shape_split (ownCtx d.owns) hsh (refCtx_refs d.refs)
          have hla : Γa.length = cells.length := by
            rw [← shape_length, hΓa, hlenc]; simp [ownCtx]
          obtain ⟨Ea, Sa, Eb, Sb, hfa, hfb, rfl, hSab⟩ := hI₃.foot.split hla
          obtain ⟨ps, hps, hlt, rfl, rfl⟩ := (foot_refs hts.symm).mp hfb
          have hnd := nodup_append_disj.mp hI₃.nodup
          obtain ⟨rfl, σ4, hdrop, hn4, hfree4, hkeep4⟩ := dropCells_ok hfa hΓa hnd.1
          have hXSa : ∀ l ∈ (E₁.filter fun l => l ∉ mutCells (olds hs)) ++ S, σ1.mem l ≠ none := by
            intro l hl
            rcases List.mem_append.mp hl with h | h
            · exact hXa l h
            · exact hI₁.allocS l h
          have hXSc := disj_append_left.mpr ⟨hXc, hSc⟩
          obtain ⟨hXSc', hXSw⟩ := hm₃.apart hwf₂ (fun l hl => hlow l (hXSa l hl)) hXSc
          have hkeep3 := hm₃.keeps hwf₂ (fun l hl => hlow l (hXSa l hl)) hXSc
          have hag : Agree σ1 σ4 ((E₁.filter fun l => l ∉ mutCells (olds hs)) ++ S) := by
            intro l hl
            rw [hkeep4 l fun h => hXSc' l hl (List.mem_append.mpr (.inl h)), hkeep3 l hl,
              hold l (hwf₁ l (hXSa l hl))]
          have hin : ∀ {Y : List Nat}, (∀ l ∈ Y, l ∈ (E₁.filter fun l => l ∉ mutCells (olds hs)) ++ S) →
              Disj Y (Ea ++ mutCells ps) ∧ Disj Y Lw := fun hY =>
            ⟨fun l hl => hXSc' l (hY l hl), fun l hl => hXSw l (hY l hl)⟩
          have hXin := @hin (E₁.filter fun l => l ∉ mutCells (olds hs)) fun l h => List.mem_append.mpr (.inl h)
          have hSin := @hin S fun l h => List.mem_append.mpr (.inr h)
          obtain ⟨E'', hI₄, hmem⟩ := caller_rebuild (σ' := σ4) hI₁ hholes hpw hps
            (fun p hp hm => (hlt p hp).frame fun l hl => hkeep4 l fun h =>
              hnd.2.2 l h (mem_mutCells.mpr ⟨p, hp, hm, hl⟩))
            hnd.2.1 hag (fun l hl h => hXin.1 l hl (List.mem_append.mpr (.inr h)))
            (fun l hl h => hSin.1 l hl (List.mem_append.mpr (.inr h)))
          have m1 : Moves σ E σ1 ((E₁.filter fun l => l ∉ mutCells (olds hs)) ++ mutCells (olds hs) ++
              Ls.flatten) [] := hm₁.relabel fun x => by
            simp only [List.mem_append, mem_keep, List.not_mem_nil, or_false]
            constructor
            · rintro ((⟨h, -⟩ | h) | h)
              · exact .inl h
              · exact .inl (hMin x h)
              · exact .inr h
            · rintro (h | h)
              · by_cases hM : x ∈ mutCells (olds hs)
                · exact .inl (.inr hM)
                · exact .inl (.inl ⟨h, hM⟩)
              · exact .inr h
          have m2 := Moves.grow (E := (E₁.filter fun l => l ∉ mutCells (olds hs)) ++ mutCells (olds hs) ++ Ls.flatten)
            (E' := (E₁.filter fun l => l ∉ mutCells (olds hs)) ++ (Eo ++ mutCells (olds hs)))
            hwf₁ hwf₂ hle hold hnew (fun l hl => by
              simp only [List.mem_append] at hl
              rcases hl with (h | h) | h
              · exact hXa l h
              · exact hI₁.alloc l (hMin l h)
              · exact hvs.alloc l h) (fun l => by
              simp only [List.mem_append, hEomem]
              constructor
              · rintro (h | (h | h) | h)
                · exact .inl (.inl (.inl h))
                · exact .inl (.inr h)
                · exact .inr h
                · exact .inl (.inl (.inr h))
              · rintro (((h | h) | h) | h)
                · exact .inl h
                · exact .inr (.inr h)
                · exact .inr (.inl (.inl h))
                · exact .inr (.inl (.inr h)))
          have m3 := hm₃.widen (fun l hl => hlow l (hXa l hl)) hXc
          generalize (E₁.filter fun l => l ∉ mutCells (olds hs)) = X at m1 m2 m3 hmem hXin
          have m3' := m3.relabel (E'' := X ++ mutCells ps ++ Lw ++ Ea) (L'' := []) fun x => by mem_iff
          have m4 := Moves.free (E := X ++ mutCells ps ++ Lw ++ Ea) (E' := X ++ mutCells ps ++ Lw) (D := Ea)
            (WF.of_free hm₃.wf hn4 hfree4 hkeep4) hn4 (fun l hl => (m3'.alloc l).mpr (.inr (.inl hl)))
            (fun x => by mem_iff) hfree4 hkeep4 (by
              intro l hl hl'
              simp only [List.mem_append] at hl
              rcases hl with (h | h) | h
              · exact hXin.1 l h (List.mem_append.mpr (.inl hl'))
              · exact hnd.2.2 l hl' h
              · exact hdw l h (List.mem_append.mpr (.inl hl')))
          refine ⟨σ4, E'', hdrop, hI₄, fun l hl => hkeep4 l fun h => hdw l hl (List.mem_append.mpr (.inl h)),
            fun l hl hl' => ?_, fun l hl hS => hSin.2 l hS hl, ?_⟩
          · rcases (hmem l).mp hl' with h | h
            · exact hXin.2 l h hl
            · exact hdw l hl (List.mem_append.mpr (.inr h))
          · refine (((m1.trans m2 disj_nil_left hwf).trans m3' disj_nil_left hwf).trans m4 disj_nil_left
              hwf).relabel fun x => ?_
            rw [hmem x]
            simp only [List.mem_append, List.not_mem_nil, or_false]
        have h3 := ih _ _ _ _ _ _ _ _ hbody hIc hwf₂
        generalize eval F n σ2 _ d.body = r3 at h3 ⊢
        rcases r3 with ⟨r3, σ3⟩
        cases r3 with
        | val w =>
          obtain ⟨Ec', Lw, hI₃, hvw, hdw, -, hm₃⟩ := h3
          obtain ⟨σ4, E'', hdrop, hI₄, hag, hdE, hdS, hm⟩ := key σ3 Ec' Lw hI₃ hdw hm₃
          simp only [Res.done, ↓reduceIte, hdrop]
          exact ⟨E'', Lw, hI₄, hvw.frame hag, hdE, hdS, hm⟩
        | fail k =>
          obtain ⟨Ec', hI₃, hm₃⟩ := h3
          obtain ⟨σ4, E'', hdrop, hI₄, -, -, -, hm⟩ := key σ3 Ec' [] hI₃ disj_nil_left hm₃
          simp only [Res.done, ↓reduceIte, hdrop]
          exact ⟨E'', hI₄, hm⟩
        | stuck => simp [Post] at h3
        | timeout => simp [Res.done, Post]
    | ite hc ha hb wa wb =>
      simp only [eval]
      have hk₀ := hI.keys
      rw [← typed_keys hc] at hk₀
      have h1 := ih _ _ _ _ _ _ _ _ hc hI hwf
      generalize eval F n σ env _ = r1 at h1 ⊢
      rcases r1 with ⟨r1, σ1⟩
      cases r1 with
      | val v =>
        obtain ⟨E₁, L₁, hI₁, hv₁, -, -, hm₁⟩ := h1
        cases hv₁ with
        | @int k =>
          dsimp only
          split
          · exact post_after hm₁ hwf (post_weaken (ih _ _ _ _ _ _ _ _ hb hI₁ hm₁.wf) wb)
          · exact post_after hm₁ hwf (post_weaken (ih _ _ _ _ _ _ _ _ ha hI₁ hm₁.wf) wa)
      | fail k => exact post_out h1 (by simp) (wa.trans (typed_weaker ha hk₀))
      | stuck => simp [Post] at h1
      | timeout => simp [Post]
    | throw_ ha =>
      simp only [eval]
      have h1 := ih _ _ _ _ _ _ _ _ ha hI hwf
      generalize eval F n σ env _ = r1 at h1 ⊢
      rcases r1 with ⟨r1, σ1⟩
      cases r1 with
      | val v =>
        obtain ⟨E₁, L₁, hI₁, hv₁, -, -, hm₁⟩ := h1
        cases hv₁ with
        | int => exact ⟨E₁, hI₁, hm₁⟩
      | fail k => exact post_out h1 (by simp) (Weaker.refl _)
      | stuck => simp [Post] at h1
      | timeout => simp [Post]
    | try_ hx hb hh =>
      simp only [eval]
      have hkb := hI.keys
      rw [← typed_keys hb] at hkb
      have hxb := lookup_none_keys hx
      have h1 := ih _ _ _ _ _ _ _ _ hb hI hwf
      generalize eval F n σ env _ = r1 at h1 ⊢
      rcases r1 with ⟨r1, σ1⟩
      cases r1 with
      | val v =>
        have w := typed_weaker hh (List.nodup_cons.mpr ⟨hxb, hkb⟩)
        cases w with
        | cons _ w => exact post_weaken h1 w
      | fail k =>
        dsimp only
        obtain ⟨E₁, hI₁, hm₁⟩ := h1
        obtain ⟨hIb, hma⟩ := bind_ok (v := .int k) hI₁ .int disj_nil_left disj_nil_left hm₁ hwf hxb
        have h2 := ih _ _ _ _ _ _ _ _ hh hIb hma.wf
        rw [show (σ1.alloc (.int k)).1 = σ1.next from rfl]
        exact leave_ok hma hwf h2
      | stuck => simp [Post] at h1
      | timeout => simp [Post]

/-- The store a program starts in: nothing allocated. -/
def Store.empty : Store := { mem := fun _ => none, next := 0 }

/-- A well-typed program never gets stuck — no use of a moved value, no use after free, no double
free — and when it ends, the only cells left allocated are those its result owns, and none if it
failed: every other value was dropped exactly once, on the way out of a failure too. -/
theorem program_ok (hF : FnsOk F) (ht : Typed F [] e τ Γ') (n : Nat) :
    match eval F n .empty [] e with
    | (.stuck, _) => False
    | (.timeout, _) => True
    | (.val v, σ') => ∃ L, VT σ' τ v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.fail _, σ') => ∀ l, σ'.mem l = none := by
  have h := eval_ok F hF n .empty [] [] [] [] e τ Γ' ht ⟨.nil, List.nodup_nil, disj_nil_left, List.nodup_nil⟩
    (fun _ h => absurd rfl h)
  generalize eval F n .empty [] e = r at h ⊢
  rcases r with ⟨r, σ'⟩
  cases r with
  | stuck => exact h
  | timeout => trivial
  | val v =>
    obtain ⟨E', L, hI, hv, -, -, hm⟩ := h
    have hΓ : Γ' = [] := List.eq_nil_of_map_eq_nil (typed_keys ht)
    subst hΓ
    cases hI.foot
    exact ⟨L, hv, fun l => by rw [hm.alloc]; simp [Store.empty]⟩
  | fail k =>
    obtain ⟨E', hI, hm⟩ := h
    have hΓ : Γ' = [] := List.eq_nil_of_map_eq_nil (typed_keys ht)
    subst hΓ
    cases hI.foot
    intro l
    have := hm.alloc l
    simp [Store.empty] at this
    exact this

end FlyCore.Ownership
