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

/-! ## Atoms -/

/-- An atom: its value, of its type, owning cells no variable does; the step accounted for. -/
theorem atom_ok (h : AtomTy Γ a τ Γ') (hI : Inv σ Γ env E S) (hwf : WF σ) :
    ∃ v σ' E' L, evalAtom σ env a = some (v, σ') ∧ Inv σ' Γ' env E' S ∧ VT σ' τ v L ∧ Disj L E' ∧
      Disj L S ∧ Moves σ E σ' E' L := by
  cases h with
  | lit => exact ⟨_, σ, E, [], rfl, hI, .int, disj_nil_left, disj_nil_left, Moves.refl hwf hI.alloc⟩
  | read hp =>
    obtain ⟨a, τr, Lr, P, l, s, ha, hLr, hpath, hres, -⟩ := place_ok hp hI.foot
    obtain ⟨Rb, hRb, rfl⟩ := path_split hpath hLr
    cases hRb with
    | @int _ k hl =>
      exact ⟨.int k, σ, E, [], by simp [evalAtom, hres, hl], hI, .int, disj_nil_left, disj_nil_left,
        Moves.refl hwf hI.alloc⟩
  | move hx =>
    obtain ⟨a, L, E₁, E₂, ha, hL, hE, hupd⟩ := foot_update hI.foot hI.keys hx rfl
    simp only [SlotOk] at hL
    cases hL with
    | @box _ b _ Rb hb hRb hn =>
      have hnd := seg_nodup (hE ▸ hI.nodup)
      have haE : a ∈ E := hE ▸ mem_seg.mpr (.inl (List.mem_cons_self ..))
      have haS : a ∉ S := fun h => hI.disj a h haE
      have ha12 : a ∉ E₁ ++ E₂ := hnd.2.1 a (List.mem_cons_self ..)
      have hag : Agree σ (σ.set a (some .moved)) (E₁ ++ E₂ ++ S) := agree_set (by
        intro h
        rcases List.mem_append.mp h with h | h
        · exact ha12 h
        · exact haS h)
      have hR' : Disj Rb (E₁ ++ E₂) := fun x hx => hnd.2.1 x (List.mem_cons_of_mem _ hx)
      refine ⟨_, _, E₁ ++ [a] ++ E₂, Rb, by simp [evalAtom, ha, hb],
        ⟨hupd _ (.own _ false) [a] (by rfl) hag (by simp [SlotOk, Store.set]), ?_, ?_, ?_⟩,
        .box (hRb.frame (agree_set hn)), ?_, ?_, ?_⟩
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

/-- The owned arguments, in order: their values, each owning cells of no variable's and of no other
value's. -/
theorem atoms_ok : AtomsTy Γ as τs Γ' → Inv σ Γ env E S → WF σ →
    ∃ vs σ' E' Ls, evalAtoms σ env as = some (vs, σ') ∧ Inv σ' Γ' env E' S ∧ Vals σ' τs vs Ls ∧
      Ls.flatten.Nodup ∧ Disj Ls.flatten E' ∧ Disj Ls.flatten S ∧ Moves σ E σ' E' Ls.flatten := by
  intro h
  induction h generalizing σ E with
  | nil =>
    intro hI hwf
    exact ⟨[], σ, E, [], rfl, hI, .nil, List.nodup_nil, disj_nil_left, disj_nil_left, Moves.refl hwf hI.alloc⟩
  | cons ha _ ih =>
    intro hI hwf
    obtain ⟨v, σ1, E₁, L₁, hev, hI₁, hv₁, hd₁, hdS₁, hm₁⟩ := atom_ok ha hI hwf
    obtain ⟨vs, σ2, E₂, Ls, hevs, hI₂, hvs, hn, hd₂, hdS₂, hm₂⟩ := ih hI₁ hm₁.wf
    obtain ⟨hdE, hdL⟩ := hm₂.apart hm₁.wf hv₁.alloc hd₁
    refine ⟨v :: vs, σ2, E₂, L₁ :: Ls, by simp [evalAtoms, hev, hevs], hI₂,
      .cons (hv₁.frame (hm₂.keeps hm₁.wf hv₁.alloc hd₁)) hvs, ?_, ?_, ?_, ?_⟩
    · simp only [List.flatten_cons]
      exact nodup_append_disj.mpr ⟨hv₁.nodup, hn, hdL⟩
    · simp only [List.flatten_cons]
      exact disj_append_left.mpr ⟨hdE, hd₂⟩
    · simp only [List.flatten_cons]
      exact disj_append_left.mpr ⟨hdS₁, hdS₂⟩
    · simpa using hm₁.trans hm₂ hd₁ hwf

theorem post_now (hI : Inv σ Γ env E S) (hwf : WF σ) (hv : VT σ τ v []) (hh : Held F O σ hs R H E) :
    Post F O σ E S R H Γ env τ hs (.val v, σ) :=
  ⟨E, H, [], hI, hv, disj_nil_left, disj_nil_left, Moves.refl hwf (fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · exact hI.alloc l h
    · exact hh.allocH l h), hh⟩

/-- A result carried on unchanged out of a sub-expression — a failure, or running out of fuel — is as
the sub-expression said, of any context weaker than the one it would have left. -/
theorem post_out {r : Res × Store} (h : Post F O σ E S R H Γ₁ env τ₁ hs r) (hv : ∀ v σ', r ≠ (.val v, σ'))
    (w : Weaker Γ' Γ₁) : Post F O σ E S R H Γ' env τ hs r := by
  rcases r with ⟨r, σ'⟩
  cases r with
  | val v => exact absurd rfl (hv v σ')
  | abort id k => obtain ⟨haim, E', H', hI, hm, hh⟩ := h; exact ⟨haim, E', H', hI.weaken w, hm, hh⟩
  | stuck => exact h
  | timeout => trivial

/-- After a step that gave nothing of its own, what the next one gives is what the two give. -/
theorem post_after {r : Res × Store} (hm : Moves σ (E ++ H) σ1 (E₁ ++ H₁) []) (hwf : WF σ)
    (h : Post F O σ1 E₁ S R H₁ Γ' env τ hs r) : Post F O σ E S R H Γ' env τ hs r := by
  rcases r with ⟨r, σ'⟩
  cases r with
  | val v =>
    obtain ⟨E', H', L, hI, hv, hd, hdS, hm', hh⟩ := h
    exact ⟨E', H', L, hI, hv, hd, hdS, (hm.trans hm' disj_nil_left hwf).relabel fun x => by simp, hh⟩
  | abort id k =>
    obtain ⟨haim, E', H', hI, hm', hh⟩ := h
    exact ⟨haim, E', H', hI, (hm.trans hm' disj_nil_left hwf).relabel fun x => by simp, hh⟩
  | stuck => exact h
  | timeout => trivial

/-- A step of the code alone: what it gives, the handlers as they were. -/
theorem post_step (hh : Held F O σ hs R H E) (hwf : WF σ) (hI₂ : Inv σ2 Γ' env E₂ S) (hv : VT σ2 τ v L₂)
    (hd₂ : Disj L₂ E₂) (hdS₂ : Disj L₂ S) (hm : Moves σ E σ2 E₂ L₂) :
    Post F O σ E S R H Γ' env τ hs (.val v, σ2) := by
  obtain ⟨hm', hh', hdH⟩ := hh.local hwf hm
  exact ⟨E₂, H, L₂, hI₂, hv, disj_append_right.mpr ⟨hd₂, hdH⟩, hdS₂, hm', hh'⟩

/-- A value, then a step of the code alone with it: what the two give. -/
theorem post_local (hh : Held F O σ hs R H E) (hwf : WF σ)
    (hm₁ : Moves σ (E ++ H) σ1 (E₁ ++ H₁) L₁) (hd₁ : Disj L₁ (E₁ ++ H₁)) (hh₁ : Held F O σ1 hs R H₁ E₁)
    (hI₂ : Inv σ2 Γ' env E₂ S) (hv : VT σ2 τ v L₂) (hd₂ : Disj L₂ E₂) (hdS₂ : Disj L₂ S)
    (hm₂ : Moves σ1 (E₁ ++ L₁) σ2 E₂ L₂) : Post F O σ E S R H Γ' env τ hs (.val v, σ2) := by
  have hRL := (hh.apart hwf hm₁).2
  have hh₁' : Held F O σ1 hs R H₁ (E₁ ++ L₁) := by
    refine ⟨hh₁.ok, hh₁.nodup, fun l hl h => ?_, fun l hl h => ?_⟩
    · rcases List.mem_append.mp h with h | h
      · exact hh₁.disj l hl h
      · exact hd₁ l h (List.mem_append.mpr (.inr hl))
    · simp only [List.mem_append] at h
      rcases h with (h | h) | h
      · exact hh₁.ro l hl (List.mem_append.mpr (.inl h))
      · exact hRL l hl h
      · exact hh₁.ro l hl (List.mem_append.mpr (.inr h))
  obtain ⟨hm₂', hh₂, hdH⟩ := hh₁'.local hm₁.wf hm₂
  refine ⟨E₂, H₁, L₂, hI₂, hv, disj_append_right.mpr ⟨hd₂, hdH⟩, hdS₂, ?_, hh₂⟩
  exact ((hm₁.relabel (E'' := E₁ ++ L₁ ++ H₁) (L'' := []) fun x => by
    simp only [List.mem_append, List.not_mem_nil, or_false]; grind).trans hm₂' disj_nil_left hwf).relabel
    fun x => by simp

/-- What code under an unwinding handler gives, said of the stack below it. -/
theorem post_pop {r : Res × Store} (h : Post F O σ E S R H Γ' env τ (.abort l i :: hs) r) (hv : ∀ id k σ', r ≠ (.abort id k, σ')) :
    Post F O σ E S R H Γ' env τ hs r := by
  rcases r with ⟨r, σ'⟩
  cases r with
  | val v => obtain ⟨E', H', L, hI, hv, hd, hdS, hm, hh⟩ := h; exact ⟨E', H', L, hI, hv, hd, hdS, hm, hh.pop_abort⟩
  | abort id k => exact absurd rfl (hv id k σ')
  | stuck => exact h
  | timeout => trivial

/-- After a value, ready for the code that has it. -/
theorem Ready.val (hR : Ready F O σ E S R H hs r) (hwf : WF σ) (hI : Inv σ Γ env E S)
    (hm : Moves σ (E ++ H) σ' (E' ++ H') L) (hh : Held F O σ' hs R H' E') (hd : Disj L (E' ++ H'))
    (hX : ∀ x ∈ X, x ∈ E' ∨ x ∈ L) : Ready F O σ' X S R H' hs r :=
  hR.post hwf hI.disj hI.allocS hm hh (fun l hl h => hd l hl (List.mem_append.mpr (.inr h))) hX

/-- A fresh cell joins what the code may change. -/
theorem Ready.alloc (hR : Ready F O σ E S R H hs r) (hwf : WF σ) :
    Ready F O (σ.alloc v).2 (σ.next :: E) S R H hs r := by
  obtain ⟨hh, hHS, hc⟩ := hR
  have hfresh : ∀ l ∈ R ++ H, l ≠ σ.next := fun l hl h => by
    subst h; exact Nat.lt_irrefl _ (hwf _ (hh.alloc _ hl))
  refine ⟨⟨hh.ok.frame (agree_alloc hwf hh.alloc), hh.nodup, ?_, ?_⟩, hHS, hc⟩
  · exact fun l hl h => by
      rcases List.mem_cons.mp h with h | h
      · exact hfresh l (List.mem_append.mpr (.inr hl)) h
      · exact hh.disj l hl h
  · intro l hl h
    simp only [List.cons_append, List.mem_cons] at h
    rcases h with h | h
    · exact hfresh l (List.mem_append.mpr (.inl hl)) h
    · exact hh.ro l hl h

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
    (hm₁ : Moves σ E σ1 (E₁ ++ H₁) L₁) (hH₁ : ∀ l ∈ H₁, σ1.mem l ≠ none) (hwf : WF σ) (hx : x ∉ Γ₁.map Prod.fst) :
    Inv (σ1.alloc v).2 ((x, .own τx true) :: Γ₁) ((x, σ1.next) :: env) (σ1.next :: L₁ ++ E₁) S ∧
      Moves σ E (σ1.alloc v).2 (σ1.next :: L₁ ++ E₁ ++ H₁) [] := by
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
  · exact (hm₁.relabel (E'' := L₁ ++ E₁ ++ H₁) (L'' := []) fun x => by mem_iff).trans
      ((Moves.allocate hwf₁ (fun l hl => by
        simp only [List.mem_append] at hl
        rcases hl with (hl | hl) | hl
        · exact hL₁ l hl
        · exact hI₁.alloc l hl
        · exact hH₁ l hl))) disj_nil_left hwf |>.relabel fun x => by mem_iff

/-- Dropping the variable a scope declared, live or perhaps moved, as the scope is left: its
footprint is freed, and the rest stands. -/
theorem drop_var (hI₃ : Inv σ3 ((x, .own τx live) :: Γ₂) ((x, c) :: env) E₃ S) (hh₃ : Held F O σ3 hs R H₃ E₃)
    (hL₃ : ∀ l ∈ L₃, σ3.mem l ≠ none) (hd₃ : Disj L₃ (E₃ ++ H₃)) (hm : Moves σ E σ3 (E₃ ++ H₃) L₃) (hwf : WF σ) :
    ∃ σ4 E₂, dropCell σ3 τx c = some σ4 ∧ Inv σ4 Γ₂ env E₂ S ∧ Agree σ3 σ4 L₃ ∧ Disj L₃ (E₂ ++ H₃) ∧
      Moves σ E σ4 (E₂ ++ H₃) L₃ ∧ Held F O σ4 hs R H₃ E₂ := by
  obtain ⟨Lx, E₂, S₂, hs, hfoot, hE₃, hS₃⟩ := hI₃.foot.uncons
  simp only [addE, addS, Slot.excl, ↓reduceIte] at hE₃ hS₃
  subst hE₃ hS₃
  obtain ⟨σ4, hdrop, hnext, hfree, hkeep⟩ := dropCell_own hs
  have hnd := nodup_append_disj.mp hI₃.nodup
  have hxH : Disj Lx H₃ := fun l hl h => hh₃.disj l h (List.mem_append.mpr (.inl hl))
  have hag4 : Agree σ3 σ4 (E₂ ++ S) := by
    intro l hl
    refine hkeep l fun h => ?_
    rcases List.mem_append.mp hl with hl | hl
    · exact hnd.2.2 l h hl
    · exact hI₃.disj l hl (List.mem_append.mpr (.inl h))
  have hm₄ := Moves.free (E := Lx ++ E₂ ++ H₃ ++ L₃) (E' := E₂ ++ H₃ ++ L₃) (D := Lx)
    (WF.of_free hm.wf hnext hfree hkeep) hnext
    (fun l hl => by
      simp only [List.mem_append] at hl
      rcases hl with ((hl | hl) | hl) | hl
      · exact hI₃.alloc l (List.mem_append.mpr (.inl hl))
      · exact hI₃.alloc l (List.mem_append.mpr (.inr hl))
      · exact hh₃.allocH l hl
      · exact hL₃ l hl)
    (fun x => by mem_iff) hfree hkeep (by
      intro l hl hlx
      simp only [List.mem_append] at hl
      rcases hl with (hl | hl) | hl
      · exact hnd.2.2 l hlx hl
      · exact hxH l hlx hl
      · exact hd₃ l hl (List.mem_append.mpr (.inl (List.mem_append.mpr (.inl hlx)))))
  refine ⟨σ4, E₂, hdrop, ⟨hfoot.frame hag4, hnd.2.1, fun l hl hl' => hI₃.disj l hl
      (List.mem_append.mpr (.inr hl')), (List.nodup_cons.mp hI₃.keys).2⟩,
    fun l hl => hkeep l fun h => hd₃ l hl (List.mem_append.mpr (.inl (List.mem_append.mpr (.inl h)))),
    fun l hl hl' => hd₃ l hl (by
      rcases List.mem_append.mp hl' with h | h
      · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr h)))
      · exact List.mem_append.mpr (.inr h)), ?_, ?_⟩
  · exact ((hm.relabel (E'' := Lx ++ E₂ ++ H₃ ++ L₃) (L'' := []) fun x => by mem_iff).trans hm₄ disj_nil_left
      hwf).relabel fun x => by mem_iff
  · refine (hh₃.frame fun l hl => hkeep l fun h => ?_).sub fun l hl => List.mem_append.mpr (.inr hl)
    rcases List.mem_append.mp hl with hl | hl
    · exact hh₃.ro l hl (List.mem_append.mpr (.inl (List.mem_append.mpr (.inl h))))
    · exact hxH l h hl

/-- Leaving a scope, with a value or a failure, drops its variable. -/
theorem leave_ok {r : Res × Store} (hm : Moves σ (E ++ H) σb (Eb ++ Hb) []) (hwf : WF σ)
    (h : Post F O σb Eb S R Hb ((x, .own τx live) :: Γ₂) ((x, c) :: env) τ hs r) :
    Post F O σ E S R H Γ₂ env τ hs (leave τx c r) := by
  rcases r with ⟨r, σ3⟩
  cases r with
  | val w =>
    obtain ⟨E₃, H₃, L₃, hI₃, hv₃, hd₃, hdS₃, hm₃, hh₃⟩ := h
    obtain ⟨σ4, E₂, hdrop, hI₄, hag, hd, hm₄, hh₄⟩ := drop_var hI₃ hh₃ hv₃.alloc hd₃
      ((hm.trans hm₃ disj_nil_left hwf).relabel fun x => by simp) hwf
    simp only [leave, Res.done, ↓reduceIte, hdrop]
    exact ⟨E₂, H₃, L₃, hI₄, hv₃.frame hag, hd, hdS₃, hm₄, hh₄⟩
  | abort id k =>
    obtain ⟨haim, E₃, H₃, hI₃, hm₃, hh₃⟩ := h
    obtain ⟨σ4, E₂, hdrop, hI₄, -, -, hm₄, hh₄⟩ := drop_var (L₃ := []) hI₃ hh₃ (by simp) disj_nil_left
      ((hm.trans hm₃ disj_nil_left hwf).relabel fun x => by simp) hwf
    simp only [leave, Res.done, ↓reduceIte, hdrop]
    exact ⟨haim, E₂, H₃, hI₄, hm₄, hh₄⟩
  | stuck => exact h
  | timeout => simp [leave, Res.done, Post]

/-! ## Entering a function or an arm -/

/-- A function's or an arm's activation, entered from a caller's whose owned arguments are
`vs`, lending it the holes `hos`, and, for an arm, the places its `handle` lent it, `post`, only
read: its parameters bound, its body run under the handlers `hs'` — the caller's, or for an arm
those below its `handle` — and the owned ones dropped, it gives the caller what a call does. -/
theorem enter_ok {d : Fn} {Γp : Ctx} {post : Env} {Hc Rp : List Nat} {hs hs' : HS} {r' : Row}
    {hos : List Hole} {Γ'' : Ctx} {R' Ha Hr : List Nat}
    (ihn : ∀ σ Γ env E S H τ Γ', Typed F O Γ d.body τ Γ' r' → Inv σ Γ env E S → WF σ →
      Ready F O σ E S R' H hs' r' → Post F O σ E S R' H Γ' env τ hs' (eval F O n hs' σ env d.body))
    (hbody : Typed F O (fnCtx d ++ Γp) d.body d.ret Γ'' r')
    (hkeys : ((d.owns.map Prod.fst) ++ (d.refs.map Prod.fst) ++ Γp.map Prod.fst).Nodup)
    (hro : RefCtx Γp) (hpost : Foot σ1 Γp post Hc Rp) (hRpR : ∀ l ∈ Rp, l ∈ R)
    (hh0 : Held F O σ hs R H E) (hh₁ : Held F O σ1 hs R (Ha ++ Hc ++ Hr) (E₁ ++ Ls.flatten))
    (hHS : Disj (Ha ++ Hc ++ Hr) S)
    (hok' : HSOk F O σ1 hs' R' Hr) (hR'R : ∀ l ∈ R', l ∈ R) (hcov' : Covers hs' r')
    (hback : ∀ σ' Hc' Rp' H', Foot σ' Γp post Hc' Rp' → HSOk F O σ' hs' R' H' → Agree σ1 σ' (R ++ Ha) →
      HSOk F O σ' hs R (Ha ++ Hc' ++ H'))
    (hsub : ∀ i, AimedIn i hs' → AimedIn i hs)
    (hwf : WF σ) (hI₁ : Inv σ1 Γ₁ env E₁ S) (hvs : Vals σ1 (d.owns.map Prod.snd) vs Ls)
    (hLn : Ls.flatten.Nodup) (hdL : Disj Ls.flatten E₁) (hdLS : Disj Ls.flatten S)
    (hm₁ : Moves σ (E ++ H) σ1 (E₁ ++ (Ha ++ Hc ++ Hr)) Ls.flatten)
    (hts : hos.map (fun h => (h.mode, h.ty)) = d.refs.map Prod.snd) (hpw : hos.Pairwise Apart)
    (hholes : ∀ h ∈ hos, HoleOk σ1 Γ₁ env h) :
    Post F O σ E S R H Γ₁ env d.ret hs (enter (eval F O n hs') σ1 d.owns vs (d.refs.map Prod.fst) (hos.map Hole.loc) post d.body) := by
  have hwf₁ := hm₁.wf
  simp only [enter]
  obtain ⟨Eo, hfo, hEo, hEomem, hle, hwf₂, hold, hnew, hlenc⟩ :=
    allocAll_ok (names := d.owns.map Prod.fst) hvs (by simp) hwf₁ hLn
  rw [zip_fst_snd] at hfo
  generalize allocAll σ1 ((d.owns.map Prod.fst).zip vs) = al at hfo hEomem hle hwf₂ hold hnew hlenc ⊢
  obtain ⟨cells, σ2⟩ := al
  dsimp only at hfo hEomem hle hwf₂ hold hnew hlenc ⊢
  -- The handlers' state, split around the frame whose arm this is.
  have hHn := hh₁.nodup
  have hHn1 := List.nodup_append.mp hHn
  have hHn2 := List.nodup_append.mp hHn1.1
  have hRa : ∀ l ∈ R, σ1.mem l ≠ none := fun l hl => hh₁.alloc l (List.mem_append.mpr (.inl hl))
  have hHa : ∀ l ∈ Ha ++ Hc ++ Hr, σ1.mem l ≠ none := hh₁.allocH
  have hRE : ∀ l ∈ R, l ∉ E₁ := fun l hl h => hh₁.ro l hl (by simp [h])
  have hRL : ∀ l ∈ R, l ∉ Ls.flatten := fun l hl h => hh₁.ro l hl (by simp [h])
  have hRH : ∀ l ∈ R, l ∉ Ha ++ Hc ++ Hr := fun l hl h => hh₁.ro l hl (List.mem_append.mpr (.inr h))
  have hHE : ∀ l ∈ Ha ++ Hc ++ Hr, l ∉ E₁ := fun l hl h => hh₁.disj l hl (by simp [h])
  have hHL : ∀ l ∈ Ha ++ Hc ++ Hr, l ∉ Ls.flatten := fun l hl h => hh₁.disj l hl (by simp [h])
  have hRpa : ∀ l ∈ Rp, σ1.mem l ≠ none := fun l hl => hRa l (hRpR l hl)
  have hMin : ∀ l ∈ (mutCells (olds hos)), l ∈ E₁ := fun l hl => by
    obtain ⟨h, hh, hm, hl⟩ := mem_olds_mut.mp hl
    exact (hole_in hI₁ (hholes h hh) l (List.mem_append.mpr (.inr hl))).1 hm
  have hRoin : ∀ l ∈ (roCells (olds hos)), l ∈ E₁ ∨ l ∈ S := fun l hl => by
    obtain ⟨h, hh, -, hl⟩ := mem_olds_ro.mp hl
    exact (hole_in hI₁ (hholes h hh) l (List.mem_append.mpr (.inr hl))).2
  have hXE : ∀ l ∈ (E₁.filter fun l => l ∉ mutCells (olds hos)), l ∈ E₁ := fun l hl => (mem_keep.mp hl).1
  have hEoin : ∀ l ∈ Eo, l ∈ Ls.flatten ∨ σ1.next ≤ l := fun l hl => by
    rcases (hEomem l).mp hl with h | h
    · exact .inl h
    · exact .inr h.1
  -- Cells the caller had before the call are below `σ1.next`.
  have hlt : ∀ l, σ1.mem l ≠ none → l < σ1.next := hwf₁
  have hIc₀ := callee_inv (d := d) hI₁ hholes hpw hts.symm (List.nodup_append.mp hkeys).1 hfo hEo hEoin hdL hdLS hwf₁ hold
  have hpost₂ : Foot σ2 Γp post Hc Rp := hpost.frame fun l hl => hold l (hwf₁ l (by
    rcases List.mem_append.mp hl with h | h
    · exact hHa l (by simp [h])
    · exact hRpa l h))
  have hHcE : Disj Hc (Eo ++ mutCells (olds hos)) := by
    intro l hl h
    have hl' : l ∈ Ha ++ Hc ++ Hr := by simp [hl]
    rcases List.mem_append.mp h with h | h
    · rcases hEoin l h with h | h
      · exact hHL l hl' h
      · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hlt l (hHa l hl')) h)
    · exact hHE l hl' (hMin l h)
  have hIc : Inv σ2 (fnCtx d ++ Γp) ((cells ++ (d.refs.map Prod.fst).zip (hos.map Hole.loc)) ++ post)
      (Eo ++ mutCells (olds hos) ++ Hc) (roCells (olds hos) ++ Rp) := by
    refine ⟨by simpa using hIc₀.foot.append hpost₂, ?_, ?_, ?_⟩
    · exact nodup_append_disj.mpr ⟨hIc₀.nodup, (List.nodup_append.mp hHn1.1).2.1, hHcE.symm⟩
    · intro l hl hl'
      rcases List.mem_append.mp hl' with h | h
      · rcases List.mem_append.mp hl with hl | hl
        · exact hIc₀.disj l hl h
        · rcases List.mem_append.mp h with h | h
          · rcases hEoin l h with h | h
            · exact hRL l (hRpR l hl) h
            · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hlt l (hRpa l hl)) h)
          · exact hRE l (hRpR l hl) (hMin l h)
      · have hl'' : l ∈ Ha ++ Hc ++ Hr := by simp [h]
        rcases List.mem_append.mp hl with hl | hl
        · rcases hRoin l hl with h | h
          · exact hHE l hl'' h
          · exact hHS l hl'' h
        · exact hRH l (hRpR l hl) hl''
    · simpa [fnCtx, List.map_append, List.map_map, Function.comp_def] using hkeys
  have hlow : ∀ l, σ1.mem l ≠ none → σ2.mem l ≠ none := fun l h => by rw [hold l (hwf₁ l h)]; exact h
  -- What the callee starts with: apart from everything the caller keeps.
  have hapart0 : ∀ l, σ1.mem l ≠ none → l ∉ Ls.flatten → l ∉ mutCells (olds hos) →
      l ∉ Eo ++ mutCells (olds hos) := by
    intro l ha h1 h2 h
    rcases List.mem_append.mp h with h | h
    · rcases hEoin l h with h | h
      · exact h1 h
      · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hlt l ha) h)
    · exact h2 h
  have hapart : ∀ l, σ1.mem l ≠ none → l ∉ Ls.flatten → l ∉ mutCells (olds hos) → l ∉ Hc → l ∉ Hr →
      l ∉ Eo ++ mutCells (olds hos) ++ Hc ++ Hr := by
    intro l ha h1 h2 h3 h4 h
    simp only [List.mem_append] at h
    rcases h with ((h | h) | h) | h
    · rcases hEoin l h with h | h
      · exact h1 h
      · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hlt l ha) h)
    · exact h2 h
    · exact h3 h
    · exact h4 h
  generalize hXdef : (E₁.filter fun l => l ∉ mutCells (olds hos)) = X
  have hXE' : ∀ l ∈ X, l ∈ E₁ := hXdef ▸ hXE
  have hXM : ∀ l ∈ X, l ∉ mutCells (olds hos) := fun l hl => (mem_keep.mp (hXdef ▸ hl)).2
  have hXa : ∀ l ∈ X, σ1.mem l ≠ none := fun l hl => hI₁.alloc l (hXE' l hl)
  have hX₀ : ∀ l ∈ X ++ Ha ++ S, l ∉ Eo ++ mutCells (olds hos) ++ Hc ++ Hr := by
    intro l hl
    simp only [List.mem_append] at hl
    rcases hl with (h | h) | h
    · exact hapart l (hXa l h) (fun h' => hdL l h' (hXE' l h)) (hXM l h)
        (fun h' => hHE l (by simp [h']) (hXE' l h)) (fun h' => hHE l (by simp [h']) (hXE' l h))
    · exact hapart l (hHa l (by simp [h])) (fun h' => hHL l (by simp [h]) h')
        (fun h' => hHE l (by simp [h]) (hMin l h')) (fun h' => hHn2.2.2 l h l h' rfl)
        (fun h' => hHn1.2.2 l (by simp [h]) l h' rfl)
    · exact hapart l (hI₁.allocS l h) (fun h' => hdLS l h' h) (fun h' => hI₁.disj l h (hMin l h'))
        (fun h' => hHS l (by simp [h']) h) (fun h' => hHS l (by simp [h']) h)
  have hX₀a : ∀ l ∈ X ++ Ha ++ S, σ1.mem l ≠ none := by
    intro l hl
    simp only [List.mem_append] at hl
    rcases hl with (h | h) | h
    · exact hXa l h
    · exact hHa l (by simp [h])
    · exact hI₁.allocS l h
  -- What the call leaves, with a value or a failure: the callee's owned parameters dropped, the
  -- caller's variables as they were, but for the trees it lent `mut`, and the frames' state.
  have key : ∀ σ3 Ec' H₃ Lw, Inv σ3 Γ'' ((cells ++ (d.refs.map Prod.fst).zip (hos.map Hole.loc)) ++ post) Ec'
      (roCells (olds hos) ++ Rp) → Disj Lw (Ec' ++ H₃) →
      Moves σ2 (Eo ++ mutCells (olds hos) ++ Hc ++ Hr) σ3 (Ec' ++ H₃) Lw → Held F O σ3 hs' R' H₃ Ec' →
      ∃ σ4 E'' H'', dropCells σ3 ((d.owns.map Prod.snd).zip (cells.map Prod.snd)) = some σ4 ∧
        Inv σ4 Γ₁ env E'' S ∧ Agree σ3 σ4 Lw ∧ Disj Lw (E'' ++ H'') ∧ Disj Lw S ∧
        Moves σ (E ++ H) σ4 (E'' ++ H'') Lw ∧ Held F O σ4 hs R H'' E'' := by
    intro σ3 Ec' H₃ Lw hI₃ hdw hm₃ hh₃
    have hsh : shape Γ'' = ownCtx d.owns ++ (refCtx d.refs ++ Γp) := by
      rw [typed_shape hbody hIc.keys, shape_append, shape_fnCtx, hro.shape, List.append_assoc]
    obtain ⟨Γa, rfl, hΓa⟩ := shape_split (ownCtx d.owns) hsh (fun p hp => by
      rcases List.mem_append.mp hp with hp | hp
      · exact refCtx_refs d.refs p hp
      · exact hro p hp)
    have hla : Γa.length = cells.length := by
      rw [← shape_length, hΓa, hlenc]; simp [ownCtx]
    rw [List.append_assoc] at hI₃
    obtain ⟨Ea, Sa, Eb, Sb, hfa, hfb, rfl, hSab⟩ := hI₃.foot.split hla
    have hlh : hos.length = d.refs.length := by simpa using congrArg List.length hts
    obtain ⟨Er, Sr, Ep, Sp, hfr, hfp, rfl, rfl⟩ := hfb.split (by simp [refCtx, hlh])
    obtain ⟨ps, hps, hlt', rfl, rfl⟩ := (foot_refs hts.symm).mp hfr
    have hnd := nodup_append_disj.mp hI₃.nodup
    have hndb := nodup_append_disj.mp hnd.2.1
    obtain ⟨rfl, σ4, hdrop, hn4, hfree4, hkeep4⟩ := dropCells_ok hfa hΓa hnd.1
    -- What the caller keeps, and what the frames above keep, the callee left alone.
    obtain ⟨hX₃, hXw⟩ := hm₃.apart hwf₂ (fun l hl => hlow l (hX₀a l hl)) (fun l hl => hX₀ l hl)
    have hkeep3 := hm₃.keeps hwf₂ (fun l hl => hlow l (hX₀a l hl)) (fun l hl => hX₀ l hl)
    have hEaH : Disj Ea H₃ := fun l hl h => hh₃.disj l h (by simp [hl])
    have hag : Agree σ1 σ4 (X ++ Ha ++ S) := by
      intro l hl
      rw [hkeep4 l fun h => hX₃ l hl (by simp [h]), hkeep3 l hl, hold l (hwf₁ l (hX₀a l hl))]
    obtain ⟨E'', hI₄, hmem⟩ := caller_rebuild (σ' := σ4) hI₁ hholes hpw hps
      (fun p hp hm => (hlt' p hp).frame fun l hl => hkeep4 l fun h =>
        hnd.2.2 l h (by simp [mem_mutCells.mpr ⟨p, hp, hm, hl⟩]))
      hndb.1 (by rw [hXdef]; exact fun l hl => hag l (by
        rcases List.mem_append.mp hl with h | h
        · simp [h]
        · simp [h]))
      (by rw [hXdef]; exact fun l hl h => hX₃ l (by simp [hl]) (by simp [h]))
      (fun l hl h => hX₃ l (by simp [hl]) (by simp [h]))
    rw [hXdef] at hmem
    have m1 : Moves σ (E ++ H) σ1 (X ++ Ha ++ mutCells (olds hos) ++ Ls.flatten ++ (Hc ++ Hr)) [] :=
      hm₁.relabel fun x => by
        have := hMin x
        have := hXdef ▸ (mem_keep (E := E₁) (M := mutCells (olds hos)) (l := x))
        simp only [List.mem_append, List.not_mem_nil, or_false] at * <;> grind
    have m2 := Moves.grow (E := X ++ Ha ++ mutCells (olds hos) ++ Ls.flatten ++ (Hc ++ Hr))
      (E' := X ++ Ha ++ (Eo ++ mutCells (olds hos) ++ Hc ++ Hr))
      hwf₁ hwf₂ hle hold hnew (fun l hl => by
        simp only [List.mem_append] at hl
        rcases hl with ((((h | h) | h) | h) | h | h)
        · exact hXa l h
        · exact hHa l (by simp [h])
        · exact hI₁.alloc l (hMin l h)
        · exact hvs.alloc l h
        · exact hHa l (by simp [h])
        · exact hHa l (by simp [h])) (fun l => by
        simp only [List.mem_append, hEomem]; grind)
    have m3 := hm₃.widen (X := X ++ Ha) (fun l hl => hlow l (hX₀a l (by simp at hl ⊢; grind)))
      (fun l hl h => hX₀ l (by simp at hl ⊢; grind) h)
    have m3' := m3.relabel (E'' := X ++ Ha ++ mutCells ps ++ Ep ++ H₃ ++ Lw ++ Ea) (L'' := []) fun x => by
      simp only [List.mem_append, List.not_mem_nil, or_false]; grind
    have m4 := Moves.free (E := X ++ Ha ++ mutCells ps ++ Ep ++ H₃ ++ Lw ++ Ea)
      (E' := X ++ Ha ++ mutCells ps ++ Ep ++ H₃ ++ Lw) (D := Ea)
      (WF.of_free hm₃.wf hn4 hfree4 hkeep4) hn4 (fun l hl => (m3'.alloc l).mpr (.inr (.inl hl)))
      (fun x => by simp only [List.mem_append] <;> grind) hfree4 hkeep4 (by
        intro l hl hl'
        have h1 := hnd.2.2 l hl'
        have h2 := hdw l
        have h3 := hX₃ l
        have h4 := hEaH l hl'
        simp only [List.mem_append] at hl h1 h2 h3
        grind)
    have hall : Moves σ (E ++ H) σ4 (E'' ++ (Ha ++ Ep ++ H₃)) Lw :=
      (((m1.trans m2 disj_nil_left hwf).trans m3' disj_nil_left hwf).trans m4 disj_nil_left
        hwf).relabel fun x => by
        simp only [List.mem_append, hmem x, List.not_mem_nil, or_false, List.append_nil]; grind
    have m234 := ((m2.trans m3' disj_nil_left hwf₁).trans m4 disj_nil_left hwf₁)
    have hRkeep' : Agree σ1 σ4 R := m234.keeps hwf₁ hRa (by
      intro l hl h
      have h1 := hXE' l
      have h2 := hMin l
      have h3 := hRE l hl
      have h4 := hRL l hl
      have h5 := hRH l hl
      simp only [List.mem_append, not_or] at h h5
      grind)
    have hRkeep : Agree σ1 σ4 (R ++ Ha) := fun l hl => by
      rcases List.mem_append.mp hl with h | h
      · exact hRkeep' l h
      · exact hag l (by simp [h])
    have hfp4 : Foot σ4 Γp post Ep Sp := hfp.frame fun l hl => hkeep4 l fun h => by
      rcases List.mem_append.mp hl with hl | hl
      · exact hnd.2.2 l h (by simp [hl])
      · exact hI₃.disj l (hSab ▸ by simp [hl]) (by simp [h])
    have hok4 : HSOk F O σ4 hs' R' H₃ := hh₃.ok.frame fun l hl => hkeep4 l fun h => by
      rcases List.mem_append.mp hl with hl | hl
      · exact hh₃.ro l hl (by simp [h])
      · exact hEaH l h hl
    obtain ⟨hRE'', -⟩ := hh0.apart hwf hall
    refine ⟨σ4, E'', Ha ++ Ep ++ H₃, hdrop, hI₄, fun l hl => hkeep4 l fun h => hdw l hl (by simp [h]),
      ?_, fun l hl hS => hXw l (by simp [hS]) hl, hall, ⟨hback σ4 Ep Sp H₃ hfp4 hok4 hRkeep, ?_, ?_, hRE''⟩⟩
    · intro l hl hl'
      have h1 := hdw l hl
      have h2 := hXw l
      simp only [List.mem_append, hmem l] at hl' h1 h2
      grind
    · have hEpn := hndb.2.1
      refine nodup_append_disj.mpr ⟨nodup_append_disj.mpr ⟨hHn2.1, hndb.2.1, ?_⟩, hh₃.nodup, ?_⟩
      · intro l hl h; exact hX₃ l (by simp [hl]) (by simp [h])
      · intro l hl h
        rcases List.mem_append.mp hl with hl | hl
        · exact hX₃ l (by simp [hl]) (by simp [h])
        · exact hh₃.disj l h (by simp [hl])
    · intro l hl hl'
      have h1 := hX₃ l
      have h2 := hh₃.disj l
      have h3 := hndb.2.2 l
      have h4 := hHE l
      simp only [List.mem_append, hmem l] at hl hl' h1 h2 h3 h4
      have h5 := fun h => hXE' l h
      have h6 := hHn1.2.2 l
      have h7 := hHn2.2.2 l
      simp only [List.mem_append] at h6 h7
      grind
  have hRdy : Ready F O σ2 (Eo ++ mutCells (olds hos) ++ Hc) (roCells (olds hos) ++ Rp) R' Hr hs' r' := by
    refine ⟨⟨hok'.frame fun l hl => hold l (hwf₁ l (by
        rcases List.mem_append.mp hl with h | h
        · exact hRa l (hR'R l h)
        · exact hHa l (by simp [h]))), (List.nodup_append.mp hHn).2.1, ?_, ?_⟩, ?_, hcov'⟩
    · intro l hl h
      have h1 := hapart0 l (hHa l (by simp [hl])) (fun h' => hHL l (by simp [hl]) h')
        (fun h' => hHE l (by simp [hl]) (hMin l h'))
      have h2 := hHn1.2.2 l
      simp only [List.mem_append] at h h1 h2
      grind
    · intro l hl h
      have h1 := hapart0 l (hRa l (hR'R l hl)) (hRL l (hR'R l hl)) (fun h' => hRE l (hR'R l hl) (hMin l h'))
      have h2 := hRH l (hR'R l hl)
      simp only [List.mem_append] at h h1 h2
      grind
    · intro l hl h
      rcases List.mem_append.mp h with h | h
      · rcases hRoin l h with h | h
        · exact hHE l (by simp [hl]) h
        · exact hHS l (by simp [hl]) h
      · exact hRH l (hRpR l h) (by simp [hl])
  have h3 := ihn _ _ _ _ _ _ _ _ hbody hIc hwf₂ hRdy
  generalize eval F O n hs' σ2 _ d.body = r3 at h3 ⊢
  rcases r3 with ⟨r3, σ3⟩
  cases r3 with
  | val w =>
    obtain ⟨Ec', H₃, Lw, hI₃, hvw, hdw, -, hm₃, hh₃⟩ := h3
    obtain ⟨σ4, E'', H'', hdrop, hI₄, hag, hdE, hdS, hm, hh⟩ := key σ3 Ec' H₃ Lw hI₃ hdw hm₃ hh₃
    simp only [Res.done, ↓reduceIte, hdrop]
    exact ⟨E'', H'', Lw, hI₄, hvw.frame hag, hdE, hdS, hm, hh⟩
  | abort i k =>
    obtain ⟨haim, Ec', H₃, hI₃, hm₃, hh₃⟩ := h3
    obtain ⟨σ4, E'', H'', hdrop, hI₄, -, -, -, hm, hh⟩ := key σ3 Ec' H₃ [] hI₃ disj_nil_left hm₃ hh₃
    simp only [Res.done, ↓reduceIte, hdrop]
    exact ⟨hsub _ haim, E'', H'', hI₄, hm, hh⟩
  | stuck => simp [Post] at h3
  | timeout => simp [Res.done, Post]

/-! ## A `handle` that resumes -/

/-- A `handle` whose arm resumes: the places it lends the arm resolved, those lent `readonly`
frozen and those lent `mut` hidden from the body, their trees the frame's state; the body run under
the arm's frame; and what was frozen and hidden given back, the hidden with the trees the arm left. -/
theorem handle_ok {hs : HS} {σ : Store} {Γ : Ctx} {env : Env} {E S R H : List Nat} {e : Nat} {op : Op}
    {os rs : List Var} {caps : List (Cap Place)} {ys : List (Mode × Var)} {arm : Expr} {Γa : Ctx}
    {r : Row} {body : Expr} {τ : Ty} {Γb : Ctx}
    (ih : ∀ hs σ Γ env E S R H e τ Γ' r, Typed F O Γ e τ Γ' r → Inv σ Γ env E S → WF σ →
      Ready F O σ E S R H hs r → Post F O σ E S R H Γ' env τ hs (eval F O n hs σ env e))
    (hop : O[e]? = some op) (hos : os.length = op.owns.length) (hrs : rs.length = op.refs.length)
    (hcaps : Caps Γ caps ys) (hexcl : Exclusive ys) (hnd : (os ++ rs ++ caps.map Cap.name).Nodup)
    (harm : Typed F O (armCtx os rs op (caps.map Cap.sig)) arm op.ret Γa r)
    (hbody : Typed F O (freeze (hideAll Γ (roots .mut ys)) (roots .ro ys)) body τ Γb (.eff e :: r))
    (hI : Inv σ Γ env E S) (hwf : WF σ) (hR : Ready F O σ E S R H hs r) :
    Post F O σ E S R H (unhideAll Γ (roots .mut ys) (thaw (hideAll Γ (roots .mut ys)) (roots .ro ys) Γb)) env τ
      hs (eval F O (n + 1) hs σ env (.handle body e caps os rs arm)) := by
  simp only [eval]
  obtain ⟨ls, Rc, Hc, hmap, hlen, hcok, hcin, htr, htr'⟩ := caps_ok hcaps hI.foot
  simp only [hmap]
  obtain ⟨hmn, hrm⟩ := hexcl.roots_ok
  generalize hms : roots .mut ys = ms at hbody hmn hrm htr htr' ⊢
  generalize hrs' : roots .ro ys = ros at hbody hrm ⊢
  have hfc : List.zipWith (fun c l => (⟨c.name, c.mode, c.ty, l⟩ : Cap Nat)) caps ls = List.zipWith Cap.at caps ls := rfl
  rw [hfc]
  -- The variables lent `mut` hidden: their trees the frame's.
  obtain ⟨Eh, hfh, hEh, hreb⟩ := hI.foot.hiddenAll hI.keys htr hmn
  have hkh : ((hideAll Γ ms).map Prod.fst).Nodup := by rw [hideAll_keys]; exact hI.keys
  -- Those lent `readonly` frozen.
  obtain ⟨Eb, Sb, Fz, hfb, hE, hS, hent, hthaw⟩ := hfh.handle hkh (ys := ros) (by
    intro y hy τ' h
    rw [lookup_hideAll (hrm y hy)] at h
    rw [← hrs', mem_roots] at hy
    exact hcaps.roots_live _ hy τ' h)
  have hEall : E.Perm (Hc ++ (Eb ++ Fz)) := hEh.trans (hE.append_left Hc)
  have hEn := hEall.nodup_iff.mp hI.nodup
  obtain ⟨hHcn, hEbFzn, hdHc⟩ := nodup_append_disj.mp hEn
  obtain ⟨hEbn, hFzn, hdEF⟩ := nodup_append_disj.mp hEbFzn
  have hmemE : ∀ l, l ∈ E ↔ l ∈ Hc ∨ l ∈ Eb ∨ l ∈ Fz := fun l => by
    rw [hEall.mem_iff]; simp
  have hEb : ∀ l ∈ Eb, l ∈ E := fun l h => (hmemE l).mpr (.inr (.inl h))
  have hFz : ∀ l ∈ Fz, l ∈ E := fun l h => (hmemE l).mpr (.inr (.inr h))
  have hHcE : ∀ l ∈ Hc, l ∈ E := fun l h => (hmemE l).mpr (.inl h)
  obtain ⟨hh, hHS, hcov⟩ := hR
  -- What the body may change is apart from what it shares, the frozen and the read, from what
  -- the arm was lent `mut`, and from what the handlers may change.
  have hshared : ∀ l, l ∈ Fz ∨ l ∈ S → l ∉ Eb ++ (Hc ++ H) := by
    rintro l (h | h) h'
    · simp only [List.mem_append] at h'
      rcases h' with h' | h' | h'
      · exact hdEF l h' h
      · exact hdHc l h' (List.mem_append.mpr (.inr h))
      · exact hh.disj l h' (hFz l h)
    · simp only [List.mem_append] at h'
      rcases h' with h' | h' | h'
      · exact hI.disj l h (hEb l h')
      · exact hI.disj l h (hHcE l h')
      · exact hHS l h' h
  have hIb : Inv σ (freeze (hideAll Γ ms) ros) env Eb Sb := by
    refine ⟨hfb, hEbn, fun l hl hl' => hshared l ?_ (List.mem_append.mpr (.inl hl')), by
      rw [freeze_keys, hideAll_keys]; exact hI.keys⟩
    exact List.mem_append.mp (hS.mem_iff.mp hl)
  -- The arm's frame: what it was lent `readonly`, apart from what the body may change.
  have hRc : ∀ l ∈ Rc, l ∈ Fz ∨ l ∈ S := by
    intro l hl
    obtain ⟨y, hy, s', a', L', he, hlL⟩ := hcin l hl
    have hyr : y ∈ ros := by rw [← hrs', mem_roots]; exact hy
    exact hent y s' a' L' (he.to_hidden (hrm y hyr)) hyr l hlL
  have hRcE : Disj Rc (Eb ++ (Hc ++ H)) := fun l hl => hshared l (hRc l hl)
  have hnames : (List.zipWith Cap.at caps ls).map Cap.name = caps.map Cap.name := zipWith_at_name hlen
  have hsigs : (List.zipWith Cap.at caps ls).map Cap.sig = caps.map Cap.sig := zipWith_at_sig hlen
  have hRb : Ready F O σ Eb Sb (Rc ++ R) (Hc ++ H) (.resume e (List.zipWith Cap.at caps ls) os rs arm :: hs)
      (.eff e :: r) := by
    refine ⟨⟨.resume hop hcok hos hrs (by rw [hnames]; exact hnd) (by rw [hsigs]; exact harm) hcov hh.ok,
      nodup_append_disj.mpr ⟨hHcn, hh.nodup, fun l hl h => hh.disj l h (hHcE l hl)⟩, ?_, ?_⟩, ?_, ?_⟩
    · intro l hl h
      rcases List.mem_append.mp hl with hl | hl
      · exact hdHc l hl (List.mem_append.mpr (.inl h))
      · exact hh.disj l hl (hEb l h)
    · intro l hl hl'
      rcases List.mem_append.mp hl with h | h
      · exact hRcE l h (by simp only [List.mem_append] at hl' ⊢; grind)
      · have := hh.ro l h
        simp only [List.mem_append] at hl' this
        rcases hl' with h' | h' | h'
        · exact this (.inl (hEb l h'))
        · exact this (.inl (hHcE l h'))
        · exact this (.inr h')
    · intro l hl hl'
      rcases List.mem_append.mp (hS.mem_iff.mp hl') with h | h
      · exact hshared l (.inl h) (by simp [hl])
      · exact hshared l (.inr h) (by simp [hl])
    · intro l hl
      rcases List.mem_cons.mp hl with rfl | hl
      · exact ⟨(.resume e (List.zipWith Cap.at caps ls) os rs arm, hs), by simp [find, Frame.handles]⟩
      · exact covers_cons _ hcov l hl
  have hw := typed_weaker hbody (by rw [freeze_keys]; exact hkh)
  have h1 := ih _ _ _ _ _ _ _ _ _ _ _ _ hbody hIb hwf hRb
  generalize eval F O n _ σ env body = r1 at h1 ⊢
  rcases r1 with ⟨r1, σ1⟩
  -- The body changed nothing it shared; the arm, what it was lent `mut`; given back.
  have thawed : ∀ Eb' H' L, Inv σ1 Γb env Eb' Sb → Moves σ (Eb ++ (Hc ++ H)) σ1 (Eb' ++ H') L →
      Held F O σ1 (.resume e (List.zipWith Cap.at caps ls) os rs arm :: hs) (Rc ++ R) H' Eb' →
      ∃ E' Hr', Inv σ1 (unhideAll Γ ms (thaw (hideAll Γ ms) ros Γb)) env E' S ∧ Moves σ (E ++ H) σ1 (E' ++ Hr') L ∧
        (∀ l, l ∈ E' ++ Hr' ↔ l ∈ Eb' ∨ l ∈ H' ∨ l ∈ Fz) ∧ Held F O σ1 hs R Hr' E' := by
    intro Eb' H' L hI' hm hh'
    have hag : Agree σ σ1 (Fz ++ S) := fun l hl => hm.frame l (hwf l (by
      rcases List.mem_append.mp hl with h | h
      · exact hI.alloc l (hFz l h)
      · exact hI.allocS l h)) (hshared l (List.mem_append.mp hl))
    obtain ⟨E1, hf1, hp1⟩ := hthaw σ1 Γb Eb' hI'.foot hw hag
    obtain ⟨Hc', Hr', rfl, hcok', hok'⟩ := hh'.ok.pop_resume hcok fun l hl => hag l (by
      rcases hRc l hl with h | h <;> simp [h])
    obtain ⟨E', hf', hp'⟩ := hreb σ1 _ E1 Hc' hf1 (thaw_weaker hw) (fun l hl => hag l (by simp [hl]))
      (htr' σ1 Rc Hc' hcok')
    -- What the body left it may change is its own, or new: not frozen.
    have hFzout : ∀ l ∈ Fz, l ∉ Eb' ++ (Hc' ++ Hr') := by
      intro l hl hl'
      rcases hm.within l (.inr hl') with h | h
      · exact hshared l (.inl hl) h
      · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hwf l (hI.alloc l (hFz l hl))) h)
    have hH'n := hh'.nodup
    have hH'n2 := List.nodup_append.mp hH'n
    have hmem' : ∀ l, l ∈ E' ↔ l ∈ Hc' ∨ l ∈ Eb' ∨ l ∈ Fz := fun l => by
      rw [hp'.mem_iff, List.mem_append, hp1.mem_iff, List.mem_append]
    refine ⟨E', Hr', ⟨hf', hp'.nodup_iff.mpr (nodup_append_disj.mpr ⟨hH'n2.1, hp1.nodup_iff.mpr
        (nodup_append_disj.mpr ⟨hI'.nodup, hFzn, fun l h h' => hFzout l h' (by simp [h])⟩), ?_⟩), ?_,
      by rw [unhideAll_keys ((thaw_keys (by rw [typed_keys hbody, freeze_keys])).trans hideAll_keys)]; exact hI.keys⟩, ?_, ?_,
      ⟨hok', hH'n2.2.1, ?_, ?_⟩⟩
    · intro l hl hl'
      rcases List.mem_append.mp (hp1.mem_iff.mp hl') with h | h
      · exact hh'.disj l (by simp [hl]) h
      · exact hFzout l h (by simp [hl])
    · intro l hl hl'
      rcases (hmem' l).mp hl' with h | h | h
      · rcases hm.within l (.inr (by simp [h])) with h' | h'
        · exact hshared l (.inr hl) h'
        · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hwf l (hI.allocS l hl)) h')
      · exact hI'.disj l (hS.mem_iff.mpr (List.mem_append.mpr (.inr hl))) h
      · exact hI.disj l hl (hFz l h)
    · have hm' := hm.widen (X := Fz) (fun l hl => hI.alloc l (hFz l hl)) fun l h h' => hshared l (.inl h) h'
      exact (hm'.congr_left fun x => by
        simp only [List.mem_append, hmemE]; grind).relabel
        fun x => by simp only [List.mem_append, hmem']; grind
    · intro l; simp only [List.mem_append, hmem']; grind
    · intro l hl hl'
      rcases (hmem' l).mp hl' with h | h | h
      · exact hH'n2.2.2 l h l hl rfl
      · exact hh'.disj l (by simp [hl]) h
      · exact hFzout l h (by simp [hl])
    · intro l hl hl'
      have h1 := hh'.ro l (by simp [hl])
      have h2 := hh.ro l hl
      simp only [List.mem_append, hmem'] at hl' h1 h2
      have h3 := fun h => h2 (.inl (hFz l h))
      grind
  cases r1 with
  | val v =>
    obtain ⟨Eb', H', L, hI', hv, hdLE, hdLS, hm, hh'⟩ := h1
    obtain ⟨E', Hr', hI'', hm', hmem, hh''⟩ := thawed Eb' H' L hI' hm hh'
    refine ⟨E', Hr', L, hI'', hv, ?_, fun l hl h => hdLS l hl (hS.mem_iff.mpr (List.mem_append.mpr (.inr h))), hm', hh''⟩
    intro l hl hl'
    rcases (hmem l).mp hl' with h | h | h
    · exact hdLE l hl (by simp [h])
    · exact hdLE l hl (by simp [h])
    · rcases hm.within l (.inl hl) with h' | h'
      · exact hshared l (.inl h) h'
      · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hwf l (hI.alloc l (hFz l h))) h')
  | abort i k =>
    obtain ⟨⟨l, hl⟩, Eb', H', hI', hm, hh'⟩ := h1
    obtain ⟨E', Hr', hI'', hm', -, hh''⟩ := thawed Eb' H' [] hI' hm hh'
    refine ⟨⟨l, ?_⟩, E', Hr', hI'', hm', hh''⟩
    rcases List.mem_cons.mp hl with h | h
    · cases h
    · exact h
  | stuck => simp [Post] at h1
  | timeout => simp [Post]

/-! ## Performing an operation -/

/-- An operation performed: its arguments evaluated and its places lent as a call's are, and then
either the arm of the handler that resumes entered as a function is, or the code unwinding to the
handler that ends its `handle`. -/
theorem perform_ok {hs : HS} {σ : Store} {Γ : Ctx} {env : Env} {E S R H : List Nat} {e : Nat} {op : Op}
    {owned : List Atom} {Γ₁ : Ctx} {lent : List (Mode × Place)} {ys : List (Mode × Var)} {r : Row}
    (ih : ∀ hs σ Γ env E S R H e τ Γ' r, Typed F O Γ e τ Γ' r → Inv σ Γ env E S → WF σ →
      Ready F O σ E S R H hs r → Post F O σ E S R H Γ' env τ hs (eval F O n hs σ env e))
    (hop : O[e]? = some op) (hlab : Label.eff e ∈ r) (hargs : AtomsTy Γ owned op.owns Γ₁)
    (hlends : Lends Γ₁ lent op.refs ys) (hexcl : Exclusive ys)
    (hI : Inv σ Γ env E S) (hwf : WF σ) (hR : Ready F O σ E S R H hs r) :
    Post F O σ E S R H Γ₁ env op.ret hs (eval F O (n + 1) hs σ env (.perform e owned lent)) := by
  simp only [eval, hop]
  obtain ⟨vs, σ1, E₁, Ls, hevs, hI₁, hvs, hLn, hdL0, hdLS, hm0⟩ := atoms_ok hargs hI hwf
  simp only [hevs]
  obtain ⟨hm₁, hh₁, hdH⟩ := hR.1.local hwf hm0
  have hdL : Disj Ls.flatten (E₁ ++ H) := disj_append_right.mpr ⟨hdL0, hdH⟩
  obtain ⟨hos, hts, hys, hmap, hholes⟩ := lends_ok hlends hI₁.foot
  have hpw : hos.Pairwise Apart := by
    rw [← hys, Exclusive, List.pairwise_map] at hexcl; exact hexcl
  simp only [hmap]
  have hR₁ := hR.val hwf hI hm₁ hh₁ hdL (X := E₁ ++ Ls.flatten) fun x hx => List.mem_append.mp hx
  obtain ⟨hh₁', hHS₁, hcov⟩ := hR₁
  obtain ⟨⟨f, rest⟩, hf⟩ := hcov _ hlab
  simp only [hf]
  have hdLE : Disj Ls.flatten E₁ := fun l hl h => hdL l hl (List.mem_append.mpr (.inl h))
  cases f with
  | abort l i =>
    -- Unwinding: the operation's argument is an integer, which owns nothing.
    obtain ⟨op', hop', howns, -⟩ := find_abort_op hh₁.ok hf
    rw [hop] at hop'
    cases hop'
    rw [howns] at hvs
    cases hvs with
    | cons hv hnil =>
      cases hnil
      cases hv with
      | int =>
        exact ⟨⟨l, (find_mem hf).1⟩, E₁, H, hI₁, by simpa using hm₁, hh₁⟩
  | resume e' caps os rs arm =>
    obtain ⟨op', Rc, Hc, Γa, ra, R', Ha, Hr, hop', hcaps, hl1, hl2, hnd, harm, hcov', hRs', hRsub, rfl, hback⟩ :=
      find_resume hh₁.ok hf
    rw [hop] at hop'
    cases hop'
    have hlen : vs.length = os.length ∧ (hos.map Hole.loc).length = rs.length := by
      refine ⟨by rw [hvs.length, hl1], ?_⟩
      have := congrArg List.length hts
      simp only [List.length_map] at this ⊢
      rw [this, hl2]
    simp only [hlen, and_self, ↓reduceIte]
    have hfo : (os.zip op.owns).map Prod.fst = os := List.map_fst_zip (by omega)
    have hso : (os.zip op.owns).map Prod.snd = op.owns := List.map_snd_zip (by omega)
    have hfr : (rs.zip op.refs).map Prod.fst = rs := List.map_fst_zip (by omega)
    have hsr : (rs.zip op.refs).map Prod.snd = op.refs := List.map_snd_zip (by omega)
    have hfc : ((capCtx (caps.map Cap.sig)).map Prod.fst) = caps.map Cap.name := by
      simp [capCtx, Cap.sig, Function.comp_def]
    have hRcR : ∀ l ∈ Rc, l ∈ R := fun l hl => hRsub l (List.mem_append.mpr (.inl hl))
    have key := enter_ok (d := { owns := os.zip op.owns, refs := rs.zip op.refs, ret := op.ret, row := ra, body := arm })
      (Γp := capCtx (caps.map Cap.sig)) (post := caps.map fun c => (c.name, c.loc)) (Hc := Hc) (Rp := Rc)
      (hs := hs) (hs' := rest) (r' := ra) (R' := R') (Ha := Ha) (Hr := Hr)
      (fun σ Γ env E S H τ Γ' => ih rest σ Γ env E S R' H arm τ Γ' ra)
      (by rw [← armCtx_eq]; exact harm)
      (by simp only [hfo, hfr, hfc]; exact hnd)
      capCtx_ref hcaps.foot hRcR
      hR.1 hh₁' hHS₁ hRs' (fun l hl => hRsub l (List.mem_append.mpr (.inr hl))) hcov'
      (fun σ' Hc' Rp' H' hfp hok hag => by
        have hc' := hfp.capsOk
        obtain rfl := hcaps.det_ro hc' fun l hl => hag l (List.mem_append.mpr (.inl (hRcR l hl)))
        exact hback σ' Hc' H' hc' hok hag)
      (fun i ⟨l, h⟩ => ⟨l, (find_mem hf).2 _ h⟩)
      hwf hI₁ (by rw [hso]; exact hvs) hLn hdLE hdLS hm₁ (by rw [hsr]; exact hts) hpw hholes
    simpa only [hfr] using key

/-! ## A borrow held for a while -/

/-- A `readonly` borrow held for the scope of `body`: what the place is rooted at is only read
while it lives, as a `handle`'s body has what its arm was lent. -/
theorem lend_ro_ok {hs : HS} {σ : Store} {Γ : Ctx} {env : Env} {E S R H : List Nat} {x : Var} {p : Place}
    {τ : Ty} {w : Bool} {y : Var} {body : Expr} {τb : Ty} {Γb : Ctx} {r : Row}
    (ih : ∀ hs σ Γ env E S R H e τ Γ' r, Typed F O Γ e τ Γ' r → Inv σ Γ env E S → WF σ →
      Ready F O σ E S R H hs r → Post F O σ E S R H Γ' env τ hs (eval F O n hs σ env e))
    (hx : lookup x Γ = none) (hp : PlaceTy Γ p τ w y)
    (hb : Typed F O ((x, .ref .ro τ) :: lendCtx .ro Γ y) body τb ((x, .ref .ro τ) :: Γb) r)
    (hI : Inv σ Γ env E S) (hwf : WF σ) (hR : Ready F O σ E S R H hs r) :
    Post F O σ E S R H (thaw Γ [y] Γb) env τb hs (eval F O (n + 1) hs σ env (.lend x .ro p body)) := by
  simp only [lendCtx] at hb
  simp only [eval]
  obtain ⟨a, τr, Lr, P, l, s, ha, hLr, hpath, hres, -, -, hsl, hso, -, -⟩ := place_ok hp hI.foot
  obtain ⟨Rt, hRt, hLrPR⟩ := path_split hpath hLr
  simp only [hres]
  have hxk : x ∉ (freeze Γ [y]).map Prod.fst := by rw [freeze_keys]; exact lookup_none_keys hx
  have hwb := typed_weaker hb (List.nodup_cons.mpr ⟨hxk, by rw [freeze_keys]; exact hI.keys⟩)
  cases hwb with
  | cons _ hwb =>
  obtain ⟨Eb, Sb, Fz, hfb, hE, hS, hent, hthaw⟩ := hI.foot.handle (ys := [y]) hI.keys (by
    intro y' hy' τ'; simp only [List.mem_singleton] at hy'; subst hy'; exact hp.root_live τ')
  obtain ⟨hEbn, hFzn, hdEF⟩ := nodup_append_disj.mp (hE.nodup_iff.mp hI.nodup)
  have hEb : ∀ l ∈ Eb, l ∈ E := fun l h => hE.mem_iff.mpr (List.mem_append.mpr (.inl h))
  have hFz : ∀ l ∈ Fz, l ∈ E := fun l h => hE.mem_iff.mpr (List.mem_append.mpr (.inr h))
  have hh := hR.1
  have hshared : ∀ l, l ∈ Fz ∨ l ∈ S → l ∉ Eb ++ H := by
    rintro l (h | h) h'
    · rcases List.mem_append.mp h' with h' | h'
      · exact hdEF l h' h
      · exact hh.disj l h' (hFz l h)
    · rcases List.mem_append.mp h' with h' | h'
      · exact hI.disj l h (hEb l h')
      · exact hR.2.1 l h' h
  -- The borrow's tree is among the root's: frozen, or read already.
  have hRin : ∀ l ∈ Rt, l ∈ Fz ∨ l ∈ S := fun l hl =>
    hent y s a Lr ⟨hsl, ha, hso⟩ (List.mem_singleton_self _) l (hLrPR ▸ List.mem_append.mpr (.inr hl))
  have hIb : Inv σ ((x, .ref .ro τ) :: freeze Γ [y]) ((x, l) :: env) Eb (Rt ++ Sb) := by
    refine ⟨by simpa [addE, addS, Slot.excl] using Foot.cons (s := .ref .ro τ) (x := x) hRt hfb, hEbn, ?_,
      List.nodup_cons.mpr ⟨hxk, by rw [freeze_keys]; exact hI.keys⟩⟩
    intro l hl hl'
    rcases List.mem_append.mp hl with h | h
    · exact hshared l (hRin l h) (List.mem_append.mpr (.inl hl'))
    · exact hshared l (List.mem_append.mp (hS.mem_iff.mp h)) (List.mem_append.mpr (.inl hl'))
  have h1 := ih _ _ _ _ _ _ _ _ _ _ _ _ hb hIb hwf (hR.sub hEb fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · rcases hRin l h with h | h
      · exact .inl (hFz l h)
      · exact .inr h
    · rcases List.mem_append.mp (hS.mem_iff.mp h) with h | h
      · exact .inl (hFz l h)
      · exact .inr h)
  generalize eval F O n hs σ ((x, l) :: env) body = r1 at h1 ⊢
  rcases r1 with ⟨r1, σ1⟩
  have thawed : ∀ Eb' H' L, Inv σ1 ((x, .ref .ro τ) :: Γb) ((x, l) :: env) Eb' (Rt ++ Sb) →
      Moves σ (Eb ++ H) σ1 (Eb' ++ H') L → Held F O σ1 hs R H' Eb' →
      ∃ E', Inv σ1 (thaw Γ [y] Γb) env E' S ∧ Moves σ (E ++ H) σ1 (E' ++ H') L ∧
        (∀ l, l ∈ E' ↔ l ∈ Eb' ∨ l ∈ Fz) ∧ Held F O σ1 hs R H' E' := by
    intro Eb' H' L hI' hm hh'
    have hag : Agree σ σ1 (Fz ++ S) := fun l hl => hm.frame l (hwf l (by
      rcases List.mem_append.mp hl with h | h
      · exact hI.alloc l (hFz l h)
      · exact hI.allocS l h)) (hshared l (List.mem_append.mp hl))
    obtain ⟨L', Et, St, hL', hft, hEt, hSt⟩ := hI'.foot.uncons
    simp only [addE, addS, Slot.excl, Bool.false_eq_true, ↓reduceIte] at hEt hSt
    -- The borrow's tree is as it was: shared, it was not changed.
    have hRR := (hRt.frame fun l hl => hag l (List.mem_append.mpr (hRin l hl))).det hL'
    subst hRR
    obtain rfl := List.append_cancel_left hSt
    subst hEt
    obtain ⟨E', hf', hp⟩ := hthaw σ1 Γb Eb' hft hwb hag
    have hFzEb' : Disj Fz (Eb' ++ H') := by
      intro l hl hl'
      rcases hm.within l (.inr hl') with h | h
      · exact hshared l (.inl hl) h
      · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hwf l (hI.alloc l (hFz l hl))) h)
    have hkb : Γb.map Prod.fst = Γ.map Prod.fst := by
      have := typed_keys hb
      simp only [List.map_cons, List.cons.injEq] at this
      rw [this.2, freeze_keys]
    refine ⟨E', ⟨hf', hp.nodup_iff.mpr (nodup_append_disj.mpr ⟨hI'.nodup, hFzn,
        fun l h h' => hFzEb' l h' (List.mem_append.mpr (.inl h))⟩),
      ?_, by rw [thaw_keys hkb]; exact hI.keys⟩, ?_, fun l => by rw [hp.mem_iff, List.mem_append], ⟨hh'.ok,
      hh'.nodup, ?_, ?_⟩⟩
    · intro l hl hl'
      rcases List.mem_append.mp (hp.mem_iff.mp hl') with h | h
      · exact hI'.disj l (List.mem_append.mpr (.inr (hS.mem_iff.mpr (List.mem_append.mpr (.inr hl))))) h
      · exact hI.disj l hl (hFz l h)
    · have hm' := (hm.widen (X := Fz) (fun l hl => hI.alloc l (hFz l hl)) fun l h h' => hshared l (.inl h) h')
      exact (hm'.congr_left fun x => by simp only [List.mem_append, hE.mem_iff]; grind).relabel
        fun x => by simp only [List.mem_append, hp.mem_iff]; grind
    · intro l hl hl'
      rcases List.mem_append.mp (hp.mem_iff.mp hl') with h | h
      · exact hh'.disj l hl h
      · exact hFzEb' l h (List.mem_append.mpr (.inr hl))
    · intro l hl hl'
      rcases List.mem_append.mp hl' with h | h
      · rcases List.mem_append.mp (hp.mem_iff.mp h) with h | h
        · exact hh'.ro l hl (List.mem_append.mpr (.inl h))
        · exact hh.ro l hl (List.mem_append.mpr (.inl (hFz l h)))
      · exact hh'.ro l hl (List.mem_append.mpr (.inr h))
  cases r1 with
  | val v =>
    obtain ⟨Eb', H', L, hI', hv, hdLE, hdLS, hm, hh'⟩ := h1
    obtain ⟨E', hI'', hm', hmem, hh''⟩ := thawed Eb' H' L hI' hm hh'
    refine ⟨E', H', L, hI'', hv, ?_, fun l hl h => hdLS l hl (List.mem_append.mpr (.inr (hS.mem_iff.mpr (List.mem_append.mpr (.inr h))))), hm', hh''⟩
    intro l hl hl'
    rcases List.mem_append.mp hl' with hl' | hl'
    · rcases (hmem l).mp hl' with h | h
      · exact hdLE l hl (List.mem_append.mpr (.inl h))
      · rcases hm.within l (.inl hl) with h' | h'
        · exact hshared l (.inl h) h'
        · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hwf l (hI.alloc l (hFz l h))) h')
    · exact hdLE l hl (List.mem_append.mpr (.inr hl'))
  | abort i k =>
    obtain ⟨haim, Eb', H', hI', hm, hh'⟩ := h1
    obtain ⟨E', hI'', hm', -, hh''⟩ := thawed Eb' H' [] hI' hm hh'
    exact ⟨haim, E', H', hI'', hm', hh''⟩
  | stuck => simp [Post] at h1
  | timeout => simp [Post]

/-- A `mut` borrow held for the scope of `body`: the borrow owns the place's tree while it lives,
and what the place is rooted at is out of reach; once it ends, the root owns again its path to the
place and what the borrow left there. -/
theorem lend_mut_ok {hs : HS} {σ : Store} {Γ : Ctx} {env : Env} {E S R H : List Nat} {x : Var} {p : Place}
    {τ : Ty} {y : Var} {body : Expr} {τb : Ty} {Γb : Ctx} {r : Row}
    (ih : ∀ hs σ Γ env E S R H e τ Γ' r, Typed F O Γ e τ Γ' r → Inv σ Γ env E S → WF σ →
      Ready F O σ E S R H hs r → Post F O σ E S R H Γ' env τ hs (eval F O n hs σ env e))
    (hx : lookup x Γ = none) (hp : PlaceTy Γ p τ true y)
    (hb : Typed F O ((x, .ref .mut τ) :: lendCtx .mut Γ y) body τb ((x, .ref .mut τ) :: Γb) r)
    (hI : Inv σ Γ env E S) (hwf : WF σ) (hR : Ready F O σ E S R H hs r) :
    Post F O σ E S R H (thaw Γ [y] Γb) env τb hs (eval F O (n + 1) hs σ env (.lend x .mut p body)) := by
  simp only [lendCtx] at hb
  simp only [eval]
  obtain ⟨a, τr, Lr, P, l, s, ha, hLr, hpath, hres, -, hsubE, hsl, hso, hexw, hslot⟩ := place_ok hp hI.foot
  obtain ⟨Rt, hRt, hLrPR⟩ := path_split hpath hLr
  subst hLrPR
  simp only [hres]
  have hsx : s.excl = true := hexw rfl
  have hLrE : ∀ l ∈ P ++ Rt, l ∈ E := hsubE rfl
  have hxk : x ∉ (hide Γ y).map Prod.fst := by rw [hide_keys]; exact lookup_none_keys hx
  have hwb := typed_weaker hb (List.nodup_cons.mpr ⟨hxk, by rw [hide_keys]; exact hI.keys⟩)
  cases hwb with
  | cons _ hwb =>
  obtain ⟨Eh, hfh, hEh, hrebuild⟩ := hI.foot.hidden hI.keys ⟨hsl, ha, hso⟩ hsx
  obtain ⟨hLrn, hEhn, hdLrEh⟩ := nodup_append_disj.mp (hEh.nodup_iff.mp hI.nodup)
  obtain ⟨hPn, hRn, hdPR⟩ := nodup_append_disj.mp hLrn
  have hEhE : ∀ l ∈ Eh, l ∈ E := fun l h => hEh.mem_iff.mpr (List.mem_append.mpr (.inr h))
  have hPE : ∀ l ∈ P, l ∈ E := fun l h => hLrE l (List.mem_append.mpr (.inl h))
  have hRE : ∀ l ∈ Rt, l ∈ E := fun l h => hLrE l (List.mem_append.mpr (.inr h))
  have hPa : ∀ l ∈ P, σ.mem l ≠ none := fun l h => hLr.alloc l (List.mem_append.mpr (.inl h))
  have hh := hR.1
  -- The borrow's activation: it owns the place's tree; the root is out of reach.
  have hIb : Inv σ ((x, .ref .mut τ) :: hide Γ y) ((x, l) :: env) (Rt ++ Eh) S := by
    refine ⟨by simpa [addE, addS, Slot.excl] using Foot.cons (s := .ref .mut τ) (x := x) hRt hfh, ?_, ?_,
      List.nodup_cons.mpr ⟨hxk, by rw [hide_keys]; exact hI.keys⟩⟩
    · exact nodup_append_disj.mpr ⟨hRn, hEhn, fun l h h' => hdLrEh l (List.mem_append.mpr (.inr h)) h'⟩
    · intro l hl hl'
      rcases List.mem_append.mp hl' with h | h
      · exact hI.disj l hl (hRE l h)
      · exact hI.disj l hl (hEhE l h)
  have h1 := ih _ _ _ _ _ _ _ _ _ _ _ _ hb hIb hwf (hR.sub (fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · exact hRE l h
    · exact hEhE l h) fun l hl => .inr hl)
  generalize eval F O n hs σ ((x, l) :: env) body = r1 at h1 ⊢
  rcases r1 with ⟨r1, σ1⟩
  -- The path to the place is none of the borrow's activation's, nor the handlers'.
  have hPout : ∀ l ∈ P, l ∉ Rt ++ Eh ++ H := fun l hl h => by
    simp only [List.mem_append] at h
    rcases h with (h | h) | h
    · exact hdPR l hl h
    · exact hdLrEh l (List.mem_append.mpr (.inl hl)) h
    · exact hh.disj l h (hPE l hl)
  have hkb : Γb.map Prod.fst = Γ.map Prod.fst := by
    have := typed_keys hb
    simp only [List.map_cons, List.cons.injEq] at this
    rw [this.2, hide_keys]
  have rebuilt : ∀ Eb' H' L, Inv σ1 ((x, .ref .mut τ) :: Γb) ((x, l) :: env) Eb' S →
      Moves σ (Rt ++ Eh ++ H) σ1 (Eb' ++ H') L → Held F O σ1 hs R H' Eb' →
      ∃ E', Inv σ1 (thaw Γ [y] Γb) env E' S ∧ Moves σ (E ++ H) σ1 (E' ++ H') L ∧
        (∀ z, z ∈ E' ↔ z ∈ Eb' ∨ z ∈ P) ∧ Held F O σ1 hs R H' E' := by
    intro Eb' H' L hI' hm hh'
    obtain ⟨R', Et, St, hR', hft, hEt, hSt⟩ := hI'.foot.uncons
    simp only [addE, addS, Slot.excl, ↓reduceIte] at hEt hSt
    subst hEt
    rw [← hSt] at hft
    have hagP : Agree σ σ1 P := fun l hl => hm.frame l (hwf l (hPa l hl)) (hPout l hl)
    have hagS : Agree σ σ1 S := fun l hl => hm.frame l (hwf l (hI.allocS l hl)) (fun h => by
      simp only [List.mem_append] at h
      rcases h with (h | h) | h
      · exact hI.disj l hl (hRE l h)
      · exact hI.disj l hl (hEhE l h)
      · exact hR.2.1 l h hl)
    -- What the body left it may change is its own, or new: not on the path.
    have hPnew : ∀ z ∈ P, z ∉ R' ++ Et ++ H' := fun z hz h => by
      rcases hm.within z (.inr h) with h | h
      · exact hPout z hz h
      · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hwf z (hPa z hz)) h)
    obtain ⟨hLT', -⟩ := path_join hpath hLr hagP hR' (fun z hz h => hPnew z hz (by simp [h]))
    obtain ⟨E', hf', hp'⟩ := hrebuild σ1 Γb Et (P ++ R') hft hwb hagS (hslot σ1 _ hLT')
    refine ⟨E', ⟨hf', hp'.nodup_iff.mpr ?_, ?_, by rw [thaw_keys hkb]; exact hI.keys⟩, ?_, ?_,
      ⟨hh'.ok, hh'.nodup, ?_, ?_⟩⟩
    · rw [List.append_assoc]
      exact nodup_append_disj.mpr ⟨hPn, hI'.nodup, fun z hz h => hPnew z hz (List.mem_append.mpr (.inl h))⟩
    · intro z hz hz'
      rcases List.mem_append.mp (hp'.mem_iff.mp hz') with h | h
      · rcases List.mem_append.mp h with h | h
        · exact hI.disj z hz (hPE z h)
        · exact hI'.disj z hz (List.mem_append.mpr (.inl h))
      · exact hI'.disj z hz (List.mem_append.mpr (.inr h))
    · have hm' := hm.widen (X := P) hPa fun z hz h => hPout z hz h
      exact (hm'.congr_left fun z => by
          simp only [List.mem_append, hEh.mem_iff]; grind).relabel
        fun z => by simp only [List.mem_append, hp'.mem_iff]; grind
    · intro z
      rw [hp'.mem_iff]
      mem_iff
    · intro z hz hz'
      rcases List.mem_append.mp (hp'.mem_iff.mp hz') with h | h
      · rcases List.mem_append.mp h with h | h
        · exact hPnew z h (List.mem_append.mpr (.inr hz))
        · exact hh'.disj z hz (List.mem_append.mpr (.inl h))
      · exact hh'.disj z hz (List.mem_append.mpr (.inr h))
    · intro z hz hz'
      rcases List.mem_append.mp hz' with h | h
      · rcases List.mem_append.mp (hp'.mem_iff.mp h) with h | h
        · rcases List.mem_append.mp h with h | h
          · exact hh.ro z hz (List.mem_append.mpr (.inl (hPE z h)))
          · exact hh'.ro z hz (List.mem_append.mpr (.inl (List.mem_append.mpr (.inl h))))
        · exact hh'.ro z hz (List.mem_append.mpr (.inl (List.mem_append.mpr (.inr h))))
      · exact hh'.ro z hz (List.mem_append.mpr (.inr h))
  cases r1 with
  | val v =>
    obtain ⟨Eb', H', L, hI', hv, hdLE, hdLS, hm, hh'⟩ := h1
    obtain ⟨E', hI'', hm', hmem, hh''⟩ := rebuilt Eb' H' L hI' hm hh'
    refine ⟨E', H', L, hI'', hv, ?_, hdLS, hm', hh''⟩
    intro z hz hz'
    rcases List.mem_append.mp hz' with hz' | hz'
    · rcases (hmem z).mp hz' with h | h
      · exact hdLE z hz (List.mem_append.mpr (.inl h))
      · rcases hm.within z (.inl hz) with h' | h'
        · exact hPout z h h'
        · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hwf z (hPa z h)) h')
    · exact hdLE z hz (List.mem_append.mpr (.inr hz'))
  | abort i k =>
    obtain ⟨haim, Eb', H', hI', hm, hh'⟩ := h1
    obtain ⟨E', hI'', hm', -, hh''⟩ := rebuilt Eb' H' [] hI' hm hh'
    exact ⟨haim, E', H', hI'', hm', hh''⟩
  | stuck => simp [Post] at h1
  | timeout => simp [Post]

theorem lend_ok {hs : HS} {σ : Store} {Γ : Ctx} {env : Env} {E S R H : List Nat} {x : Var} {m : Mode}
    {p : Place} {τ : Ty} {w : Bool} {y : Var} {body : Expr} {τb : Ty} {Γb : Ctx} {r : Row}
    (ih : ∀ hs σ Γ env E S R H e τ Γ' r, Typed F O Γ e τ Γ' r → Inv σ Γ env E S → WF σ →
      Ready F O σ E S R H hs r → Post F O σ E S R H Γ' env τ hs (eval F O n hs σ env e))
    (hx : lookup x Γ = none) (hp : PlaceTy Γ p τ w y) (hm : m = .mut → w = true)
    (hb : Typed F O ((x, .ref m τ) :: lendCtx m Γ y) body τb ((x, .ref m τ) :: Γb) r)
    (hI : Inv σ Γ env E S) (hwf : WF σ) (hR : Ready F O σ E S R H hs r) :
    Post F O σ E S R H (thaw Γ [y] Γb) env τb hs (eval F O (n + 1) hs σ env (.lend x m p body)) := by
  cases m with
  | ro => exact lend_ro_ok ih hx hp hb hI hwf hR
  | «mut» => obtain rfl := hm rfl; exact lend_mut_ok ih hx hp hb hI hwf hR

/-! ## Soundness -/

theorem eval_ok (F : List Fn) (O : List Op) (hF : FnsOk F O) : ∀ n hs σ Γ env E S R H e τ Γ' r,
    Typed F O Γ e τ Γ' r → Inv σ Γ env E S → WF σ → Ready F O σ E S R H hs r →
    Post F O σ E S R H Γ' env τ hs (eval F O n hs σ env e) := by
  intro n
  induction n with
  | zero => intros; simp [eval, Post]
  | succ n ih =>
    intro hs σ Γ env E S R H e τ Γ' r ht hI hwf hR
    cases ht with
    | atom ha =>
      obtain ⟨v, σ1, E₁, L₁, hev, hI₁, hv₁, hd₁, hdS₁, hm₁⟩ := atom_ok ha hI hwf
      simp only [eval, hev]
      exact post_step hR.1 hwf hI₁ hv₁ hd₁ hdS₁ hm₁
    | add ha hb =>
      obtain ⟨v, σ1, E₁, L₁, hev, hI₁, hv₁, -, -, hm₁⟩ := atom_ok ha hI hwf
      cases hv₁ with
      | int =>
      obtain ⟨w, σ2, E₂, L₂, hev2, hI₂, hv₂, -, -, hm₂⟩ := atom_ok hb hI₁ hm₁.wf
      cases hv₂ with
      | int =>
      simp only [eval, hev, hev2]
      exact post_step hR.1 hwf hI₂ .int disj_nil_left disj_nil_left
        ((hm₁.trans hm₂ disj_nil_left hwf).relabel (by simp))
    | new ha =>
      obtain ⟨v, σ1, E₁, L₁, hev, hI₁, hv₁, hd₁, hdS₁, hm₁⟩ := atom_ok ha hI hwf
      simp only [eval, hev]
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
      refine post_step hR.1 hwf ⟨hI₁.foot.frame fun l hl => hag l ?_, hI₁.nodup, hI₁.disj, hI₁.keys⟩
        (.box (LT.of_contents (by simp [Store.alloc]) (hv₁.frame fun l hl => hag l ?_) ?_)) ?_ ?_
        ((hm₁.trans (Moves.allocate hm₁.wf hI₁.alloc) hd₁ hwf).relabel fun x => by
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
            show (σ1.alloc v).1 = σ1.next from rfl]; grind)
      · rcases List.mem_append.mp hl with hl | hl
        · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr hl)))
        · exact List.mem_append.mpr (.inr hl)
      · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inl hl)))
      · exact fun h => hfresh _ (List.mem_append.mpr (.inl (List.mem_append.mpr (.inl h)))) rfl
      · exact disj_cons_left.mpr ⟨fun h => hfresh _ (List.mem_append.mpr (.inl (List.mem_append.mpr (.inr h)))) rfl, hd₁⟩
      · exact disj_cons_left.mpr ⟨fun h => hfresh _ (List.mem_append.mpr (.inr h)) rfl, hdS₁⟩
    | write ha hp =>
      obtain ⟨v, σ1, E₁, L₁, hev, hI₁, hv₁, -, -, hm₁⟩ := atom_ok ha hI hwf
      cases hv₁ with
      | @int k =>
      obtain ⟨l, Rb, P, A, B, hres, hRb, hE, hupd⟩ := replace_at hI₁ hp
      cases hRb with
      | int hl =>
        simp only [eval, hev, hres, hl]
        have hnd := seg_nodup (hE ▸ hI₁.nodup)
        have hlE : l ∈ E₁ := hE ▸ mem_seg.mpr (.inl (by simp))
        have hlP : l ∉ P := by
          have := hnd.1; rw [nodup_append_disj] at this; exact fun h => this.2.2 l h (by simp)
        have hlAB : l ∉ A ++ B := hnd.2.1 l (by simp)
        have hlS : l ∉ S := fun h => hI₁.disj l h hlE
        have hout : l ∉ A ++ P ++ B ++ S := by
          simp only [List.mem_append, not_or] at hlAB ⊢
          exact ⟨⟨⟨hlAB.1, hlP⟩, hlAB.2⟩, hlS⟩
        refine post_step hR.1 hwf ?_ .int disj_nil_left disj_nil_left
          ((hm₁.trans (Moves.set hm₁.wf hI₁.alloc hlE) disj_nil_left hwf).relabel (E'' := E₁) (L'' := [])
            (by simp))
        have := hupd (σ1.set l (some (.int k))) [l] (agree_set hout) (.int (n := k) (by simp [Store.set])) (by
          intro x hx; simp at hx; subst hx
          simp only [List.mem_append, not_or] at hout ⊢; exact hout.1) (by
          intro x hx; simp at hx; subst hx; exact hlS)
        rwa [← hE] at this
    | assign ha hp =>
      obtain ⟨v, σ1, E₁, L₁, hev, hI₁, hv₁, hd₁, hdS₁, hm₁⟩ := atom_ok ha hI hwf
      obtain ⟨l, Rb, P, A, B, hres, hRb, hE, hupd⟩ := replace_at hI₁ hp
      obtain ⟨w, R', hw, hvw, rfl, hlR'⟩ := hRb.contents
      obtain ⟨σ2, hdrop, hnext, hfree, hkeep⟩ := drop_ok _ σ1 w R' hvw
      simp only [eval, hev, hres, hw, hdrop]
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
      refine post_step hR.1 hwf (hupd σ3 _ hag hLt ?_ ?_) .int disj_nil_left disj_nil_left ?_
      · exact disj_cons_left.mpr ⟨hlAPB, fun x hx hx' => hd₁ x hx (hAPB x hx')⟩
      · exact disj_cons_left.mpr ⟨hlS, hdS₁⟩
      · have := (hm₁.relabel (E'' := E₁ ++ L₁) (L'' := []) fun x => by mem_iff).trans
          ((hm₂.trans hm₃ disj_nil_left hm₁.wf).relabel (E'' := A ++ (P ++ (l :: L₁)) ++ B) (L'' := [])
            fun x => by mem_iff) disj_nil_left hwf
        simpa using this
    | let_ hx ha hb =>
      rename_i x a τx Γ₁ b live
      simp only [eval]
      have hk₁ : (Γ₁.map Prod.fst).Nodup := by rw [typed_keys ha]; exact hI.keys
      have hx₁ : x ∉ Γ₁.map Prod.fst := by rw [typed_keys ha]; exact lookup_none_keys hx
      have h1 := ih _ _ _ _ _ _ _ _ _ _ _ _ ha hI hwf hR
      generalize eval F O n hs σ env _ = r1 at h1 ⊢
      rcases r1 with ⟨r1, σ1⟩
      cases r1 with
      | val v =>
        dsimp only
        obtain ⟨E₁, H₁, L₁, hI₁, hv₁, hd₁, hdS₁, hm₁, hh₁⟩ := h1
        obtain ⟨hIb, hma⟩ := bind_ok hI₁ hv₁ (fun l hl h => hd₁ l hl (List.mem_append.mpr (.inl h))) hdS₁ hm₁
          hh₁.allocH hwf hx₁
        have hRb := (hR.val hwf hI hm₁ hh₁ hd₁ (X := L₁ ++ E₁) fun x hx => by
          rcases List.mem_append.mp hx with h | h
          · exact .inr h
          · exact .inl h).alloc (v := v) hm₁.wf
        have h2 := ih _ _ _ _ _ _ _ _ _ _ _ _ hb hIb hma.wf hRb
        rw [show (σ1.alloc v).1 = σ1.next from rfl]
        exact leave_ok hma hwf h2
      | abort i k =>
        have w := typed_weaker hb (List.nodup_cons.mpr ⟨hx₁, hk₁⟩)
        cases w with
        | cons _ w => exact post_out h1 (by simp) w
      | stuck => simp [Post] at h1
      | timeout => simp [Post]
    | call hfd hrow hargs hlends hexcl =>
      rename_i f d owned lent ys
      obtain ⟨vs, σ1, E₁, Ls, hevs, hI₁, hvs, hLn, hdL0, hdLS, hm0⟩ := atoms_ok hargs hI hwf
      simp only [eval, hfd, hevs]
      obtain ⟨hm₁, hh₁, hdH⟩ := hR.1.local hwf hm0
      have hdL : Disj Ls.flatten (E₁ ++ H) := disj_append_right.mpr ⟨hdL0, hdH⟩
      obtain ⟨hos, hts, hys, hmap, hholes⟩ := lends_ok hlends hI₁.foot
      have hpw : hos.Pairwise Apart := by
        rw [← hys, Exclusive, List.pairwise_map] at hexcl; exact hexcl
      obtain ⟨hkeys, Γ'', hbody⟩ := hF d (List.mem_of_getElem? hfd)
      have hlen : vs.length = d.owns.length ∧ (hos.map Hole.loc).length = d.refs.length := by
        refine ⟨by rw [hvs.length]; simp, ?_⟩
        have := congrArg List.length hts
        simp only [List.length_map] at this ⊢
        exact this
      simp only [hmap, hlen, and_self, ↓reduceIte]
      have hR₁ := (hR.val hwf hI hm₁ hh₁ hdL (X := E₁ ++ Ls.flatten) fun x hx => List.mem_append.mp hx).row hrow
      exact enter_ok (Γp := []) (post := []) (Hc := []) (Rp := []) (R' := R) (Ha := []) (Hr := H)
        (fun σ Γ env E S H τ Γ' => ih hs σ Γ env E S R H d.body τ Γ' d.row)
        (by simpa using hbody) (by simpa using hkeys) (by intro p hp; simp at hp) .nil (by simp)
        hR.1 (by simpa using hR₁.1) (by simpa using hR₁.2.1) hR₁.1.ok (fun _ h => h) hR₁.2.2
        (fun σ' Hc' Rp' H' hfp hok _ => by cases hfp; simpa using hok) (fun _ h => h)
        hwf hI₁ hvs hLn hdL0 hdLS (by simpa using hm₁) hts hpw hholes
    | ite hc ha hb wa wb =>
      have hk₀ := hI.keys
      rw [← atom_keys hc] at hk₀
      obtain ⟨v, σ1, E₁, L₁, hev, hI₁, hv₁, -, -, hm0⟩ := atom_ok hc hI hwf
      cases hv₁ with
      | @int k =>
      simp only [eval, hev]
      obtain ⟨hm₁, hh₁, -⟩ := hR.1.local hwf hm0
      have hR₁ := hR.val hwf hI hm₁ hh₁ disj_nil_left fun x hx => .inl hx
      split
      · exact post_after hm₁ hwf (post_weaken (ih _ _ _ _ _ _ _ _ _ _ _ _ hb hI₁ hm₁.wf hR₁) wb)
      · exact post_after hm₁ hwf (post_weaken (ih _ _ _ _ _ _ _ _ _ _ _ _ ha hI₁ hm₁.wf hR₁) wa)
    | throw_ ha hlab =>
      obtain ⟨v, σ1, E₁, L₁, hev, hI₁, hv₁, -, -, hm0⟩ := atom_ok ha hI hwf
      cases hv₁ with
      | int =>
      simp only [eval, hev]
      obtain ⟨hm₁, hh₁, -⟩ := hR.1.local hwf hm0
      obtain ⟨-, -, hcov⟩ := hR
      obtain ⟨⟨f, rest⟩, hf⟩ := hcov _ hlab
      have hh := find_handles hf
      cases f with
      | resume => simp [Frame.handles] at hh
      | abort l i =>
        simp only [hf]
        exact ⟨⟨l, (find_mem hf).1⟩, E₁, H, hI₁, hm₁, hh₁⟩
    | try_ hx hb hh =>
      simp only [eval]
      have hkb := hI.keys
      rw [← typed_keys hb] at hkb
      have hxb := lookup_none_keys hx
      have w := typed_weaker hh (List.nodup_cons.mpr ⟨hxb, hkb⟩)
      cases w with
      | cons _ w =>
      have h1 := ih _ _ _ _ _ _ _ _ _ _ _ _ hb hI hwf (hR.push_abort (by intro e h; cases h))
      generalize eval F O n (.abort .fail hs.length :: hs) σ env _ = r1 at h1 ⊢
      rcases r1 with ⟨r1, σ1⟩
      cases r1 with
      | val v => simp only [catchAt]; exact post_weaken (post_pop h1 (by simp)) w
      | abort i k =>
        simp only [catchAt]
        split
        · obtain ⟨-, E₁, H₁, hI₁, hm₁, hh₁⟩ := h1
          obtain ⟨hIb, hma⟩ := bind_ok (v := .int k) hI₁ .int disj_nil_left disj_nil_left hm₁ hh₁.allocH hwf hxb
          have hRb := (hR.post hwf hI.disj hI.allocS hm₁ hh₁.pop_abort disj_nil_left (X := E₁)
            fun x hx => .inl hx).alloc (v := .int k) hm₁.wf
          have h2 := ih _ _ _ _ _ _ _ _ _ _ _ _ hh hIb hma.wf hRb
          rw [show (σ1.alloc (.int k)).1 = σ1.next from rfl]
          exact leave_ok hma hwf h2
        · obtain ⟨haim, E₁, H₁, hI₁, hm₁, hh₁⟩ := h1
          exact ⟨aimed_pop haim ‹_›, E₁, H₁, hI₁.weaken w, hm₁, hh₁.pop_abort⟩
      | stuck => simp [Post] at h1
      | timeout => simp [catchAt, Post]
    | while_ hc hb =>
      simp only [eval]
      have h1 := ih _ _ _ _ _ _ _ _ _ _ _ _ hc hI hwf hR
      generalize eval F O n hs σ env _ = r1 at h1 ⊢
      rcases r1 with ⟨r1, σ1⟩
      cases r1 with
      | val v =>
        obtain ⟨E₁, H₁, L₁, hI₁, hv₁, hd₁, -, hm₁, hh₁⟩ := h1
        cases hv₁ with
        | @int k =>
          dsimp only
          split
          · exact ⟨E₁, H₁, [], hI₁, .int, disj_nil_left, disj_nil_left, hm₁, hh₁⟩
          · have h2 := ih _ _ _ _ _ _ _ _ _ _ _ _ hb hI₁ hm₁.wf (hR.val hwf hI hm₁ hh₁ hd₁ fun x hx => .inl hx)
            generalize eval F O n hs σ1 env _ = r2 at h2 ⊢
            rcases r2 with ⟨r2, σ2⟩
            cases r2 with
            | val w =>
              obtain ⟨E₂, H₂, L₂, hI₂, hv₂, -, -, hm₂, hh₂⟩ := h2
              cases hv₂ with
              | int =>
                dsimp only
                have hm₁₂ := (hm₁.trans hm₂ disj_nil_left hwf).relabel (E'' := E₂ ++ H₂) (L'' := []) (by simp)
                exact post_after hm₁₂ hwf
                  (ih _ _ _ _ _ _ _ _ _ _ _ _ (.while_ hc hb) hI₂ hm₂.wf
                    (hR.val hwf hI hm₁₂ hh₂ disj_nil_left fun x hx => .inl hx))
            | abort i k => exact post_after hm₁ hwf h2
            | stuck => simp [Post] at h2
            | timeout => simp [Post]
      | abort i k => exact post_out h1 (by simp) (Weaker.refl _)
      | stuck => simp [Post] at h1
      | timeout => simp [Post]
    | defer hb hd =>
      simp only [eval]
      have h1 := ih _ _ _ _ _ _ _ _ _ _ _ _ hb hI hwf hR
      generalize eval F O n hs σ env _ = r1 at h1 ⊢
      rcases r1 with ⟨r1, σ1⟩
      cases r1 with
      | val v =>
        obtain ⟨E₁, H₁, L₁, hI₁, hv₁, hd₁, hdS₁, hm₁, hh₁⟩ := h1
        dsimp only
        have hRL₁ := (hR.1.apart hwf hm₁).2
        have h2 := ih _ _ _ _ _ _ _ _ _ _ _ _ hd hI₁ hm₁.wf (hR.val hwf hI hm₁ hh₁ hd₁ fun x hx => .inl hx)
        generalize eval F O n hs σ1 env _ = r2 at h2 ⊢
        rcases r2 with ⟨r2, σ2⟩
        cases r2 with
        | val w =>
          obtain ⟨E₂, H₂, L₂, hI₂, hv₂, -, -, hm₂, hh₂⟩ := h2
          cases hv₂ with
          | int =>
            dsimp only
            -- The body's value owns cells the cleanup cannot reach: none of the activation's.
            obtain ⟨hdE, -⟩ := hm₂.apart hm₁.wf hv₁.alloc hd₁
            exact ⟨E₂, H₂, L₁, hI₂, hv₁.frame (hm₂.keeps hm₁.wf hv₁.alloc hd₁), hdE, hdS₁,
              (hm₁.trans hm₂ hd₁ hwf).relabel fun x => by simp, hh₂⟩
        | abort i k =>
          -- The cleanup unwinds: the body's value is dropped on the way out.
          dsimp only
          obtain ⟨haim, E₂, H₂, hI₂, hm₂, hh₂⟩ := h2
          have hv₂ := hv₁.frame (hm₂.keeps hm₁.wf hv₁.alloc hd₁)
          obtain ⟨hdE, -⟩ := hm₂.apart hm₁.wf hv₁.alloc hd₁
          obtain ⟨σ3, hdrop, hn, hfree, hkeep⟩ := drop_ok _ σ2 v L₁ hv₂
          simp only [hdrop]
          refine ⟨haim, E₂, H₂, ⟨hI₂.foot.frame fun l hl => hkeep l fun h => ?_, hI₂.nodup, hI₂.disj, hI₂.keys⟩, ?_,
            hh₂.frame fun l hl => hkeep l fun h => ?_⟩
          · rcases List.mem_append.mp hl with hl | hl
            · exact hdE l h (List.mem_append.mpr (.inl hl))
            · exact hdS₁ l h hl
          · refine ((hm₁.trans hm₂ hd₁ hwf).relabel (E'' := E₂ ++ H₂ ++ L₁) (L'' := []) fun x => by mem_iff).trans
              (Moves.free (E := E₂ ++ H₂ ++ L₁) (E' := E₂ ++ H₂) (D := L₁) (WF.of_free hm₂.wf hn hfree hkeep) hn
                (fun l hl => by
                  rcases List.mem_append.mp hl with hl | hl
                  · rcases List.mem_append.mp hl with hl | hl
                    · exact hI₂.alloc l hl
                    · exact hh₂.allocH l hl
                  · exact hv₂.alloc l hl)
                (fun x => by simp [or_assoc]) hfree hkeep hdE.symm) disj_nil_left hwf |>.relabel fun x => by simp
          · rcases List.mem_append.mp hl with hl | hl
            · exact hRL₁ l hl h
            · exact hdE l h (List.mem_append.mpr (.inr hl))
        | stuck => simp [Post] at h2
        | timeout => simp [Post]
      | abort i k =>
        dsimp only
        obtain ⟨haim, E₁, H₁, hI₁, hm₁, hh₁⟩ := h1
        have h2 := ih _ _ _ _ _ _ _ _ _ _ _ _ hd hI₁ hm₁.wf
          (hR.post hwf hI.disj hI.allocS hm₁ hh₁ disj_nil_left (X := E₁) fun x hx => .inl hx)
        generalize eval F O n hs σ1 env _ = r2 at h2 ⊢
        rcases r2 with ⟨r2, σ2⟩
        cases r2 with
        | val w =>
          obtain ⟨E₂, H₂, L₂, hI₂, hv₂, -, -, hm₂, hh₂⟩ := h2
          cases hv₂ with
          | int => exact ⟨haim, E₂, H₂, hI₂, (hm₁.trans hm₂ disj_nil_left hwf).relabel fun x => by simp, hh₂⟩
        | abort i' k' => exact post_after hm₁ hwf (post_out h2 (by simp) (Weaker.refl _))
        | stuck => simp [Post] at h2
        | timeout => simp [Post]
      | stuck => simp [Post] at h1
      | timeout => simp [Post]
    | lend hx hp hm hb => exact lend_ok ih hx hp hm hb hI hwf hR
    | perform hop hlab hargs hlends hexcl => exact perform_ok ih hop hlab hargs hlends hexcl hI hwf hR
    | handle hop hos hrs hcaps hexcl hnd harm hbody =>
      exact handle_ok ih hop hos hrs hcaps hexcl hnd harm hbody hI hwf hR
    | handleAbort hop howns hrefs hx hb hh =>
      simp only [eval]
      have hkb := hI.keys
      rw [← typed_keys hb] at hkb
      have hxb := lookup_none_keys hx
      have w := typed_weaker hh (List.nodup_cons.mpr ⟨hxb, hkb⟩)
      cases w with
      | cons _ w =>
      have h1 := ih _ _ _ _ _ _ _ _ _ _ _ _ hb hI hwf (hR.push_abort (by
        intro e' h; cases h; exact ⟨_, hop, howns, hrefs⟩))
      generalize eval F O n (.abort (.eff _) hs.length :: hs) σ env _ = r1 at h1 ⊢
      rcases r1 with ⟨r1, σ1⟩
      cases r1 with
      | val v => simp only [catchAt]; exact post_weaken (post_pop h1 (by simp)) w
      | abort i k =>
        simp only [catchAt]
        split
        · obtain ⟨-, E₁, H₁, hI₁, hm₁, hh₁⟩ := h1
          obtain ⟨hIb, hma⟩ := bind_ok (v := .int k) hI₁ .int disj_nil_left disj_nil_left hm₁ hh₁.allocH hwf hxb
          have hRb := (hR.post hwf hI.disj hI.allocS hm₁ hh₁.pop_abort disj_nil_left (X := E₁)
            fun x hx => .inl hx).alloc (v := .int k) hm₁.wf
          have h2 := ih _ _ _ _ _ _ _ _ _ _ _ _ hh hIb hma.wf hRb
          rw [show (σ1.alloc (.int k)).1 = σ1.next from rfl]
          exact leave_ok hma hwf h2
        · obtain ⟨haim, E₁, H₁, hI₁, hm₁, hh₁⟩ := h1
          exact ⟨aimed_pop haim ‹_›, E₁, H₁, hI₁.weaken w, hm₁, hh₁.pop_abort⟩
      | stuck => simp [Post] at h1
      | timeout => simp [catchAt, Post]

/-- The store a program starts in: nothing allocated. -/
def Store.empty : Store := { mem := fun _ => none, next := 0 }

/-- A well-typed program, run where a failure it lets out ends it, as `main`'s does, never gets
stuck — no use of a moved value, no use after free, no double free, no operation nothing handles —
and when it ends, the only cells left allocated are those its result owns, and none if it failed:
every other value was dropped exactly once, on the way out of a failure too. -/
theorem program_ok (hF : FnsOk F O) (ht : Typed F O [] e τ Γ' [.fail]) (n : Nat) :
    match eval F O n [.abort .fail 0] .empty [] e with
    | (.stuck, _) => False
    | (.timeout, _) => True
    | (.val v, σ') => ∃ L, VT σ' τ v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none := by
  have hR : Ready F O .empty [] [] [] [] [.abort .fail 0] [.fail] :=
    (show Ready F O .empty [] [] [] [] [] [] from
      ⟨⟨.nil, List.nodup_nil, disj_nil_left, disj_nil_left⟩, disj_nil_left, fun _ h => by simp at h⟩).push_abort
      (by intro e h; cases h)
  have h := eval_ok F O hF n [.abort .fail 0] .empty [] [] [] [] [] [] e τ Γ' [.fail] ht
    ⟨.nil, List.nodup_nil, disj_nil_left, List.nodup_nil⟩ (fun _ h => absurd rfl h) hR
  -- The handlers of a whole program hold nothing.
  have hnil : ∀ {σ H}, Held F O σ [.abort .fail 0] [] H [] → H = [] := by
    intro σ H hh
    obtain ⟨hok, -⟩ := hh
    cases hok with
    | abort _ _ hr => cases hr; rfl
  generalize eval F O n [.abort .fail 0] .empty [] e = r at h ⊢
  rcases r with ⟨r, σ'⟩
  have hΓ : Γ' = [] := List.eq_nil_of_map_eq_nil (typed_keys ht)
  subst hΓ
  cases r with
  | stuck => exact h
  | timeout => trivial
  | val v =>
    obtain ⟨E', H', L, hI, hv, -, -, hm, hh⟩ := h
    cases hI.foot
    obtain rfl := hnil hh
    exact ⟨L, hv, fun l => by rw [hm.alloc]; simp [Store.empty]⟩
  | abort i k =>
    obtain ⟨-, E', H', hI, hm, hh⟩ := h
    cases hI.foot
    obtain rfl := hnil hh
    intro l
    have := hm.alloc l
    simp [Store.empty] at this
    exact this

end FlyCore.Ownership
