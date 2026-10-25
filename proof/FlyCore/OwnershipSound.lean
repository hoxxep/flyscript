import FlyCore.OwnershipFlush

/-!
# Ownership: soundness

`eval_ok`: a well-typed expression, evaluated in a store that keeps its activation's invariant,
never gets stuck. It gives a value of its type owning cells of no variable's, the invariant still
holds, and the step is accounted for (`Moves`); or it unwinds to a handler in force; or it performs an
operation whose handler takes the code that performed it as typed frames. `ret_ok` is what each frame
does with what the code it ran gives, and `evalK_ok` what a continuation does when it is resumed or
dropped. `program_ok` is the consequence for a whole program: never stuck, and when it ends nothing
is allocated but the cells of its result.
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
theorem atom_ok (h : AtomTy Γ a τ Γ') (hI : Inv F ι σ Γ env E S) (hwf : WF σ) :
    ∃ v σ' E' L, evalAtom σ env a = some (v, σ') ∧ Inv F ι σ' Γ' env E' S ∧ VT F ι σ' τ v L ∧ Disj L E' ∧
      Disj L S ∧ Moves σ E σ' E' L := by
  cases h with
  | lit => exact ⟨_, σ, E, [], rfl, hI, .int, disj_nil_left, disj_nil_left, Moves.refl hwf hI.alloc⟩
  | read hp =>
    obtain ⟨a, τr, Lr, P, l, s, ha, hLr, hpath, hres, -⟩ := place_ok hp hI.foot
    obtain ⟨Rb, hRb, -⟩ := path_split hpath hLr
    cases hRb with
    | @int _ k hl =>
      exact ⟨.int k, σ, E, [], by simp [evalAtom, hres, hl], hI, .int, disj_nil_left, disj_nil_left,
        Moves.refl hwf hI.alloc⟩
  | readRef hp =>
    obtain ⟨a, τr, Lr, P, l, s, ha, hLr, hpath, hres, -⟩ := place_ok hp hI.foot
    obtain ⟨Rb, hRb, -⟩ := path_split hpath hLr
    cases hRb with
    | @rref _ r _ _ _ hl hr =>
      exact ⟨.rptr r, σ, E, [], by simp [evalAtom, hres, hl], hI, .rref hr, disj_nil_left, disj_nil_left,
        Moves.refl hwf hI.alloc⟩
  | @move x τ hx hc =>
    obtain ⟨a, L, E₁, E₂, ha, hL, hE, hupd⟩ := foot_update hI.foot hI.keys hx rfl rfl
    simp only [SlotOk] at hL
    obtain ⟨w, Rb, hw, hv, rfl, hn⟩ := hL.contents hc
    have hwm : w ≠ .moved := fun h => by subst h; cases hv
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
    have hev : evalAtom σ env (.move x) = some (w, σ.set a (some .moved)) := by
      cases w with
      | moved => exact absurd rfl hwm
      | _ => simp [evalAtom, ha, hw]
    refine ⟨_, _, E₁ ++ [a] ++ E₂, Rb, hev,
      ⟨hupd _ (.own _ false) [a] (by rfl) rfl hag (by simp [SlotOk, Store.set]), ?_, ?_, ?_⟩,
      hv.frame (agree_set hn), ?_, ?_, ?_⟩
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

/-- A closure moved out of its variable: what it captured is the mover's, the variable left moved. -/
theorem move_clo (hx : lookup x Γ = some (.own (.fn k A B r Rf) true)) (hI : Inv F ι σ Γ env E S) (hwf : WF σ) :
    ∃ cx f c τc Rc E', lookup x env = some cx ∧ σ.mem cx = some (.clo f c τc) ∧ CloOk F f τc k A B r Rf ∧
      LT F ι σ c τc Rc ∧ cx ∉ Rc ∧ Inv F ι (σ.set cx (some .moved)) (setSlot Γ x (.own (.fn k A B r Rf) false)) env E' S ∧
      Disj Rc E' ∧ Disj Rc S ∧ Moves σ E (σ.set cx (some .moved)) E' Rc := by
  obtain ⟨a, L, E₁, E₂, ha, hL, hE, hupd⟩ := foot_update hI.foot hI.keys hx rfl rfl
  simp only [SlotOk] at hL
  cases hL with
  | @clo _ f c τc _ _ _ _ _ Rb hla hco hRb hn =>
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
    refine ⟨a, f, c, τc, Rb, E₁ ++ [a] ++ E₂, ha, hla, hco, hRb, hn,
      ⟨hupd _ (.own _ false) [a] (by rfl) rfl hag (by simp [SlotOk, Store.set]), ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
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
theorem atoms_ok : AtomsTy Γ as τs Γ' → Inv F ι σ Γ env E S → WF σ →
    ∃ vs σ' E' Ls, evalAtoms σ env as = some (vs, σ') ∧ Inv F ι σ' Γ' env E' S ∧ Vals F ι σ' τs vs Ls ∧
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
theorem bind_ok (hI₁ : Inv F ι σ1 Γ₁ env E₁ S) (hv₁ : VT F ι σ1 τx v L₁) (hd₁ : Disj L₁ E₁) (hdS₁ : Disj L₁ S)
    (hm₁ : Moves σ E σ1 E₁ L₁) (hwf : WF σ) (hx : x ∉ Γ₁.map Prod.fst) :
    Inv F ι (σ1.alloc v).2 ((x, .own τx true) :: Γ₁) ((x, σ1.next) :: env) (σ1.next :: L₁ ++ E₁) S ∧
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
  have hLt : LT F ι (σ1.alloc v).2 σ1.next τx (σ1.next :: L₁) :=
    LT.of_contents (by simp [Store.alloc]) (hv₁.frame (hag.mono fun l hl => by simp [hl])) hcL
  refine ⟨⟨.cons (s := .own τx true) hLt (hI₁.foot.frame (hag.mono fun l hl => by
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

/-- Dropping the variable a scope declared, live or perhaps moved, as the scope is left, and then
the continuations it held: its footprint is freed, and the rest stands. -/
theorem drop_var (hfl : FlushOk F ι fl) (hτx : τx.complete = true)
    (hI₃ : Inv F ι σ3 ((x, .own τx live) :: Γ₂) ((x, c) :: env) E₃ S)
    (hL₃ : ∀ l ∈ L₃, σ3.mem l ≠ none) (hd₃ : Disj L₃ E₃) (hm : Moves σ E σ3 E₃ L₃) (hwf : WF σ) :
    ∃ σ4, dropCell σ3 τx c = some σ4 ∧ ∃ Lx, FlushGives (fl (cellKonts σ3 τx c) σ4) σ3 Lx ∧
      ∀ σ5, Dropped σ3 Lx σ5 → ∃ E₂, Inv F ι σ5 Γ₂ env E₂ S ∧ Agree σ3 σ5 L₃ ∧ Disj L₃ E₂ ∧
        Moves σ E σ5 E₂ L₃ := by
  obtain ⟨Lx, E₂, S₂, hs, hfoot, hE₃, hS₃⟩ := hI₃.foot.uncons
  simp only [addE, addS, Slot.excl, ↓reduceIte, exclPart, sharedPart, Slot.shell, Ty.shell, Bool.false_eq_true, ↓reduceIte, List.nil_append] at hE₃ hS₃
  subst hE₃ hS₃
  obtain ⟨σ4, hdrop, hfg⟩ := dropCellF hfl hm.wf hτx hs
  refine ⟨σ4, hdrop, Lx, hfg, fun σ5 hd5 => ?_⟩
  have hnd := nodup_append_disj.mp hI₃.nodup
  have hag5 : Agree σ3 σ5 (E₂ ++ S) := hd5.keeps hm.wf (fun l hl => by
      rcases List.mem_append.mp hl with hl | hl
      · exact hI₃.alloc l (List.mem_append.mpr (.inr hl))
      · exact hI₃.allocS l hl)
    (fun l hl hlx => by
      rcases List.mem_append.mp hl with hl | hl
      · exact hnd.2.2 l hlx hl
      · exact hI₃.disj l hl (List.mem_append.mpr (.inl hlx)))
  have hX : ∀ l ∈ E₂ ++ L₃, σ3.mem l ≠ none := fun l hl => by
    rcases List.mem_append.mp hl with hl | hl
    · exact hI₃.alloc l (List.mem_append.mpr (.inr hl))
    · exact hL₃ l hl
  have hm₄ : Moves σ3 (Lx ++ E₂ ++ L₃) σ5 (E₂ ++ L₃) [] :=
    ((hd5.widen hX (fun l hl hlx => by
      rcases List.mem_append.mp hl with hl | hl
      · exact hnd.2.2 l hlx hl
      · exact hd₃ l hl (List.mem_append.mpr (.inl hlx)))).congr_left fun x => by mem_iff).relabel
      fun x => by mem_iff
  refine ⟨E₂, ⟨hfoot.frame hag5, hnd.2.1, fun l hl hl' => hI₃.disj l hl
      (List.mem_append.mpr (.inr hl')), (List.nodup_cons.mp hI₃.keys).2⟩,
    hd5.keeps hm.wf hL₃ fun l hl h => hd₃ l hl (List.mem_append.mpr (.inl h)),
    fun l hl hl' => hd₃ l hl (List.mem_append.mpr (.inr hl')), ?_⟩
  exact ((hm.relabel (E'' := Lx ++ E₂ ++ L₃) (L'' := []) fun x => by mem_iff).trans hm₄ disj_nil_left
    hwf).relabel fun x => by mem_iff


/-! ## What a step gives -/

theorem post_now (hI : Inv F ι σ Γ env E S) (hwf : WF σ) (hv : VT F ι σ τ v []) :
    Post F ι O σ E S Γ env τ r hs (.val v, σ) :=
  ⟨E, [], hI, hv, disj_nil_left, disj_nil_left, Moves.refl hwf hI.alloc⟩

/-- An unwinding carried on unchanged out of a sub-expression, said of any context weaker than the one
the sub-expression would have left. -/
theorem post_out (h : Post F ι O σ E S Γ₁ env τ₁ r₁ hs (.abort j k, σ')) (w : Weaker Γ' Γ₁) :
    Post F ι O σ E S Γ' env τ r hs (.abort j k, σ') := by
  obtain ⟨haim, E', hI, hm⟩ := h
  exact ⟨haim, E', hI.weaken w, hm⟩

/-- After a step that gave nothing of its own, what the next one gives is what the two give. -/
theorem post_after {r : Res × Store} (hm : Moves σ E σ1 E₁ []) (hwf : WF σ)
    (h : Post F ι O σ1 E₁ S Γ' env τ rw hs r) : Post F ι O σ E S Γ' env τ rw hs r := by
  rcases r with ⟨r, σ'⟩
  cases r with
  | val v =>
    obtain ⟨E', L, hI, hv, hd, hdS, hm'⟩ := h
    exact ⟨E', L, hI, hv, hd, hdS, (hm.trans hm' disj_nil_left hwf).relabel fun x => by simp⟩
  | abort id k =>
    obtain ⟨haim, E', hI, hm'⟩ := h
    exact ⟨haim, E', hI, (hm.trans hm' disj_nil_left hwf).relabel fun x => by simp⟩
  | susp id ef vs ls K =>
    obtain ⟨op, X, hos, A, Lv, hc, hop, hcov, haim, hK, hls, hvs, hn, hd, hdS, hm'⟩ := h
    exact ⟨op, X, hos, A, Lv, hc, hop, hcov, haim, hK, hls, hvs, hn, hd, hdS,
      (hm.trans hm' disj_nil_left hwf).relabel fun x => by simp⟩
  | stuck => exact h
  | timeout => trivial
  | ended => trivial

/-- What an expression may give, said of a context it leaves, holds of one that is weaker. -/
theorem post_weaken {r : Res × Store} (h : Post F ι O σ E S Γ₁ env τ rw hs r) (w : Weaker Γ' Γ₁) :
    Post F ι O σ E S Γ' env τ rw hs r := by
  rcases r with ⟨r, σ'⟩
  cases r with
  | val v => obtain ⟨E', L, hI, hv, hd, hdS, hm⟩ := h; exact ⟨E', L, hI.weaken w, hv, hd, hdS, hm⟩
  | abort id k => obtain ⟨haim, E', hI, hm⟩ := h; exact ⟨haim, E', hI.weaken w, hm⟩
  | susp id ef vs ls K =>
    obtain ⟨op, X, hos, A, Lv, hc, hop, hcov, haim, hK, hls, hvs, hn, hd, hdS, hm⟩ := h
    exact ⟨op, X, hos, A, Lv, hc, hop, hcov, haim, hK.weaken w, hls, hvs, hn, hd, hdS, hm⟩
  | stuck => exact h
  | timeout => trivial
  | ended => trivial

/-- A frame of no cells of its own joins a continuation taken through its construct. -/
theorem post_frame (h : Post F ι O σ E S Γ₁ env₁ τ₁ r hs (.susp j ef vs ls K, σ'))
    (hf : FrameOk F O ι ι σ' f ⟨Γ₁, env₁, τ₁, S, r⟩ ⟨Γ', env, τ, S, r⟩ [] []) :
    Post F ι O σ E S Γ' env τ r hs (.susp j ef vs ls (f :: K), σ') := by
  obtain ⟨op, X, hos, A, Lv, hc, hop, hcov, haim, hK, hls, hvs, hn, hd, hdS, hm⟩ := h
  have hK' := FramesOk.cons (σf := σ') (A := A) hf (Weaker.refl _) Agree.self
    (fun _ h => by simp at h) List.nodup_nil disj_nil_left hK (fun _ h => by simp at h) (fun a ha => .inl ha)
  simp only [List.nil_append] at hK'
  exact ⟨op, X, hos, A, Lv, hc, hop, hcov, haim, hK', hls, hvs, hn, hd, hdS, hm⟩

/-- Leaving a scope, with a value or a failure, drops its variable; a continuation taken in it keeps
it. -/
theorem leave_ok {r : Res × Store} (hfl : FlushOk F ι fl) (hτx : τx.complete = true) (hm : Moves σ E σb Eb []) (hwf : WF σ) (hx : x ∉ Γ₂.map Prod.fst)
    (hk : (Γ₂.map Prod.fst).Nodup)
    (h : Post F ι O σb Eb S ((x, .own τx live) :: Γ₂) ((x, c) :: env) τ rw hs r) :
    Post F ι O σ E S Γ₂ env τ rw hs (leave fl τx c r) := by
  rcases r with ⟨r, σ3⟩
  cases r with
  | val w =>
    obtain ⟨E₃, L₃, hI₃, hv₃, hd₃, hdS₃, hm₃⟩ := h
    obtain ⟨σ4, hdrop, Lx, hfg, hk5⟩ := drop_var hfl hτx hI₃ hv₃.alloc hd₃
      ((hm.trans hm₃ disj_nil_left hwf).relabel fun x => by simp) hwf
    simp only [leave, Res.done, ↓reduceIte, hdrop]
    refine hfg.post fun σ5 hd5 => ?_
    obtain ⟨E₂, hI₄, hag, hd, hm₄⟩ := hk5 σ5 hd5
    exact ⟨E₂, L₃, hI₄, hv₃.frame hag, hd, hdS₃, hm₄⟩
  | abort id k =>
    obtain ⟨haim, E₃, hI₃, hm₃⟩ := h
    obtain ⟨σ4, hdrop, Lx, hfg, hk5⟩ := drop_var (L₃ := []) hfl hτx hI₃ (by simp) disj_nil_left
      ((hm.trans hm₃ disj_nil_left hwf).relabel fun x => by simp) hwf
    simp only [leave, Res.done, ↓reduceIte, hdrop]
    refine hfg.post fun σ5 hd5 => ?_
    obtain ⟨E₂, hI₄, -, -, hm₄⟩ := hk5 σ5 hd5
    exact ⟨haim, E₂, hI₄, hm₄⟩
  | susp id ef vs ls K =>
    simp only [leave]
    exact post_after hm hwf (post_frame h (.scopeK hx hk hτx))
  | stuck => exact h
  | timeout => simp [leave, Res.done, Post]
  | ended => simp [leave, Res.done, Post]

/-- Leaving a scope, said of where its code started. -/
theorem leave_ok' {r : Res × Store} (hfl : FlushOk F ι fl) (hτx : τx.complete = true) (hwf : WF σ) (hx : x ∉ Γ₂.map Prod.fst) (hk : (Γ₂.map Prod.fst).Nodup)
    (h : Post F ι O σ E S ((x, .own τx live) :: Γ₂) ((x, c) :: env) τ rw hs r) :
    Post F ι O σ E S Γ₂ env τ rw hs (leave fl τx c r) := by
  rcases r with ⟨r, σ3⟩
  cases r with
  | val w =>
    obtain ⟨E₃, L₃, hI₃, hv₃, hd₃, hdS₃, hm₃⟩ := h
    obtain ⟨σ4, hdrop, Lx, hfg, hk5⟩ := drop_var hfl hτx hI₃ hv₃.alloc hd₃ hm₃ hwf
    simp only [leave, Res.done, ↓reduceIte, hdrop]
    refine hfg.post fun σ5 hd5 => ?_
    obtain ⟨E₂, hI₄, hag, hd, hm₄⟩ := hk5 σ5 hd5
    exact ⟨E₂, L₃, hI₄, hv₃.frame hag, hd, hdS₃, hm₄⟩
  | abort id k =>
    obtain ⟨haim, E₃, hI₃, hm₃⟩ := h
    obtain ⟨σ4, hdrop, Lx, hfg, hk5⟩ := drop_var (L₃ := []) hfl hτx hI₃ (by simp) disj_nil_left hm₃ hwf
    simp only [leave, Res.done, ↓reduceIte, hdrop]
    refine hfg.post fun σ5 hd5 => ?_
    obtain ⟨E₂, hI₄, -, -, hm₄⟩ := hk5 σ5 hd5
    exact ⟨haim, E₂, hI₄, hm₄⟩
  | susp id ef vs ls K =>
    simp only [leave]
    exact post_frame h (.scopeK hx hk hτx)
  | stuck => exact h
  | timeout => simp [leave, Res.done, Post]
  | ended => simp [leave, Res.done, Post]

/-! ## The statements, by fuel -/

/-- Expressions: what evaluating one gives. -/
def EvalOk (F : List Fn) (O : List Op) (n : Nat) : Prop :=
  ∀ hs σ ι Γ env E S e τ Γ' r, [WorldOk F O ι.w] → Typed F O Γ e τ Γ' r → Inv F ι σ Γ env E S → WF σ → Ready O hs r →
    Post F ι O σ E S Γ' env τ r hs (eval F O n hs σ env e)

/-- Frames: what one does with what the code it ran gives, its own cells as they were. -/
def RetOk (F : List Fn) (O : List Op) (n : Nat) : Prop :=
  ∀ hs ιi ιo σf f inL outL Xf A σ0 Ein r, [WorldOk F O ιo.w] →
    FrameOk F O ιi ιo σf f inL outL Xf A → Ready O hs outL.r → (∀ a ∈ A, AimedIn a hs) → WF σ0 →
    Agree σf σ0 (Xf ++ outL.S) → (∀ l ∈ Xf, σf.mem l ≠ none) → Xf.Nodup → Disj Xf Ein →
    (∀ l ∈ outL.S, σ0.mem l ≠ none) → Disj outL.S (Xf ++ Ein) →
    Post F ιi O σ0 Ein inL.S inL.Γ inL.env inL.τ inL.r (f.push hs) r →
    Post F ιo O σ0 (Xf ++ Ein) outL.S outL.Γ outL.env outL.τ outL.r hs (ret F O n hs f r)

/-- Continuations: what one does, resumed with a value of the operation's type, or dropped by
unwinding it to a handler in force, its own cells as they were and the places it lent given back with
trees of their types. -/
def EvalKOk (F : List Fn) (O : List Op) (n : Nat) : Prop :=
  ∀ hs ι σs K top X hos A σr (ps : List (Hole × List Nat)) r0 op0 Lv, [WorldOk F O ι.w] →
    FramesOk F O ι σs K op0 top X hos A → Ready O hs top.r → (∀ a ∈ A, AimedIn a hs) → WF σr →
    Agree σs σr (X ++ top.S) → (∀ l ∈ X ++ top.S, σs.mem l ≠ none) → X.Nodup →
    ps.map Prod.fst = hos → (∀ p ∈ ps, p.1.mode = .mut → LT F ι σr p.1.loc p.1.ty p.2) →
    (mutCells ps).Nodup → Disj X (mutCells ps) → Disj top.S (X ++ mutCells ps ++ Lv) →
    ((∃ v, r0 = .val v ∧ VT F ι σr op0.ret v Lv ∧ Disj Lv (X ++ mutCells ps)) ∨
      (∃ a k, r0 = .abort a k ∧ AimedIn a hs ∧ Lv = [])) →
    Post F ι O σr (X ++ mutCells ps ++ Lv) top.S top.Γ top.env top.τ top.r hs (evalK F O n hs σr K r0)

/-- A fiber whose continuation is kept, taken through an operation of the code around: what it does
when the code around answers it, or drops it, as `EvalKOk` says. -/
def NestOk (F : List Fn) (O : List Op) (n : Nat) : Prop :=
  ∀ hs ι σs τf e g fa ff K Xr ls top X hos A σr (ps : List (Hole × List Nat)) r0 op0 Lv, [WorldOk F O ι.w] →
    FramesOk F O ι σs [.enterK τf e g fa ff K Xr ls] op0 top X hos A → Ready O hs top.r →
    (∀ a ∈ A, AimedIn a hs) → WF σr →
    Agree σs σr (X ++ top.S) → (∀ l ∈ X ++ top.S, σs.mem l ≠ none) → X.Nodup →
    ps.map Prod.fst = hos → (∀ p ∈ ps, p.1.mode = .mut → LT F ι σr p.1.loc p.1.ty p.2) →
    (mutCells ps).Nodup → Disj X (mutCells ps) → Disj top.S (X ++ mutCells ps ++ Lv) →
    ((∃ v, r0 = .val v ∧ VT F ι σr op0.ret v Lv ∧ Disj Lv (X ++ mutCells ps)) ∨
      (∃ a k, r0 = .abort a k ∧ AimedIn a hs ∧ Lv = [])) →
    Post F ι O σr (X ++ mutCells ps ++ Lv) top.S top.Γ top.env top.τ top.r hs
      (evalK F O n hs σr [.enterK τf e g fa ff K Xr ls] r0)

/-! ## Frames, generally -/

theorem covers_cons (f : Frame) : Covers hs r → Covers (f :: hs) r := by
  intro h l hl
  obtain ⟨p, hp⟩ := h l hl
  by_cases hf : f.handles l = true
  · exact ⟨f, by simp [find, hf]⟩
  · exact ⟨p, by simp [find, hf, hp]⟩

theorem find_head : ∃ f, find l (Frame.abort l i :: hs) = some f :=
  ⟨Frame.abort l i, by simp [find, Frame.handles]⟩

theorem AimedIn.push (h : AimedIn a hs) : AimedIn a (Kont.push f hs) := by
  rcases h with h | ⟨l, hl⟩
  · exact .inl h
  refine .inr ⟨l, ?_⟩
  cases f
  all_goals try first | exact hl | exact List.mem_cons_of_mem _ hl | exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hl)
  case catchK l' _ _ _ _ => cases l' <;> simp [Kont.push, hl]

/-- A scope's frames put in force the handlers of its two operations. -/
theorem sc_ready (hop : O[e]? = some op) (hopS : O[eS]? = some opS) (hok : HSOk O hs) (hcov : Covers hs r) :
    Ready O (.capture e hid :: .capture eS hid :: hs) (.eff e :: .eff eS :: r) := by
  refine ⟨.capture ⟨_, hop⟩ (.capture ⟨_, hopS⟩ hok), fun l hl => ?_⟩
  rcases List.mem_cons.mp hl with rfl | hl
  · exact ⟨_, by simp only [find, Frame.handles, beq_self_eq_true, ↓reduceIte]; rfl⟩
  rcases List.mem_cons.mp hl with rfl | hl
  · by_cases h : e = eS
    · subst h; exact ⟨_, by simp only [find, Frame.handles, beq_self_eq_true, ↓reduceIte]; rfl⟩
    · exact ⟨.capture eS hid, by simp [find, Frame.handles, h]⟩
  · exact covers_cons _ (covers_cons _ hcov) l hl

theorem catch_hsok (hl : ∀ e, l = .eff e → ∃ op, O[e]? = some op ∧ op.owns = [.int] ∧ op.refs = [])
    (h : HSOk O hs) : HSOk O ((Kont.catchK l c x env b).push hs) := by
  cases l with
  | eff e =>
    obtain ⟨op, hop, -⟩ := hl e rfl
    exact .capture ⟨op, hop⟩ (.abort hl h)
  | fail => exact .abort (fun _ h => by cases h) h
  | drop => exact .abort (fun _ h => by cases h) h

theorem catch_covers (h : Covers hs r) : Covers ((Kont.catchK l c x env b).push hs) (l :: r) := by
  intro l' hl'
  cases l with
  | eff e =>
    rcases List.mem_cons.mp hl' with rfl | hl'
    · exact ⟨.capture e c, by simp [Kont.push, find, Frame.handles]⟩
    · exact covers_cons _ (covers_cons _ h) l' hl'
  | fail =>
    rcases List.mem_cons.mp hl' with rfl | hl'
    · exact find_head
    · exact covers_cons _ h l' hl'
  | drop =>
    rcases List.mem_cons.mp hl' with rfl | hl'
    · exact find_head
    · exact covers_cons _ h l' hl'

/-- What a frame puts in force is well formed, and handles what the code it runs may perform. -/
theorem FrameOk.ready (hf : FrameOk F O ιi ιo σf f inL outL Xf A) (hR : Ready O hs outL.r) :
    Ready O (f.push hs) inL.r := by
  obtain ⟨hok, hcov⟩ := hR
  cases hf with
  | callK hrow | callLendK hrow | taskK hrow =>
    exact ⟨hok, fun l hl => hcov l (hrow l hl)⟩
  | parS hP | parD hP =>
    refine ⟨.capture ⟨_, hP.hop⟩ hok, fun l hl => ?_⟩
    rcases List.mem_cons.mp hl with rfl | hl
    · exact ⟨_, by simp only [Kont.push, find, Frame.handles, beq_self_eq_true, ↓reduceIte]; rfl⟩
    · exact covers_cons _ hcov l hl
  | parY hop =>
    refine ⟨.capture ⟨_, hop⟩ hok, fun l hl => ?_⟩
    rcases List.mem_cons.mp hl with rfl | hl
    · exact ⟨_, by simp only [Kont.push, find, Frame.handles, beq_self_eq_true, ↓reduceIte]; rfl⟩
    · exact covers_cons _ hcov l hl
  | capD hop _ _ hrin =>
    refine ⟨.cancel hok, fun l hl => ?_⟩
    rcases hrin l hl with ⟨e', rfl⟩ | hl
    · exact ⟨_, by simp [Kont.push, find, Frame.handles]; rfl⟩
    · exact covers_cons _ hcov l hl
  | catchK _ _ _ hl => exact ⟨catch_hsok hl hok, catch_covers hcov⟩
  | dropK | dropKv _ =>
    exact ⟨.abort (by intro e h; cases h) hok, fun l hl => covers_cons _ hcov l hl⟩
  | capK hH =>
    refine ⟨.capture ⟨_, hH.hop⟩ hok, fun l hl => ?_⟩
    rcases List.mem_cons.mp hl with rfl | hl
    · exact ⟨_, by simp only [Kont.push, find, Frame.handles, beq_self_eq_true, ↓reduceIte]; rfl⟩
    · exact covers_cons _ hcov l hl
  | genC hG | genCd hG =>
    refine ⟨.capture ⟨_, hG.hopN⟩ hok, fun l hl => ?_⟩
    rcases List.mem_cons.mp hl with rfl | hl
    · exact ⟨_, by simp only [Kont.push, find, Frame.handles, beq_self_eq_true, ↓reduceIte]; rfl⟩
    · exact covers_cons _ hcov l hl
  | genP hG =>
    refine ⟨.capture ⟨_, hG.hopY⟩ hok, fun l hl => ?_⟩
    rcases List.mem_cons.mp hl with rfl | hl
    · exact ⟨_, by simp only [Kont.push, find, Frame.handles, beq_self_eq_true, ↓reduceIte]; rfl⟩
    · exact covers_cons _ hcov l hl
  | genY hop | genN hop =>
    refine ⟨.capture ⟨_, hop⟩ hok, fun l hl => ?_⟩
    rcases List.mem_cons.mp hl with rfl | hl
    · exact ⟨_, by simp only [Kont.push, find, Frame.handles, beq_self_eq_true, ↓reduceIte]; rfl⟩
    · exact covers_cons _ hcov l hl
  | genE | scEb | scEt =>
    exact ⟨.abort (by intro e h; cases h) hok, fun l hl => covers_cons _ hcov l hl⟩
  | scB hS | scW hS | scV hS => exact sc_ready hS.hop hS.hopS hok hcov
  | scX hop _ _ _ hopS => exact sc_ready hop hopS hok hcov
  | _ => exact ⟨hok, hcov⟩

/-- What a frame's code only reads is its own, or what its construct only reads. -/
theorem FrameOk.S_sub (hf : FrameOk F O ιi ιo σf f inL outL Xf A) : ∀ l ∈ inL.S, l ∈ Xf ∨ l ∈ outL.S := by
  cases hf with
  | callK _ hI hholes hpw | callLendK _ hI hholes hpw =>
    intro l hl
    obtain ⟨h, hh, hlo⟩ := mem_olds_ro.mp hl
    rcases (hole_in hI (hholes h hh)).1 l (List.mem_append.mpr (.inr (sharedPart_sub hlo))) with h' | h'
    · exact .inl (mem_keep.mpr ⟨h', shared_not_mut hI hholes hpw hh hlo⟩)
    · exact .inr h'
  | lendK hSin => exact hSin
  | cloK hSin => exact hSin
  | capK hH =>
    intro l hl
    rcases hH.hSin l hl with h | h
    · exact .inl (List.mem_append.mpr (.inl h))
    · exact .inr h
  | armK hH _ _ hro =>
    intro l hl
    rcases List.mem_append.mp hl with h | h
    · rcases hro l h with h | h
      · exact .inl (List.mem_append.mpr (.inl h))
      · rcases hH.hSin l h with h | h
        · exact .inl (List.mem_append.mpr (.inr h))
        · exact .inr h
    · rcases hH.hRc l h with h | h
      · exact .inl (List.mem_append.mpr (.inr h))
      · exact .inr h
  | parS _ _ _ hSr | parD _ _ hSr =>
    intro l hl
    rcases hSr l hl with h | h
    · exact .inl (List.mem_append.mpr (.inl h))
    · exact .inr h
  | parE _ _ hSo =>
    intro l hl
    rcases hSo l hl with h | h
    · exact .inl h
    · exact .inr h
  | genC hG =>
    intro l hl
    rcases hG.hSin l hl with h | h
    · exact .inl (List.mem_append.mpr (.inl h))
    · exact .inr h
  | genCd hG =>
    intro l hl
    rcases hG.hSin l hl with h | h
    · exact .inl (List.mem_append.mpr (.inl h))
    · exact .inr h
  | genP _ hSo =>
    intro l hl
    rcases hSo l hl with h | h
    · exact .inl (List.mem_append.mpr (.inl h))
    · exact .inr h
  | genE _ _ _ hSo =>
    intro l hl
    rcases hSo l hl with h | h
    · exact .inl (by simp [h])
    · exact .inr h
  | scW _ _ _ _ _ _ _ _ _ hSt _ | scV _ _ _ _ _ _ _ _ hSt _ | scEt _ _ _ _ hSt _ => intro l hl; exact .inr (hSt l hl)
  | _ => intro l hl; exact .inr hl

/-- The code that performed the operation a continuation was taken at: its activation, the places
it lent, and how its cells and what it read are among the continuation's. -/
theorem FramesOk.base_of : ∀ {ι : Iota} {K : List Kont} {top : Lvl} {X : List Nat} {A : List Nat},
    FramesOk F O ι σs K op top X hos A →
    ∃ ι₁ Γ₁ env₁ E₁ S₁, Inv F ι₁ σs Γ₁ env₁ E₁ S₁ ∧ (∀ h ∈ hos, HoleOk F ι₁ σs Γ₁ env₁ h) ∧ hos.Pairwise Apart ∧
      hos.map (fun h => (h.mode, h.ty)) = op.refs ∧ (∀ l ∈ E₁, l ∉ mutCells (olds hos) → l ∈ X) ∧
      (∀ l ∈ S₁, l ∈ X ∨ l ∈ top.S) ∧ X.Nodup ∧ Disj X (mutCells (olds hos)) ∧ ι₁.w = ι.w
  | _, [], _, _, _, .base hI hholes hpw _ hts _ =>
    ⟨_, _, _, _, _, hI, hholes, hpw, hts, fun l hl hm => mem_keep.mpr ⟨hl, hm⟩, fun l hl => .inr hl,
      hI.nodup.filter _, fun l hl => (mem_keep.mp hl).2, rfl⟩
  | _, _ :: _, _, _, _, .cons hf _ _ _ hn hd hK _ _ => by
    obtain ⟨ι₁, Γ₁, env₁, E₁, S₁, hI, hholes, hpw, hts, hE, hS, hXn, hXM, hw₁⟩ := hK.base_of
    refine ⟨ι₁, Γ₁, env₁, E₁, S₁, hI, hholes, hpw, hts, fun l hl hm => List.mem_append.mpr (.inr (hE l hl hm)),
      fun l hl => ?_, nodup_append_disj.mpr ⟨hn, hXn, fun l h1 h2 => hd l h1 (List.mem_append.mpr (.inl h2))⟩,
      fun l hl hm => ?_, hw₁.trans hf.w_eq⟩
    rotate_left
    · rcases List.mem_append.mp hl with h | h
      · exact hd l h (List.mem_append.mpr (.inr hm))
      · exact hXM l h hm
    rcases hS l hl with h | h
    · exact .inl (List.mem_append.mpr (.inr h))
    · rcases hf.S_sub l h with h | h
      · exact .inl (List.mem_append.mpr (.inl h))
      · exact .inr h
  | _, _, _, _, _, .nest _ _ _ _ hK hI _ hd _ _ _ _ => by
    obtain ⟨ι₁, Γ₁, env₁, E₁, S₁, hI₁, hholes, hpw, hts, hE, hS, hXn, hXM, hw₁⟩ := hK.base_of
    refine ⟨ι₁, Γ₁, env₁, E₁, S₁, hI₁, hholes, hpw, hts, fun l hl hm => List.mem_append.mpr (.inr (hE l hl hm)),
      fun l hl => ?_, nodup_append_disj.mpr ⟨hI.nodup, hXn, fun l h1 h2 => hd l h1 (List.mem_append.mpr (.inl h2))⟩,
      fun l hl hm => ?_, hw₁⟩
    · rcases hS l hl with h | h
      · exact .inl (List.mem_append.mpr (.inr h))
      · simp at h
    · rcases List.mem_append.mp hl with h | h
      · exact hd l h (List.mem_append.mpr (.inr hm))
      · exact hXM l h hm

theorem Kont.push_mem {f : Kont} {x : Frame} (h : x ∈ f.push []) : x ∈ f.push hs := by
  cases f <;> simp only [Kont.push, List.mem_cons, List.not_mem_nil, or_false] at h ⊢ <;> first | simp_all | grind

/-- The continuation of an operation: resumed with a value of the operation's type, or dropped,
it gives what its outermost frame's construct does. -/
theorem evalK_ok (hR : RetOk F O n) (hN : NestOk F O n) : EvalKOk F O n := by
  intro hs ι σs K
  induction K generalizing hs ι with
  | nil =>
    intro top X hos A σr ps r0 op0 Lv _ hK hR' haim hwf hag halloc hnd hps hnew hMn hX hdS hin
    cases hK with
    | base hI hholes hpw hop hts w =>
    obtain ⟨E', hI', hmem⟩ := caller_rebuild hI hholes hpw hps hnew hMn hag hX
      (fun l hl h => hdS l hl (by simp [h]))
    have hXa := fun l hl => (hag l (List.mem_append.mpr (.inl hl))).symm ▸ halloc l (List.mem_append.mpr (.inl hl))
    have hMa : ∀ l ∈ mutCells ps, σr.mem l ≠ none := fun l hl => by
      obtain ⟨p, hp, hlp⟩ := mem_mutCells.mp hl
      exact (hnew p hp (Hole.excl_mut hlp).1).alloc l (exclPart_sub hlp)
    simp only [evalK]
    rcases hin with ⟨v, rfl, hv, hdv⟩ | ⟨a, k, rfl, ha, rfl⟩
    · refine ⟨E', Lv, hI'.weaken w, hv, fun l hl h => hdv l hl (by rw [hmem] at h; simpa using h),
        fun l hl h => hdS l h (by simp [hl]), ?_⟩
      refine (Moves.refl hwf (fun l hl => ?_)).relabel fun x => ?_
      · simp only [List.mem_append] at hl
        rcases hl with (h | h) | h
        · exact hXa l h
        · exact hMa l h
        · exact hv.alloc l h
      · simp only [List.mem_append, hmem, List.not_mem_nil, or_false]
    · refine ⟨ha, E', hI'.weaken w, (Moves.refl hwf (fun l hl => ?_)).relabel fun x => ?_⟩
      · simp only [List.append_nil, List.mem_append] at hl
        rcases hl with h | h
        · exact hXa l h
        · exact hMa l h
      · simp only [List.mem_append, hmem, List.append_nil, List.not_mem_nil, or_false]
  | cons f K ih =>
    intro top X hos A σr ps r0 op0 Lv _ hK hR' haim hwf hag halloc hnd hps hnew hMn hX hdS hin
    have hK0 := hK
    cases hK with
    | nest => exact hN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ σr ps r0 op0 Lv hK0 hR' haim hwf hag halloc hnd hps hnew hMn hX hdS hin
    | cons hf w hagf hallocf hndf hdf hK hA1 hA2 =>
    have hwι := hf.w_eq
    have hwι' := hwι.symm
    haveI := WorldOk.of_eq (F := F) (O := O) hwι
    have hSsub := hf.S_sub
    simp only at hSsub
    obtain ⟨-, -, -, -, -, -, -, -, hts, -, -, -, -⟩ := hK.base_of
    have hrf : ∀ p ∈ ps, p.1.ty.rfree = true := fun p hp => by
      have : (p.1.mode, p.1.ty) ∈ op0.refs := by
        rw [← hts, ← hps]; exact List.mem_map_of_mem (List.mem_map_of_mem hp)
      exact op0.refs_rfree _ this
    have hpost := ih (Kont.push f hs) _ _ _ _ _ σr ps r0 op0 Lv hK (hf.ready hR')
      (fun a ha => by
        rcases hA2 a ha with h | h
        · exact (haim a h).push
        · exact h.imp_right fun ⟨l, hl⟩ => ⟨l, Kont.push_mem hl⟩) hwf
      (hag.mono fun l hl => by
        rcases List.mem_append.mp hl with h | h
        · exact by simp [h]
        · rcases hSsub l h with h | h
          · exact by simp [h]
          · exact List.mem_append.mpr (.inr h))
      (fun l hl => by
        rcases List.mem_append.mp hl with h | h
        · exact halloc l (by simp [h])
        · rcases hSsub l h with h | h
          · exact halloc l (by simp [h])
          · exact halloc l (List.mem_append.mpr (.inr h)))
      (List.nodup_append.mp hnd).2.1 hps (fun p hp hm => (hnew p hp hm).rfree_iota (hrf p hp)) hMn
      (fun l hl h => hX l (by simp [hl]) h)
      (fun l hl h => by
        rcases hSsub l hl with h' | h'
        · simp only [List.mem_append] at h
          rcases h with (h | h) | h
          · exact (List.nodup_append.mp hnd).2.2 l h' l h rfl
          · exact hX l (by simp [h']) h
          · rcases hin with ⟨v, -, -, hdv⟩ | ⟨a, k, -, -, rfl⟩
            · exact hdv l h (by simp [h'])
            · simp at h
        · exact hdS l h' (by simp only [List.mem_append] at h ⊢; grind))
      (by
        rcases hin with ⟨v, rfl, hv, hdv⟩ | ⟨a, k, rfl, ha, rfl⟩
        · exact .inl ⟨v, rfl, hv.rfree_iota op0.ret_rfree, fun l hl h => hdv l hl (by simp only [List.mem_append] at h ⊢; grind)⟩
        · exact .inr ⟨a, k, rfl, ha.push, rfl⟩)
    simp only [evalK]
    have := hR hs _ _ _ f _ _ _ _ σr (_ ++ mutCells ps ++ Lv) _ hf hR'
      (fun a ha => haim a (hA1 a ha)) hwf
      ((Agree.trans (hagf) (hag.mono fun l hl => (by simp only [List.mem_append] at hl ⊢; grind)))) hallocf hndf
      (fun l hl h => by
        simp only [List.mem_append] at h
        rcases h with (h | h) | h
        · exact (List.nodup_append.mp hnd).2.2 l hl l h rfl
        · exact hX l (by simp [hl]) h
        · rcases hin with ⟨v, -, -, hdv⟩ | ⟨a, k, -, -, rfl⟩
          · exact hdv l h (by simp [hl])
          · simp at h)
      (fun l hl => by rw [hag l (List.mem_append.mpr (.inr hl))]; exact halloc l (List.mem_append.mpr (.inr hl)))
      (fun l hl h => hdS l hl (by simp only [List.mem_append] at h ⊢; grind)) hpost
    simpa [List.append_assoc] using post_weaken this w

/-! ## Frames that keep no cells -/

/-- `let x = □; b`: the variable bound to what the code gave, `b` run in its scope. -/
theorem ret_letK [WorldOk F O ι.w] (hfl : FlushOk F ι (flushR F O n)) (hE : EvalOk F O n) (hx : lookup x Γ₁ = none) (hk : (Γ₁.map Prod.fst).Nodup)
    (hb : Typed F O ((x, .own τx true) :: Γ₁) b τb ((x, .own τx live) :: Γ₂) r) (hR : Ready O hs r)
    (hwf : WF σ0) (h : Post F ι O σ0 E S Γ₁ env τx r hs res) :
    Post F ι O σ0 E S Γ₂ env τb r hs (ret F O n hs (.letK x τx env b) res) := by
  have hx₁ := lookup_none_keys hx
  have hk₂ : x ∉ Γ₂.map Prod.fst ∧ (Γ₂.map Prod.fst).Nodup := by
    have := typed_keys hb
    simp only [List.map_cons, List.cons.injEq] at this
    rw [this.2]; exact ⟨hx₁, hk⟩
  rcases res with ⟨res, σ1⟩
  cases res with
  | val v =>
    obtain ⟨E₁, L₁, hI₁, hv₁, hd₁, hdS₁, hm₁⟩ := h
    obtain ⟨hIb, hma⟩ := bind_ok hI₁ hv₁ hd₁ hdS₁ hm₁ hwf hx₁
    simp only [ret]
    exact leave_ok hfl hv₁.complete hma hwf hk₂.1 hk₂.2 (hE _ _ _ _ _ _ _ _ _ _ _ hb hIb hma.wf hR)
  | abort j k =>
    simp only [ret]
    have w := typed_weaker hb (List.nodup_cons.mpr ⟨hx₁, hk⟩)
    cases w with
    | cons _ w => exact post_out h w
  | susp j ef vs ls K =>
    simp only [ret]
    exact post_frame h (.letK hx hk hb)
  | stuck => simp [Post] at h
  | timeout => simp [ret, Post]
  | ended => simp [ret, Post]

/-- Unwinding past a handler named `c`: an unwinding aimed elsewhere is aimed below. -/
theorem aimed_pop : AimedIn i (.abort l c :: hs) → i ≠ c → AimedIn i hs := by
  rintro (h | ⟨l', hl⟩) hne
  · exact .inl h
  rcases List.mem_cons.mp hl with h | h
  · cases h; exact absurd rfl hne
  · exact .inr ⟨l', h⟩

/-- A continuation taken through a frame putting an unwinding handler named `c` in force: unwindings
aimed at `c` are the continuation's own. -/
theorem post_frame_abort (h : Post F ι O σ E S Γ₁ env₁ τ₁ r₁ (.abort l c :: hs) (.susp j ef vs ls K, σ'))
    (hf : FrameOk F O ι ι σ' f ⟨Γ₁, env₁, τ₁, S, r₁⟩ ⟨Γ', env, τ, S, r⟩ [] Af) (hpush : ∀ hs, f.push hs = .abort l c :: hs)
    (hAf : ∀ a ∈ Af, AimedIn a hs) (hcov : Covers hs r) (hlne : ∀ e, l ≠ .eff e := by intro e h; cases h) :
    Post F ι O σ E S Γ' env τ r hs (.susp j ef vs ls (f :: K), σ') := by
  obtain ⟨op, X, hos, A, Lv, hc, hop, -, haim, hK, hls, hvs, hn, hd, hdS, hm⟩ := h
  have hK' := FramesOk.cons (σf := σ') (A := Af ++ A.filter (· ≠ c)) hf (Weaker.refl _) Agree.self
    (fun _ h => by simp at h) List.nodup_nil disj_nil_left hK (fun a ha => List.mem_append.mpr (.inl ha))
    (fun a ha => by
      by_cases hac : a = c
      · subst hac; exact .inr (.inr ⟨l, by simp [hpush]⟩)
      · exact .inl (List.mem_append.mpr (.inr (List.mem_filter.mpr ⟨ha, by simpa using hac⟩))))
  simp only [List.nil_append] at hK'
  refine ⟨op, X, hos, Af ++ A.filter (· ≠ c), Lv, hc.of_cons_abort.resolve_left fun h => hlne _ h.1, hop, hcov, fun a ha => ?_, hK', hls, hvs, hn, hd,
    hdS, hm⟩
  · rcases List.mem_append.mp ha with ha | ha
    · exact hAf a ha
    · obtain ⟨ha, hne⟩ := List.mem_filter.mp ha
      exact aimed_pop (haim a ha) (by simpa using hne)

/-- A `try`, or a `handle` whose arm ends it, puts in force a handler that unwinds, which an operation
of its effect may also reach by being taken: unwindings aimed elsewhere are aimed further out. -/
theorem aimed_catch (h : AimedIn a ((Kont.catchK l c x env b).push hs)) (hne : a ≠ c) : AimedIn a hs := by
  rcases h with h | ⟨l', hl⟩
  · exact .inl h
  cases l <;> simp only [Kont.push, List.mem_cons, Frame.abort.injEq, reduceCtorEq, false_or] at hl
  all_goals
    rcases hl with ⟨-, rfl⟩ | hl
    · exact absurd rfl hne
    · exact .inr ⟨l', hl⟩

/-- `try { □ } catch (x) { h }`, or a `handle` whose arm ends it: an unwinding aimed at its handler
runs `h`, and so does an operation of its effect, taken as the continuation is unwound from it;
anything else goes on. -/
theorem ret_catchK [WorldOk F O ι.w] (hfl : FlushOk F ι (flushR F O n)) (hE : EvalOk F O n)
    (hKo : ∀ m, n = m + 1 → EvalKOk F O m ∧ RetOk F O m) (hx : lookup x Γb = none) (hk : (Γb.map Prod.fst).Nodup)
    (hh : Typed F O ((x, .own .int true) :: Γb) h τ ((x, .own .int live) :: Γh) r)
    (hl : ∀ e, l = .eff e → ∃ op, O[e]? = some op ∧ op.owns = [.int] ∧ op.refs = [])
    (hR : Ready O hs r) (hwf : WF σ0) (hSa : ∀ l ∈ S, σ0.mem l ≠ none) (hSd : Disj S E)
    (hp : Post F ι O σ0 E S Γb env τ (l :: r) ((Kont.catchK l hid x env h).push hs) res) :
    Post F ι O σ0 E S Γh env τ r hs (ret F O n hs (.catchK l hid x env h) res) := by
  have hxb := lookup_none_keys hx
  have w := typed_weaker hh (List.nodup_cons.mpr ⟨hxb, hk⟩)
  have hkh : x ∉ Γh.map Prod.fst ∧ (Γh.map Prod.fst).Nodup := by
    have := typed_keys hh
    simp only [List.map_cons, List.cons.injEq] at this
    rw [this.2]; exact ⟨hxb, hk⟩
  have hfr : ∀ σf, FrameOk F O ι ι σf (.catchK l hid x env h) ⟨Γb, env, τ, S, l :: r⟩ ⟨Γh, env, τ, S, r⟩ [] [] :=
    fun _ => .catchK hx hk hh hl
  cases w with
  | cons _ w =>
  rcases res with ⟨res, σ1⟩
  cases res with
  | val v =>
    obtain ⟨E₁, L₁, hI₁, hv₁, hd₁, hdS₁, hm₁⟩ := hp
    simp only [ret]
    exact ⟨E₁, L₁, hI₁.weaken w, hv₁, hd₁, hdS₁, hm₁⟩
  | abort j k =>
    simp only [ret]
    split
    · rename_i hj
      subst hj
      obtain ⟨-, E₁, hI₁, hm₁⟩ := hp
      obtain ⟨hIb, hma⟩ := bind_ok (v := .int k) hI₁ .int disj_nil_left disj_nil_left hm₁ hwf hxb
      exact leave_ok hfl rfl hma hwf hkh.1 hkh.2 (hE _ _ _ _ _ _ _ _ _ _ _ hh hIb hma.wf hR)
    · rename_i hj
      obtain ⟨haim, E₁, hI₁, hm₁⟩ := hp
      exact ⟨aimed_catch haim hj, E₁, hI₁.weaken w, hm₁⟩
  | susp j ef vs ls K =>
    by_cases hown : l = .eff ef ∧ j = hid
    · obtain ⟨rfl, rfl⟩ := hown
      obtain ⟨op', X, hos, A, Lv, -, hop', hcov, haim, hK, hls, hvs, hLn, hdLX, hdLS, hm⟩ := hp
      obtain ⟨op, hop, howns, hrefs⟩ := hl ef rfl
      obtain rfl : op = op' := Option.some.inj (hop.symm.trans hop')
      obtain ⟨-, -, -, -, -, -, -, -, hts, -, -, hXn, -⟩ := hK.base_of
      rw [hrefs] at hts
      obtain rfl : hos = [] := List.map_eq_nil_iff.mp hts
      rw [howns] at hvs
      cases hvs with
      | cons hv hr =>
      cases hr
      cases hv with
      | @int k =>
      simp only [olds, mutCells, List.map_nil, List.flatMap_nil, List.append_nil, List.flatten_cons,
        List.flatten_nil] at hm hdLX hdLS hLn
      cases n with
      | zero => simp [ret, Post]
      | succ m =>
      obtain ⟨hKk, hRr⟩ := hKo m rfl
      simp only [ret, and_self, ↓reduceIte]
      have hwf₁ := hm.wf
      have hSa1 : ∀ l ∈ S, σ1.mem l ≠ none := fun l hl => by
        rw [hm.keeps hwf hSa (fun l h1 h2 => hSd l h1 h2) l hl]; exact hSa l hl
      have hXa1 : ∀ l ∈ X, σ1.mem l ≠ none := fun l hl => (hm.alloc l).mpr (.inr (.inl hl))
      have hdSX : Disj S X := fun l h1 h2 => (hm.apart hwf hSa hSd).1 l h1 h2
      -- Taken as it is unwound from the operation.
      have hres := hKk ((Kont.catchK (.eff ef) j x env h).push hs) ι σ1 K ⟨Γb, env, τ, S, .eff ef :: r⟩ X [] A σ1 []
        (.abort j k) op [] hK ⟨catch_hsok hl hR.1, hcov⟩ haim hwf₁ Agree.self
        (fun l hl => by
          rcases List.mem_append.mp hl with h | h
          · exact hXa1 l h
          · exact hSa1 l h) hXn rfl (fun _ h => by simp at h) (by simp [mutCells]) (by simp [mutCells, Disj])
        (by simp only [mutCells, List.flatMap_nil, List.append_nil]; exact hdSX)
        (.inr ⟨j, k, rfl, .inr ⟨.eff ef, by simp [Kont.push]⟩, rfl⟩)
      simp only [mutCells, List.flatMap_nil, List.append_nil] at hres
      have h2 := hRr hs ι ι σ1 (.catchK (.eff ef) j x env h) ⟨Γb, env, τ, S, .eff ef :: r⟩ ⟨Γh, env, τ, S, r⟩ [] []
        σ1 X _ (hfr σ1) hR (fun _ h => by simp at h) hwf₁ Agree.self (fun _ h => by simp at h) List.nodup_nil
        disj_nil_left hSa1 (by simpa using hdSX) hres
      exact post_after (hm.relabel (E'' := X) (L'' := []) fun x => by simp) hwf (by simpa using h2)
    · have : ret F O n hs (.catchK l hid x env h) (.susp j ef vs ls K, σ1) =
          (.susp j ef vs ls (.catchK l hid x env h :: K), σ1) := by
        rw [ret.eq_def]; simp [hown]
      rw [this]
      obtain ⟨op, X, hos, A, Lv, hc, hop, -, haim, hK, hls, hvs, hn, hd, hdS, hm⟩ := hp
      have hK' := FramesOk.cons (σf := σ1) (A := A.filter (· ≠ hid)) (hfr σ1) (Weaker.refl _) Agree.self
        (fun _ h => by simp at h) List.nodup_nil disj_nil_left hK (fun a ha => by simp at ha)
        (fun a ha => by
          by_cases hac : a = hid
          · subst hac
            refine .inr ?_
            cases l with
            | eff e' => exact .inr ⟨.eff e', by simp [Kont.push]⟩
            | fail => exact .inr ⟨.fail, by simp [Kont.push]⟩
            | drop => exact .inr ⟨.drop, by simp [Kont.push]⟩
          · exact .inl (List.mem_filter.mpr ⟨ha, by simpa using hac⟩))
      simp only [List.nil_append] at hK'
      refine ⟨op, X, hos, A.filter (· ≠ hid), Lv, ?_, hop, hR.2, fun a ha => ?_, hK', hls, hvs, hn, hd, hdS, hm⟩
      · cases l with
        | eff e' =>
          rcases hc.of_cons_capture with ⟨h1, h2⟩ | hc
          · exact absurd ⟨by rw [h2], h1⟩ hown
          · rcases hc.of_cons_abort with ⟨h1, h2⟩ | hc
            · exact absurd ⟨h1, h2⟩ hown
            · exact hc
        | fail => exact hc.of_cons_fail
        | drop => exact hc.of_cons_drop
      · obtain ⟨ha, hne⟩ := List.mem_filter.mp ha
        exact aimed_catch (haim a ha) (by simpa using hne)
  | stuck => simp [Post] at hp
  | timeout => simp [ret, Post]
  | ended => simp [ret, Post]

/-- A loop's body ended: the loop goes round again. -/
theorem ret_whileB [WorldOk F O ι.w] (hE : EvalOk F O n) (hc : Typed F O Γ c .int Γ r) (hb : Typed F O Γ b .int Γ r)
    (hR : Ready O hs r) (hwf : WF σ0) (hp : Post F ι O σ0 E S Γ env .int r hs res) :
    Post F ι O σ0 E S Γ env .int r hs (ret F O n hs (.whileB env c b) res) := by
  rcases res with ⟨res, σ1⟩
  cases res with
  | val v =>
    obtain ⟨E₁, L₁, hI₁, hv₁, -, -, hm₁⟩ := hp
    cases hv₁ with
    | int =>
      simp only [ret]
      exact post_after (by simpa using hm₁) hwf (hE _ _ _ _ _ _ _ _ _ _ _ (.while_ hc hb) hI₁ hm₁.wf hR)
  | abort j k => simp only [ret]; exact hp
  | susp j ef vs ls K => simp only [ret]; exact post_frame hp (.whileB hc hb)
  | stuck => simp [Post] at hp
  | timeout => simp [ret, Post]
  | ended => simp [ret, Post]

/-- A loop's condition ended: zero ends the loop; anything else runs the body, and the loop goes
round again. -/
theorem ret_whileC [WorldOk F O ι.w] (hE : EvalOk F O n) (hc : Typed F O Γ c .int Γ r) (hb : Typed F O Γ b .int Γ r)
    (hR : Ready O hs r) (hwf : WF σ0) (hp : Post F ι O σ0 E S Γ env .int r hs res) :
    Post F ι O σ0 E S Γ env .int r hs (ret F O n hs (.whileC env c b) res) := by
  rcases res with ⟨res, σ1⟩
  cases res with
  | val v =>
    obtain ⟨E₁, L₁, hI₁, hv₁, -, -, hm₁⟩ := hp
    cases hv₁ with
    | @int k =>
      by_cases hk : k = 0
      · subst hk
        simp only [ret]
        exact ⟨E₁, [], hI₁, .int, disj_nil_left, disj_nil_left, hm₁⟩
      · rw [ret.eq_def]
        simp only [hk]
        have h2 := hE _ _ _ _ _ _ _ _ _ _ _ hb hI₁ hm₁.wf hR
        generalize eval F O n hs σ1 env b = r2 at h2 ⊢
        rcases r2 with ⟨r2, σ2⟩
        cases r2 with
        | val w =>
          obtain ⟨E₂, L₂, hI₂, hv₂, -, -, hm₂⟩ := h2
          cases hv₂ with
          | int =>
            have hm₁₂ := (hm₁.trans hm₂ disj_nil_left hwf).relabel (E'' := E₂) (L'' := []) (by simp)
            exact post_after hm₁₂ hwf (hE _ _ _ _ _ _ _ _ _ _ _ (.while_ hc hb) hI₂ hm₂.wf hR)
        | abort j k => exact post_after (by simpa using hm₁) hwf h2
        | susp j ef vs ls K => exact post_after (by simpa using hm₁) hwf (post_frame h2 (.whileB hc hb))
        | stuck => simp [Post] at h2
        | timeout => simp [Post]
        | ended => simp [Post]
  | abort j k => simp only [ret]; exact hp
  | susp j ef vs ls K => simp only [ret]; exact post_frame hp (.whileC hc hb)
  | stuck => simp [Post] at hp
  | timeout => simp [ret, Post]
  | ended => simp [ret, Post]

/-! ## Frames that only pass on what their code gives -/

/-- What a frame that keeps nothing to do gives: what its code did, a continuation taken in it
keeping the frame. -/
def passK (f : Kont) : Res × Store → Res × Store
  | (.susp j ef vs ls K, σ) => (.susp j ef vs ls (f :: K), σ)
  | r => r

/-- A frame that only passes on what its code gives: once its code ends, the activation around it
is rebuilt from its code's, with the cells the frame kept as they were. -/
theorem post_pass (hf : FrameOk F O ι ι σf f ⟨Γin, envin, τ, Sin, rin⟩ ⟨Γout, env, τ, S, r⟩ Xf [])
    (hSS : ∀ l ∈ S, l ∈ Sin)
    (hre : ∀ σ1 Eb, Agree σf σ1 (Xf ++ S) → Disj Xf Eb → Inv F ι σ1 Γin envin Eb Sin →
      ∃ E', Inv F ι σ1 Γout env E' S ∧ ∀ z, z ∈ E' ↔ z ∈ Eb ∨ z ∈ Xf)
    (hcov : Covers hs r) (hA : ∀ a, AimedIn a hsin → AimedIn a hs)
    (hcap : ∀ j ef vs ls K σ', res = (.susp j ef vs ls K, σ') → Takes hsin j ef → Takes hs j ef)
    (hwf : WF σ0) (hag : Agree σf σ0 (Xf ++ S)) (halloc : ∀ l ∈ Xf, σf.mem l ≠ none) (hnd : Xf.Nodup)
    (hd : Disj Xf Ein) (hSa : ∀ l ∈ S, σ0.mem l ≠ none) (hSd : Disj S (Xf ++ Ein))
    (hp : Post F ι O σ0 Ein Sin Γin envin τ rin hsin res) :
    Post F ι O σ0 (Xf ++ Ein) S Γout env τ r hs (passK f res) := by
  have hXa : ∀ l ∈ Xf, σ0.mem l ≠ none := fun l hl => by
    rw [hag l (List.mem_append.mpr (.inl hl))]; exact halloc l hl
  have hXSa : ∀ l ∈ Xf ++ S, σ0.mem l ≠ none := fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · exact hXa l h
    · exact hSa l h
  have hXSd : Disj (Xf ++ S) Ein := fun l hl h => by
    rcases List.mem_append.mp hl with hl | hl
    · exact hd l hl h
    · exact hSd l hl (List.mem_append.mpr (.inr h))
  have agree : ∀ {E' L σ1}, Moves σ0 Ein σ1 E' L → Agree σf σ1 (Xf ++ S) := fun hm => Agree.trans hag (hm.keeps hwf hXSa hXSd)
  rcases res with ⟨res, σ1⟩
  cases res with
  | val v =>
    obtain ⟨Eb, L, hI, hv, hdL, hdLS, hm⟩ := hp
    obtain ⟨hdXE, hdXL⟩ := hm.apart hwf hXa hd
    obtain ⟨E', hI', hmem⟩ := hre σ1 Eb (agree hm) hdXE hI
    refine ⟨E', L, hI', hv, fun l hl h => ?_, fun l hl h => hdLS l hl (hSS l h),
      (hm.widen hXa hd).relabel fun x => by simp only [List.mem_append, hmem]; grind⟩
    rcases (hmem l).mp h with h | h
    · exact hdL l hl h
    · exact hdXL l h hl
  | abort j k =>
    obtain ⟨haim, Eb, hI, hm⟩ := hp
    obtain ⟨E', hI', hmem⟩ := hre σ1 Eb (agree hm) (hm.apart hwf hXa hd).1 hI
    exact ⟨hA _ haim, E', hI', (hm.widen hXa hd).relabel fun x => by simp only [List.mem_append, hmem]; grind⟩
  | susp j ef vs ls K =>
    obtain ⟨op, X, hos, A, Lw, hc, hop, -, haim, hK, hls, hvs, hn, hdw, hdS, hm⟩ := hp
    obtain ⟨hdX, hdL⟩ := hm.apart hwf hXa hd
    have hK' := FramesOk.cons (A := A) hf (Weaker.refl _) (agree hm) halloc hnd hdX hK
      (fun _ h => by simp at h) (fun a ha => .inl ha)
    refine ⟨op, Xf ++ X, hos, A, Lw, hcap _ _ _ _ _ _ rfl hc, hop, hcov, fun a ha => hA a (haim a ha), hK', hls,
      hvs, hn, ?_, fun l hl h => hdS l hl (hSS l h), ?_⟩
    · intro l hl h
      simp only [List.mem_append] at h
      rcases h with (h | h) | h
      · exact hdL l h hl
      · exact hdw l hl (by simp [h])
      · exact hdw l hl (by simp [h])
    · exact (hm.widen hXa hd).relabel fun x => by simp only [List.mem_append, List.append_assoc]
  | stuck => simp [Post] at hp
  | timeout => simp [passK, Post]
  | ended => simp [passK, Post]

/-! ## A closure over a borrow -/

/-- The code a closure over a borrow was in scope for ended: the closure's cell is freed, and the
activation is the lender's again. -/
theorem ret_cloK (hSin : ∀ l ∈ Sin, l ∈ Xf ∨ l ∈ S) (hSS : ∀ l ∈ S, l ∈ Sin) (haX : a ∈ Xf)
    (hre : ∀ W, ι.w.le W → ∀ σ1 Eb, Agree σf σ1 (Xf ++ S) → Disj Xf Eb → Inv F (ι.inW W) σ1 Γin envin Eb Sin →
      ∃ E', Inv F (ι.inW W) σ1 Γout env E' S ∧ ∀ z, z ∈ E' ↔ z ∈ Eb ∨ (z ∈ Xf ∧ z ≠ a))
    (hcov : Covers hs r) (hwf : WF σ0) (hag : Agree σf σ0 (Xf ++ S)) (halloc : ∀ l ∈ Xf, σf.mem l ≠ none)
    (hnd : Xf.Nodup) (hd : Disj Xf Ein) (hSa : ∀ l ∈ S, σ0.mem l ≠ none) (hSd : Disj S (Xf ++ Ein))
    (hp : Post F ι O σ0 Ein Sin Γin envin τ r hs res) :
    Post F ι O σ0 (Xf ++ Ein) S Γout env τ r hs (ret F O n hs (.cloK a) res) := by
  have hXa : ∀ l ∈ Xf, σ0.mem l ≠ none := fun l hl => by
    rw [hag l (List.mem_append.mpr (.inl hl))]; exact halloc l hl
  have hXSa : ∀ l ∈ Xf ++ S, σ0.mem l ≠ none := fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · exact hXa l h
    · exact hSa l h
  have hXSd : Disj (Xf ++ S) Ein := fun l hl h => by
    rcases List.mem_append.mp hl with hl | hl
    · exact hd l hl h
    · exact hSd l hl (List.mem_append.mpr (.inr h))
  have agree : ∀ {E' L σ1}, Moves σ0 Ein σ1 E' L → Agree σf σ1 (Xf ++ S) := fun hm => Agree.trans hag (hm.keeps hwf hXSa hXSd)
  have haS : a ∉ S := fun h => hSd a h (List.mem_append.mpr (.inl haX))
  -- Freeing the closure's cell, which is the frame's and no one else's.
  have free : ∀ {σ1 Eb L E'}, Moves σ0 Ein σ1 Eb L → Disj Xf Eb → Disj Xf L →
      (∀ z, z ∈ E' ↔ z ∈ Eb ∨ (z ∈ Xf ∧ z ≠ a)) →
      σ1.mem a ≠ none ∧ Agree σ1 (σ1.set a none) (E' ++ S ++ L) ∧
        Moves σ0 (Xf ++ Ein) (σ1.set a none) E' L := by
    intro σ1 Eb L E' hm hdE hdL hmem
    have ha1 : σ1.mem a ≠ none := by rw [agree hm a (List.mem_append.mpr (.inl haX))]; exact halloc a haX
    have hout : ∀ z ∈ E' ++ S ++ L, z ≠ a := fun z hz e => by
      subst e
      simp only [List.mem_append] at hz
      rcases hz with (hz | hz) | hz
      · rcases (hmem z).mp hz with h | h
        · exact hdE z haX h
        · exact h.2 rfl
      · exact haS hz
      · exact hdL z haX hz
    refine ⟨ha1, Agree.of' fun z hz => by simp [Store.set, hout z hz], ?_⟩
    have m1 := (hm.widen hXa hd).relabel (E'' := E' ++ L ++ [a]) (L'' := []) fun x => by
      simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false, hmem]
      by_cases hx : x = a
      · subst hx; simp [haX]
      · simp [hx]; grind
    have m2 := Moves.free (σ := σ1) (σ' := σ1.set a none) (E := E' ++ L ++ [a]) (E' := E' ++ L) (D := [a])
      (WF.set_none hm.wf) rfl (fun z hz => (m1.alloc z).mpr (.inr (.inl hz)))
      (fun x => by simp only [List.mem_append, List.mem_singleton])
      (fun z hz => by simp at hz; subst hz; simp [Store.set])
      (fun z hz => by simp at hz; simp [Store.set, hz])
      (fun z hz hz' => by
        simp only [List.mem_singleton] at hz'
        subst hz'
        exact hout _ (by simp only [List.mem_append] at hz ⊢; grind) rfl)
    exact (m1.trans m2 disj_nil_left hwf).relabel fun x => by simp
  rcases res with ⟨res, σ1⟩
  cases res with
  | val v =>
    obtain ⟨Eb, L, hI, hv, hdL, hdLS, hm⟩ := hp
    obtain ⟨hdXE, hdXL⟩ := hm.apart hwf hXa hd
    obtain ⟨E', hI', hmem⟩ := hre _ (World.le_refl _) σ1 Eb (agree hm) hdXE hI
    obtain ⟨ha1, hagf, hmf⟩ := free hm hdXE hdXL hmem
    simp only [ret]
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp ha1
    simp only [hw]
    refine ⟨E', L, ⟨hI'.foot.frame (hagf.mono fun z hz => by simp only [List.mem_append] at hz ⊢; grind),
      hI'.nodup, hI'.disj, hI'.keys⟩, hv.frame (hagf.mono fun z hz => by simp [hz]), fun l hl h => ?_,
      fun l hl h => hdLS l hl (hSS l h), hmf⟩
    rcases (hmem l).mp h with h | h
    · exact hdL l hl h
    · exact hdXL l h.1 hl
  | abort j k =>
    obtain ⟨haim, Eb, hI, hm⟩ := hp
    obtain ⟨E', hI', hmem⟩ := hre _ (World.le_refl _) σ1 Eb (agree hm) (hm.apart hwf hXa hd).1 hI
    obtain ⟨ha1, hagf, hmf⟩ := free (L := []) hm (hm.apart hwf hXa hd).1 disj_nil_right hmem
    simp only [ret]
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp ha1
    simp only [hw]
    exact ⟨haim, E', ⟨hI'.foot.frame (hagf.mono fun z hz => by simp only [List.mem_append] at hz ⊢; grind),
      hI'.nodup, hI'.disj, hI'.keys⟩, hmf⟩
  | susp j ef vs ls K =>
    obtain ⟨op, X, hos, A, Lw, hc, hop, -, haim, hK, hls, hvs, hn, hdw, hdS, hm⟩ := hp
    obtain ⟨hdX, hdL⟩ := hm.apart hwf hXa hd
    have hK' := FramesOk.cons (A := A) (.cloK hSin hSS haX hre) (Weaker.refl _) (agree hm) halloc hnd hdX hK
      (fun _ h => by simp at h) (fun a ha => .inl ha)
    simp only [ret]
    refine ⟨op, Xf ++ X, hos, A, Lw, hc, hop, hcov, haim, hK', hls, hvs, hn, ?_,
      fun l hl h => hdS l hl (hSS l h), ?_⟩
    · intro l hl h
      simp only [List.mem_append] at h
      rcases h with (h | h) | h
      · exact hdL l h hl
      · exact hdw l hl (by simp [h])
      · exact hdw l hl (by simp [h])
    · exact (hm.widen hXa hd).relabel fun x => by simp only [List.mem_append, List.append_assoc]
  | stuck => simp [Post] at hp
  | timeout => simp [ret, Post]
  | ended => simp [ret, Post]

/-! ## A borrow held for a while -/

/-- A borrow ended: the activation is the lender's again, the cells the frame kept as they were. -/
theorem ret_lendK (hSin : ∀ l ∈ Sin, l ∈ Xf ∨ l ∈ S) (hSS : ∀ l ∈ S, l ∈ Sin)
    (hre : ∀ W, ι.w.le W → ∀ σ1 Eb, Agree σf σ1 (Xf ++ S) → Disj Xf Eb → Inv F (ι.inW W) σ1 Γin envin Eb Sin →
      ∃ E', Inv F (ι.inW W) σ1 Γout env E' S ∧ ∀ z, z ∈ E' ↔ z ∈ Eb ∨ z ∈ Xf)
    (hcov : Covers hs r) (hwf : WF σ0) (hag : Agree σf σ0 (Xf ++ S)) (halloc : ∀ l ∈ Xf, σf.mem l ≠ none)
    (hnd : Xf.Nodup) (hd : Disj Xf Ein) (hSa : ∀ l ∈ S, σ0.mem l ≠ none) (hSd : Disj S (Xf ++ Ein))
    (hp : Post F ι O σ0 Ein Sin Γin envin τ r hs res) :
    Post F ι O σ0 (Xf ++ Ein) S Γout env τ r hs (ret F O n hs .lendK res) := by
  have : ret F O n hs .lendK res = passK .lendK res := by
    rcases res with ⟨_ | _ | _ | _ | _, _⟩ <;> simp [ret, passK]
  rw [this]
  exact post_pass (.lendK hSin hSS hre) hSS (hre _ (World.le_refl _)) hcov (fun _ h => h) (fun _ _ _ _ _ _ _ h => h) hwf hag halloc
    hnd hd hSa hSd hp

/-! ## Cleanup -/

/-- A cleanup ended, the body having given `v`, whose cells `Lv` the cleanup cannot reach: `v`
again, or, if the cleanup unwinds, `v` dropped; a continuation taken in the cleanup keeps `v`. -/
theorem ret_deferV (hfl : FlushOk F ι fl) (hv : VT F ι σf τ v Lv) (hag : Agree σf σ0 (Lv ++ S)) (halloc : ∀ l ∈ Lv, σf.mem l ≠ none)
    (hnd : Lv.Nodup) (hd : Disj Lv Ein) (hSd : Disj S Lv) (hSE : Disj S Ein) (hSa : ∀ l ∈ S, σ0.mem l ≠ none)
    (hwf : WF σ0)
    (hp : Post F ι O σ0 Ein S Γb env .int r hs res) :
    Post F ι O σ0 (Lv ++ Ein) S Γb env τ r hs (cleanV fl τ v res) := by
  have hLa : ∀ l ∈ Lv, σ0.mem l ≠ none := fun l hl => by
    rw [hag l (List.mem_append.mpr (.inl hl))]; exact halloc l hl
  have hv0 : VT F ι σ0 τ v Lv := hv.frame (hag.mono fun l hl => List.mem_append.mpr (.inl hl))
  rcases res with ⟨res, σ1⟩
  cases res with
  | val w =>
    obtain ⟨E₁, L₁, hI₁, hv₁, -, -, hm₁⟩ := hp
    cases hv₁ with
    | int =>
      simp only [cleanV]
      obtain ⟨hdE, -⟩ := hm₁.apart hwf hLa hd
      exact ⟨E₁, Lv, hI₁, hv0.frame (hm₁.keeps hwf hLa hd), hdE, fun l hl h => hSd l h hl,
        (hm₁.widen hLa hd).relabel fun x => by simp only [List.mem_append, List.not_mem_nil, or_false]; grind⟩
  | abort j k =>
    obtain ⟨haim, E₁, hI₁, hm₁⟩ := hp
    have hv₁ := hv0.frame (hm₁.keeps hwf hLa hd)
    obtain ⟨hdE, -⟩ := hm₁.apart hwf hLa hd
    obtain ⟨σ3, hdrop, hfg⟩ := dropF hfl hm₁.wf hv₁
    simp only [cleanV, hdrop]
    refine hfg.post fun σ4 hd4 => ⟨haim, E₁, hI₁.dropped hd4 hm₁.wf hdE (fun l hl h => hSd l h hl), ?_⟩
    exact Moves.thenDrop ((hm₁.widen hLa hd).relabel fun x => by mem_iff) hd4
      (fun l hl => hI₁.alloc l (by simpa using hl)) (fun l hl h => hdE l h (by simpa using hl)) hwf
  | susp j ef vs ls K =>
    obtain ⟨op, X, hos, A, Lw, hc, hop, hcov, haim, hK, hls, hvs, hn, hdw, hdS, hm⟩ := hp
    simp only [cleanV]
    obtain ⟨hdX, hdL⟩ := hm.apart hwf hLa hd
    have hLS : ∀ l ∈ Lv ++ S, σ0.mem l ≠ none := fun l hl => by
      rcases List.mem_append.mp hl with h | h
      · exact hLa l h
      · exact hSa l h
    have hK' := FramesOk.cons (A := A) (.deferV hv) (Weaker.refl _)
      ((Agree.trans (hag) ((hm.keeps hwf hLS (fun l hl h => by
        rcases List.mem_append.mp hl with hl | hl
        · exact hd l hl h
        · exact hSE l hl h))))) halloc hnd hdX hK
      (fun _ h => by simp at h) (fun a ha => .inl ha)
    refine ⟨op, Lv ++ X, hos, A, Lw, hc, hop, hcov, haim, hK', hls, hvs, hn, ?_, hdS, ?_⟩
    · intro l hl h
      simp only [List.mem_append] at h
      rcases h with (h | h) | h
      · exact hdL l h hl
      · exact hdw l hl (by simp [h])
      · exact hdw l hl (by simp [h])
    · exact (hm.widen hLa hd).relabel fun x => by simp only [List.mem_append, List.append_assoc]
  | stuck => simp [Post] at hp
  | timeout => simp [cleanV, Post]
  | ended => simp [cleanV, Post]

/-- A cleanup ended as the body unwound to `j`: the unwinding goes on, unless the cleanup unwound
itself; a continuation taken in the cleanup keeps the unwinding. -/
theorem ret_deferA (haim : AimedIn j hs) (hp : Post F ι O σ0 Ein S Γb env .int r hs res) :
    Post F ι O σ0 Ein S Γb env τ r hs (cleanA j k res) := by
  rcases res with ⟨res, σ1⟩
  cases res with
  | val w =>
    obtain ⟨E₁, L₁, hI₁, hv₁, -, -, hm₁⟩ := hp
    cases hv₁ with
    | int => simp only [cleanA]; exact ⟨haim, E₁, hI₁, by simpa using hm₁⟩
  | abort j' k' =>
    obtain ⟨haim', E₁, hI₁, hm₁⟩ := hp
    by_cases h0 : j' = 0
    · subst h0
      simp only [cleanA]
      split
      · trivial
      · exact ⟨.inl rfl, E₁, hI₁, hm₁⟩
    · have : cleanA j k (.abort j' k', σ1) = (.abort j' k', σ1) := by
        cases j' with
        | zero => exact absurd rfl h0
        | succ _ => rfl
      rw [this]; exact ⟨haim', E₁, hI₁, hm₁⟩
  | susp j' ef vs ls K =>
    obtain ⟨op, X, hos, A, Lw, hc, hop, hcov, haim', hK, hls, hvs, hn, hdw, hdS, hm⟩ := hp
    simp only [cleanA]
    have hK' := FramesOk.cons (σf := σ1) (A := j :: A) (FrameOk.deferA (hid := j) (k := k) (τ := τ)) (Weaker.refl _)
      Agree.self (fun _ h => by simp at h) List.nodup_nil disj_nil_left hK
      (fun a ha => by simp at ha; simp [ha]) (fun a ha => .inl (List.mem_cons_of_mem _ ha))
    simp only [List.nil_append] at hK'
    refine ⟨op, X, hos, j :: A, Lw, hc, hop, hcov, fun a ha => ?_, hK', hls, hvs, hn, hdw, hdS, hm⟩
    rcases List.mem_cons.mp ha with rfl | ha
    · exact haim
    · exact haim' a ha
  | stuck => simp [Post] at hp
  | timeout => simp [cleanA, Post]
  | ended => simp [cleanA, Post]

/-- `{ defer { d }; □ }`: the cleanup runs as the body ends, with a value or unwinding. -/
theorem ret_deferK [WorldOk F O ι.w] (hfl : FlushOk F ι (flushR F O n)) (hE : EvalOk F O n) (hd : Typed F O Γb d .int Γb r) (hR : Ready O hs r)
    (hwf : WF σ0) (hp : Post F ι O σ0 Ein S Γb env τ r hs res) :
    Post F ι O σ0 Ein S Γb env τ r hs (ret F O n hs (.deferK τ env d) res) := by
  rcases res with ⟨res, σ1⟩
  cases res with
  | val v =>
    obtain ⟨E₁, L₁, hI₁, hv₁, hd₁, hdS₁, hm₁⟩ := hp
    simp only [ret]
    have h2 := hE _ _ _ _ _ _ _ _ _ _ _ hd hI₁ hm₁.wf hR
    exact post_after ((hm₁.relabel (E'' := L₁ ++ E₁) (L'' := []) fun x => by mem_iff)) hwf
      (ret_deferV hfl hv₁ Agree.self hv₁.alloc hv₁.nodup hd₁ hdS₁.symm hI₁.disj hI₁.allocS hm₁.wf h2)
  | abort j k =>
    obtain ⟨haim, E₁, hI₁, hm₁⟩ := hp
    simp only [ret]
    exact post_after hm₁ hwf (ret_deferA haim (hE _ _ _ _ _ _ _ _ _ _ _ hd hI₁ hm₁.wf hR))
  | susp j ef vs ls K => simp only [ret]; exact post_frame hp (.deferK hd)
  | stuck => simp [Post] at hp
  | timeout => simp [ret, Post]
  | ended => simp [ret, Post]

/-- Code of type `τ` dropped as an arm unwound to `j`: once its unwinding reaches the barrier, the
arm's goes on. -/
theorem ret_dropK (hfl : FlushOk F ι fl) (haim : AimedIn j hs) (hcov : Covers hs r) (hwf : WF σ0)
    (hp : Post F ι O σ0 Ein S Γ env τ r (.abort .drop d :: hs) res) :
    Post F ι O σ0 Ein S Γ env τ' r hs (dropRet fl τ (.abort j k) d res) := by
  rcases res with ⟨res, σ1⟩
  cases res with
  | val v =>
    obtain ⟨E₁, L₁, hI₁, hv₁, hd₁, hdS₁, hm₁⟩ := hp
    obtain ⟨σ3, hdrop, hfg⟩ := dropF hfl hm₁.wf hv₁
    simp only [ret, dropRet, hdrop, Outcome.res]
    refine hfg.post fun σ4 hd4 => ⟨haim, E₁, hI₁.dropped hd4 hm₁.wf hd₁ hdS₁, ?_⟩
    exact Moves.thenDrop (hm₁.relabel fun x => by mem_iff) hd4 (fun l hl => hI₁.alloc l (by simpa using hl))
      (fun l hl h => hd₁ l h (by simpa using hl)) hwf
  | abort a k' =>
    obtain ⟨haim', E₁, hI₁, hm₁⟩ := hp
    simp only [ret, dropRet]
    split
    · exact ⟨haim, E₁, hI₁, hm₁⟩
    · rename_i hne
      -- A panic in the dropped code's cleanup, as a panic unwinds, ends the program.
      split
      · trivial
      · exact ⟨aimed_pop haim' hne, E₁, hI₁, hm₁⟩
  | susp j' ef vs ls K =>
    simp only [ret, dropRet]
    exact post_frame_abort hp .dropK (fun _ => rfl) (fun a ha => by simp at ha; subst ha; exact haim) hcov
  | stuck => simp [Post] at hp
  | timeout => simp [dropRet, Post]
  | ended => simp [dropRet, Post]

/-- An arm ended without resuming, giving `v`, whose cells `Lv` the continuation cannot reach: the
continuation unwound to its barrier, `v` again; an unwinding past the barrier drops `v` and goes on; a
continuation taken while unwinding keeps `v`. -/
theorem ret_dropKv (hfl : FlushOk F ι fl) (hv : VT F ι σf τ v Lv) (hcov : Covers hs r) (hag : Agree σf σ0 (Lv ++ S))
    (halloc : ∀ l ∈ Lv, σf.mem l ≠ none) (hnd : Lv.Nodup) (hd : Disj Lv Ein) (hSd : Disj S Lv)
    (hSE : Disj S Ein) (hSa : ∀ l ∈ S, σ0.mem l ≠ none) (hwf : WF σ0)
    (hp : Post F ι O σ0 Ein S Γ env τ r (.abort .drop d :: hs) res) :
    Post F ι O σ0 (Lv ++ Ein) S Γ env τ r hs (dropRet fl τ (.val v) d res) := by
  have hLa : ∀ l ∈ Lv, σ0.mem l ≠ none := fun l hl => by
    rw [hag l (List.mem_append.mpr (.inl hl))]; exact halloc l hl
  have hv0 : VT F ι σ0 τ v Lv := hv.frame (hag.mono fun l hl => List.mem_append.mpr (.inl hl))
  rcases res with ⟨res, σ1⟩
  cases res with
  | val w =>
    obtain ⟨E₁, L₁, hI₁, hv₁, hd₁, hdS₁, hm₁⟩ := hp
    obtain ⟨σ3, hdrop, hfg⟩ := dropF hfl hm₁.wf hv₁
    simp only [ret, dropRet, hdrop, Outcome.res]
    obtain ⟨hdE, hdL⟩ := hm₁.apart hwf hLa hd
    have hk1 := hm₁.keeps hwf hLa hd
    have hLa1 : ∀ l ∈ Lv, σ1.mem l ≠ none := fun l hl => by rw [hk1 l hl]; exact hLa l hl
    refine hfg.post fun σ4 hd4 => ⟨E₁, Lv, hI₁.dropped hd4 hm₁.wf hd₁ hdS₁,
      hv0.frame (Agree.trans hk1 (hd4.keeps hm₁.wf hLa1 hdL)), hdE, fun l hl h => hSd l h hl, ?_⟩
    exact (Moves.thenDrop (E₂ := Lv ++ E₁) (L := []) (D := L₁) ((hm₁.widen hLa hd).relabel fun x => by mem_iff) hd4
      (fun l hl => by
        simp only [List.append_nil, List.mem_append] at hl
        rcases hl with hl | hl
        · exact hLa1 l hl
        · exact hI₁.alloc l hl)
      (fun l hl h => by
        simp only [List.append_nil, List.mem_append] at hl
        rcases hl with hl | hl
        · exact hdL l hl h
        · exact hd₁ l h hl) hwf).relabel fun x => by mem_iff
  | abort a k' =>
    obtain ⟨haim', E₁, hI₁, hm₁⟩ := hp
    have hv₁ := hv0.frame (hm₁.keeps hwf hLa hd)
    obtain ⟨hdE, -⟩ := hm₁.apart hwf hLa hd
    simp only [ret, dropRet]
    split
    · exact ⟨E₁, Lv, hI₁, hv₁, hdE, fun l hl h => hSd l h hl,
        (hm₁.widen hLa hd).relabel fun x => by simp only [List.mem_append, List.not_mem_nil, or_false]; grind⟩
    · rename_i hne
      obtain ⟨σ3, hdrop, hfg⟩ := dropF hfl hm₁.wf hv₁
      simp only [hdrop]
      refine hfg.post fun σ4 hd4 => ⟨aimed_pop haim' hne, E₁, hI₁.dropped hd4 hm₁.wf hdE (fun l hl h => hSd l h hl), ?_⟩
      exact Moves.thenDrop ((hm₁.widen hLa hd).relabel fun x => by mem_iff) hd4
        (fun l hl => hI₁.alloc l (by simpa using hl)) (fun l hl h => hdE l h (by simpa using hl)) hwf
  | susp j ef vs ls K =>
    obtain ⟨op, X, hos, A, Lw, hc, hop, -, haim, hK, hls, hvs, hn, hdw, hdS, hm⟩ := hp
    simp only [ret, dropRet]
    obtain ⟨hdX, hdL⟩ := hm.apart hwf hLa hd
    have hLS : ∀ l ∈ Lv ++ S, σ0.mem l ≠ none := fun l hl => by
      rcases List.mem_append.mp hl with h | h
      · exact hLa l h
      · exact hSa l h
    have hK' := FramesOk.cons (A := A.filter (· ≠ d)) (.dropKv (d := d) hv) (Weaker.refl _)
      ((Agree.trans (hag) ((hm.keeps hwf hLS (fun l hl h => by
        rcases List.mem_append.mp hl with hl | hl
        · exact hd l hl h
        · exact hSE l hl h))))) halloc hnd hdX hK
      (fun _ h => by simp at h) (fun a ha => by
        by_cases had : a = d
        · subst had; exact .inr (.inr ⟨.drop, by simp [Kont.push]⟩)
        · exact .inl (List.mem_filter.mpr ⟨ha, by simpa using had⟩))
    refine ⟨op, Lv ++ X, hos, A.filter (· ≠ d), Lw, hc.of_cons_drop, hop, hcov, fun a ha => ?_, hK', hls, hvs, hn, ?_,
      hdS, ?_⟩
    · obtain ⟨ha, hne⟩ := List.mem_filter.mp ha
      exact aimed_pop (haim a ha) (by simpa using hne)
    · intro l hl h
      simp only [List.mem_append] at h
      rcases h with (h | h) | h
      · exact hdL l h hl
      · exact hdw l hl (by simp [h])
      · exact hdw l hl (by simp [h])
    · exact (hm.widen hLa hd).relabel fun x => by simp only [List.mem_append, List.append_assoc]
  | stuck => simp [Post] at hp
  | timeout => simp [dropRet, Post]
  | ended => simp [dropRet, Post]

/-! ## Calls -/

/-- Places lent to a call whose callee's innermost region is the caller's `k`th: each of a type of the
callee's `k` regions further out. -/
theorem refs_lower {d : Fn} {hos : List Hole}
    (hts : hos.map (fun h => (h.mode, h.ty)) = d.refs.map (fun p => (p.2.1, p.2.2.shiftBy k))) :
    d.refs.map Prod.snd = hos.map (fun h => (h.mode, h.ty.lowerBy k)) := by
  have := congrArg (List.map fun p : Mode × Ty => (p.1, p.2.lowerBy k)) hts
  simpa [List.map_map, Function.comp_def] using this.symm

theorem holes_shift {d : Fn} {hos : List Hole}
    (hts : hos.map (fun h => (h.mode, h.ty)) = d.refs.map (fun p => (p.2.1, p.2.2.shiftBy k))) :
    ∀ h ∈ hos, (h.ty.lowerBy k).shiftBy k = h.ty := fun h hh => by
  have := List.mem_map_of_mem (f := fun h : Hole => (h.mode, h.ty)) hh
  rw [hts] at this
  obtain ⟨p, -, hp⟩ := List.mem_map.mp this
  rw [← (Prod.mk.inj hp).2, Ty.lowerBy_shiftBy]

/-- A call's body ended: the parameters it owns are dropped, and the caller's variables are as they
were, but for the places it lent `mut`, whose trees are the callee's; a continuation taken in the
callee keeps the caller as it was. -/
theorem ret_callK (hfl : FlushOk F (ι.drop k) (flushR F O n)) {d : Fn} {hos : List Hole} {cells : Env}
    (hrow : ∀ l ∈ d.row, l ∈ r) (hI₁ : Inv F ι σf Γ₁ env E₁ S) (hholes : ∀ h ∈ hos, HoleOk F ι σf Γ₁ env h)
    (hpw : hos.Pairwise Apart) (hts : hos.map (fun h => (h.mode, h.ty)) = d.refs.map (fun p => (p.2.1, p.2.2.shiftBy k)))
    (hkeys : ((d.owns.map Prod.fst) ++ (d.refs.map Prod.fst)).Nodup) (hoc : ∀ o ∈ d.owns, o.2.complete = true)
    (hbody : Typed F O (fnCtx d) d.body d.ret Γ'' d.row) (hcells : cells.map Prod.fst = d.owns.map Prod.fst)
    (hR : Ready O hs r) (hwf : WF σ0)
    (hag : Agree σf σ0 (E₁.filter (· ∉ mutCells (olds hos)) ++ S))
    (hdX : Disj (E₁.filter (· ∉ mutCells (olds hos))) Ein) (hSa : ∀ l ∈ S, σ0.mem l ≠ none)
    (hdS : Disj S (E₁.filter (· ∉ mutCells (olds hos)) ++ Ein))
    (hp : Post F (ι.drop k) O σ0 Ein (roCells (olds hos)) Γ'' (cells ++ (d.refs.map Prod.fst).zip (hos.map Hole.loc))
      d.ret d.row hs res) :
    Post F ι O σ0 (E₁.filter (· ∉ mutCells (olds hos)) ++ Ein) S Γ₁ env (d.ret.shiftBy k) r hs
      (ret F O n hs (.callK ((d.owns.map Prod.snd).zip (cells.map Prod.snd))) res) := by
  have hts' := refs_lower hts
  have hshift := holes_shift hts
  generalize hX : E₁.filter (· ∉ mutCells (olds hos)) = X at hag hdX hdS ⊢
  have hXE : ∀ l ∈ X, l ∈ E₁ := fun l hl => (mem_keep.mp (hX ▸ hl)).1
  have hXM : ∀ l ∈ X, l ∉ mutCells (olds hos) := fun l hl => (mem_keep.mp (hX ▸ hl)).2
  have hXa : ∀ l ∈ X, σ0.mem l ≠ none := fun l hl => by
    rw [hag l (List.mem_append.mpr (.inl hl))]; exact hI₁.alloc l (hXE l hl)
  have hXS : ∀ l ∈ X ++ S, σ0.mem l ≠ none := fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · exact hXa l h
    · exact hSa l h
  have hXSd : Disj (X ++ S) Ein := fun l hl h => by
    rcases List.mem_append.mp hl with hl | hl
    · exact hdX l hl h
    · exact hdS l hl (List.mem_append.mpr (.inr h))
  -- What the call leaves, with a value or a failure: the callee's owned parameters dropped, and the
  -- caller's variables as they were, but for the trees it lent `mut`.
  have key : ∀ σ3 Ec' Lw, Inv F (ι.drop k) σ3 Γ'' (cells ++ (d.refs.map Prod.fst).zip (hos.map Hole.loc)) Ec'
      (roCells (olds hos)) → Disj Lw Ec' → Moves σ0 Ein σ3 Ec' Lw →
      ∃ σ4, dropCells σ3 ((d.owns.map Prod.snd).zip (cells.map Prod.snd)) = some σ4 ∧ ∃ Ea,
        FlushGives (flushR F O n (cellsKonts σ3 ((d.owns.map Prod.snd).zip (cells.map Prod.snd))) σ4) σ3 Ea ∧
        ∀ σ5, Dropped σ3 Ea σ5 → ∃ E'', Inv F ι σ5 Γ₁ env E'' S ∧ Agree σ3 σ5 Lw ∧ Disj Lw E'' ∧ Disj Lw S ∧
          Moves σ0 (X ++ Ein) σ5 E'' Lw := by
    intro σ3 Ec' Lw hI₃ hdw hm₃
    have hk₃ := hI₃.keys
    have hsh : shape Γ'' = ownCtx d.owns ++ refCtx d.refs := by
      rw [typed_shape hbody (by simpa [fnCtx, List.map_append, List.map_map, Function.comp_def] using hkeys),
        shape_fnCtx]
    obtain ⟨Γa, rfl, hΓa⟩ := shape_split (ownCtx d.owns) hsh (refCtx_refs d.refs)
    have hla : Γa.length = cells.length := by
      rw [← shape_length, hΓa]; simpa [ownCtx] using (congrArg List.length hcells).symm
    obtain ⟨Ea, Sa, Er, Sr, hfa, hfr, rfl, hSab⟩ := hI₃.foot.split hla
    obtain ⟨ps, hps, hlt, rfl, rfl⟩ := foot_refs_lower hts' hfr
    have hnd := nodup_append_disj.mp hI₃.nodup
    obtain ⟨rfl, σ4, hdrop, hfg⟩ := dropCellsF hfl hfa hΓa hnd.1 hm₃.wf hoc
    refine ⟨σ4, hdrop, Ea, hfg, fun σ5 hd5 => ?_⟩
    have hkeep4 := hd5.keep hm₃.wf
    obtain ⟨hXSc, hXSw⟩ := hm₃.apart hwf hXS hXSd
    have hkeep3 := hm₃.keeps hwf hXS hXSd
    have hag4 : Agree σf σ5 (X ++ S) := Agree.trans (Agree.trans hag hkeep3)
      (hd5.keeps hm₃.wf (fun l hl => by rw [hkeep3 l hl]; exact hXS l hl)
        fun l hl h => hXSc l hl (List.mem_append.mpr (.inl h)))
    obtain ⟨E'', hI₄, hmem⟩ := caller_rebuild (σ' := σ5) hI₁ hholes hpw hps
      (fun p hp _ => by
        have := ((hlt p hp).frame (hd5.keeps hm₃.wf (fun l hl => (hlt p hp).alloc l hl) fun l hl h =>
          (mem_cells_of hp hl).elim (fun hM => hnd.2.2 l h hM)
            (fun hR => hI₃.disj l (by rw [hSab]; simp [hR]) (List.mem_append.mpr (.inl h))))).shiftk
        rwa [hshift p.1 (by rw [← hps]; exact List.mem_map_of_mem hp)] at this)
      hnd.2.1 (by rw [hX]; exact hag4)
      (by rw [hX]; exact fun l hl h => hXSc l (List.mem_append.mpr (.inl hl)) (List.mem_append.mpr (.inr h)))
      (fun l hl h => hXSc l (List.mem_append.mpr (.inr hl)) (List.mem_append.mpr (.inr h)))
    rw [hX] at hmem
    have m3 := (hm₃.widen hXa hdX).relabel (E'' := X ++ mutCells ps ++ Lw ++ Ea) (L'' := []) fun x => by
      simp only [List.mem_append, List.not_mem_nil, or_false]; grind
    have m4 : Moves σ3 (X ++ mutCells ps ++ Lw ++ Ea) σ5 (X ++ mutCells ps ++ Lw) [] :=
      (hd5.widen (X := X ++ mutCells ps ++ Lw)
        (fun l hl => (m3.alloc l).mpr (.inr (.inl (List.mem_append.mpr (.inl hl))))) (by
          intro l hl hl'
          simp only [List.mem_append] at hl
          rcases hl with (h | h) | h
          · exact hXSc l (List.mem_append.mpr (.inl h)) (List.mem_append.mpr (.inl hl'))
          · exact hnd.2.2 l hl' h
          · exact hdw l h (List.mem_append.mpr (.inl hl')))).relabel fun x => by simp
    refine ⟨E'', hI₄, hd5.keeps hm₃.wf (fun l hl => (hm₃.alloc l).mpr (.inr (.inr hl)))
        (fun l hl h => hdw l hl (List.mem_append.mpr (.inl h))),
      fun l hl hl' => ?_, fun l hl hS => hXSw l (List.mem_append.mpr (.inr hS)) hl, ?_⟩
    · rcases (hmem l).mp hl' with h | h
      · exact hXSw l (List.mem_append.mpr (.inl h)) hl
      · exact hdw l hl (List.mem_append.mpr (.inr h))
    · exact (m3.trans m4 disj_nil_left hwf).relabel fun x => by
        simp only [List.mem_append, hmem x, List.not_mem_nil, or_false, List.append_nil] <;> grind
  rcases res with ⟨res, σ3⟩
  cases res with
  | val w =>
    obtain ⟨Ec', Lw, hI₃, hvw, hdw, -, hm₃⟩ := hp
    obtain ⟨σ4, hdrop, Ea, hfg, hk⟩ := key σ3 Ec' Lw hI₃ hdw hm₃
    simp only [ret, hdrop]
    refine hfg.post fun σ5 hd5 => ?_
    obtain ⟨E'', hI₄, hag', hdE, hdS', hm⟩ := hk σ5 hd5
    exact ⟨E'', Lw, hI₄, hvw.shiftk.frame hag', hdE, hdS', hm⟩
  | abort i k =>
    obtain ⟨haim, Ec', hI₃, hm₃⟩ := hp
    obtain ⟨σ4, hdrop, Ea, hfg, hk⟩ := key σ3 Ec' [] hI₃ disj_nil_left hm₃
    simp only [ret, hdrop]
    refine hfg.post fun σ5 hd5 => ?_
    obtain ⟨E'', hI₄, -, -, -, hm⟩ := hk σ5 hd5
    exact ⟨haim, E'', hI₄, hm⟩
  | susp j ef vs ls K =>
    obtain ⟨op, X', hos', A, Lv, hc, hop, hcov, haim, hK, hls, hvs, hn, hdv, hdSv, hm⟩ := hp
    simp only [ret]
    obtain ⟨hXc, hXv⟩ := hm.apart hwf hXa hdX
    have hK' := FramesOk.cons (σf := σf) (A := A) (.callK hrow hI₁ hholes hpw hts hkeys hoc hbody hcells)
      (Weaker.refl _) (by rw [hX]; exact Agree.trans hag (hm.keeps hwf hXS hXSd))
      (fun l hl => hI₁.alloc l (hXE l (hX ▸ hl))) (hI₁.nodup.filter _)
      (by rw [hX]; exact hXc) hK (fun _ h => by simp at h) (fun a ha => .inl ha)
    rw [hX] at hK'
    refine ⟨op, X ++ X', hos', A, Lv, hc, hop, hR.2, haim, hK', hls, hvs.rfree_iota op.owns_rfree, hn, ?_, ?_, ?_⟩
    · intro l hl h
      simp only [List.mem_append] at h
      rcases h with (h | h) | h
      · exact hXv l h hl
      · exact hdv l hl (by simp [h])
      · exact hdv l hl (by simp [h])
    · exact fun l hl h => (hm.apart hwf hSa (fun l hl h => hdS l hl (List.mem_append.mpr (.inr h)))).2 l h hl
    · exact (hm.widen hXa hdX).relabel fun x => by simp only [List.mem_append, List.append_assoc]
  | stuck => simp [Post] at hp
  | timeout => simp [ret, Post]
  | ended => simp [ret, Post]

/-! ## Expressions -/

theorem post_val (hI : Inv F ι σ' Γ' env E' S) (hv : VT F ι σ' τ v L) (hd : Disj L E') (hdS : Disj L S)
    (hm : Moves σ E σ' E' L) : Post F ι O σ E S Γ' env τ r hs (.val v, σ') :=
  ⟨E', L, hI, hv, hd, hdS, hm⟩

/-- Naming a handler changes no cell. -/
theorem Moves.freshen (hwf : WF σ) (hE : ∀ l ∈ E, σ.mem l ≠ none) : Moves σ E σ.fresh.2 E [] :=
  have h := Moves.refl (σ := σ) hwf hE
  ⟨h.within, h.next, h.wf, h.frame, h.alloc, h.rt, fun _ _ _ hx h0 => by simp only [Store.fresh_rt] at hx; rw [h0] at hx; cases hx⟩

theorem lookup_none_of_keys {α : Type} {Γ : List (Var × α)} : x ∉ Γ.map Prod.fst → lookup x Γ = none := by
  induction Γ with
  | nil => intro; rfl
  | cons p Γ ih =>
    obtain ⟨y, t⟩ := p
    intro h
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [lookup, h.1, ↓reduceIte]
    exact ih h.2

theorem Inv.fresh (h : Inv F ι σ Γ env E S) : Inv F ι σ.fresh.2 Γ env E S :=
  ⟨h.foot.frame <| Agree.of' fun _ _ => rfl, h.nodup, h.disj, h.keys⟩

theorem find_mem : find l hs = some f → f ∈ hs := by
  induction hs with
  | nil => simp [find]
  | cons g hs ih =>
    intro h
    simp only [find] at h
    split at h
    · simp at h; subst h; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih h)

theorem find_handles : find l hs = some f → f.handles l = true := by
  induction hs with
  | nil => simp [find]
  | cons g hs ih =>
    intro h
    simp only [find] at h
    split at h
    · simp at h; subst h; assumption
    · exact ih h

/-- An unwinding handler of an operation is for one that takes an integer and lends nothing. -/
theorem find_abort_op (hR : HSOk O hs) (hf : find (.eff e) hs = some (.abort l i)) :
    ∃ op, O[e]? = some op ∧ op.owns = [.int] ∧ op.refs = [] := by
  induction hR with
  | nil => simp [find] at hf
  | abort hl _ ih =>
    simp only [find] at hf
    split at hf
    · rename_i hh
      simp only [Option.some.injEq, Frame.abort.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      simp only [Frame.handles, beq_iff_eq] at hh
      exact hl e hh
    · exact ih hf
  | capture _ _ ih =>
    simp only [find] at hf
    split at hf
    · simp at hf
    · exact ih hf
  | cancel _ ih =>
    simp only [find] at hf
    split at hf
    · simp at hf
    · exact ih hf

theorem allocAll_fst : ∀ (σ : Store) (xs : List (Var × Val)), (allocAll σ xs).1.map Prod.fst = xs.map Prod.fst
  | _, [] => rfl
  | σ, (x, v) :: rest => by simp [allocAll, allocAll_fst _ rest]

/-- A pair: its two values, each put in a fresh cell, which the pair owns with what they own. -/
theorem pair_ok (ha : AtomTy Γ a A Γ₁) (hb : AtomTy Γ₁ b B Γ₂) (hI : Inv F ι σ Γ env E S) (hwf : WF σ) :
    Post F ι O σ E S Γ₂ env (.pair A B) r hs (evalS F O n hs σ env (.pair a b)) := by
  obtain ⟨vs, σ2a, E₂, Ls, hevs, hI₂, hvs, hLn, hdL, hdLS, hm₂⟩ := atoms_ok (.cons ha (.cons hb .nil)) hI hwf
  cases hvs with
  | @cons _ v0 Lv _ _ _ hv hrest =>
  cases hrest with
  | @cons _ w0 Lw _ _ _ hw hnil =>
  cases hnil
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hLn hdL hdLS hm₂
  -- The atoms, one after the other.
  cases hea : evalAtom σ env a with
  | none => simp [evalAtoms, hea] at hevs
  | some p =>
    obtain ⟨v, σ1⟩ := p
    cases heb : evalAtom σ1 env b with
    | none => simp [evalAtoms, hea, heb] at hevs
    | some q =>
      obtain ⟨w, σ2⟩ := q
      simp only [evalAtoms, hea, heb, Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hevs
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hevs
      have hwf2 := hm₂.wf
      let σ3 := (σ2.alloc v).2
      let σ4 := (σ3.alloc w).2
      have hn3 : σ3.next = σ2.next + 1 := rfl
      -- The cells allocated before, and the two new ones.
      have hold3 : ∀ z, σ2.mem z ≠ none → σ3.mem z = σ2.mem z := fun z hz => by
        simp only [σ3, Store.alloc]; rw [if_neg (fun e => Nat.lt_irrefl _ (e ▸ hwf2 z hz))]
      have hold4 : ∀ z, σ2.mem z ≠ none → σ4.mem z = σ2.mem z := fun z hz => by
        simp only [σ4, Store.alloc]
        rw [if_neg (fun e => by have := hwf2 z hz; simp [σ3, Store.alloc] at e; omega)]
        exact hold3 z hz
      have hb4 : σ4.mem σ2.next = some v := by
        simp only [σ4, σ3, Store.alloc]; simp
      have hc4 : σ4.mem (σ2.next + 1) = some w := by
        simp only [σ4, σ3, Store.alloc]; simp
      have hfresh : ∀ z, σ2.mem z ≠ none → z ≠ σ2.next ∧ z ≠ σ2.next + 1 := fun z hz =>
        ⟨fun e => Nat.lt_irrefl _ (e ▸ hwf2 z hz), fun e => by have := hwf2 z hz; omega⟩
      have hLva := hv.alloc
      have hLwa := hw.alloc
      have hLv1 : LT F ι σ4 σ2.next A (σ2.next :: Lv) :=
        LT.of_contents hb4 (hv.frame <| Agree.of' fun z hz => hold4 z (hLva z hz)) (fun h => (hfresh _ (hLva _ h)).1 rfl)
      have hLw1 : LT F ι σ4 (σ2.next + 1) B ((σ2.next + 1) :: Lw) :=
        LT.of_contents hc4 (hw.frame <| Agree.of' fun z hz => hold4 z (hLwa z hz)) (fun h => (hfresh _ (hLwa _ h)).2 rfl)
      obtain ⟨hnv, hnw, hdvw⟩ := nodup_append_disj.mp hLn
      have hdisj : ∀ x ∈ σ2.next :: Lv, x ∉ (σ2.next + 1) :: Lw := by
        intro x hx hx'
        rcases List.mem_cons.mp hx with rfl | hx <;> rcases List.mem_cons.mp hx' with e | hx'
        · omega
        · exact (hfresh _ (hLwa _ hx')).1 rfl
        · exact (hfresh _ (hLva _ hx)).2 e
        · exact hdvw x hx hx'
      simp only [evalS, hea, heb]
      refine post_val (L := (σ2.next :: Lv) ++ ((σ2.next + 1) :: Lw)) (E' := E₂) ?_ (.pair hLv1 hLw1 hdisj hv.complete hw.complete) ?_ ?_ ?_
      · exact ⟨hI₂.foot.frame <| Agree.of' fun z hz => hold4 z (hI₂.foot.alloc z (List.mem_append.mp hz)), hI₂.nodup,
          hI₂.disj, hI₂.keys⟩
      · intro x hx hx'
        have hxa := hI₂.alloc x hx'
        simp only [List.mem_append, List.mem_cons] at hx
        rcases hx with (rfl | hx) | (rfl | hx)
        · exact (hfresh _ hxa).1 rfl
        · exact hdL x (List.mem_append.mpr (.inl hx)) hx'
        · exact (hfresh _ hxa).2 rfl
        · exact hdL x (List.mem_append.mpr (.inr hx)) hx'
      · intro x hx hx'
        have hxa := hI₂.allocS x hx'
        simp only [List.mem_append, List.mem_cons] at hx
        rcases hx with (rfl | hx) | (rfl | hx)
        · exact (hfresh _ hxa).1 rfl
        · exact hdLS x (List.mem_append.mpr (.inl hx)) hx'
        · exact (hfresh _ hxa).2 rfl
        · exact hdLS x (List.mem_append.mpr (.inr hx)) hx'
      · have m3 := hm₂.trans (Moves.allocate (v := v) hwf2 hI₂.alloc) hdL hwf
        have m4 := m3.trans (Moves.allocate (σ := σ3) (v := w) hwf2.alloc (fun z hz => by
            rw [hold3 z (hI₂.alloc z hz)]; exact hI₂.alloc z hz))
          (fun x hx hx' => by
            rcases List.mem_append.mp hx with hx | hx
            · exact hdL x hx hx'
            · simp at hx; subst hx; exact (hfresh _ (hI₂.alloc _ hx')).1 rfl) hwf
        exact m4.relabel fun x => by
          simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
            show (σ2.alloc v).1 = σ2.next from rfl, show (σ3.alloc w).1 = σ3.next from rfl, hn3]
          grind

/-- What a step gives, said of the cells it started with in another order. -/
theorem post_relabel {r : Res × Store} (hwf : WF σ) (hE : ∀ l ∈ E, σ.mem l ≠ none) (hEE : ∀ x, x ∈ E₁ ↔ x ∈ E)
    (h : Post F ι O σ E₁ S Γ' env τ rw hs r) : Post F ι O σ E S Γ' env τ rw hs r :=
  post_after ((Moves.refl hwf hE).relabel fun x => by simp [hEE]) hwf h

/-- The tree at `a` reaches the tree at `l`: it is that tree and the cells `P`; and given a new tree
at `l`, in a store that kept `P`, it is that tree and `P` again. -/
structure Reach (F : List Fn) (ι : Iota) (σ : Store) (a : Nat) (τr : Ty) (P : List Nat) (l : Nat) (τ : Ty) :
    Prop where
  split : ∀ {Lr}, LT F ι σ a τr Lr → ∃ Rt, LT F ι σ l τ Rt ∧ Lr.Perm (P ++ Rt)
  join : P.Nodup → ∀ W, ι.w.le W → ∀ σ' R', Agree σ σ' P → LT F (ι.inW W) σ' l τ R' → Disj P R' →
    ∃ L', LT F (ι.inW W) σ' a τr L' ∧ L'.Perm (P ++ R')

theorem Path.reach (hp : Path F ι σ a τr P l τ) : Reach F ι σ a τr P l τ :=
  ⟨fun h => path_split hp h, fun hn _ hW _ _ hag h hd =>
    let ⟨L', h1, h2, _⟩ := path_join (hp.mono hW) hn hag h hd; ⟨L', h1, h2⟩⟩

/-- A `readonly` borrow held for the scope of `body`: what the place is rooted at is only read
while it lives. -/
theorem lend_ro_all [WorldOk F O ι.w] (hE : EvalOk F O n) (hx : lookup x Γ = none) (ha : lookup y env = some a)
    (hsl : lookup y Γ = some s) (hLr : LT F ι σ a τr Lr) (hpath : Reach F ι σ a τr P l τ) (hso : SlotOk F ι σ s a Lr)
    (hys : y ∈ ys) (hlive : ∀ y' ∈ ys, ∀ τ', lookup y' Γ ≠ some (.own τ' false))
    (hb : Typed F O ((x, .ref .ro τ) :: freeze Γ ys) body τb ((x, .ref .ro τ) :: Γb) r)
    (hI : Inv F ι σ Γ env E S) (hwf : WF σ) (hR : Ready O hs r) :
    Post F ι O σ E S (thaw Γ ys Γb) env τb r hs (ret F O n hs .lendK (eval F O n hs σ ((x, l) :: env) body)) := by
  obtain ⟨Rt, hRt, hLrPR⟩ := hpath.split hLr
  have hxk : x ∉ (freeze Γ ys).map Prod.fst := by rw [freeze_keys]; exact lookup_none_keys hx
  have hwb := typed_weaker hb (List.nodup_cons.mpr ⟨hxk, by rw [freeze_keys]; exact hI.keys⟩)
  cases hwb with
  | cons _ hwb =>
  obtain ⟨Eb, Sb, Fz, hfb, hEp, hS, hent, hthaw⟩ := hI.foot.handle (ys := ys) hI.keys hlive
  obtain ⟨hEbn, hFzn, hdEF⟩ := nodup_append_disj.mp (hEp.nodup_iff.mp hI.nodup)
  have hEb : ∀ l ∈ Eb, l ∈ E := fun l h => hEp.mem_iff.mpr (List.mem_append.mpr (.inl h))
  have hFz : ∀ l ∈ Fz, l ∈ E := fun l h => hEp.mem_iff.mpr (List.mem_append.mpr (.inr h))
  -- The borrow's tree is among the root's: frozen, or read already.
  have hRin : ∀ l ∈ Rt, l ∈ Fz ∨ l ∈ S := fun l hl =>
    hent y s a Lr ⟨hsl, ha, hso⟩ hys l (hLrPR.mem_iff.mpr (List.mem_append.mpr (.inr hl)))
  have hSin : ∀ l ∈ Rt ++ Sb, l ∈ Fz ∨ l ∈ S := fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · exact hRin l h
    · exact List.mem_append.mp (hS.mem_iff.mp h)
  have hIb : Inv F ι σ ((x, .ref .ro τ) :: freeze Γ ys) ((x, l) :: env) Eb (Rt ++ Sb) := by
    refine ⟨by simpa [addE, addS, Slot.excl, exclPart, sharedPart, Slot.shell, Ty.shell, Bool.false_eq_true] using Foot.cons (s := .ref .ro τ) (x := x) hRt hfb, hEbn, ?_,
      List.nodup_cons.mpr ⟨hxk, by rw [freeze_keys]; exact hI.keys⟩⟩
    intro l hl hl'
    rcases hSin l hl with h | h
    · exact hdEF l hl' h
    · exact hI.disj l h (hEb l hl')
  have hkb : Γb.map Prod.fst = Γ.map Prod.fst := by
    have := typed_keys hb
    simp only [List.map_cons, List.cons.injEq] at this
    rw [this.2, freeze_keys]
  have hre : ∀ W, ι.w.le W → ∀ σ1 Eb', Agree σ σ1 (Fz ++ S) → Disj Fz Eb' →
      Inv F (ι.inW W) σ1 ((x, .ref .ro τ) :: Γb) ((x, l) :: env) Eb' (Rt ++ Sb) →
      ∃ E', Inv F (ι.inW W) σ1 (thaw Γ ys Γb) env E' S ∧ ∀ z, z ∈ E' ↔ z ∈ Eb' ∨ z ∈ Fz := by
    intro W hW σ1 Eb' hag hdX hI'
    obtain ⟨L', Et, St, hL', hft, hEt, hSt⟩ := hI'.foot.uncons
    simp only [addE, addS, Slot.excl, Bool.false_eq_true, ↓reduceIte, exclPart, sharedPart, Slot.shell, Ty.shell] at hEt hSt
    -- The borrow's tree is as it was: shared, it was not changed.
    have hRR := ((hRt.frame (hag.mono fun l hl => List.mem_append.mpr (hRin l hl))).mono hW).det hL'
    subst hRR
    obtain rfl := List.append_cancel_left hSt
    subst hEt
    obtain ⟨E', hf', hp⟩ := hthaw W hW σ1 Γb Eb' hft hwb hag
    refine ⟨E', ⟨hf', hp.nodup_iff.mpr (nodup_append_disj.mpr ⟨hI'.nodup, hFzn,
        fun l h h' => hdX l h' h⟩), ?_, by rw [thaw_keys hkb]; exact hI.keys⟩,
      fun z => by rw [hp.mem_iff, List.mem_append]⟩
    intro l hl hl'
    rcases List.mem_append.mp (hp.mem_iff.mp hl') with h | h
    · exact hI'.disj l (List.mem_append.mpr (.inr (hS.mem_iff.mpr (List.mem_append.mpr (.inr hl))))) h
    · exact hI.disj l hl (hFz l h)
  have hSS : ∀ l ∈ S, l ∈ Rt ++ Sb := fun l hl =>
    List.mem_append.mpr (.inr (hS.mem_iff.mpr (List.mem_append.mpr (.inr hl))))
  refine post_relabel (E₁ := Fz ++ Eb) hwf hI.alloc (fun z => by
    rw [hEp.mem_iff]; simp only [List.mem_append]; exact Or.comm) ?_
  exact ret_lendK hSin hSS hre hR.2 hwf Agree.self (fun l h => hI.alloc l (hFz l h)) hFzn
    (fun l h h' => hdEF l h' h) hI.allocS
    (fun l hl h => by
      rcases List.mem_append.mp h with h | h
      · exact hI.disj l hl (hFz l h)
      · exact hI.disj l hl (hEb l h))
    (hE _ _ _ _ _ _ _ _ _ _ _ hb hIb hwf hR)

theorem lend_ro_core [WorldOk F O ι.w] (hE : EvalOk F O n) (hx : lookup x Γ = none) (ha : lookup y env = some a)
    (hsl : lookup y Γ = some s) (hLr : LT F ι σ a τr Lr) (hpath : Reach F ι σ a τr P l τ) (hso : SlotOk F ι σ s a Lr)
    (hlive : ∀ τ', lookup y Γ ≠ some (.own τ' false))
    (hb : Typed F O ((x, .ref .ro τ) :: lendCtx .ro Γ y) body τb ((x, .ref .ro τ) :: Γb) r)
    (hI : Inv F ι σ Γ env E S) (hwf : WF σ) (hR : Ready O hs r) :
    Post F ι O σ E S (thaw Γ [y] Γb) env τb r hs (ret F O n hs .lendK (eval F O n hs σ ((x, l) :: env) body)) :=
  lend_ro_all hE hx ha hsl hLr hpath hso (List.mem_singleton_self y)
    (fun y' hy' => by simp only [List.mem_singleton] at hy'; subst hy'; exact hlive) hb hI hwf hR

/-- A `mut` borrow of the tree at `l`, on a path from `y`, one of the variables `ys` hidden from
`body` while it runs: the borrow owns the tree, the others keep theirs out of reach, and once it
ends, each owns again what it had, `y` its path to `l` and what the borrow left there. -/
theorem lend_mut_all [WorldOk F O ι.w] (hE : EvalOk F O n) (hx : lookup x Γ = none) (ha : lookup y env = some a)
    (hsl : lookup y Γ = some s) (hLr : LT F ι σ a τr Lr) (hpath : Reach F ι σ a τr P l τ)
    (hso : SlotOk F ι σ s a Lr)
    (hslot : ∀ ι' σ' L', LT F ι' σ' a τr L' → SlotOk F ι' σ' s a L') (hτ : τ.shell = false)
    (hys : y ∈ ys) (hn : ys.Nodup) (htr : Trees F ι σ Γ env ys H)
    (hb : Typed F O ((x, .ref .mut τ) :: hideAll Γ ys) body τb ((x, .ref .mut τ) :: Γb) r)
    (hI : Inv F ι σ Γ env E S) (hwf : WF σ) (hR : Ready O hs r) :
    Post F ι O σ E S (unhideAll Γ ys Γb) env τb r hs (ret F O n hs .lendK (eval F O n hs σ ((x, l) :: env) body)) := by
  obtain ⟨Rt, hRt, hLrp⟩ := hpath.split hLr
  have hxk : x ∉ (hideAll Γ ys).map Prod.fst := by rw [hideAll_keys]; exact lookup_none_keys hx
  have hwb := typed_weaker hb (List.nodup_cons.mpr ⟨hxk, by rw [hideAll_keys]; exact hI.keys⟩)
  cases hwb with
  | cons _ hwb =>
  obtain ⟨Eh, hfh, hEh, hrebuild⟩ := hI.foot.hiddenAll hI.keys htr hn
  obtain ⟨Hr, hHr, hsplit⟩ := htr.split hys hn ⟨hsl, ha, hso⟩
  have hxs : (Slot.ref .mut τ).shell = false := by simp [Slot.shell_ref, hτ]
  -- `E` is the borrowed tree, the path to it, the others' trees and the rest.
  have hEp : E.Perm (Rt ++ Eh ++ (P ++ Hr)) := hEh.trans (by
    refine ((hHr.append_right Eh).trans ?_)
    refine (((hLrp.append_right Hr).append_right Eh)).trans ?_
    exact List.perm_iff_count.mpr fun z => by simp only [List.count_append]; omega)
  have hEn := hEp.nodup_iff.mp hI.nodup
  obtain ⟨hBn, hXn, hdBX⟩ := nodup_append_disj.mp hEn
  obtain ⟨hRn, hEhn, hdREh⟩ := nodup_append_disj.mp hBn
  have hmemE : ∀ z, z ∈ E ↔ z ∈ Rt ++ Eh ++ (P ++ Hr) := fun z => hEp.mem_iff
  have hXE : ∀ z ∈ P ++ Hr, z ∈ E := fun z h => (hmemE z).mpr (List.mem_append.mpr (.inr h))
  have hBE : ∀ z ∈ Rt ++ Eh, z ∈ E := fun z h => (hmemE z).mpr (List.mem_append.mpr (.inl h))
  have hXa : ∀ z ∈ P ++ Hr, σ.mem z ≠ none := fun z h => hI.alloc z (hXE z h)
  -- The borrow's activation: it owns the place's tree; the roots are out of reach.
  have hIb : Inv F ι σ ((x, .ref .mut τ) :: hideAll Γ ys) ((x, l) :: env) (Rt ++ Eh) S := by
    refine ⟨by simpa [addE, addS, Slot.excl, exclPart_plain hxs, sharedPart_plain hxs] using
        Foot.cons (s := .ref .mut τ) (x := x) hRt hfh, hBn, fun z hz h => hI.disj z hz (hBE z h),
      List.nodup_cons.mpr ⟨hxk, by rw [hideAll_keys]; exact hI.keys⟩⟩
  have hkb : Γb.map Prod.fst = Γ.map Prod.fst := by
    have := typed_keys hb
    simp only [List.map_cons, List.cons.injEq] at this
    rw [this.2, hideAll_keys]
  have hre : ∀ W, ι.w.le W → ∀ σ1 Eb', Agree σ σ1 ((P ++ Hr) ++ S) → Disj (P ++ Hr) Eb' →
      Inv F (ι.inW W) σ1 ((x, .ref .mut τ) :: Γb) ((x, l) :: env) Eb' S →
      ∃ E', Inv F (ι.inW W) σ1 (unhideAll Γ ys Γb) env E' S ∧ ∀ z, z ∈ E' ↔ z ∈ Eb' ∨ z ∈ P ++ Hr := by
    intro W hW σ1 Eb' hag hdX hI'
    obtain ⟨R', Et, St, hR', hft, hEt, hSt⟩ := hI'.foot.uncons
    simp only [addE, addS, Slot.excl, ↓reduceIte, exclPart_plain hxs, sharedPart_plain hxs, List.nil_append] at hEt hSt
    subst hEt
    rw [← hSt] at hft
    have hagP : Agree σ σ1 P := (hag.mono fun z hz => by simp [hz])
    have hagH : Agree σ σ1 Hr := (hag.mono fun z hz => by simp [hz])
    have hagS : Agree σ σ1 S := (hag.mono fun z hz => List.mem_append.mpr (.inr hz))
    have hPnew : ∀ z ∈ P, z ∉ R' ++ Et := fun z hz h => hdX z (by simp [hz]) h
    have hPn : P.Nodup := (nodup_append_disj.mp hXn).1
    obtain ⟨L', hLT', hL'p⟩ := hpath.join hPn W hW σ1 _ hagP hR' (fun z hz h => hPnew z hz (by simp [h]))
    obtain ⟨H', ht', hH'⟩ := hsplit W hW σ1 _ hagH (hslot _ σ1 _ hLT')
    obtain ⟨E', hf', hp'⟩ := hrebuild W hW σ1 Γb Et H' hft hwb hagS ht'
    have hp'' : E'.Perm ((R' ++ Et) ++ (P ++ Hr)) := hp'.trans (by
      refine (hH'.append_right Et).trans ?_
      refine (((hL'p.append_right Hr).append_right Et)).trans ?_
      exact List.perm_iff_count.mpr fun z => by simp only [List.count_append]; omega)
    refine ⟨E', ⟨hf', hp''.nodup_iff.mpr (nodup_append_disj.mpr ⟨hI'.nodup, hXn, fun z h h' => hdX z h' h⟩),
      ?_, by rw [unhideAll_keys hkb]; exact hI.keys⟩, fun z => by rw [hp''.mem_iff, List.mem_append]⟩
    intro z hz hz'
    rcases List.mem_append.mp (hp''.mem_iff.mp hz') with h | h
    · exact hI'.disj z hz h
    · exact hI.disj z hz (hXE z h)
  refine post_relabel (E₁ := (P ++ Hr) ++ (Rt ++ Eh)) hwf hI.alloc (fun z => by
    rw [hmemE z]; simp only [List.mem_append]; grind) ?_
  exact ret_lendK (fun z hz => .inr hz) (fun z hz => hz) hre hR.2 hwf Agree.self hXa hXn
    (fun z hz h => hdBX z h hz) hI.allocS
    (fun z hz h => by
      rcases List.mem_append.mp h with h | h
      · exact hI.disj z hz (hXE z h)
      · exact hI.disj z hz (hBE z h))
    (hE _ _ _ _ _ _ _ _ _ _ _ hb hIb hwf hR)

theorem lend_mut_core [WorldOk F O ι.w] (hE : EvalOk F O n) (hx : lookup x Γ = none) (ha : lookup y env = some a)
    (hsl : lookup y Γ = some s) (hLr : LT F ι σ a τr Lr) (hpath : Reach F ι σ a τr P l τ) (hso : SlotOk F ι σ s a Lr)
    (hsubE : ∀ l ∈ Lr, l ∈ E) (hsx : s.excl = true) (hslot : ∀ ι' σ' L', LT F ι' σ' a τr L' → SlotOk F ι' σ' s a L')
    (hsh : s.shell = false) (hτ : τ.shell = false)
    (hb : Typed F O ((x, .ref .mut τ) :: lendCtx .mut Γ y) body τb ((x, .ref .mut τ) :: Γb) r)
    (hI : Inv F ι σ Γ env E S) (hwf : WF σ) (hR : Ready O hs r) :
    Post F ι O σ E S (thaw Γ [y] Γb) env τb r hs (ret F O n hs .lendK (eval F O n hs σ ((x, l) :: env) body)) :=
  lend_mut_all hE hx ha hsl hLr hpath hso hslot hτ (List.mem_singleton_self y) (by simp)
    (.cons ⟨hsl, ha, hso⟩ hsx hsh .nil) hb hI hwf hR

theorem lend_ro_ok [WorldOk F O ι.w] (hE : EvalOk F O n) (hx : lookup x Γ = none) (hp : PlaceTy Γ p τ w y)
    (hb : Typed F O ((x, .ref .ro τ) :: lendCtx .ro Γ y) body τb ((x, .ref .ro τ) :: Γb) r)
    (hI : Inv F ι σ Γ env E S) (hwf : WF σ) (hR : Ready O hs r) :
    Post F ι O σ E S (thaw Γ [y] Γb) env τb r hs (evalS F O n hs σ env (.lend x .ro p body)) := by
  simp only [evalS]
  obtain ⟨a, τr, Lr, P, l, s, ha, hLr, hpath, hres, -, -, hsl, hso, -, -⟩ := place_ok hp hI.foot
  simp only [hres]
  exact lend_ro_core hE hx ha hsl hLr hpath.reach hso hp.root_live hb hI hwf hR

/-- A place holding no closure, rooted at a variable no field of which is lent, is rooted at a
variable that may change all it holds: a closure borrowed `mut` lends only itself, a closure. -/
theorem root_whole (hsl : lookup y Γ = some s) (hun : Unsplit Γ y)
    (hshp : s.shell = true → (P = [] ∧ τ = τr) ∨ (τr.shell = false ∧ ∃ P', P = a :: P')) (hty : τr = s.ty)
    (hτ : τ.shell = false) : s.shell = false := by
  cases h : s.shell
  · rfl
  · exfalso
    match s, h, hsl with
    | .half t A B, _, hsl => exact hun t A B hsl
    | .ref .mut τ', h, _ =>
      have h' : τ'.shell = true := h
      rcases hshp h with ⟨-, rfl⟩ | ⟨hfn, -⟩
      · simp only [hty, Slot.ty] at hτ; rw [hτ] at h'; cases h'
      · simp only [hty, Slot.ty] at hfn; rw [hfn] at h'; cases h'

/-- A variable none of whose fields is lent, that may change all but its first cell, is a closure or a
slice borrowed `mut`. -/
theorem shell_fn_of (hsl : lookup y Γ = some s) (hun : Unsplit Γ y) (h : s.shell = true) : s.ty.shell = true := by
  match s, h, hsl with
  | .half t A B, _, hsl => exact absurd hsl (hun t A B)
  | .ref .mut _, h, _ => exact h

/-- A `mut` borrow held for the scope of `body`: the borrow owns the place's tree while it lives,
and what the place is rooted at is out of reach; once it ends, the root owns again its path to the
place and what the borrow left there. -/
theorem lend_mut_ok [WorldOk F O ι.w] (hE : EvalOk F O n) (hx : lookup x Γ = none) (hp : PlaceTy Γ p τ true y)
    (hτ : τ.shell = false) (hun : Unsplit Γ y)
    (hb : Typed F O ((x, .ref .mut τ) :: lendCtx .mut Γ y) body τb ((x, .ref .mut τ) :: Γb) r)
    (hI : Inv F ι σ Γ env E S) (hwf : WF σ) (hR : Ready O hs r) :
    Post F ι O σ E S (thaw Γ [y] Γb) env τb r hs (evalS F O n hs σ env (.lend x .mut p body)) := by
  simp only [evalS]
  obtain ⟨a, τr, Lr, P, l, s, ha, hLr, hpath, hres, -, hsubE, hsl, hso, hexw, hslot, hshp, hty⟩ := place_ok hp hI.foot
  simp only [hres]
  have hsh : s.shell = false := root_whole hsl hun hshp hty hτ
  exact lend_mut_core hE hx ha hsl hLr hpath.reach hso (hsubE rfl hsh) (hexw rfl) hslot hsh hτ hb hI hwf hR

/-- A closure over a `readonly` borrow, held for the scope of `body`: its cell is the frame's, and
what the borrowed place is rooted at is only read while it lives; once it ends, the cell is freed. -/
theorem lendClo_ok [WorldOk F O ι.w] (hE : EvalOk F O n) (hfd : F[f]? = some d) (hcap : d.cap = some (xc, τc, .shared))
    (hown : d.owns = [(pn, A)]) (hrefs : d.refs = []) (hretp : d.retp = none) (hdat : τc.data = true)
    (hp : PlaceTy Γ p τc w y) (hx : lookup x Γ = none)
    (hb : Typed F O ((x, .ref .ro (.fn .shared A d.ret d.row .nil)) :: freeze Γ [y]) body τb
      ((x, .ref .ro (.fn .shared A d.ret d.row .nil)) :: Γb) r)
    (hI : Inv F ι σ Γ env E S) (hwf : WF σ) (hR : Ready O hs r) :
    Post F ι O σ E S (thaw Γ [y] Γb) env τb r hs (evalS F O n hs σ env (.lendClo x f p body)) := by
  obtain ⟨a0, τr, Lr, P, l, s, ha0, hLr, hpath, hres, -, -, hsl, hso, -, -⟩ := place_ok hp hI.foot
  obtain ⟨Rt, hRt, hLrPR⟩ := path_split hpath hLr
  simp only [evalS, hfd, hres, hcap]
  have hxk : x ∉ (freeze Γ [y]).map Prod.fst := by rw [freeze_keys]; exact lookup_none_keys hx
  have hwb := typed_weaker hb (List.nodup_cons.mpr ⟨hxk, by rw [freeze_keys]; exact hI.keys⟩)
  cases hwb with
  | cons _ hwb =>
  obtain ⟨Eb, Sb, Fz, hfb, hEp, hS, hent, hthaw⟩ := hI.foot.handle (ys := [y]) hI.keys (by
    intro y' hy' τ'; simp only [List.mem_singleton] at hy'; subst hy'; exact hp.root_live τ')
  obtain ⟨hEbn, hFzn, hdEF⟩ := nodup_append_disj.mp (hEp.nodup_iff.mp hI.nodup)
  have hEb : ∀ l ∈ Eb, l ∈ E := fun l h => hEp.mem_iff.mpr (List.mem_append.mpr (.inl h))
  have hFz : ∀ l ∈ Fz, l ∈ E := fun l h => hEp.mem_iff.mpr (List.mem_append.mpr (.inr h))
  have hRin : ∀ l ∈ Rt, l ∈ Fz ∨ l ∈ S := fun l hl =>
    hent y s a0 Lr ⟨hsl, ha0, hso⟩ (List.mem_singleton_self _) l (hLrPR.mem_iff.mpr (List.mem_append.mpr (.inr hl)))
  -- The closure's cell, new.
  have hold : ∀ z, σ.mem z ≠ none → (σ.alloc (.clo f l τc)).2.mem z = σ.mem z := fun z hz => by
    simp only [Store.alloc]; rw [if_neg (fun e => Nat.lt_irrefl _ (e ▸ hwf z hz))]
  have hRta : ∀ z ∈ Rt, σ.mem z ≠ none := hRt.alloc
  have hna : ∀ z, σ.mem z ≠ none → z ≠ σ.next := fun z hz e => Nat.lt_irrefl _ (e ▸ hwf z hz)
  have haRt : σ.next ∉ Rt := fun h => hna _ (hRta _ h) rfl
  have hco : CloOk F f τc .shared A d.ret d.row .nil :=
    ⟨d, xc, pn, hfd, hcap, hown, by simp [hrefs, TyList.toList], hretp, rfl, rfl, Ty.data_complete hdat, Ty.data_rfree hdat⟩
  have hLa : LT F ι (σ.alloc (.clo f l τc)).2 σ.next (.fn .shared A d.ret d.row .nil) (σ.next :: Rt) :=
    .clo (by simp [Store.alloc]) hco (hRt.frame <| Agree.of' fun z hz => hold z (hRta z hz)) haRt
  have hFza : ∀ z ∈ Fz, σ.mem z ≠ none := fun z hz => hI.alloc z (hFz z hz)
  have hSin : ∀ z ∈ (σ.next :: Rt) ++ Sb, z ∈ (σ.next :: Fz) ∨ z ∈ S := fun z hz => by
    rcases List.mem_append.mp hz with h | h
    · rcases List.mem_cons.mp h with rfl | h
      · exact .inl (List.mem_cons_self ..)
      · rcases hRin z h with h | h
        · exact .inl (List.mem_cons_of_mem _ h)
        · exact .inr h
    · rcases List.mem_append.mp (hS.mem_iff.mp h) with h | h
      · exact .inl (List.mem_cons_of_mem _ h)
      · exact .inr h
  have hIb : Inv F ι (σ.alloc (.clo f l τc)).2 ((x, .ref .ro (.fn .shared A d.ret d.row .nil)) :: freeze Γ [y])
      ((x, σ.next) :: env) Eb ((σ.next :: Rt) ++ Sb) := by
    have hfoot := Foot.cons (s := .ref .ro (.fn .shared A d.ret d.row .nil)) (x := x) (a := σ.next) hLa
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
  have hre : ∀ W, ι.w.le W → ∀ σ1 Eb', Agree (σ.alloc (.clo f l τc)).2 σ1 ((σ.next :: Fz) ++ S) →
      Disj (σ.next :: Fz) Eb' →
      Inv F (ι.inW W) σ1 ((x, .ref .ro (.fn .shared A d.ret d.row .nil)) :: Γb) ((x, σ.next) :: env) Eb'
        ((σ.next :: Rt) ++ Sb) →
      ∃ E', Inv F (ι.inW W) σ1 (thaw Γ [y] Γb) env E' S ∧
        ∀ z, z ∈ E' ↔ z ∈ Eb' ∨ (z ∈ σ.next :: Fz ∧ z ≠ σ.next) := by
    intro W hW σ1 Eb' hag hdX hI'
    obtain ⟨L', Et, St, hL', hft, hEt, hSt⟩ := hI'.foot.uncons
    simp only [addE, addS, Slot.excl, Bool.false_eq_true, ↓reduceIte, exclPart, sharedPart, Slot.shell, Ty.shell] at hEt hSt
    have hagR : Agree (σ.alloc (.clo f l τc)).2 σ1 (σ.next :: Rt) := (hag.mono fun z hz => by
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
  have hSS : ∀ z ∈ S, z ∈ (σ.next :: Rt) ++ Sb := fun z hz =>
    List.mem_append.mpr (.inr (hS.mem_iff.mpr (List.mem_append.mpr (.inr hz))))
  have hnd : (σ.next :: Fz).Nodup := List.nodup_cons.mpr ⟨fun h => hna _ (hFza _ h) rfl, hFzn⟩
  have hd : Disj (σ.next :: Fz) Eb := fun z hz hz' => by
    rcases List.mem_cons.mp hz with rfl | h
    · exact hna _ (hI.alloc _ (hEb _ hz')) rfl
    · exact hdEF z hz' h
  have hwf1 : WF (σ.alloc (.clo f l τc)).2 := hwf.alloc
  refine post_after (E₁ := (σ.next :: Fz) ++ Eb) ((Moves.allocate (v := .clo f l τc) hwf hI.alloc).relabel fun z => by
    rw [hEp.mem_iff]; simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      show (σ.alloc (Val.clo f l τc)).1 = σ.next from rfl]; grind) hwf ?_
  exact ret_cloK (σf := (σ.alloc (.clo f l τc)).2) hSin hSS (List.mem_cons_self ..) hre hR.2 hwf1 Agree.self
    (fun z hz => by
      rcases List.mem_cons.mp hz with rfl | h
      · simp [Store.alloc]
      · rw [hold z (hFza z h)]; exact hFza z h)
    hnd hd (fun z hz => by rw [hold z (hI.allocS z hz)]; exact hI.allocS z hz)
    (fun z hz h => by
      simp only [List.mem_append, List.mem_cons] at h
      rcases h with (rfl | h) | h
      · exact hna _ (hI.allocS _ hz) rfl
      · exact hI.disj z hz (hFz z h)
      · exact hI.disj z hz (hEb z h))
    (hE _ _ _ _ _ _ _ _ _ _ _ hb hIb hwf1 hR)

/-- A closure over a `mut` borrow, held for the scope of `body`: its cell is the frame's and only
read, what it captured is the closure's to change, and what the borrowed place is rooted at is out of
reach; once it ends, the cell is freed and the root owns again its path and what the closure left. -/
theorem lendCloMut_ok [WorldOk F O ι.w] (hE : EvalOk F O n) (hfd : F[f]? = some d) (hcap : d.cap = some (xc, τc, .excl))
    (hown : d.owns = [(pn, A)]) (hrefs : d.refs = []) (hretp : d.retp = none) (hdat : τc.data = true)
    (hp : PlaceTy Γ p τc true y) (hun : Unsplit Γ y) (hx : lookup x Γ = none)
    (hb : Typed F O ((x, .ref .mut (.fn .excl A d.ret d.row .nil)) :: hide Γ y) body τb
      ((x, .ref .mut (.fn .excl A d.ret d.row .nil)) :: Γb) r)
    (hI : Inv F ι σ Γ env E S) (hwf : WF σ) (hR : Ready O hs r) :
    Post F ι O σ E S (thaw Γ [y] Γb) env τb r hs (evalS F O n hs σ env (.lendClo x f p body)) := by
  obtain ⟨a0, τr, Lr, P, l, s, ha0, hLr, hpath, hres, -, hsubE, hsl, hso, hexw, hslot, hshp, hty⟩ := place_ok hp hI.foot
  -- What is captured is plain data, so its root is no closure borrowed `mut`.
  have hsh : s.shell = false := root_whole hsl hun hshp hty (Ty.data_not_fn hdat)
  have hLrE := hsubE rfl hsh
  obtain ⟨Rt, hRt, hLrPR⟩ := path_split hpath hLr
  simp only [evalS, hfd, hres, hcap]
  have hxk : x ∉ (hide Γ y).map Prod.fst := by rw [hide_keys]; exact lookup_none_keys hx
  have hwb := typed_weaker hb (List.nodup_cons.mpr ⟨hxk, by rw [hide_keys]; exact hI.keys⟩)
  cases hwb with
  | cons _ hwb =>
  obtain ⟨Eh, hfh, hEh0, hrebuild⟩ := hI.foot.hidden hI.keys ⟨hsl, ha0, hso⟩ (hexw rfl) hsh
  have hEh : E.Perm ((P ++ Rt) ++ Eh) := hEh0.trans (hLrPR.append_right Eh)
  obtain ⟨hLrn, hEhn, hdLrEh⟩ := nodup_append_disj.mp (hEh.nodup_iff.mp hI.nodup)
  obtain ⟨hPn, hRn, hdPR⟩ := nodup_append_disj.mp hLrn
  have hEhE : ∀ z ∈ Eh, z ∈ E := fun z h => hEh.mem_iff.mpr (List.mem_append.mpr (.inr h))
  have hPE : ∀ z ∈ P, z ∈ E := fun z h => hLrE z (hLrPR.mem_iff.mpr (List.mem_append.mpr (.inl h)))
  have hRE : ∀ z ∈ Rt, z ∈ E := fun z h => hLrE z (hLrPR.mem_iff.mpr (List.mem_append.mpr (.inr h)))
  -- The closure's cell, new.
  have hold : ∀ z, σ.mem z ≠ none → (σ.alloc (.clo f l τc)).2.mem z = σ.mem z := fun z hz => by
    simp only [Store.alloc]; rw [if_neg (fun e => Nat.lt_irrefl _ (e ▸ hwf z hz))]
  have hna : ∀ z, σ.mem z ≠ none → z ≠ σ.next := fun z hz e => Nat.lt_irrefl _ (e ▸ hwf z hz)
  have hRta : ∀ z ∈ Rt, σ.mem z ≠ none := hRt.alloc
  have hPa : ∀ z ∈ P, σ.mem z ≠ none := fun z h => hLr.alloc z (hLrPR.mem_iff.mpr (List.mem_append.mpr (.inl h)))
  have haRt : σ.next ∉ Rt := fun h => hna _ (hRta _ h) rfl
  have haP : σ.next ∉ P := fun h => hna _ (hPa _ h) rfl
  have hco : CloOk F f τc .excl A d.ret d.row .nil :=
    ⟨d, xc, pn, hfd, hcap, hown, by simp [hrefs, TyList.toList], hretp, rfl, rfl, Ty.data_complete hdat, Ty.data_rfree hdat⟩
  have hLa : LT F ι (σ.alloc (.clo f l τc)).2 σ.next (.fn .excl A d.ret d.row .nil) (σ.next :: Rt) :=
    .clo (by simp [Store.alloc]) hco (hRt.frame <| Agree.of' fun z hz => hold z (hRta z hz)) haRt
  have hIb : Inv F ι (σ.alloc (.clo f l τc)).2 ((x, .ref .mut (.fn .excl A d.ret d.row .nil)) :: hide Γ y)
      ((x, σ.next) :: env) (Rt ++ Eh) (σ.next :: S) := by
    have hfoot := Foot.cons (s := .ref .mut (.fn .excl A d.ret d.row .nil)) (x := x) (a := σ.next) hLa
      (hfh.frame <| Agree.of' fun z hz => hold z (hfh.alloc z (List.mem_append.mp hz)))
    refine ⟨by simpa [addE, addS, exclPart, sharedPart, Slot.excl, Slot.shell, Ty.shell] using hfoot,
      nodup_append_disj.mpr ⟨hRn, hEhn, fun z h h' => hdLrEh z (List.mem_append.mpr (.inr h)) h'⟩, ?_,
      List.nodup_cons.mpr ⟨hxk, by rw [hide_keys]; exact hI.keys⟩⟩
    intro z hz hz'
    have hzE : z ∈ E := by
      rcases List.mem_append.mp hz' with h | h
      · exact hRE z h
      · exact hEhE z h
    rcases List.mem_cons.mp hz with rfl | h
    · exact hna _ (hI.alloc _ hzE) rfl
    · exact hI.disj z h hzE
  have hkb : Γb.map Prod.fst = Γ.map Prod.fst := by
    have := typed_keys hb
    simp only [List.map_cons, List.cons.injEq] at this
    rw [this.2, hide_keys]
  have hre : ∀ W, ι.w.le W → ∀ σ1 Eb', Agree (σ.alloc (.clo f l τc)).2 σ1 ((σ.next :: P) ++ S) →
      Disj (σ.next :: P) Eb' →
      Inv F (ι.inW W) σ1 ((x, .ref .mut (.fn .excl A d.ret d.row .nil)) :: Γb) ((x, σ.next) :: env) Eb' (σ.next :: S) →
      ∃ E', Inv F (ι.inW W) σ1 (thaw Γ [y] Γb) env E' S ∧ ∀ z, z ∈ E' ↔ z ∈ Eb' ∨ (z ∈ σ.next :: P ∧ z ≠ σ.next) := by
    intro W hW σ1 Eb' hag hdX hI'
    obtain ⟨L', Et, St, hL', hft, hEt, hSt⟩ := hI'.foot.uncons
    -- The closure is the one made: its cell was only read.
    have ha1 : σ1.mem σ.next = some (.clo f l τc) := by
      rw [hag _ (List.mem_append.mpr (.inl (List.mem_cons_self ..)))]; simp [Store.alloc]
    simp only [SlotOk] at hL'
    cases hL' with
    | @clo _ f' c' τc' _ _ _ _ _ R' ha' _ hR' hn' =>
    rw [ha1] at ha'
    cases ha'
    simp only [addE, addS, exclPart, sharedPart, Slot.excl, Slot.shell, Ty.shell, ↓reduceIte, List.tail_cons,
      List.take_succ_cons, List.take_zero, List.singleton_append, List.cons.injEq, true_and] at hEt hSt
    subst hEt hSt
    have hagS : Agree σ σ1 S := Agree.ofPre (by rt_tac) hag (fun z hz => List.mem_append.mpr (.inr hz)) (fun z hz => by
      rw [hag z (List.mem_append.mpr (.inr hz))]; exact hold z (hI.allocS z hz))
    have hagP : Agree σ σ1 P := Agree.ofPre (by rt_tac) hag
      (fun z hz => List.mem_append.mpr (.inl (List.mem_cons_of_mem _ hz)))
      (fun z hz => by
      rw [hag z (List.mem_append.mpr (.inl (List.mem_cons_of_mem _ hz)))]; exact hold z (hPa z hz))
    have hPnew : ∀ z ∈ P, z ∉ R' ++ Et := fun z hz h => hdX z (List.mem_cons_of_mem _ hz) h
    obtain ⟨L'', hLT', hL''p, -⟩ := path_join (hpath.mono hW) hPn hagP hR' (fun z hz h => hPnew z hz (by simp [h]))
    obtain ⟨E', hf', hp0⟩ := hrebuild W hW σ1 Γb Et L'' hft hwb hagS (hslot _ σ1 _ hLT')
    have hp' : E'.Perm ((P ++ R') ++ Et) := hp0.trans (hL''p.append_right Et)
    refine ⟨E', ⟨hf', hp'.nodup_iff.mpr ?_, ?_, by rw [thaw_keys hkb]; exact hI.keys⟩, ?_⟩
    · rw [List.append_assoc]
      exact nodup_append_disj.mpr ⟨hPn, hI'.nodup, fun z hz h => hPnew z hz h⟩
    · intro z hz hz'
      rcases List.mem_append.mp (hp'.mem_iff.mp hz') with h | h
      · rcases List.mem_append.mp h with h | h
        · exact hI.disj z hz (hPE z h)
        · exact hI'.disj z (List.mem_cons_of_mem _ hz) (List.mem_append.mpr (.inl h))
      · exact hI'.disj z (List.mem_cons_of_mem _ hz) (List.mem_append.mpr (.inr h))
    · intro z
      rw [hp'.mem_iff]
      simp only [List.mem_append, List.mem_cons]
      constructor
      · rintro ((h | h) | h)
        · exact .inr ⟨.inr h, fun e => haP (e ▸ h)⟩
        · exact .inl (.inl h)
        · exact .inl (.inr h)
      · rintro ((h | h) | ⟨(h | h), hne⟩)
        · exact .inl (.inr h)
        · exact .inr h
        · exact absurd h hne
        · exact .inl (.inl h)
  have hSin : ∀ z ∈ σ.next :: S, z ∈ (σ.next :: P) ∨ z ∈ S := fun z hz => by
    rcases List.mem_cons.mp hz with rfl | h
    · exact .inl (List.mem_cons_self ..)
    · exact .inr h
  have hnd : (σ.next :: P).Nodup := List.nodup_cons.mpr ⟨haP, hPn⟩
  have hd : Disj (σ.next :: P) (Rt ++ Eh) := fun z hz hz' => by
    rcases List.mem_cons.mp hz with rfl | h
    · rcases List.mem_append.mp hz' with h | h
      · exact haRt h
      · exact hna _ (hI.alloc _ (hEhE _ h)) rfl
    · rcases List.mem_append.mp hz' with h' | h'
      · exact hdPR z h h'
      · exact hdLrEh z (List.mem_append.mpr (.inl h)) h'
  have hwf1 : WF (σ.alloc (.clo f l τc)).2 := hwf.alloc
  refine post_after (E₁ := (σ.next :: P) ++ (Rt ++ Eh)) ((Moves.allocate (v := .clo f l τc) hwf hI.alloc).relabel fun z => by
    rw [hEh.mem_iff]; simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
      show (σ.alloc (Val.clo f l τc)).1 = σ.next from rfl]; grind) hwf ?_
  exact ret_cloK (σf := (σ.alloc (.clo f l τc)).2) hSin (fun z hz => List.mem_cons_of_mem _ hz)
    (List.mem_cons_self ..) hre hR.2 hwf1 Agree.self
    (fun z hz => by
      rcases List.mem_cons.mp hz with rfl | h
      · simp [Store.alloc]
      · rw [hold z (hPa z h)]; exact hPa z h)
    hnd hd (fun z hz => by rw [hold z (hI.allocS z hz)]; exact hI.allocS z hz)
    (fun z hz h => by
      simp only [List.mem_append, List.mem_cons] at h
      rcases h with (rfl | h) | h | h
      · exact hna _ (hI.allocS _ hz) rfl
      · exact hI.disj z hz (hPE z h)
      · exact hI.disj z hz (hRE z h)
      · exact hI.disj z hz (hEhE z h))
    (hE _ _ _ _ _ _ _ _ _ _ _ hb hIb hwf1 hR)

/-- Taking a tag apart: what it carried is the arm's variable's, and the tag's own variable is
left moved; the arm's variable is dropped as the arm ends. -/
theorem case_ok [WorldOk F O ι.w] (hfl : FlushOk F ι (flushR F O n)) (hE : EvalOk F O n) (hx : lookup x Γ = some (.own (.sum A B) true))
    (hAB : (Ty.sum A B).complete = true) (hy : lookup y Γ = none)
    (h₁ : Typed F O ((y, .own A true) :: setSlot Γ x (.own (.sum A B) false)) e₁ τ ((y, .own A l₁) :: Γ₁) r)
    (h₂ : Typed F O ((y, .own B true) :: setSlot Γ x (.own (.sum A B) false)) e₂ τ ((y, .own B l₂) :: Γ₂) r)
    (w₁ : Weaker Γ' Γ₁) (w₂ : Weaker Γ' Γ₂)
    (hI : Inv F ι σ Γ env E S) (hwf : WF σ) (hR : Ready O hs r) :
    Post F ι O σ E S Γ' env τ r hs (evalS F O n hs σ env (.case x y A B e₁ e₂)) := by
  obtain ⟨a, L, E₁, E₂, ha, hL, hE', hupd⟩ := foot_update hI.foot hI.keys hx rfl rfl
  simp only [SlotOk] at hL
  cases hL with
  | @tag _ _ _ t l _ _ R hat hRp hn =>
  have hnd := seg_nodup (hE' ▸ hI.nodup)
  have haE : a ∈ E := hE' ▸ mem_seg.mpr (.inl (List.mem_cons_self ..))
  have haS : a ∉ S := fun h => hI.disj a h haE
  have ha12 : a ∉ E₁ ++ E₂ := hnd.2.1 a (List.mem_cons_self ..)
  let σ1 := σ.set a (some .moved)
  have hag : Agree σ σ1 (E₁ ++ E₂ ++ S) := agree_set (by
    intro h
    rcases List.mem_append.mp h with h | h
    · exact ha12 h
    · exact haS h)
  have hfoot := hupd σ1 (.own (.sum A B) false) [a] (by rfl) rfl hag (by simp [SlotOk, σ1, Store.set])
  have hR1 : LT F ι σ1 l (if t then A else B) R := hRp.frame (agree_set hn)
  have hRd : Disj R (E₁ ++ E₂) := fun z hz => hnd.2.1 z (List.mem_cons_of_mem _ hz)
  have hyk : y ∉ (setSlot Γ x (.own (.sum A B) false)).map Prod.fst := by
    rw [setSlot_keys]; exact lookup_none_keys hy
  have hIb : ∀ {Ay : Ty}, Ay = (if t then A else B) →
      Inv F ι σ1 ((y, .own Ay true) :: setSlot Γ x (.own (.sum A B) false)) ((y, l) :: env)
        (R ++ (E₁ ++ [a] ++ E₂)) S := by
    intro Ay hAy
    subst hAy
    refine ⟨by simpa [addE, addS, exclPart, sharedPart, Slot.excl, Slot.shell, Ty.shell] using Foot.cons (x := y) (s := .own _ true) hR1 hfoot, ?_, ?_, ?_⟩
    · refine nodup_append_disj.mpr ⟨hRp.nodup, seg_replace hnd.2.2 (by simp) (disj_cons_left.mpr ⟨ha12, disj_nil_left⟩), ?_⟩
      intro z hz hz'
      rcases mem_seg.mp hz' with hz' | hz'
      · simp at hz'; subst hz'; exact hn hz
      · exact hRd z hz hz'
    · intro z hz hz'
      rcases List.mem_append.mp hz' with hz' | hz'
      · exact hI.disj z hz (hE' ▸ mem_seg.mpr (.inl (List.mem_cons_of_mem _ hz')))
      · rcases mem_seg.mp hz' with hz' | hz'
        · simp at hz'; subst hz'; exact haS hz
        · exact hI.disj z hz (hE' ▸ mem_seg.mpr (.inr hz'))
    · exact List.nodup_cons.mpr ⟨hyk, by rw [setSlot_keys]; exact hI.keys⟩
  have hm : Moves σ E σ1 (R ++ (E₁ ++ [a] ++ E₂)) [] :=
    (Moves.set hwf hI.alloc haE).relabel fun z => by rw [hE']; mem_iff
  have hk₁ : ∀ {Γb : Ctx} {e : Expr} {Ay ly}, Typed F O ((y, .own Ay true) :: setSlot Γ x (.own (.sum A B) false)) e τ
      ((y, .own Ay ly) :: Γb) r → y ∉ Γb.map Prod.fst ∧ (Γb.map Prod.fst).Nodup := by
    intro Γb e Ay ly h
    have := typed_keys h
    simp only [List.map_cons, List.cons.injEq, setSlot_keys] at this
    rw [this.2]; exact ⟨lookup_none_keys hy, hI.keys⟩
  have hret : ∀ τy c res, ret F O n hs (.scopeK τy c) res = leave (flushR F O n) τy c res := fun τy c res => by
    rcases res with ⟨_ | _ | _ | _ | _, _⟩ <;> simp [ret, leave, Res.done]
  simp only [evalS, ha, hat, hret]
  cases t with
  | true =>
    simp only [↓reduceIte] at hIb ⊢
    simp only [Ty.complete, Bool.and_eq_true] at hAB
    exact post_weaken (leave_ok hfl hAB.1 hm hwf (hk₁ h₁).1 (hk₁ h₁).2
      (hE _ _ _ _ _ _ _ _ _ _ _ h₁ (hIb rfl) hm.wf hR)) w₁
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hIb ⊢
    simp only [Ty.complete, Bool.and_eq_true] at hAB
    exact post_weaken (leave_ok hfl hAB.2 hm hwf (hk₁ h₂).1 (hk₁ h₂).2
      (hE _ _ _ _ _ _ _ _ _ _ _ h₂ (hIb rfl) hm.wf hR)) w₂

/-- Matching a tag through a borrow: the arm borrows what it carries, as a borrow of a place does. -/
theorem caseRef_ok [WorldOk F O ι.w] (hE : EvalOk F O n) (hx : lookup x Γ = none) (hp : PlaceTy Γ p (.sum A B) w y)
    (hun : Unsplit Γ y)
    (hm : m = .mut → w = true) (hmf : m = .mut → A.shell = false ∧ B.shell = false)
    (h₁ : Typed F O ((x, .ref m A) :: lendCtx m Γ y) e₁ τ ((x, .ref m A) :: Γb₁) r)
    (h₂ : Typed F O ((x, .ref m B) :: lendCtx m Γ y) e₂ τ ((x, .ref m B) :: Γb₂) r)
    (w₁ : Weaker Γb Γb₁) (w₂ : Weaker Γb Γb₂)
    (hI : Inv F ι σ Γ env E S) (hwf : WF σ) (hR : Ready O hs r) :
    Post F ι O σ E S (thaw Γ [y] Γb) env τ r hs (evalS F O n hs σ env (.caseRef x m p e₁ e₂)) := by
  obtain ⟨a, τr, Lr, P, l0, s, ha, hLr, hpath, hres, -, hsubE, hsl, hso, hexw, hslot, hshp, hty⟩ := place_ok hp hI.foot
  obtain ⟨R0, hR0, -⟩ := path_split hpath hLr
  cases hR0 with
  | @tag _ _ _ t l _ _ R hat _ hn =>
  have hpath' := hpath.snocTag' rfl hat
  simp only [evalS, hres, hat]
  -- The root is no closure borrowed `mut`: the place holds a tag.
  have hsh : s.shell = false := root_whole hsl hun hshp hty rfl
  cases m with
  | ro =>
    cases t with
    | true =>
      simp only [↓reduceIte]
      exact post_weaken (lend_ro_core hE hx ha hsl hLr hpath'.reach hso hp.root_live h₁ hI hwf hR) (thaw_mono w₁)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact post_weaken (lend_ro_core hE hx ha hsl hLr hpath'.reach hso hp.root_live h₂ hI hwf hR) (thaw_mono w₂)
  | «mut» =>
    obtain rfl := hm rfl
    cases t with
    | true =>
      simp only [↓reduceIte]
      exact post_weaken (lend_mut_core hE hx ha hsl hLr hpath'.reach hso (hsubE rfl hsh) (hexw rfl) hslot hsh
        (hmf rfl).1 h₁ hI hwf hR) (thaw_mono w₁)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact post_weaken (lend_mut_core hE hx ha hsl hLr hpath'.reach hso (hsubE rfl hsh) (hexw rfl) hslot hsh
        (hmf rfl).2 h₂ hI hwf hR) (thaw_mono w₂)

theorem lend_ok [WorldOk F O ι.w] {m : Mode} (hE : EvalOk F O n) (hx : lookup x Γ = none) (hp : PlaceTy Γ p τ w y)
    (hm : m = .mut → w = true) (hmf : m = .mut → τ.shell = false) (hun : m = .mut → Unsplit Γ y)
    (hb : Typed F O ((x, .ref m τ) :: lendCtx m Γ y) body τb ((x, .ref m τ) :: Γb) r)
    (hI : Inv F ι σ Γ env E S) (hwf : WF σ) (hR : Ready O hs r) :
    Post F ι O σ E S (thaw Γ [y] Γb) env τb r hs (evalS F O n hs σ env (.lend x m p body)) := by
  cases m with
  | ro => exact lend_ro_ok hE hx hp hb hI hwf hR
  | «mut» => obtain rfl := hm rfl; exact lend_mut_ok hE hx hp (hmf rfl) (hun rfl) hb hI hwf hR

/-- The footprint of a variable that may be changed, holding a tree whose first cell is `a`: all of
it, or, if it may change all but that cell, the rest. -/
theorem parts_head (hsx : s.excl = true) :
    exclPart s (a :: R) = (if s.shell then [] else [a]) ++ R ∧
      sharedPart s (a :: R) = if s.shell then [a] else [] := by
  cases h : s.shell <;> simp [exclPart, sharedPart, hsx, h]

/-- One field of a variable's pair borrowed for the scope of `body`: the variable keeps the pair's
cell, only read, and the other field, which it may read, change or lend meanwhile; once the borrow
ends, the variable owns the field again, as the borrow left it. -/
theorem lendField_ok [WorldOk F O ι.w] (hE : EvalOk F O n) (hx : lookup x Γ = none) (hy : lookup y Γ = some s)
    (hty : s.ty = .pair A B) (hsl : (∃ τ, s = .own τ true) ∨ (∃ τ, s = .ref .mut τ) ∨ ∃ t' A' B', s = .half t' A' B')
    (hmf : m = .mut → (if t then A else B).shell = false)
    (hb : Typed F O ((x, .ref m (if t then A else B)) :: setSlot Γ y (.half t A B)) body τb
      ((x, .ref m (if t then A else B)) :: Γb) r)
    (hI : Inv F ι σ Γ env E S) (hwf : WF σ) (hR : Ready O hs r) :
    Post F ι O σ E S (thaw Γ [y] Γb) env τb r hs (evalS F O n hs σ env (.lend x m (fieldOf t y) body)) := by
  obtain ⟨a, Ly, ha, hso, -, -⟩ := foot_lookup hI.foot hy
  -- What the variable holds is a pair, wherever it is.
  have hslot : ∀ {ι' σ' L}, SlotOk F ι' σ' s a L ↔ LT F ι' σ' a (.pair A B) L := by
    intro ι' σ' L
    rcases hsl with ⟨τ, rfl⟩ | ⟨τ, rfl⟩ | ⟨t', A', B', rfl⟩ <;>
      simp only [Slot.ty] at hty <;> simp only [SlotOk, hty]
  have hsx : s.excl = true := by rcases hsl with ⟨τ, rfl⟩ | ⟨τ, rfl⟩ | ⟨t', A', B', rfl⟩ <;> rfl
  have hLy := hslot.mp hso
  obtain ⟨b, c, Rt, Ro, hab, hRt, hLh, hLyp, hdRR, haRR, hfill⟩ := split_field t hLy
  have hres : resolve σ env (fieldOf t y) = some (if t then b else c) := by
    cases t <;> simp [fieldOf, resolve, ha, hab]
  simp only [evalS, hres]
  generalize hl : (if t then b else c) = l at hRt hfill ⊢
  generalize hτf : (if t then A else B) = τf at hRt hfill hb hmf
  -- The borrow's slot: it may change all it holds, or nothing.
  have hxsh : (Slot.ref m τf).shell = false := by
    cases m
    · rfl
    · simp [Slot.shell_ref, hmf rfl]
  -- The variable's footprint: the pair's cell, then the two fields' trees.
  obtain ⟨R, hRLy⟩ := hLy.cons rfl
  have hRp : R.Perm (Rt ++ Ro) := by rw [hRLy] at hLyp; simpa using hLyp
  obtain ⟨hEy, hSy⟩ := parts_head (R := R) (a := a) hsx
  rw [← hRLy] at hEy hSy
  -- Swapped for the half the pair the borrow leaves.
  obtain ⟨Er, Sr, E', S', hf', hEp, hSp, hE'p, hS'p, hreb⟩ :=
    hI.foot.swap hI.keys ⟨hy, ha, hso⟩ (s' := .half t A B) hLh rfl (by simp) ⟨Ro, rfl⟩
  have hhx : (Slot.half t A B).excl = true := rfl
  obtain ⟨hEh, hSh⟩ := parts_head (s := .half t A B) (a := a) (R := Ro) hhx
  simp only [Slot.shell, Ty.shell, ↓reduceIte, List.nil_append] at hEh hSh
  rw [hEh] at hE'p
  rw [hSh] at hS'p
  -- What the frame keeps: the pair's cell, if the variable may change it, and the field, if the
  -- borrow only reads it.
  let Xa : List Nat := if s.shell then [] else [a]
  let Xf := Xa ++ sharedPart (.ref m τf) Rt
  have hEb0 : Foot F ι σ ((x, .ref m τf) :: setSlot Γ y (.half t A B)) ((x, l) :: env)
      (exclPart (.ref m τf) Rt ++ E') (sharedPart (.ref m τf) Rt ++ S') := by
    simpa [addE, addS] using Foot.cons (x := x) (s := .ref m τf) hRt hf'
  have hcnt : ∀ {X Y : List Nat}, (∀ z, X.count z = Y.count z) → X.Perm Y := fun h => List.perm_iff_count.mpr h
  have hEXf : E.Perm (Xf ++ (exclPart (.ref m τf) Rt ++ E')) := by
    refine hEp.trans (hcnt fun z => ?_)
    have h1 := hRp.count_eq z
    have h2 := hE'p.count_eq z
    have h3 := (parts_perm (L := Rt) (s := .ref m τf)).count_eq z
    rw [hEy]
    simp only [Xf, Xa, List.count_append] at *
    omega
  have hEn := hEXf.nodup_iff.mp hI.nodup
  obtain ⟨hXfn, hEb0n, hdXE⟩ := nodup_append_disj.mp hEn
  have hinE : ∀ z, z ∈ Xf ++ (exclPart (.ref m τf) Rt ++ E') → z ∈ E := fun z h => hEXf.mem_iff.mpr h
  have hSdX : Disj S Xf := fun z hz h => hI.disj z hz (hinE z (List.mem_append.mpr (.inl h)))
  have hSdE : Disj S (exclPart (.ref m τf) Rt ++ E') := fun z hz h => hI.disj z hz (hinE z (List.mem_append.mpr (.inr h)))
  -- What the borrow's code only reads: what the frame keeps, or what the lender only reads.
  have hSin : ∀ z ∈ sharedPart (.ref m τf) Rt ++ S', z ∈ Xf ∨ z ∈ S := by
    intro z hz
    rcases List.mem_append.mp hz with h | h
    · exact .inl (List.mem_append.mpr (.inr h))
    · rcases List.mem_cons.mp (hS'p.mem_iff.mp h) with rfl | h
      · cases hsh : s.shell
        · exact .inl (List.mem_append.mpr (.inl (by simp [Xa, hsh])))
        · exact .inr (hSp.mem_iff.mpr (List.mem_append.mpr (.inl (by simp [hSy, hsh]))))
      · exact .inr (hSp.mem_iff.mpr (List.mem_append.mpr (.inr h)))
  have hSS : ∀ z ∈ S, z ∈ sharedPart (.ref m τf) Rt ++ S' := by
    intro z hz
    refine List.mem_append.mpr (.inr (hS'p.mem_iff.mpr ?_))
    rcases List.mem_append.mp (hSp.mem_iff.mp hz) with h | h
    · rw [hSy] at h
      split at h
      · exact List.mem_cons.mpr (.inl (List.mem_singleton.mp h))
      · simp at h
    · exact List.mem_cons_of_mem _ h
  have hdSb0 : Disj (sharedPart (.ref m τf) Rt ++ S') (exclPart (.ref m τf) Rt ++ E') := fun z hz h => by
    rcases hSin z hz with h' | h'
    · exact hdXE z h' h
    · exact hSdE z h' h
  have hxk : x ∉ (setSlot Γ y (.half t A B)).map Prod.fst := by rw [setSlot_keys]; exact lookup_none_keys hx
  have hIb : Inv F ι σ ((x, .ref m τf) :: setSlot Γ y (.half t A B)) ((x, l) :: env)
      (exclPart (.ref m τf) Rt ++ E') (sharedPart (.ref m τf) Rt ++ S') :=
    ⟨hEb0, hEb0n, hdSb0, List.nodup_cons.mpr ⟨hxk, by rw [setSlot_keys]; exact hI.keys⟩⟩
  have hwb := typed_weaker hb (List.nodup_cons.mpr ⟨hxk, by rw [setSlot_keys]; exact hI.keys⟩)
  cases hwb with
  | cons _ hwb =>
  -- As the borrow ends: the variable owns the field again, as the borrow left it.
  have hre : ∀ W, ι.w.le W → ∀ σ1 Eb, Agree σ σ1 (Xf ++ S) → Disj Xf Eb →
      Inv F (ι.inW W) σ1 ((x, .ref m τf) :: Γb) ((x, l) :: env) Eb (sharedPart (.ref m τf) Rt ++ S') →
      ∃ E2, Inv F (ι.inW W) σ1 (thaw Γ [y] Γb) env E2 S ∧ ∀ z, z ∈ E2 ↔ z ∈ Eb ∨ z ∈ Xf := by
    intro W hW σ1 Eb hag hdX hI'
    obtain ⟨Rx, Et, St, hRx, hft, hEb, hSb⟩ := hI'.foot.uncons
    -- What the borrow only reads is as it was.
    have hsx2 : sharedPart (.ref m τf) Rx = sharedPart (.ref m τf) Rt := by
      cases hxe : (Slot.ref m τf).excl
      · have hro : ∀ {L}, sharedPart (.ref m τf) L = L := by simp [sharedPart_plain hxsh, hxe]
        rw [hro, hro]
        refine (((hRt.frame (hag.mono fun z hz => List.mem_append.mpr (.inl (List.mem_append.mpr
          (.inr (by rw [hro]; exact hz)))))).mono hW).det hRx).symm
      · simp [sharedPart_plain hxsh, hxe]
    simp only [addS, hsx2] at hSb
    obtain rfl := List.append_cancel_left hSb
    obtain ⟨Lb, Ebr, hLb, hEtp, hk2⟩ := hreb W hW σ1 Γb Et hft hwb
      ((hag.mono fun z hz => List.mem_append.mpr (.inr (hSp.mem_iff.mpr (List.mem_append.mpr (.inr hz))))))
    obtain ⟨Ro', rfl⟩ := LT.cons (hLb : LT F (ι.inW W) σ1 a (Ty.lent1 t A B) Lb) Ty.lent1_isHole
    obtain ⟨hEh', -⟩ := parts_head (s := .half t A B) (a := a) (R := Ro') hhx
    simp only [Slot.shell, Ty.shell, ↓reduceIte, List.nil_append] at hEh'
    rw [hEh'] at hEtp
    simp only [addE] at hEb
    have hEbn := hI'.nodup
    rw [hEb] at hEbn
    obtain ⟨-, -, hdxt⟩ := nodup_append_disj.mp hEbn
    have hRo'E : ∀ z ∈ Ro', z ∈ Et := fun z hz => hEtp.mem_iff.mpr (List.mem_append.mpr (.inl hz))
    have hinEb : ∀ z ∈ Et, z ∈ Eb := fun z hz => by rw [hEb]; exact List.mem_append.mpr (.inr hz)
    have haSb : a ∈ sharedPart (.ref m τf) Rt ++ S' :=
      List.mem_append.mpr (.inr (hS'p.mem_iff.mpr (List.mem_cons_self ..)))
    -- The pair's cell is as it was: kept by the frame, or only read.
    have hagA : σ1.mem a = σ.mem a := by
      cases hsh : s.shell
      · exact hag a (List.mem_append.mpr (.inl (List.mem_append.mpr (.inl (by simp [Xa, hsh])))))
      · exact hag a (List.mem_append.mpr (.inr (hSp.mem_iff.mpr (List.mem_append.mpr (.inl (by simp [hSy, hsh]))))))
    have hdRxRo : Disj Rx Ro' := fun z hz hz' => by
      rcases mem_parts (s := .ref m τf) hz with h | h
      · exact hdxt z h (hRo'E z hz')
      · rw [hsx2] at h
        exact hI'.disj z (List.mem_append.mpr (.inl h)) (hinEb z (hRo'E z hz'))
    have haRx : a ∉ Rx ++ Ro' := fun h => by
      rcases List.mem_append.mp h with h | h
      · rcases mem_parts (s := .ref m τf) h with h | h
        · exact hI'.disj a haSb (by rw [hEb]; exact List.mem_append.mpr (.inl h))
        · rw [hsx2] at h
          exact haRR (List.mem_append.mpr (.inl (sharedPart_sub h)))
      · exact hI'.disj a haSb (hinEb a (hRo'E a h))
    obtain ⟨Lnew, hLnew, hLnp⟩ := hfill _ σ1 Ro' Rx hagA hLb hRx hdRxRo haRx
    obtain ⟨Rn, hRn⟩ := hLnew.cons rfl
    have hRnp : Rn.Perm (Rx ++ Ro') := by rw [hRn] at hLnp; simpa using hLnp
    have hshn : sharedPart s Lnew = sharedPart s Ly := by
      rw [hRn, (parts_head (R := Rn) (a := a) hsx).2, hSy]
    obtain ⟨E2, hf2, hE2p⟩ := hk2 Lnew (hslot.mpr hLnew) hshn
    have hE2 : E2.Perm (Xf ++ Eb) := by
      refine hE2p.trans (hcnt fun z => ?_)
      rw [hRn, (parts_head (R := Rn) (a := a) hsx).1, hEb]
      have h1 := hRnp.count_eq z
      have h2 := hEtp.count_eq z
      have h3 := (parts_perm (L := Rx) (s := .ref m τf)).count_eq z
      simp only [Xf, Xa, List.count_append, ← hsx2] at *
      omega
    have hkb : Γb.map Prod.fst = Γ.map Prod.fst := by rw [hwb.keys, setSlot_keys]
    refine ⟨E2, ⟨hf2, hE2.nodup_iff.mpr (nodup_append_disj.mpr ⟨hXfn, hI'.nodup, hdX⟩), fun z hz h => ?_,
      by rw [thaw_keys hkb]; exact hI.keys⟩, fun z => by rw [hE2.mem_iff, List.mem_append, or_comm]⟩
    rcases List.mem_append.mp (hE2.mem_iff.mp h) with h | h
    · exact hSdX z hz h
    · exact hI'.disj z (hSS z hz) h
  refine post_relabel (E₁ := Xf ++ (exclPart (.ref m τf) Rt ++ E')) hwf hI.alloc (fun z => hEXf.mem_iff.symm) ?_
  exact ret_lendK hSin hSS hre hR.2 hwf Agree.self
    (fun z hz => hI.alloc z (hinE z (List.mem_append.mpr (.inl hz)))) hXfn hdXE hI.allocS
    (fun z hz h => by
      rcases List.mem_append.mp h with h | h
      · exact hSdX z hz h
      · exact hSdE z hz h)
    (hE _ _ _ _ _ _ _ _ _ _ _ hb hIb hwf hR)

/-! ## A borrow a call returns -/

theorem lookup_append_right {α : Type} {x : Var} : ∀ {A B : List (Var × α)}, x ∉ A.map Prod.fst →
    lookup x (A ++ B) = lookup x B
  | [], _, _ => rfl
  | (y, v) :: A, B, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.cons_append, lookup, h.1, ↓reduceIte]
    exact lookup_append_right h.2

/-- A variable of a weaker context has a slot there that its slot weakens. -/
theorem Weaker.lookup_le : Weaker Γ' Γ → lookup x Γ' = some s' → ∃ s, lookup x Γ = some s ∧ Slot.Le s' s := by
  intro w
  induction w with
  | nil => simp [lookup]
  | @cons s1 s2 Γ1 Γ2 y hle _ ih =>
    intro h
    by_cases hy : x = y
    · subst hy
      simp only [lookup, ↓reduceIte, Option.some.injEq] at h ⊢
      subst h; exact ⟨_, rfl, hle⟩
    · simp only [lookup, hy, ↓reduceIte] at h ⊢
      exact ih h

/-- A function's borrowed parameter has its declared slot. -/
theorem lookup_refs : ∀ {refs : List (Var × Mode × Ty)} {i : Nat} {x : Var} {m : Mode} {τ : Ty},
    (refs.map Prod.fst).Nodup → refs[i]? = some (x, m, τ) →
    lookup x (refs.map fun p => (p.1, Slot.ref p.2.1 p.2.2)) = some (.ref m τ)
  | [], _, _, _, _, _, h => by simp at h
  | (y, m', τ') :: refs, 0, x, m, τ, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp [lookup]
  | (y, m', τ') :: refs, i + 1, x, m, τ, hn, h => by
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [List.getElem?_cons_succ] at h
    have hx : x ≠ y := fun e => hn.1 (e ▸ List.mem_map.mpr ⟨_, List.mem_of_getElem? h, rfl⟩)
    simp only [List.map_cons, lookup, hx, ↓reduceIte]
    exact lookup_refs hn.2 h

theorem lookup_zip_get {α : Type} : ∀ {names : List Var} {vals : List α} {i : Nat} {x : Var} {v : α},
    names.Nodup → names[i]? = some x → vals[i]? = some v → lookup x (names.zip vals) = some v
  | [], _, _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, _, _, h => by simp at h
  | y :: names, w :: vals, 0, x, v, _, h1, h2 => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
    subst h1 h2
    simp [lookup]
  | y :: names, w :: vals, i + 1, x, v, hn, h1, h2 => by
    simp only [List.getElem?_cons_succ] at h1 h2
    have hxy : x ≠ y := fun e => (List.nodup_cons.mp hn).1 (e ▸ List.mem_of_getElem? h1)
    simp only [List.zip_cons_cons, lookup, hxy, ↓reduceIte]
    exact lookup_zip_get (List.nodup_cons.mp hn).2 h1 h2

/-- Leaving the code a borrow is in scope for passes on what the code gave. -/
theorem ret_lendK_eq : ret F O n hs .lendK r =
    (match r with
     | (.susp j ef vs ls K, σ) => (.susp j ef vs ls (.lendK :: K), σ)
     | r => r) := by
  rcases r with ⟨_ | _ | _ | _ | _, _⟩ <;> simp [ret]

/-- A call that returns a borrow ended: the borrow is taken in the callee's variables, its owned
parameters dropped, and the caller's variables are as they were but for the places lent `mut`;
then `body` runs with the borrow, what it is of only read, or out of reach, until it ends. -/
theorem ret_callLendK [WorldOk F O ι.w] (hfl : FlushOk F ι (flushR F O n)) {d : Fn} {hos : List Hole} {cs : List (Nat × Place)} {zs : List Var} {cells : Env}
    (hE : EvalOk F O n)
    (hrow : ∀ l ∈ d.row, l ∈ r) (hI₁ : Inv F ι σf Γ₁ env E₁ S) (hholes : ∀ h ∈ hos, HoleOk F ι σf Γ₁ env h)
    (hpw : hos.Pairwise Apart) (hts : hos.map (fun h => (h.mode, h.ty)) = d.refs.map Prod.snd)
    (hkeys : ((d.owns.map Prod.fst) ++ (d.refs.map Prod.fst)).Nodup) (hoc : ∀ o ∈ d.owns, o.2.complete = true)
    (hbody : Typed F O (fnCtx d) d.body .int Γ'' d.row) (hcells : cells.map Prod.fst = d.owns.map Prod.fst)
    (hcne : cs ≠ [])
    (hcs : ∀ c ∈ cs, ∃ xi mi τi w hd, d.refs[c.1]? = some (xi, mi, τi) ∧ PlaceTy Γ'' c.2 d.ret w xi ∧
      (m = .mut → w = true) ∧ hos[c.1]? = some (hd : Hole) ∧ (m = .mut → hd.mode = .mut ∧ τi.shell = false) ∧
      (m = .mut → ∀ s, lookup hd.root Γ₁ = some s → s.shell = true → hd.path = []))
    (hzs : Pairs (fun c z => ∃ hd : Hole, hos[c.1]? = some hd ∧ hd.root = z) cs zs)
    (hzm : m = .mut → zs.Nodup ∧ d.ret.shell = false)
    (hlive : ∀ z ∈ zs, ∀ τ', lookup z Γ₁ ≠ some (.own τ' false)) (hx : lookup x Γ₁ = none)
    (hb : Typed F O ((x, .ref m d.ret) :: lendCtxs m Γ₁ zs) body τb ((x, .ref m d.ret) :: Γb) r)
    (hR : Ready O hs r) (hwf : WF σ0)
    (hag : Agree σf σ0 (E₁.filter (· ∉ mutCells (olds hos)) ++ S))
    (hdX : Disj (E₁.filter (· ∉ mutCells (olds hos))) Ein) (hSa : ∀ l ∈ S, σ0.mem l ≠ none)
    (hdS : Disj S (E₁.filter (· ∉ mutCells (olds hos)) ++ Ein))
    (hp : Post F ι O σ0 Ein (roCells (olds hos)) Γ'' (cells ++ (d.refs.map Prod.fst).zip (hos.map Hole.loc))
      .int d.row hs res) :
    Post F ι O σ0 (E₁.filter (· ∉ mutCells (olds hos)) ++ Ein) S (unlend m Γ₁ zs Γb) env τb r hs
      (ret F O n hs (.callLendK x (cs.map Prod.snd) (cells ++ (d.refs.map Prod.fst).zip (hos.map Hole.loc))
        ((d.owns.map Prod.snd).zip (cells.map Prod.snd)) env body) res) := by
  generalize hX : E₁.filter (· ∉ mutCells (olds hos)) = X at hag hdX hdS ⊢
  have hXE : ∀ l ∈ X, l ∈ E₁ := fun l hl => (mem_keep.mp (hX ▸ hl)).1
  have hXa : ∀ l ∈ X, σ0.mem l ≠ none := fun l hl => by
    rw [hag l (List.mem_append.mpr (.inl hl))]; exact hI₁.alloc l (hXE l hl)
  have hXS : ∀ l ∈ X ++ S, σ0.mem l ≠ none := fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · exact hXa l h
    · exact hSa l h
  have hXSd : Disj (X ++ S) Ein := fun l hl h => by
    rcases List.mem_append.mp hl with hl | hl
    · exact hdX l hl h
    · exact hdS l hl (List.mem_append.mpr (.inr h))
  have hk₁ := hI₁.keys
  have hwb := typed_weaker hb (List.nodup_cons.mpr ⟨by rw [lendCtxs_keys]; exact lookup_none_keys hx,
    by rw [lendCtxs_keys]; exact hk₁⟩)
  have hw : Weaker (unlend m Γ₁ zs Γb) Γ₁ := by
    cases hwb with
    | cons _ w =>
      cases m
      · exact thaw_weaker w
      · exact unhideAll_weaker w
  -- The callee ended: its owned parameters dropped, and the caller's variables rebuilt.
  have key : ∀ σ3 Ec', Inv F ι σ3 Γ'' (cells ++ (d.refs.map Prod.fst).zip (hos.map Hole.loc)) Ec'
      (roCells (olds hos)) → Moves σ0 Ein σ3 Ec' [] →
      ∃ σ4', dropCells σ3 ((d.owns.map Prod.snd).zip (cells.map Prod.snd)) = some σ4' ∧ ∃ Ea,
        FlushGives (flushR F O n (cellsKonts σ3 ((d.owns.map Prod.snd).zip (cells.map Prod.snd))) σ4') σ3 Ea ∧
        ∀ σ4, Dropped σ3 Ea σ4 → ∃ E'' ps,
        Inv F ι σ4 Γ₁ env E'' S ∧ Moves σ0 (X ++ Ein) σ4 E'' [] ∧ ps.map Prod.fst = hos ∧
        (∀ p ∈ ps, p.1.mode = .mut → LT F ι σ4 p.1.loc p.1.ty p.2) ∧
        Agree σf σ4 (E₁.filter (fun l => l ∉ mutCells (olds hos)) ++ S) ∧
        Disj (E₁.filter (fun l => l ∉ mutCells (olds hos))) (mutCells ps) ∧
        Ec' = Ea ++ mutCells ps ∧ (∀ l, l ∉ Ea → σ4.mem l = σ3.mem l) ∧
        (∀ p ∈ ps, LT F ι σ3 p.1.loc p.1.ty p.2) ∧ roCells ps = roCells (olds hos) ∧ Disj S (mutCells ps) := by
    intro σ3 Ec' hI₃ hm₃
    have hk₃ := hI₃.keys
    have hsh : shape Γ'' = ownCtx d.owns ++ refCtx d.refs := by
      rw [typed_shape hbody (by simpa [fnCtx, List.map_append, List.map_map, Function.comp_def] using hkeys),
        shape_fnCtx]
    obtain ⟨Γa, rfl, hΓa⟩ := shape_split (ownCtx d.owns) hsh (refCtx_refs d.refs)
    have hla : Γa.length = cells.length := by
      rw [← shape_length, hΓa]; simpa [ownCtx] using (congrArg List.length hcells).symm
    obtain ⟨Ea, Sa, Er, Sr, hfa, hfr, rfl, hSab⟩ := hI₃.foot.split hla
    obtain ⟨ps, hps, hlt, rfl, rfl⟩ := (foot_refs hts.symm).mp hfr
    have hnd := nodup_append_disj.mp hI₃.nodup
    obtain ⟨rfl, σ4', hdrop, hfg⟩ := dropCellsF hfl hfa hΓa hnd.1 hm₃.wf hoc
    refine ⟨σ4', hdrop, Ea, hfg, fun σ4 hd5 => ?_⟩
    have hkeep4 := hd5.keep hm₃.wf
    simp only [List.nil_append] at hSab
    obtain ⟨hXSc, -⟩ := hm₃.apart hwf hXS hXSd
    have hkeep3 := hm₃.keeps hwf hXS hXSd
    have hag4 : Agree σf σ4 (X ++ S) := Agree.trans (Agree.trans hag hkeep3)
      (hd5.keeps hm₃.wf (fun l hl => by rw [hkeep3 l hl]; exact hXS l hl)
        fun l hl h => hXSc l hl (List.mem_append.mpr (.inl h)))
    have hnew4 : ∀ p ∈ ps, p.1.mode = .mut → LT F ι σ4 p.1.loc p.1.ty p.2 := fun p hp _ =>
      (hlt p hp).frame <| hd5.keeps hm₃.wf (fun l hl => (hlt p hp).alloc l hl) fun l hl h =>
        (mem_cells_of hp hl).elim (fun hM => hnd.2.2 l h hM)
        (fun hR => hI₃.disj l (by rw [hSab]; simp [hR]) (List.mem_append.mpr (.inl h)))
    have hXM : Disj X (mutCells ps) := fun l hl h =>
      hXSc l (List.mem_append.mpr (.inl hl)) (List.mem_append.mpr (.inr h))
    obtain ⟨E'', hI₄, hmem⟩ := caller_rebuild (σ' := σ4) hI₁ hholes hpw hps hnew4 hnd.2.1
      (by rw [hX]; exact hag4) (by rw [hX]; exact hXM)
      (fun l hl h => hXSc l (List.mem_append.mpr (.inr hl)) (List.mem_append.mpr (.inr h)))
    rw [hX] at hmem
    have m3 := (hm₃.widen hXa hdX).relabel (E'' := X ++ mutCells ps ++ Ea) (L'' := []) fun x => by
      simp only [List.mem_append, List.not_mem_nil, or_false]; grind
    have m4 : Moves σ3 (X ++ mutCells ps ++ Ea) σ4 (X ++ mutCells ps) [] :=
      (hd5.widen (X := X ++ mutCells ps) (fun l hl => (m3.alloc l).mpr (.inr (.inl (List.mem_append.mpr (.inl hl))))) (by
        intro l hl hl'
        rcases List.mem_append.mp hl with h | h
        · exact hXSc l (List.mem_append.mpr (.inl h)) (List.mem_append.mpr (.inl hl'))
        · exact hnd.2.2 l hl' h)).relabel fun x => by simp
    refine ⟨E'', ps, hI₄, (m3.trans m4 disj_nil_left hwf).relabel fun x => by
        simp only [List.mem_append, hmem x, List.not_mem_nil, or_false, List.append_nil] <;> grind,
      hps, hnew4, by rw [hX]; exact hag4, by rw [hX]; exact hXM, rfl, fun l hl => hkeep4 l hl, hlt,
      hSab.symm, fun l hl h => hXSc l (List.mem_append.mpr (.inr hl)) (List.mem_append.mpr (.inr h))⟩
  rcases res with ⟨res, σ3⟩
  cases res with
  | val v =>
    obtain ⟨Ec', Lw, hI₃, hvw, -, -, hm₃⟩ := hp
    cases hvw with
    | int =>
    rename_i k
    obtain ⟨σ4', hdrop, Ea, hfg, hk⟩ := key σ3 Ec' hI₃ (by simpa using hm₃)
    -- The place the callee picked.
    obtain ⟨p, hpick, hpm⟩ := pick_mem k (by simpa using hcne : cs.map Prod.snd ≠ [])
    obtain ⟨⟨i, p'⟩, hc, rfl⟩ := List.mem_map.mp hpm
    obtain ⟨xi, mi, τi, w, hd, hri, hpt, hmw, hhi, hmh, hdp⟩ := hcs _ hc
    -- What the callee could pick lies in the trees of `zs`, which hold what the call left.
    have hzin : hd.root ∈ zs := by
      obtain ⟨z, hz, hd', hhi', rfl⟩ := hzs.mem_left hc
      rw [hhi] at hhi'; cases hhi'; exact hz
    -- The borrow the callee returns: a path from the place it was lent.
    obtain ⟨a', τr', Lr', P', l, s', ha', hLr', hpath', hres, -, -, hsl', hso', -, -, -, hτr'⟩ :=
      place_ok hpt hI₃.foot
    simp only [ret, hpick, hres, hdrop]
    refine hfg.post fun σ4 hd5 => ?_
    obtain ⟨E'', ps, hI₄, hm, hps, hnew4, hag4, hXM, rfl, hkeep4, hlt3, hro, hSM⟩ := hk σ4 hd5
    have hMn : (mutCells ps).Nodup := (nodup_append_disj.mp hI₃.nodup).2.1
    have hni : (d.refs.map Prod.fst)[i]? = some xi := by simp [hri]
    have hxio : xi ∉ cells.map Prod.fst := by
      rw [hcells]
      intro h
      exact (List.nodup_append.mp hkeys).2.2 xi h xi (List.mem_of_getElem? hni) rfl
    have hloc : a' = hd.loc := by
      rw [lookup_append_right hxio, lookup_zip_get (List.nodup_append.mp hkeys).2.1 hni
        (show (hos.map Hole.loc)[i]? = some hd.loc by simp [hhi])] at ha'
      exact (Option.some.inj ha').symm
    subst hloc
    have hty : (hd.mode, hd.ty) = (mi, τi) := by
      have h1 : (hos.map (fun h => (h.mode, h.ty)))[i]? = some (hd.mode, hd.ty) := by simp [hhi]
      have h2 : (d.refs.map Prod.snd)[i]? = some (mi, τi) := by simp [hri]
      rw [hts] at h1
      exact Option.some.inj (h1.symm.trans h2)
    simp only [Prod.mk.injEq] at hty
    obtain ⟨rfl, rfl⟩ := hty
    -- The hole's tree in the callee, where the path runs, is no owned parameter's.
    obtain ⟨q, hq, rfl⟩ : ∃ q ∈ ps, q.1 = hd := by
      have : hd ∈ ps.map Prod.fst := by rw [hps]; exact List.mem_of_getElem? hhi
      simpa using this
    -- The parameter's slot in the callee is the one it was declared with, a borrow of the hole's type.
    have hs' : s' = .ref q.1.mode q.1.ty := by
      obtain ⟨s0, hs0, hle⟩ := (typed_weaker hbody (by
        simpa [fnCtx, List.map_append, List.map_map, Function.comp_def] using hkeys)).lookup_le hsl'
      have hl0 : lookup xi (fnCtx d) = some (.ref q.1.mode q.1.ty) := by
        rw [fnCtx, lookup_append_right (by
          simp only [List.map_map, Function.comp_def]
          intro h; exact (List.nodup_append.mp hkeys).2.2 xi h xi (List.mem_of_getElem? hni) rfl)]
        exact lookup_refs (List.nodup_append.mp hkeys).2.1 hri
      rw [hl0] at hs0; cases hs0
      cases hle; rfl
    subst hs'
    obtain rfl : τr' = q.1.ty := hτr'
    obtain rfl := LT.det hLr' (hlt3 q hq)
    obtain ⟨R, -, hPR⟩ := path_split hpath' hLr'
    have hqEo : ∀ z ∈ q.2, z ∉ Ea := fun z hz hEo => by
      rcases mem_cells_of hq hz with hM | hR
      · exact (nodup_append_disj.mp hI₃.nodup).2.2 z hEo hM
      · exact hI₃.disj z (hro ▸ hR) (List.mem_append.mpr (.inl hEo))
    have hpath4 : Path F ι σ4 q.1.loc q.1.ty P' l d.ret := hpath'.frame <| hd5.keeps hm₃.wf
      (fun z hz => hLr'.alloc z (hPR.mem_iff.mpr (List.mem_append.mpr (.inl hz))))
      fun z hz h => hqEo z (hPR.mem_iff.mpr (List.mem_append.mpr (.inl hz))) h
    have hqh : q.1 ∈ hos := hps ▸ List.mem_map_of_mem hq
    refine post_after hm hwf ?_
    -- After the call, the root of a place lent `mut` that the callee could pick: changeable, and no
    -- closure borrowed `mut`, its parameter's type being no closure.
    have hafter : ∀ q' ∈ ps, ∀ c' ∈ cs, hos[c'.1]? = some q'.1 → q'.1.mode = .mut → m = .mut →
        ∃ s a τr, lookup q'.1.root Γ₁ = some s ∧ lookup q'.1.root env = some a ∧
          s.excl = true ∧ s.shell = false ∧ (∃ P, Path F ι σ4 a τr P q'.1.loc q'.1.ty) ∧
          ∃ L', LT F ι σ4 a τr L' ∧ SlotOk F ι σ4 s a L' ∧
          ∀ ι'' σ'' L', LT F ι'' σ'' a τr L' → SlotOk F ι'' σ'' s a L' := by
      intro q' hq' c' hc' hhi' hm' hmm
      obtain ⟨xi', mi', τi', w', hd'', hri', -, -, hhi'', hmh', hdp'⟩ := hcs c' hc'
      rw [hhi'] at hhi''; cases hhi''
      have hqh' : q'.1 ∈ hos := List.mem_of_getElem? hhi'
      obtain ⟨s, a, τr, P, L', hs, ha, hex, hpathH, hLT, hso, hslot, -⟩ :=
        hole_after hI₁ hholes hpw hps hnew4 hMn hag4 hXM hSM hqh'
      refine ⟨s, a, τr, hs, ha, hex hm', ?_, ⟨P, hpathH⟩, L', hLT, hso, hslot⟩
      cases h : s.shell
      · rfl
      · have he : Entry F ι σf Γ₁ env q'.1.root s a q'.1.tree := by
          obtain ⟨s', a', -, hs', ha', -, -, -, -, hso', -⟩ := hholes q'.1 hqh'
          obtain rfl := lookup_det hs hs'
          obtain rfl := lookup_det ha ha'
          exact ⟨hs', ha', hso'⟩
        rcases (hholes q'.1 hqh').shell_root he h hm' with ⟨-, rfl⟩ | hp1
        · have hτ' : τi'.shell = false := (hmh' hmm).2
          have hty : q'.1.ty = τi' := by
            have h1 : (hos.map (fun h => (h.mode, h.ty)))[c'.1]? = some (q'.1.mode, q'.1.ty) := by simp [hhi']
            have h2 : (d.refs.map Prod.snd)[c'.1]? = some (mi', τi') := by simp [hri']
            rw [hts] at h1
            exact (Prod.mk.inj (Option.some.inj (h1.symm.trans h2))).2
          simp [Hole.slot, Slot.shell_ref, hty, hτ'] at h
        · obtain ⟨P1, hP1⟩ := hp1
          rw [hdp' hmm s hs h] at hP1; cases hP1
    -- The borrow, on a path from what the place lent is rooted at, through the place.
    have hcore : Post F ι O σ4 E'' S (unlend m Γ₁ zs Γb) env τb r hs
        (ret F O n hs .lendK (eval F O n hs σ4 ((x, l) :: env) body)) := by
      cases m with
      | ro =>
        simp only [lendCtxs] at hb
        obtain ⟨s, a, τr, P, L', hs, ha, -, hpathH, hLT, hso, -, -⟩ :=
          hole_after hI₁ hholes hpw hps hnew4 hMn hag4 hXM hSM hqh
        exact lend_ro_all hE hx ha hs hLT (hpathH.trans hpath4).reach hso hzin hlive hb hI₄ hm.wf hR
      | «mut» =>
        simp only [lendCtxs] at hb
        obtain ⟨s, a, τr, hs, ha, hex, hsh, ⟨P, hpathH⟩, L', hLT, hso, hslot⟩ := hafter q hq _ hc hhi (hmh rfl).1 rfl
        obtain ⟨H, htr⟩ := Trees.of_pairs hzs fun c' hc' z ⟨hd', hhi', hz⟩ => by
          obtain ⟨_, _, _, _, hd'', _, _, _, hhi'', hmh', _⟩ := hcs c' hc'
          rw [hhi'] at hhi''; cases hhi''
          obtain ⟨q', hq', hqe⟩ : ∃ q' ∈ ps, q'.1 = hd' := by
            have : hd' ∈ ps.map Prod.fst := by rw [hps]; exact List.mem_of_getElem? hhi'
            simpa using this
          subst hqe
          obtain ⟨s', a', τr', hs', ha', hex', hsh', -, L'', hLT', hso', -⟩ :=
            hafter q' hq' c' hc' hhi' (hmh' rfl).1 rfl
          subst hz
          exact ⟨s', a', _, ⟨hs', ha', hso'⟩, hex', hsh'⟩
        exact lend_mut_all hE hx ha hs hLT (hpathH.trans hpath4).reach hso hslot (hzm rfl).2 hzin (hzm rfl).1 htr
          hb hI₄ hm.wf hR
    generalize eval F O n hs σ4 ((x, l) :: env) body = res at hcore ⊢
    rcases res with ⟨_ | _ | _ | _ | _, σq⟩ <;> simpa [ret] using hcore
  | abort j k =>
    obtain ⟨haim, Ec', hI₃, hm₃⟩ := hp
    obtain ⟨σ4', hdrop, Ea, hfg, hk⟩ := key σ3 Ec' hI₃ hm₃
    simp only [ret, hdrop]
    refine hfg.post fun σ4 hd5 => ?_
    obtain ⟨E'', -, hI₄, hm, -⟩ := hk σ4 hd5
    exact ⟨haim, E'', hI₄.weaken hw, hm⟩
  | susp j ef vs ls K =>
    obtain ⟨op, X', hos', A, Lv, hc, hop, hcov, haim, hK, hls, hvs, hn, hdv, hdSv, hm⟩ := hp
    simp only [ret]
    obtain ⟨hXc, hXv⟩ := hm.apart hwf hXa hdX
    have hK' := FramesOk.cons (σf := σf) (A := A) (.callLendK hrow hI₁ hholes hpw hts hkeys hoc hbody hcells hcne hcs
      hzs hzm hlive hx hb)
      (Weaker.refl _) (by rw [hX]; exact Agree.trans hag (hm.keeps hwf hXS hXSd))
      (fun l hl => hI₁.alloc l (hXE l (hX ▸ hl))) (hI₁.nodup.filter _)
      (by rw [hX]; exact hXc) hK (fun _ h => by simp at h) (fun a ha => .inl ha)
    rw [hX] at hK'
    refine ⟨op, X ++ X', hos', A, Lv, hc, hop, hR.2, haim, hK', hls, hvs, hn, ?_, ?_, ?_⟩
    · intro l hl h
      simp only [List.mem_append] at h
      rcases h with (h | h) | h
      · exact hXv l h hl
      · exact hdv l hl (by simp [h])
      · exact hdv l hl (by simp [h])
    · exact fun l hl h => (hm.apart hwf hSa (fun l hl h => hdS l hl (List.mem_append.mpr (.inr h)))).2 l h hl
    · exact (hm.widen hXa hdX).relabel fun x => by simp only [List.mem_append, List.append_assoc]
  | stuck => simp [Post] at hp
  | timeout => simp [ret, Post]
  | ended => simp [ret, Post]

/-! ## Arms -/

/-- An arm as a function: its owned parameters, then its borrowed ones. -/
def armFn (os rs : List Var) (op : Op) (r : Row) (arm : Expr) : Fn :=
  { owns := os.zip op.owns, refs := rs.zip op.refs, ret := op.ret, row := r, body := arm }

/-- An arm ended: its owned parameters dropped, what it was lent `mut` holds trees of their types —
at the places the operation lent it, `ps`, and at those its `handle` lent it, `Hc` — and what it was
lent `readonly` is as it was. -/
theorem arm_end {cells : Env} {hos : List Hole} (hfl : FlushOk F ι fl) (harm : Typed F O (armCtx os rs op (caps.map Cap.sig)) arm τa Γa r)
    (hnames : (os ++ rs ++ caps.map Cap.name).Nodup) (hown : os.length = op.owns.length)
    (href : rs.length = op.refs.length) (hcells : cells.map Prod.fst = os)
    (hts : hos.map (fun h => (h.mode, h.ty)) = op.refs)
    (hI : Inv F ι σ3 Γa (cells ++ rs.zip (hos.map Hole.loc) ++ caps.map (fun c => (c.name, c.loc))) Ea
      (roCells (olds hos) ++ Rc))
    (hdet : ∀ Rc' Hc, CapsOk F ι σ3 caps Rc' Hc → Rc' = Rc) (hfns : CapsFns caps) (hwf3 : WF σ3)
    (hcomp : ∀ τ ∈ op.owns, τ.complete = true) :
    ∃ σ4' ps Hc Eo, dropCells σ3 (op.owns.zip (cells.map Prod.snd)) = some σ4' ∧
      FlushGives (fl (cellsKonts σ3 (op.owns.zip (cells.map Prod.snd))) σ4') σ3 Eo ∧ ps.map Prod.fst = hos ∧
      Ea = Eo ++ mutCells ps ++ Hc ∧ roCells ps = roCells (olds hos) ∧
      ∀ σ4, Dropped σ3 Eo σ4 → (∀ p ∈ ps, LT F ι σ4 p.1.loc p.1.ty p.2) ∧ CapsOk F ι σ4 caps Rc Hc := by
  have hrs : (armFn os rs op r arm).refs.map Prod.fst = rs := by
    simp only [armFn]; exact List.map_fst_zip (by omega)
  have hrefs : (armFn os rs op r arm).refs.map Prod.snd = hos.map (fun h => (h.mode, h.ty)) := by
    rw [hts]; simp only [armFn]; exact List.map_snd_zip (by omega)
  have hkeys : ((armFn os rs op r arm).owns.map Prod.fst ++ (armFn os rs op r arm).refs.map Prod.fst ++
      (capCtx (caps.map Cap.sig)).map Prod.fst).Nodup := by
    rw [hrs]
    have : (armFn os rs op r arm).owns.map Prod.fst = os := by
      simp only [armFn]; exact List.map_fst_zip (by omega)
    rw [this]
    simpa [capCtx, Cap.sig, Function.comp_def] using hnames
  have hsh : shape Γa = ownCtx (armFn os rs op r arm).owns ++ (refCtx (armFn os rs op r arm).refs ++
      capCtx (caps.map Cap.sig)) := by
    rw [typed_shape harm (by rw [armCtx_eq (r := r) (arm := arm)]; simpa [fnCtx, List.map_append, List.map_map,
      Function.comp_def, ownCtx, refCtx, armFn] using hkeys), armCtx_eq (r := r) (arm := arm), shape_append, ← armFn,
      shape_fnCtx, capCtx_ref.shape, List.append_assoc]
  obtain ⟨Γo, rfl, hΓo⟩ := shape_split (ownCtx (armFn os rs op r arm).owns) hsh (fun p hp => by
    rcases List.mem_append.mp hp with h | h
    · exact refCtx_refs _ p h
    · exact capCtx_ref p h)
  have hlo : Γo.length = cells.length := by
    have h1 := congrArg List.length hcells
    simp only [List.length_map] at h1
    rw [← shape_length, hΓo]; simp only [ownCtx, armFn, List.length_map, List.length_zip]; omega
  rw [List.append_assoc] at hI
  obtain ⟨Eo, So, Er, Sr, hfo, hfr, rfl, hS⟩ := hI.foot.split hlo
  have hlr : (refCtx (armFn os rs op r arm).refs).length = (rs.zip (hos.map Hole.loc)).length := by
    have := congrArg List.length hts
    simp only [List.length_map] at this
    simp [refCtx, armFn]; omega
  obtain ⟨Ep, Sp, Ec, Sc, hfp, hfc, rfl, rfl⟩ := hfr.split hlr
  have hfp' : Foot F ι σ3 (refCtx (armFn os rs op r arm).refs)
      (((armFn os rs op r arm).refs.map Prod.fst).zip (hos.map Hole.loc)) Ep Sp := by rw [hrs]; exact hfp
  obtain ⟨ps, hps, hlt, rfl, rfl⟩ := (foot_refs hrefs).mp hfp'
  have hcap := Foot.capsOk hfns hfc
  have hnd := hI.nodup
  obtain ⟨rfl, σ4', hdrop, hfg⟩ := dropCellsF hfl hfo hΓo (nodup_append_disj.mp hnd).1 hwf3
    (fun o ho => by
      simp only [armFn] at ho
      exact hcomp o.2 (List.of_mem_zip ho).2)
  simp only [List.nil_append] at hS
  obtain rfl := hdet _ _ hcap
  have hro := List.append_cancel_right hS
  have hdis := nodup_append_disj.mp hnd
  have hsnd : (armFn os rs op r arm).owns.map Prod.snd = op.owns := List.map_snd_zip (by omega)
  rw [hsnd] at hdrop hfg
  refine ⟨σ4', ps, Ec, Eo, hdrop, hfg, hps, by simp [List.append_assoc], hro.symm, fun σ4 hd4 => ?_⟩
  have hkeep4 := hd4.keep hwf3
  have hdisj : ∀ l ∈ mutCells ps ++ Ec ++ roCells ps ++ Sc, l ∉ Eo := fun l hl h => by
    simp only [List.mem_append] at hl
    rcases hl with ((h' | h') | h') | h'
    · exact hdis.2.2 l h (List.mem_append.mpr (.inl h'))
    · exact hdis.2.2 l h (List.mem_append.mpr (.inr h'))
    · exact hI.disj l (by simp [hS, h']) (by simp [h])
    · exact hI.disj l (by simp [hS, h']) (by simp [h])
  have hlive : ∀ l ∈ mutCells ps ++ Ec ++ roCells ps ++ Sc, σ3.mem l ≠ none := fun l hl => by
    simp only [List.mem_append] at hl
    rcases hl with ((h' | h') | h') | h'
    · exact hI.alloc l (by simp [h'])
    · exact hI.alloc l (by simp [h'])
    · exact hI.allocS l (by simp [hS, h'])
    · exact hI.allocS l (by simp [hS, h'])
  have hagk : Agree σ3 σ4 (mutCells ps ++ Ec ++ roCells ps ++ Sc) := hd4.keeps hwf3 hlive hdisj
  refine ⟨fun p hp => (hlt p hp).frame (hagk.mono fun l hl => ?_),
    hcap.frame <| hagk.mono fun l hl => by simp only [List.mem_append] at hl ⊢; grind⟩
  rcases mem_cells_of hp hl with hM | hR
  · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inl (List.mem_append.mpr (.inl hM)))))
  · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr hR)))

/-- The code a `handle` ran, resumed once its arm ended — with the arm's value, or unwinding to be
dropped: its frames as they were, the places the operation lent the arm holding the trees the arm left
there, and the `handle`'s frame in force again, with the trees the arm left at the places it was lent
`mut`. -/
theorem resume_ok [WorldOk F O ι.w] (hKk : EvalKOk F O m) (hRr : RetOk F O m)
    (hH : HandleOk F ι O σf e caps os rs arm post Γin Γout env Sin S r Fz Rc op) (hP : PostOk F O Γout env τ r post)
    (hK : FramesOk F O ι σf K op ⟨Γin, env, τ, Sin, .eff e :: r⟩ X hos A)
    (hR : Ready O hs r) (hA : ∀ a ∈ A, AimedIn a hs) (hwf : WF σr)
    (hag : Agree σf σr (X ++ Fz ++ S)) (halloc : ∀ l ∈ X ++ Fz ++ S, σf.mem l ≠ none)
    (hnd : (X ++ Fz).Nodup) (hSX : Disj S (X ++ Fz))
    (hps : ps.map Prod.fst = hos) (hnew : ∀ p ∈ ps, p.1.mode = .mut → LT F ι σr p.1.loc p.1.ty p.2)
    (hcaps : CapsOk F ι σr caps Rc Hc)
    (hN : (mutCells ps ++ Hc ++ Lv).Nodup) (hdN : Disj (X ++ Fz ++ S) (mutCells ps ++ Hc ++ Lv))
    (hin : (∃ v, r0 = .val v ∧ VT F ι σr op.ret v Lv) ∨ (∃ a k, r0 = .abort a k ∧ AimedIn a hs ∧ Lv = [])) :
    Post F ι O σr ((Fz ++ Hc) ++ (X ++ mutCells ps ++ Lv)) S Γout env τ r hs
      (evalK F O m hs σr (.capK τ e hid caps os rs arm post :: K) r0) := by
  -- Where each cell is: the frames' own, the frozen and the read are apart from what the arm left.
  have mXFS : ∀ l, l ∈ X ++ Fz ++ S ↔ l ∈ X ∨ l ∈ Fz ∨ l ∈ S := fun l => by simp
  have mN : ∀ l, l ∈ mutCells ps ++ Hc ++ Lv ↔ l ∈ mutCells ps ∨ l ∈ Hc ∨ l ∈ Lv := fun l => by simp
  have hXF : Disj X Fz := (nodup_append_disj.mp hnd).2.2
  have hN3 := nodup_append_disj.mp hN
  have hN2 := nodup_append_disj.mp hN3.1
  have dout : ∀ l, (l ∈ X ∨ l ∈ Fz ∨ l ∈ S) → (l ∈ mutCells ps ∨ l ∈ Hc ∨ l ∈ Lv) → False :=
    fun l h1 h2 => hdN l ((mXFS l).mpr h1) ((mN l).mpr h2)
  have hSin : ∀ l ∈ Sin, l ∈ Fz ∨ l ∈ S := hH.hSin
  have hagFS : Agree σf σr (Fz ++ S) := (hag.mono fun l hl => by simp only [List.mem_append] at hl ⊢; grind)
  have hf := FrameOk.capK (τ := τ) (hid := hid) (hH.transfer hagFS) hP hcaps
  have hFa : ∀ l ∈ X ++ Fz ++ S, σr.mem l ≠ none := fun l hl => by rw [hag l hl]; exact halloc l hl
  have hpost := hKk (Kont.push (.capK τ e hid caps os rs arm post) hs) _ σf K _ X hos A σr ps r0 op Lv hK
    (hf.ready hR) (fun a ha => (hA a ha).push) hwf
    ((hag.mono fun l hl => by
      simp only [List.mem_append] at hl ⊢
      rcases hl with h | h
      · exact .inl (.inl h)
      · rcases hSin l h with h | h
        · exact .inl (.inr h)
        · exact .inr h))
    (fun l hl => halloc l (by
      simp only [List.mem_append] at hl ⊢
      rcases hl with h | h
      · exact .inl (.inl h)
      · rcases hSin l h with h | h
        · exact .inl (.inr h)
        · exact .inr h))
    (nodup_append_disj.mp hnd).1 hps hnew hN2.1
    (fun l h1 h2 => dout l (.inl h1) (.inl h2))
    (fun l h1 h2 => by
      simp only [List.mem_append] at h2
      rcases hSin l h1 with h1 | h1
      · rcases h2 with (h2 | h2) | h2
        · exact hXF l h2 h1
        · exact dout l (.inr (.inl h1)) (.inl h2)
        · exact dout l (.inr (.inl h1)) (.inr (.inr h2))
      · rcases h2 with (h2 | h2) | h2
        · exact hSX l h1 (List.mem_append.mpr (.inl h2))
        · exact dout l (.inr (.inr h1)) (.inl h2)
        · exact dout l (.inr (.inr h1)) (.inr (.inr h2)))
    (by
      rcases hin with ⟨v, rfl, hv⟩ | ⟨a, k, rfl, ha, rfl⟩
      · refine .inl ⟨v, rfl, hv, fun l h1 h2 => ?_⟩
        rcases List.mem_append.mp h2 with h2 | h2
        · exact dout l (.inl h2) (.inr (.inr h1))
        · exact hN3.2.2 l (List.mem_append.mpr (.inl h2)) h1
      · exact .inr ⟨a, k, rfl, ha.push, rfl⟩)
  simp only [evalK]
  refine hRr hs _ _ σr _ _ _ (Fz ++ Hc) [] σr _ _ hf hR (fun _ h => by simp at h) hwf Agree.self
    (fun l hl => ?_) ?_ ?_ (fun l hl => hFa l (by simp [hl])) ?_ hpost
  · rcases List.mem_append.mp hl with h | h
    · exact hFa l (by simp [h])
    · exact hcaps.alloc l (List.mem_append.mpr (.inr h))
  · exact nodup_append_disj.mpr ⟨(nodup_append_disj.mp hnd).2.1, hN2.2.1, fun l h1 h2 => dout l (.inr (.inl h1)) (.inr (.inl h2))⟩
  · intro l h1 h2
    simp only [List.mem_append] at h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with (h2 | h2) | h2
    · exact hXF l h2 h1
    · exact dout l (.inr (.inl h1)) (.inl h2)
    · exact dout l (.inr (.inl h1)) (.inr (.inr h2))
    · exact dout l (.inl h2) (.inr (.inl h1))
    · exact hN2.2.2 l h2 h1
    · exact hN3.2.2 l (List.mem_append.mpr (.inr h1)) h2
  · intro l h1 h2
    simp only [List.mem_append] at h2
    rcases h2 with (h2 | h2) | (h2 | h2) | h2
    · exact hSX l h1 (List.mem_append.mpr (.inr h2))
    · exact dout l (.inr (.inr h1)) (.inr (.inl h2))
    · exact hSX l h1 (List.mem_append.mpr (.inl h2))
    · exact dout l (.inr (.inr h1)) (.inl h2)
    · exact dout l (.inr (.inr h1)) (.inr (.inr h2))

theorem dropRet_eq : dropRet (flushR F O n) τ o d res = ret F O n hs (.dropK τ o d) res := by
  rcases res with ⟨_ | _ | _ | _ | _, _⟩ <;> simp [ret, dropRet]

/-- An arm ended: its parameters dropped, the code its `handle` ran goes on with its value, or, if it
unwinds, is dropped first; a continuation taken in the arm keeps the code. -/
theorem ret_armK [WorldOk F O ι.w] (hfl : FlushOk F ι (flushR F O n)) {cells : Env} (hKo : ∀ m, n = m + 1 → EvalKOk F O m ∧ RetOk F O m)
    (hH : HandleOk F ι O σf e caps os rs arm post Γin Γout env Sin S r Fz Rc op) (hP : PostOk F O Γout env τ r post)
    (hK : FramesOk F O ι σf K op ⟨Γin, env, τ, Sin, .eff e :: r⟩ X hos AK)
    (hro : ∀ l ∈ roCells (olds hos), l ∈ X ∨ l ∈ Sin)
    (harm : Typed F O (armCtx os rs op (caps.map Cap.sig)) arm (armTy op post) Γa r) (hcells : cells.map Prod.fst = os)
    (hR : Ready O hs r) (hA : ∀ a ∈ AK, AimedIn a hs) (hwf : WF σ0)
    (hag : Agree σf σ0 (X ++ Fz ++ S)) (halloc : ∀ l ∈ X ++ Fz, σf.mem l ≠ none) (hnd : (X ++ Fz).Nodup)
    (hd : Disj (X ++ Fz) Ein) (hSa : ∀ l ∈ S, σ0.mem l ≠ none) (hSd : Disj S (X ++ Fz ++ Ein))
    (hp : Post F ι O σ0 Ein (roCells (olds hos) ++ Rc) Γa
      (cells ++ rs.zip (hos.map Hole.loc) ++ caps.map (fun c => (c.name, c.loc))) (armTy op post) r hs res) :
    Post F ι O σ0 (X ++ Fz ++ Ein) S Γout env τ r hs
      (ret F O n hs (.armK τ (op.owns.zip (cells.map Prod.snd)) (.capK τ e hid caps os rs arm post :: K) post) res) := by
  obtain ⟨-, -, -, -, -, -, -, -, hts, -, -, -, -⟩ := hK.base_of
  have hXa : ∀ l ∈ X ++ Fz, σ0.mem l ≠ none := fun l hl => by
    rw [hag l (List.mem_append.mpr (.inl hl))]; exact halloc l hl
  have hXSa : ∀ l ∈ X ++ Fz ++ S, σ0.mem l ≠ none := fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · exact hXa l h
    · exact hSa l h
  have hXSd : Disj (X ++ Fz ++ S) Ein := fun l hl h => by
    rcases List.mem_append.mp hl with hl | hl
    · exact hd l hl h
    · exact hSd l hl (List.mem_append.mpr (.inr h))
  have hfS : ∀ l ∈ S, σf.mem l ≠ none := fun l hl => by
    rw [← hag l (List.mem_append.mpr (.inr hl))]; exact hSa l hl
  have hSX : Disj S (X ++ Fz) := fun l hl h => hSd l hl (List.mem_append.mpr (.inl h))
  -- The arm ended with `L` its value's cells: its parameters dropped, the code its `handle` ran is
  -- resumed with what the arm left.
  have key : ∀ σ3 Ea L, Inv F ι σ3 Γa (cells ++ rs.zip (hos.map Hole.loc) ++ caps.map (fun c => (c.name, c.loc))) Ea
      (roCells (olds hos) ++ Rc) → Disj L Ea → Moves σ0 Ein σ3 Ea L →
      ∃ σ4', dropCells σ3 (op.owns.zip (cells.map Prod.snd)) = some σ4' ∧ ∃ Eo,
        FlushGives (flushR F O n (cellsKonts σ3 (op.owns.zip (cells.map Prod.snd)))  σ4') σ3 Eo ∧
        ∀ σ4, Dropped σ3 Eo σ4 → ∃ ps Hc, Agree σ3 σ4 L ∧ WF σ4 ∧
        ps.map Prod.fst = hos ∧ (∀ p ∈ ps, LT F ι σ4 p.1.loc p.1.ty p.2) ∧ CapsOk F ι σ4 caps Rc Hc ∧
        Agree σf σ4 (X ++ Fz ++ S) ∧ (mutCells ps ++ Hc).Nodup ∧ Disj L (mutCells ps ++ Hc) ∧
        Disj (X ++ Fz ++ S) (mutCells ps ++ Hc ++ L) ∧
        Moves σ0 (X ++ Fz ++ Ein) σ4 ((Fz ++ Hc) ++ (X ++ mutCells ps ++ L)) [] ∧
        roCells ps = roCells (olds hos) := by
    intro σ3 Ea L hI₃ hdL hm₃
    have hag3 := hm₃.keeps hwf hXSa hXSd
    obtain ⟨σ4', ps, Hc, Eo, hdrop, hfg, hps, rfl, hroc, hk4⟩ :=
      arm_end (r := r) hfl harm hH.hnames hH.hown hH.href hcells hts hI₃ (fun Rc' Hc' hc =>
        hH.hRcdet _ (World.le_refl _) σ3 Rc' Hc' (Agree.trans (hag.mono fun l hl => by simp only [List.mem_append] at hl ⊢; grind)
          (hag3.mono fun l hl => by simp only [List.mem_append] at hl ⊢; grind)) hc) hH.hfns hm₃.wf hH.hcomp
    refine ⟨σ4', hdrop, Eo, hfg, fun σ4 hd4 => ?_⟩
    obtain ⟨hlt, hcaps⟩ := hk4 σ4 hd4
    have hnd3 := hI₃.nodup
    obtain ⟨hdA, hdL'⟩ := hm₃.apart hwf hXSa hXSd
    have hagL : Agree σ3 σ4 L := hd4.keeps hm₃.wf (fun l hl => (hm₃.alloc l).mpr (.inr (.inr hl)))
      fun l hl h => hdL l hl (by simp [h])
    have hwf4 := hd4.wf
    have hag4 : Agree σf σ4 (X ++ Fz ++ S) := Agree.trans (Agree.trans hag hag3)
      (hd4.keeps hm₃.wf (fun l hl => by rw [hag3 l hl]; exact hXSa l hl) fun l hl h => hdA l hl (by simp [h]))
    have m3 := (hm₃.widen hXa hd).relabel (E'' := X ++ Fz ++ (mutCells ps ++ Hc ++ L) ++ Eo) (L'' := [])
      fun x => by simp only [List.mem_append, List.not_mem_nil, or_false]; grind
    have m4 : Moves σ3 (X ++ Fz ++ (mutCells ps ++ Hc ++ L) ++ Eo) σ4 (X ++ Fz ++ (mutCells ps ++ Hc ++ L)) [] :=
      (hd4.widen (X := X ++ Fz ++ (mutCells ps ++ Hc ++ L))
      (fun l hl => (m3.alloc l).mpr (.inr (.inl (List.mem_append.mpr (.inl hl)))))
      (by
        intro l hl hl'
        simp only [List.mem_append] at hl
        have hdE : Disj Eo (mutCells ps ++ Hc) :=
          (nodup_append_disj.mp (by simpa only [List.append_assoc] using hnd3)).2.2
        rcases hl with (h | h) | (h | h) | h
        · exact hdA l (by simp [h]) (by simp [hl'])
        · exact hdA l (by simp [h]) (by simp [hl'])
        · exact hdE l hl' (List.mem_append.mpr (.inl h))
        · exact hdE l hl' (List.mem_append.mpr (.inr h))
        · exact hdL l h (by simp [hl']))).relabel fun x => by simp
    refine ⟨ps, Hc, hagL, hwf4, hps, hlt, hcaps, hag4,
      (List.nodup_append.mp (by simpa [List.append_assoc] using hnd3)).2.1,
      fun l h1 h2 => hdL l h1 (by simp only [List.mem_append] at h2 ⊢; grind), ?_,
      (m3.trans m4 disj_nil_left hwf).relabel (fun x => by
        simp only [List.mem_append, List.not_mem_nil, or_false]; grind), hroc⟩
    intro l h1 h2
    simp only [List.mem_append] at h2
    rcases h2 with (h2 | h2) | h2
    · exact hdA l h1 (by simp [h2])
    · exact hdA l h1 (by simp [h2])
    · exact hdL' l h1 h2
  rcases res with ⟨res, σ3⟩
  cases res with
  | val w =>
    obtain ⟨Ea, Lw, hI₃, hvw, hdw, -, hm₃⟩ := hp
    obtain ⟨σ4', hdrop, Eo, hfg, hk⟩ := key σ3 Ea Lw hI₃ hdw hm₃
    simp only [ret, armEnd, hdrop]
    refine hfg.post fun σ4 hd4 => ?_
    obtain ⟨ps, Hc, hagL, hwf4, hps, hlt, hcaps, hag4, hN, hdLN, hdN, hm, hroc⟩ := hk σ4 hd4
    cases n with
    | zero => trivial
    | succ m =>
      obtain ⟨hKk, hRr⟩ := hKo m rfl
      cases post with
      | none =>
        refine post_after hm hwf (resume_ok hKk hRr hH hP hK hR hA hwf4 hag4 (fun l hl => ?_) hnd hSX hps
          (fun p hp _ => hlt p hp) hcaps ?_ hdN (.inl ⟨w, rfl, hvw.frame hagL⟩))
        · rcases List.mem_append.mp hl with h | h
          · exact halloc l h
          · exact hfS l h
        · exact nodup_append_disj.mpr ⟨hN, (hvw.frame hagL).nodup, fun l h1 h2 => hdLN l h2 h1⟩
      | some pst =>
        obtain ⟨C, τ', f, env', cps⟩ := pst
        have hτ : τ = τ' := hP.1.symm
        subst hτ
        obtain rfl : env' = env := hP.2.1
        have hvw4 := hvw.frame hagL
        simp only [armTy] at hvw4
        cases hvw4 with
        | tag hlt' hcS hcT =>
        rename_i a t _ _
        rcases t with _ | _
        · -- The arm is done without resuming: the code unwinds to a barrier, and the arm's value is
          -- the `handle`'s.
          simp only [Bool.false_eq_true, ↓reduceIte] at hlt'
          obtain ⟨w', R', ha, hw', rfl, haR⟩ := hlt'.contents hcT
          simp only [ha, Bool.false_eq_true, ↓reduceIte]
          generalize hσ5 : σ4.set a none = σ5
          have hk5 : ∀ l, l ≠ a → σ5.mem l = σ4.mem l := fun l hla => by
            rw [← hσ5]; simp [Store.set, hla]
          have ha5 : σ5.mem a = none := by rw [← hσ5]; simp [Store.set]
          have hwf5 : WF σ5 := by rw [← hσ5]; exact hwf4.set_none
          have hn5 : σ5.next = σ4.next := by rw [← hσ5]; rfl
          have hout : ∀ l, (l ∈ X ∨ l ∈ Fz ∨ l ∈ S ∨ l ∈ mutCells ps ∨ l ∈ Hc ∨ l ∈ R') → l ≠ a := by
            intro l hl e
            rcases hl with h | h | h | h | h | h
            · exact hdN l (by simp [h]) (by simp [e])
            · exact hdN l (by simp [h]) (by simp [e])
            · exact hdN l (by simp [h]) (by simp [e])
            · exact hdLN l (by simp [e]) (by simp [h])
            · exact hdLN l (by simp [e]) (by simp [h])
            · exact haR (e ▸ h)
          have hag45 : ∀ l, (l ∈ X ∨ l ∈ Fz ∨ l ∈ S ∨ l ∈ mutCells ps ∨ l ∈ Hc ∨ l ∈ R') →
              σ5.mem l = σ4.mem l := fun l hl => hk5 l (hout l hl)
          have hag5 : Agree σf σ5 (X ++ Fz ++ S) := Agree.ofTrans hag4 (fun _ h => h) (fun l hl => by
            have hl' := hl
            simp only [List.mem_append] at hl'
            rw [hag45 l (by rcases hl' with (h | h) | h <;> simp [h])]; exact hag4 l hl) (by rt_tac)
          have hw5 := hw'.frame (Agree.of' fun l hl => hag45 l <| by simp [hl])
          have hRcS : ∀ l ∈ Rc, l ∈ Fz ∨ l ∈ S := hH.hRc
          have hcaps5 := hcaps.frame (Agree.of' fun l hl => hag45 l <| by
            rcases List.mem_append.mp hl with h | h
            · rcases hRcS l h with h | h <;> simp [h]
            · simp [h])
          have hfS5 : ∀ l ∈ S, σ5.mem l ≠ none := fun l hl => by
            rw [hag45 l (by simp [hl]), hag4 l (List.mem_append.mpr (.inr hl))]; exact hfS l hl
          have hR' : Ready O (.abort .drop (σ5.ids + 1) :: hs) r :=
            ⟨.abort (by intro e h; cases h) hR.1, fun l hl => covers_cons _ hR.2 l hl⟩
          have hrs := resume_ok (hs := .abort .drop (σ5.ids + 1) :: hs) (σr := σ5.fresh.2) (Lv := [])
            (r0 := .abort (σ5.ids + 1) 0) (hid := hid) hKk hRr hH hP hK hR'
            (fun a ha => (hA a ha).imp_right fun ⟨l, hl⟩ => ⟨l, List.mem_cons_of_mem _ hl⟩) (hwf5 : WF _)
            (hag5.trans (Agree.of' fun _ _ => rfl)) (fun l hl => by
              rcases List.mem_append.mp hl with h | h
              · exact halloc l h
              · exact hfS l h) hnd hSX hps (fun p hp _ => (hlt p hp).frame (Agree.of' fun l hl => hag45 l <| by
                rcases mem_parts (s := p.1.slot) hl with h | h
                · exact .inr (.inr (.inr (.inl (mem_mutCells.mpr ⟨p, hp, h⟩))))
                · have h' : l ∈ roCells (olds hos) := hroc ▸ mem_roCells.mpr ⟨p, hp, h⟩
                  rcases hro l h' with h' | h'
                  · exact .inl h'
                  · rcases hH.hSin l h' with h'' | h''
                    · exact .inr (.inl h'')
                    · exact .inr (.inr (.inl h''))))
            (hcaps5.frame <| Agree.of' fun _ _ => rfl) (by simpa using hN) (fun l h1 h2 => hdN l h1 (by simp only [List.mem_append] at h2 ⊢; grind))
            (.inr ⟨_, 0, rfl, .inr ⟨.drop, List.mem_cons_self ..⟩, rfl⟩)
          simp only [List.append_nil] at hrs
          have hw6 : VT F ι σ5.fresh.2 τ w' R' := hw5.frame <| Agree.of' fun _ _ => rfl
          have hdone := ret_dropKv (σf := σ5.fresh.2) (v := w') hfl hw6 hR.2 Agree.self
            (fun l hl => hw6.alloc l hl) hw6.nodup
            (fun l h1 h2 => by
              simp only [List.mem_append] at h2
              rcases h2 with (h2 | h2) | (h2 | h2)
              · exact hdN l (by simp [h2]) (by simp [h1])
              · exact hdLN l (by simp [h1]) (by simp [h2])
              · exact hdN l (by simp [h2]) (by simp [h1])
              · exact hdLN l (by simp [h1]) (by simp [h2]))
            (fun l h1 h2 => hdN l (by simp [h1]) (by simp [h2]))
            (fun l h1 h2 => by
              simp only [List.mem_append] at h2
              rcases h2 with (h2 | h2) | (h2 | h2)
              · exact hSX l h1 (by simp [h2])
              · exact hdN l (by simp [h1]) (by simp [h2])
              · exact hSX l h1 (by simp [h2])
              · exact hdN l (by simp [h1]) (by simp [h2]))
            hfS5 (hwf5 : WF _) hrs
          have hfree : Moves σ4 ((Fz ++ Hc) ++ (X ++ mutCells ps ++ (a :: R'))) σ5.fresh.2
              (R' ++ ((Fz ++ Hc) ++ (X ++ mutCells ps))) [] :=
            Moves.free (D := [a]) (hwf5 : WF _) hn5 (fun l hl => (hm.alloc l).mpr (.inr (.inl hl)))
              (fun l => by simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; grind)
              (fun l hl => by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
                subst hl; exact ha5)
              (fun l hl => hk5 l (fun e => hl (by simp [e])))
              (fun l h1 h2 => by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
                subst h2
                simp only [List.mem_append] at h1
                rcases h1 with h | ((h | h) | (h | h))
                · exact haR h
                · exact hout _ (.inr (.inl h)) rfl
                · exact hout _ (.inr (.inr (.inr (.inr (.inl h))))) rfl
                · exact hout _ (.inl h) rfl
                · exact hout _ (.inr (.inr (.inr (.inl h)))) rfl)
          exact post_after hm hwf (post_after hfree hwf4 hdone)
        -- The arm resumes: a pair of what the code resumes with and what it carries past.
        simp only [↓reduceIte] at hlt'
        obtain ⟨wp, Rp, ha, hwp, rfl, haR⟩ := hlt'.contents hcS
        cases hwp with
        | pair h1 h2 hdR hcA hcC =>
        rename_i b R1 c R2
        obtain ⟨vr, R1', hb, hvr, rfl, hbR⟩ := h1.contents hcA
        obtain ⟨vc, R2', hc, hvc, rfl, hcR⟩ := h2.contents hcC
        simp only [ha, hb, hc, ↓reduceIte]
        have hbc : b ≠ c := fun e => hdR b (List.mem_cons_self ..) (e ▸ List.mem_cons_self ..)
        have hbR2 : b ∉ R2' := fun h => hdR b (List.mem_cons_self ..) (List.mem_cons_of_mem _ h)
        have hcR1 : c ∉ R1' := fun h => hdR c (List.mem_cons_of_mem _ h) (List.mem_cons_self ..)
        have hdR12 : Disj R1' R2' := fun l h1 h2 => hdR l (List.mem_cons_of_mem _ h1) (List.mem_cons_of_mem _ h2)
        have hab : a ≠ b := fun e => haR (by simp [e])
        have hac : a ≠ c := fun e => haR (by simp [e])
        generalize hσ5 : ((σ4.set a none).set b none).set c none = σ5
        have hk5 : ∀ l, l ≠ a → l ≠ b → l ≠ c → σ5.mem l = σ4.mem l := fun l hla hlb hlc => by
          rw [← hσ5]; simp [Store.set, hla, hlb, hlc]
        have hbc5 : σ5.mem a = none ∧ σ5.mem b = none ∧ σ5.mem c = none := by
          rw [← hσ5]; simp [Store.set, hbc, hab, hac]
        have hwf5 : WF σ5 := by rw [← hσ5]; exact ((hwf4.set_none).set_none).set_none
        have hn5 : σ5.next = σ4.next := by rw [← hσ5]; rfl
        -- Where `a`, `b` and `c` are not: in the arm's value only.
        have hout : ∀ l, (l ∈ X ∨ l ∈ Fz ∨ l ∈ S ∨ l ∈ mutCells ps ∨ l ∈ Hc ∨ l ∈ R1' ∨ l ∈ R2') →
            l ≠ a ∧ l ≠ b ∧ l ≠ c := by
          intro l hl
          refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
          · rcases hl with h | h | h | h | h | h | h
            · exact hdN l (by simp [h]) (by simp [e])
            · exact hdN l (by simp [h]) (by simp [e])
            · exact hdN l (by simp [h]) (by simp [e])
            · exact hdLN l (by simp [e]) (by simp [h])
            · exact hdLN l (by simp [e]) (by simp [h])
            · exact haR (by simp [← e, h])
            · exact haR (by simp [← e, h])
          · rcases hl with h | h | h | h | h | h | h
            · exact hdN l (by simp [h]) (by simp [e])
            · exact hdN l (by simp [h]) (by simp [e])
            · exact hdN l (by simp [h]) (by simp [e])
            · exact hdLN l (by simp [e]) (by simp [h])
            · exact hdLN l (by simp [e]) (by simp [h])
            · exact hbR (e ▸ h)
            · exact hbR2 (e ▸ h)
          · rcases hl with h | h | h | h | h | h | h
            · exact hdN l (by simp [h]) (by simp [e])
            · exact hdN l (by simp [h]) (by simp [e])
            · exact hdN l (by simp [h]) (by simp [e])
            · exact hdLN l (by simp [e]) (by simp [h])
            · exact hdLN l (by simp [e]) (by simp [h])
            · exact hcR1 (e ▸ h)
            · exact hcR (e ▸ h)
        have hag45 : ∀ l, (l ∈ X ∨ l ∈ Fz ∨ l ∈ S ∨ l ∈ mutCells ps ∨ l ∈ Hc ∨ l ∈ R1' ∨ l ∈ R2') →
            σ5.mem l = σ4.mem l := fun l hl => hk5 l (hout l hl).1 (hout l hl).2.1 (hout l hl).2.2
        have hag5 : Agree σf σ5 (X ++ Fz ++ S) := Agree.ofTrans hag4 (fun _ h => h) (fun l hl => by
          have hl' := hl
          simp only [List.mem_append] at hl'
          rw [hag45 l (by rcases hl' with (h | h) | h <;> simp [h])]; exact hag4 l hl) (by rt_tac)
        have hvr5 := hvr.frame (Agree.of' fun l hl => hag45 l <| by simp [hl])
        have hvc5 := hvc.frame (Agree.of' fun l hl => hag45 l <| by simp [hl])
        have hRcS : ∀ l ∈ Rc, l ∈ Fz ∨ l ∈ S := hH.hRc
        have hcaps5 := hcaps.frame (Agree.of' fun l hl => hag45 l <| by
          rcases List.mem_append.mp hl with h | h
          · rcases hRcS l h with h | h <;> simp [h]
          · simp [h])
        have hfS5 : ∀ l ∈ S, σ5.mem l ≠ none := fun l hl => by
          rw [hag45 l (by simp [hl]), hag4 l (List.mem_append.mpr (.inr hl))]; exact hfS l hl
        have hdN' : Disj (X ++ Fz ++ S) (mutCells ps ++ Hc ++ R1') := fun l h1 h2 => by
          simp only [List.mem_append] at h2
          rcases h2 with (h2 | h2) | h2
          · exact hdN l h1 (by simp [h2])
          · exact hdN l h1 (by simp [h2])
          · exact hdN l h1 (by simp [h2])
        have hN' : (mutCells ps ++ Hc ++ R1').Nodup := nodup_append_disj.mpr ⟨hN, hvr5.nodup,
          fun l h1 h2 => hdLN l (by simp [h2]) h1⟩
        have hres := resume_ok (σr := σ5) (Lv := R1') (r0 := .val vr) (hid := hid) hKk hRr hH hP hK hR hA hwf5
          hag5 (fun l hl => by
            rcases List.mem_append.mp hl with h | h
            · exact halloc l h
            · exact hfS l h) hnd hSX hps (fun p hp _ => (hlt p hp).frame (Agree.of' fun l hl => hag45 l <| by
              rcases mem_parts (s := p.1.slot) hl with h | h
              · exact .inr (.inr (.inr (.inl (mem_mutCells.mpr ⟨p, hp, h⟩))))
              · have h' : l ∈ roCells (olds hos) := hroc ▸ mem_roCells.mpr ⟨p, hp, h⟩
                rcases hro l h' with h' | h'
                · exact .inl h'
                · rcases hH.hSin l h' with h'' | h''
                  · exact .inr (.inl h'')
                  · exact .inr (.inr (.inl h''))))
            hcaps5 hN' hdN' (.inl ⟨vr, rfl, hvr5⟩)
        -- What the arm carried waits for the rest of the `handle`, its cells the post frame's.
        have hdc : Disj R2' ((Fz ++ Hc) ++ (X ++ mutCells ps ++ R1')) := fun l h1 h2 => by
          simp only [List.mem_append] at h2
          rcases h2 with (h2 | h2) | (h2 | h2) | h2
          · exact hdN l (by simp [h2]) (by simp [h1])
          · exact hdLN l (by simp [h1]) (by simp [h2])
          · exact hdN l (by simp [h2]) (by simp [h1])
          · exact hdLN l (by simp [h1]) (by simp [h2])
          · exact hdR12 l h2 h1
        have hpost := hRr hs _ _ σ5 (.postR C f vc env' cps) ⟨Γout, env', τ, S, r⟩ ⟨Γout, env', τ, S, r⟩ R2' [] σ5
          ((Fz ++ Hc) ++ (X ++ mutCells ps ++ R1')) _ (.postR hP hvc5) hR (fun _ h => by simp at h) hwf5
          Agree.self (fun l hl => hvc5.alloc l hl) hvc5.nodup hdc hfS5
          (fun l hl h => by
            simp only [List.mem_append] at h
            rcases h with h | ((h | h) | (h | h) | h)
            · exact hdN l (by simp [hl]) (by simp [h])
            · exact hSX l hl (by simp [h])
            · exact hdN l (by simp [hl]) (by simp [h])
            · exact hSX l hl (by simp [h])
            · exact hdN l (by simp [hl]) (by simp [h])
            · exact hdN l (by simp [hl]) (by simp [h])) hres
        -- The pair's own cells freed.
        have hfree : Moves σ4 ((Fz ++ Hc) ++ (X ++ mutCells ps ++ (a :: ((b :: R1') ++ (c :: R2'))))) σ5
            (R2' ++ ((Fz ++ Hc) ++ (X ++ mutCells ps ++ R1'))) [] :=
          Moves.free (D := [a, b, c]) hwf5 hn5 (fun l hl => (hm.alloc l).mpr (.inr (.inl hl)))
            (fun l => by simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; grind)
            (fun l hl => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
              rcases hl with rfl | rfl | rfl
              · exact hbc5.1
              · exact hbc5.2.1
              · exact hbc5.2.2)
            (fun l hl => hk5 l (fun e => hl (by simp [e])) (fun e => hl (by simp [e])) (fun e => hl (by simp [e])))
            (fun l h1 h2 => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
              have hh := hout l (by
                simp only [List.mem_append] at h1
                rcases h1 with h | ((h | h) | (h | h) | h)
                · exact .inr (.inr (.inr (.inr (.inr (.inr h)))))
                · exact .inr (.inl h)
                · exact .inr (.inr (.inr (.inr (.inl h))))
                · exact .inl h
                · exact .inr (.inr (.inr (.inl h)))
                · exact .inr (.inr (.inr (.inr (.inr (.inl h))))))
              rcases h2 with rfl | rfl | rfl
              · exact hh.1 rfl
              · exact hh.2.1 rfl
              · exact hh.2.2 rfl)
        exact post_after ((hm.trans hfree disj_nil_left hwf).relabel fun x => by simp) hwf hpost
  | abort j k =>
    obtain ⟨haim, Ea, hI₃, hm₃⟩ := hp
    obtain ⟨σ4', hdrop, Eo, hfg, hk⟩ := key σ3 Ea [] hI₃ disj_nil_left (by simpa using hm₃)
    simp only [ret, armEnd, hdrop]
    refine hfg.post fun σ4 hd4 => ?_
    obtain ⟨ps, Hc, -, hwf4, hps, hlt, hcaps, hag4, hN, -, hdN, hm, -⟩ := hk σ4 hd4
    cases n with
    | zero => trivial
    | succ m =>
      obtain ⟨hKk, hRr⟩ := hKo m rfl
      simp only [List.append_nil] at hm hdN
      dsimp only
      have hR' : Ready O (.abort .drop (σ4.ids + 1) :: hs) r :=
        ⟨.abort (by intro e h; cases h) hR.1, fun l hl => covers_cons _ hR.2 l hl⟩
      have hrs := resume_ok (hs := .abort .drop (σ4.ids + 1) :: hs) (σr := σ4.fresh.2) (Lv := [])
        (r0 := .abort (σ4.ids + 1) 0) (hid := hid) hKk hRr hH hP hK hR'
        (fun a ha => (hA a ha).imp_right fun ⟨l, hl⟩ => ⟨l, List.mem_cons_of_mem _ hl⟩) (hwf4 : WF _)
        (hag4.trans (Agree.of' fun _ _ => rfl)) (fun l hl => by
          rcases List.mem_append.mp hl with h | h
          · exact halloc l h
          · exact hfS l h) hnd hSX hps (fun p hp _ => (hlt p hp).frame <| Agree.of' fun _ _ => rfl)
        (hcaps.frame <| Agree.of' fun _ _ => rfl) (by simpa using hN) (by simpa using hdN)
        (.inr ⟨_, 0, rfl, .inr ⟨.drop, List.mem_cons_self ..⟩, rfl⟩)
      simp only [List.append_nil] at hrs
      exact post_after hm hwf (post_after (Moves.freshen hwf4 fun l hl => (hm.alloc l).mpr (.inr (.inl hl))) hwf4
        (ret_dropK hfl haim hR.2 (hwf4 : WF _) hrs))
  | susp j ef vs ls K' =>
    obtain ⟨op', X', hos', A', Lw, hc, hop, hcov, haim, hK', hls, hvs, hn, hdw, hdS, hm⟩ := hp
    obtain ⟨hdX, hdL⟩ := hm.apart hwf hXa hd
    have hK'' := FramesOk.cons (A := AK ++ A') (.armK (hid := hid) hH hP hK hro harm hcells) (Weaker.refl _)
      ((Agree.trans (hag) ((hm.keeps hwf hXSa hXSd)))) halloc hnd hdX hK'
      (fun a ha => List.mem_append.mpr (.inl ha)) (fun a ha => .inl (List.mem_append.mpr (.inr ha)))
    simp only [ret]
    refine ⟨op', X ++ Fz ++ X', hos', AK ++ A', Lw, hc, hop, hcov, fun a ha => ?_, hK'', hls, hvs, hn, ?_,
      fun l hl h => (hm.apart hwf hSa (fun l hl h => hSd l hl (List.mem_append.mpr (.inr h)))).2 l h hl, ?_⟩
    · rcases List.mem_append.mp ha with h | h
      · exact hA a h
      · exact haim a h
    · intro l hl h
      simp only [List.mem_append] at h
      rcases h with ((h | h) | h) | h
      · exact hdL l (by simp [h]) hl
      · exact hdL l (by simp [h]) hl
      · exact hdw l hl (by simp [h])
      · exact hdw l hl (by simp [h])
    · exact (hm.widen hXa hd).relabel fun x => by simp only [List.mem_append, List.append_assoc]
  | stuck => simp [Post] at hp
  | timeout => simp [ret, Post]
  | ended => simp [ret, Post]

theorem ret_armK_eq : ret F O n hs (.armK τ cells K post) res =
    armEnd (flushR F O n) τ cells K post
      (fun σ v => match n with
        | 0 => (.timeout, σ)
        | m + 1 =>
          match post with
          | none => evalK F O m hs σ K (.val v)
          | some (C, _, f, env', cps) =>
            match v with
            | .tag _ _ t l =>
              match σ.mem l with
              | some w =>
                if t then
                  match w with
                  | .pair b c =>
                    match σ.mem b, σ.mem c with
                    | some vr, some vc =>
                      ret F O m hs (.postR C f vc env' cps)
                        (evalK F O m hs (((σ.set l none).set b none).set c none) K (.val vr))
                    | _, _ => (.stuck, σ)
                  | _ => (.stuck, σ)
                else
                  let (d, σ1) := (σ.set l none).fresh
                  dropRet (flushR F O (m + 1)) τ (.val w) d (evalK F O m (.abort .drop d :: hs) σ1 K (.abort d 0))
              | none => (.stuck, σ)
            | _ => (.stuck, σ))
      (fun σ o => match n with
        | 0 => (.timeout, σ)
        | m + 1 =>
          let (d, σ1) := σ.fresh
          dropRet (flushR F O (m + 1)) τ o d (evalK F O m (.abort .drop d :: hs) σ1 K (.abort d 0))) res := by
  rcases res with ⟨_ | _ | _ | _ | _, _⟩ <;> simp only [ret, armEnd] <;> rfl

theorem ret_capK_catch (hH : HandleOk F ι O σf e caps os rs arm post Γin Γout env Sin S r Fz Rc op)
    (hl : vs.length = os.length ∧ ls.length = rs.length) :
    ret F O n hs (.capK τ e hid caps os rs arm post) (.susp hid e vs ls K, σ) = ret F O n hs (.armK τ (op.owns.zip ((allocAll σ (os.zip vs)).1.map Prod.snd)) (.capK τ e hid caps os rs arm post :: K) post)
      (eval F O n hs (allocAll σ (os.zip vs)).2 ((allocAll σ (os.zip vs)).1 ++ rs.zip ls ++ caps.map (fun c => (c.name, c.loc))) arm) := by
  rw [ret_armK_eq]
  simp only [ret, ne_eq, not_true_eq_false, or_self, ↓reduceIte, hH.hop, hl, and_self]
  rfl

theorem armCtx_keys (hown : os.length = op.owns.length) (href : rs.length = op.refs.length) :
    (armCtx os rs op caps).map Prod.fst = os ++ rs ++ caps.map Prod.fst := by
  simp only [armCtx, List.map_append, List.map_map, Function.comp_def]
  rw [show (os.zip op.owns).map (fun x => x.1) = os from List.map_fst_zip (by omega),
    show (rs.zip op.refs).map (fun x => x.1) = rs from List.map_fst_zip (by omega)]

/-- The body of a `handle` whose arm resumes ended: if it performed the `handle`'s operation, the arm
runs, lent the places the operation lent and those the `handle` did, and then the body goes on with
what the arm gave; otherwise the activation is the `handle`'s again. -/
theorem ret_capK [WorldOk F O ι.w] (hfl : FlushOk F ι (flushR F O n)) (hE : EvalOk F O n) (hKo : ∀ m, n = m + 1 → EvalKOk F O m ∧ RetOk F O m)
    (hH : HandleOk F ι O σf e caps os rs arm post Γin Γout env Sin S r Fz Rc op) (hP : PostOk F O Γout env τ r post)
    (hcaps : CapsOk F ι σf caps Rc Hc) (hR : Ready O hs r) (hwf : WF σ0)
    (hag : Agree σf σ0 (Fz ++ Hc ++ S)) (halloc : ∀ l ∈ Fz ++ Hc, σf.mem l ≠ none) (hnd : (Fz ++ Hc).Nodup)
    (hd : Disj (Fz ++ Hc) Ein) (hSa : ∀ l ∈ S, σ0.mem l ≠ none) (hSd : Disj S (Fz ++ Hc ++ Ein))
    (hp : Post F ι O σ0 Ein Sin Γin env τ (.eff e :: r) (.capture e hid :: hs) res) :
    Post F ι O σ0 (Fz ++ Hc ++ Ein) S Γout env τ r hs (ret F O n hs (.capK τ e hid caps os rs arm post) res) := by
  have hSHc : Disj S Hc := fun l h1 h2 => hSd l h1 (by simp [h2])
  have hFHc := nodup_append_disj.mp hnd
  have hRcO : ∀ l ∈ Rc ++ Hc, l ∈ Fz ++ Hc ++ S := fun l hl => by
    rcases List.mem_append.mp hl with hl | hl
    · rcases hH.hRc l hl with h | h <;> simp [h]
    · simp [hl]
  have hA : ∀ a, AimedIn a (.capture e hid :: hs) → AimedIn a hs := fun a h =>
    h.imp_right fun ⟨l, hl⟩ => ⟨l, (List.mem_cons.mp hl).resolve_left (by simp)⟩
  rcases res with ⟨res, σ1⟩
  -- What the body gave, but for its handle's operation: the activation is the `handle`'s again.
  have pass : (∀ j ef vs ls K, res = .susp j ef vs ls K → j ≠ hid ∨ ef ≠ e) →
      Post F ι O σ0 (Fz ++ Hc ++ Ein) S Γout env τ r hs (ret F O n hs (.capK τ e hid caps os rs arm post) (res, σ1)) := by
    intro hnot
    have : ret F O n hs (.capK τ e hid caps os rs arm post) (res, σ1) = passK (.capK τ e hid caps os rs arm post) (res, σ1) := by
      cases res with
      | susp j ef vs ls K => simp [ret, passK, hnot j ef vs ls K rfl]
      | _ => simp [ret, passK]
    rw [this]
    refine post_pass (.capK hH hP hcaps) hH.hS ?_ hR.2 hA ?_ hwf hag halloc hnd hd hSa hSd hp
    · intro σ2 Eb hag2 hdE hI2
      obtain ⟨E', hI', hmem⟩ := hH.hre _ (World.le_refl _) σ2 Eb Hc ((hag2.mono fun l hl => by simp only [List.mem_append] at hl ⊢; grind))
        hdE hSHc hnd (hcaps.frame (hag2.mono fun l hl => hRcO l hl)) hI2
      exact ⟨E', hI', fun z => by rw [hmem]; simp only [List.mem_append]⟩
    · intro j ef vs ls K σ' h hc
      have h1 := hnot j ef vs ls K (congrArg Prod.fst h)
      rcases hc.of_cons_capture with ⟨rfl, rfl⟩ | h
      · simp at h1
      · exact h
  cases res with
  | val v => exact pass fun _ _ _ _ _ h => by cases h
  | abort j k => exact pass fun _ _ _ _ _ h => by cases h
  | stuck => exact pass fun _ _ _ _ _ h => by cases h
  | timeout => exact pass fun _ _ _ _ _ h => by cases h
  | ended => exact pass fun _ _ _ _ _ h => by cases h
  | susp j ef vs ls K =>
  by_cases hc : j ≠ hid ∨ ef ≠ e
  · exact pass fun _ _ _ _ _ h => by cases h; exact hc
  simp only [ne_eq, not_or, Decidable.not_not] at hc
  obtain ⟨h1, h2⟩ := hc
  subst j ef
  obtain ⟨op', X, hos, A, Lv, -, hop', -, haim, hK, rfl, hvs, hLn, hdLX, hdLS, hm⟩ := hp
  obtain rfl : op = op' := Option.some.inj (hH.hop.symm.trans hop')
  obtain ⟨ι₁, Γ₁, env₁, E₁, S₁, hI₁, hholes, hpw, hts, hE₁, hS₁, hXn, hXM, hw₁⟩ := hK.base_of
  have hw₁' := hw₁.symm
  obtain ⟨Γa, harm⟩ := hH.harm
  have hwf₁ := hm.wf
  have hlenl : hos.length = rs.length := by
    have := congrArg List.length hts
    simp only [List.length_map] at this
    rw [this, hH.href]
  have hlenv : vs.length = os.length := by rw [hvs.length, hH.hown]
  rw [ret_capK_catch hH ⟨hlenv, by simpa using hlenl⟩]
  have hcf : (allocAll σ1 (os.zip vs)).1.map Prod.fst = os := by
    rw [allocAll_fst]; exact List.map_fst_zip (by omega)
  obtain ⟨Eo, hfo, hEo, hEomem, hle, hwf₂, hold, hnew, -⟩ :=
    allocAll_ok (names := os) hvs (by rw [hH.hown]) hwf₁ hLn
  have hrtAl := allocAll_rt σ1 (os.zip vs)
  generalize allocAll σ1 (os.zip vs) = al at hfo hEomem hle hwf₂ hold hnew hcf hrtAl ⊢
  obtain ⟨cells, σ2⟩ := al
  dsimp only at hfo hEomem hle hwf₂ hold hnew hcf hrtAl ⊢
  -- The `handle`'s cells, frozen or lent its arm, and what its activation reads: apart from all the
  -- body did, and from the arm's new cells.
  have hOa : ∀ l ∈ Fz ++ Hc ++ S, σ0.mem l ≠ none := fun l hl => by
    rw [hag l hl]
    rcases List.mem_append.mp hl with h | h
    · exact halloc l h
    · rw [← hag l hl]; exact hSa l h
  have hOd : Disj (Fz ++ Hc ++ S) Ein := fun l hl h => by
    rcases List.mem_append.mp hl with hl | hl
    · exact hd l hl h
    · exact hSd l hl (by simp [h])
  obtain ⟨hOB, hOL⟩ := hm.apart hwf hOa hOd
  have hag01 := hm.keeps hwf hOa hOd
  have hOa1 : ∀ l ∈ Fz ++ Hc ++ S, σ1.mem l ≠ none := fun l hl => by rw [hag01 l hl]; exact hOa l hl
  have hOEo : ∀ l ∈ Fz ++ Hc ++ S, l ∉ Eo := fun l hl h => by
    rcases (hEomem l).mp h with h | h
    · exact hOL l hl h
    · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hwf₁ l (hOa1 l hl)) h.1)
  have hag12 : ∀ l, σ1.mem l ≠ none → σ2.mem l = σ1.mem l := fun l h => hold l (hwf₁ l h)
  have hXa1 : ∀ l ∈ X, σ1.mem l ≠ none := fun l hl => (hm.alloc l).mpr (.inr (.inl (by simp [hl])))
  have hMa1 : ∀ l ∈ mutCells (olds hos), σ1.mem l ≠ none := fun l hl =>
    (hm.alloc l).mpr (.inr (.inl (by simp [hl])))
  have hXEo : ∀ l ∈ X, l ∉ Eo := fun l hl h => by
    rcases (hEomem l).mp h with h | h
    · exact hdLX l h (by simp [hl])
    · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hwf₁ l (hXa1 l hl)) h.1)
  -- The arm's activation: its owned parameters, the places the operation lent, and those its
  -- `handle` did.
  have hrefs : (armFn os rs op r arm).refs.map Prod.snd = hos.map (fun h => (h.mode, h.ty)) := by
    rw [hts]; simp only [armFn]; exact List.map_snd_zip (by have := hH.href; omega)
  have hrs : (armFn os rs op r arm).refs.map Prod.fst = rs := by
    simp only [armFn]; exact List.map_fst_zip (by have := hH.href; omega)
  have hkeys : ((armFn os rs op r arm).owns.map Prod.fst ++ (armFn os rs op r arm).refs.map Prod.fst).Nodup := by
    rw [hrs, show (armFn os rs op r arm).owns.map Prod.fst = os from List.map_fst_zip (by have := hH.hown; omega)]
    exact (List.nodup_append.mp hH.hnames).1
  have hIc := callee_inv (k := 0) (d := armFn os rs op r arm) (Lall := Lv.flatten) hI₁ hholes hpw (by simpa using hrefs) hkeys hfo hEo
    (fun l hl => by
      rcases (hEomem l).mp hl with h | h
      · exact .inl h
      · exact .inr h.1)
    (fun l hl h => by
      by_cases hM : l ∈ mutCells (olds hos)
      · exact hdLX l hl (by simp [hM])
      · exact hdLX l hl (by simp [hE₁ l h hM]))
    (fun l hl h => by
      rcases hS₁ l h with h | h
      · exact hdLX l hl (by simp [h])
      · exact hdLS l hl h) hwf₁ hold (by rt_tac)
    (fun h hh L hL => by simpa using hL.rfree_iota (op.refs_rfree _ (by rw [← hts]; exact List.mem_map_of_mem hh)))
  rw [hrs] at hIc
  have hro : ∀ l ∈ roCells (olds hos), l ∈ X ∨ l ∈ Sin := fun l hl => by
    obtain ⟨h, hh, hlo⟩ := mem_olds_ro.mp hl
    rcases (hole_in hI₁ (hholes h hh)).1 l (List.mem_append.mpr (.inr (sharedPart_sub hlo))) with h' | h'
    · exact .inl (hE₁ l h' fun hM => hIc.disj l hl (by simp [hM]))
    · exact hS₁ l h'
  have hcaps2 : CapsOk F ι σ2 caps Rc Hc := hcaps.frame (Agree.ofTrans (Agree.trans hag hag01) hRcO (fun l hl => by
    have hO := hRcO l hl
    rw [hag12 l (hOa1 l hO), hag01 l hO, hag l hO]) (by rt_tac))
  have hIa : Inv F ι σ2 (armCtx os rs op (caps.map Cap.sig))
      (cells ++ rs.zip (hos.map Hole.loc) ++ caps.map (fun c => (c.name, c.loc)))
      (Eo ++ mutCells (olds hos) ++ Hc) (roCells (olds hos) ++ Rc) := by
    refine ⟨?_, nodup_append_disj.mpr ⟨hIc.nodup, hFHc.2.1, ?_⟩, ?_, ?_⟩
    · rw [armCtx_eq (r := r) (arm := arm)]
      exact hIc.foot.append hcaps2.foot
    · intro l h1 h2
      rcases List.mem_append.mp h1 with h1 | h1
      · exact hOEo l (by simp [h2]) h1
      · exact hOB l (by simp [h2]) (by simp [h1])
    · intro l h1 h2
      have hRcO' : l ∈ Rc → l ∈ Fz ++ Hc ++ S := fun h => hRcO l (by simp [h])
      simp only [List.mem_append] at h1 h2
      rcases h1 with h1 | h1
      · rcases h2 with h2 | h2
        · exact hIc.disj l h1 (by simpa using h2)
        · rcases hro l h1 with h | h
          · exact hOB l (by simp [h2]) (by simp [h])
          · rcases hH.hSin l h with h | h
            · exact hFHc.2.2 l h h2
            · exact hSHc l h h2
      · have hO := hRcO' h1
        rcases h2 with (h2 | h2) | h2
        · exact hOEo l hO h2
        · exact hOB l hO (by simp [h2])
        · rcases hH.hRc l h1 with h | h
          · exact hFHc.2.2 l h h2
          · exact hSHc l h h2
    · rw [armCtx_keys hH.hown hH.href]
      simpa [Cap.sig, Function.comp_def] using hH.hnames
  have hp2 := hE hs σ2 _ _ _ _ _ arm (armTy op post) Γa r harm hIa hwf₂ hR
  have hSFX : ∀ l, l ∈ Fz ++ Hc ++ S → l ∉ X := fun l hl h => hOB l hl (by simp [h])
  have hkey := ret_armK (cells := cells) (hid := hid) (σ0 := σ2) hfl hKo
    (hH.transfer (Agree.trans (hag.mono fun l hl => by simp only [List.mem_append] at hl ⊢; grind)
      (hag01.mono fun l hl => by simp only [List.mem_append] at hl ⊢; grind))) hP
    hK hro harm hcf hR (fun a ha => hA a (haim a ha)) hwf₂
    ((Agree.of' fun l hl => hag12 l <| by
      simp only [List.mem_append] at hl
      rcases hl with (h | h) | h
      · exact hXa1 l h
      · exact hOa1 l (by simp [h])
      · exact hOa1 l (by simp [h])))
    (fun l hl => by
      rcases List.mem_append.mp hl with h | h
      · exact hXa1 l h
      · exact hOa1 l (by simp [h]))
    (nodup_append_disj.mpr ⟨hXn, hFHc.1, fun l h1 h2 => hSFX l (by simp [h2]) h1⟩)
    (by
      intro l h1 h2
      simp only [List.mem_append] at h1 h2
      rcases h1 with h1 | h1 <;> rcases h2 with (h2 | h2) | h2
      · exact hXEo l h1 h2
      · exact hXM l h1 h2
      · exact hSFX l (by simp [h2]) h1
      · exact hOEo l (by simp [h1]) h2
      · exact hOB l (by simp [h1]) (by simp [h2])
      · exact hFHc.2.2 l h1 h2)
    (fun l hl => by rw [hag12 l (hOa1 l (by simp [hl]))]; exact hOa1 l (by simp [hl]))
    (by
      intro l h1 h2
      simp only [List.mem_append] at h2
      rcases h2 with (h2 | h2) | (h2 | h2) | h2
      · exact hSFX l (by simp [h1]) h2
      · exact hSd l h1 (by simp [h2])
      · exact hOEo l (by simp [h1]) h2
      · exact hOB l (by simp [h1]) (by simp [h2])
      · exact hSHc l h1 h2)
    hp2
  refine post_after ?_ hwf hkey
  have m1 := (hm.widen (X := Fz ++ Hc) (fun l hl => hOa l (List.mem_append.mpr (.inl hl))) hd).relabel
    (E'' := Fz ++ Hc ++ X ++ mutCells (olds hos) ++ Lv.flatten) (L'' := []) fun x => by
      simp only [List.mem_append, List.not_mem_nil, or_false]; grind
  have m2 := Moves.grow (E := Fz ++ Hc ++ X ++ mutCells (olds hos) ++ Lv.flatten)
    (E' := X ++ Fz ++ (Eo ++ mutCells (olds hos) ++ Hc)) hwf₁ hwf₂ hle hold hnew
    (fun l hl => by
      simp only [List.mem_append] at hl
      rcases hl with (((h | h) | h) | h) | h
      · exact hOa1 l (by simp [h])
      · exact hOa1 l (by simp [h])
      · exact hXa1 l h
      · exact hMa1 l h
      · exact hvs.alloc l h)
    (fun l => by simp only [List.mem_append, hEomem]; grind)
  exact (m1.trans m2 disj_nil_left hwf).relabel fun x => by simp

/-- A `handle` whose arm resumes: the places it lends the arm resolved, those lent `readonly`
frozen and those lent `mut` hidden from the body, their trees the frame's own; the body run under the
frame; and what was frozen and hidden given back, the hidden with the trees the arm last left. -/
theorem handle_core [WorldOk F O ι.w] (hE : EvalOk F O n) (hR : RetOk F O n) (hop : O[e]? = some op)
    (hcomp : ∀ τ ∈ op.owns, τ.complete = true)
    (hos : os.length = op.owns.length) (hrs : rs.length = op.refs.length)
    (hcaps : Caps Γ caps ys) (hexcl : Exclusive ys) (hnd : (os ++ rs ++ caps.map Cap.name).Nodup)
    (hP : PostOk F O (unhideAll Γ (roots .mut ys) (thaw (hideAll Γ (roots .mut ys)) (roots .ro ys) Γb)) env τ r post)
    (harm : Typed F O (armCtx os rs op (caps.map Cap.sig)) arm (armTy op post) Γa r)
    (hbody : Typed F O (freeze (hideAll Γ (roots .mut ys)) (roots .ro ys)) body τ Γb (.eff e :: r))
    (heval : evalS F O n hs σ env h = match caps.mapM (fun c => resolve σ env c.loc) with
      | some ls => ret F O n hs (.capK τ e σ.fresh.1 (List.zipWith Cap.at caps ls) os rs arm post)
          (eval F O n (.capture e σ.fresh.1 :: hs) σ.fresh.2 env body)
      | none => (.stuck, σ))
    (hI : Inv F ι σ Γ env E S) (hwf : WF σ) (hRdy : Ready O hs r) :
    Post F ι O σ E S (unhideAll Γ (roots .mut ys) (thaw (hideAll Γ (roots .mut ys)) (roots .ro ys) Γb)) env τ r
      hs (evalS F O n hs σ env h) := by
  rw [heval]
  obtain ⟨ls, Rc, Hc, hmap, hlen, hcok, hcin, htr, htr'⟩ := caps_ok hcaps hI.foot
  simp only [hmap]
  obtain ⟨hmn, hrm⟩ := hexcl.roots_ok
  generalize hms : roots .mut ys = ms at hbody hmn hrm htr htr' ⊢
  generalize hrs' : roots .ro ys = ros at hbody hrm ⊢
  generalize hcz : List.zipWith Cap.at caps ls = cz at hcok htr' ⊢
  have hnames : cz.map Cap.name = caps.map Cap.name := hcz ▸ zipWith_at_name hlen
  have hsigs : cz.map Cap.sig = caps.map Cap.sig := hcz ▸ zipWith_at_sig hlen
  -- The variables lent `mut` hidden: their trees the frame's.
  obtain ⟨Eh, hfh, hEh, hreb⟩ := hI.foot.hiddenAll hI.keys htr hmn
  have hkh : ((hideAll Γ ms).map Prod.fst).Nodup := by rw [hideAll_keys]; exact hI.keys
  -- Those lent `readonly` frozen.
  obtain ⟨Eb, Sb, Fz, hfb, hEp, hS, hent, hthaw⟩ := hfh.handle hkh (ys := ros) (by
    intro y hy τ' h
    rw [lookup_hideAll (hrm y hy)] at h
    rw [← hrs', mem_roots] at hy
    exact hcaps.roots_live _ hy τ' h)
  have hEall : E.Perm (Hc ++ (Eb ++ Fz)) := hEh.trans (hEp.append_left Hc)
  obtain ⟨hHcn, hEbFzn, hdHc⟩ := nodup_append_disj.mp (hEall.nodup_iff.mp hI.nodup)
  obtain ⟨hEbn, hFzn, hdEF⟩ := nodup_append_disj.mp hEbFzn
  have hmemE : ∀ l, l ∈ E ↔ l ∈ Hc ∨ l ∈ Eb ∨ l ∈ Fz := fun l => by
    rw [hEall.mem_iff]; simp
  have hEb : ∀ l ∈ Eb, l ∈ E := fun l h => (hmemE l).mpr (.inr (.inl h))
  have hFz : ∀ l ∈ Fz, l ∈ E := fun l h => (hmemE l).mpr (.inr (.inr h))
  have hHcE : ∀ l ∈ Hc, l ∈ E := fun l h => (hmemE l).mpr (.inl h)
  have hIb : Inv F ι σ (freeze (hideAll Γ ms) ros) env Eb Sb := by
    refine ⟨hfb, hEbn, fun l hl hl' => ?_, by rw [freeze_keys, hideAll_keys]; exact hI.keys⟩
    rcases List.mem_append.mp (hS.mem_iff.mp hl) with h | h
    · exact hdEF l hl' h
    · exact hI.disj l h (hEb l hl')
  -- What the arm is lent `readonly` is frozen, or read already.
  have hRc : ∀ l ∈ Rc, l ∈ Fz ∨ l ∈ S := by
    intro l hl
    obtain ⟨y, hy, s', a', L', he, hlL⟩ := hcin l hl
    have hyr : y ∈ ros := by rw [← hrs', mem_roots]; exact hy
    exact hent y s' a' L' (he.to_hidden (hrm y hyr)) hyr l hlL
  have hw := typed_weaker hbody (by rw [freeze_keys]; exact hkh)
  have hH : HandleOk F ι O σ e cz os rs arm post Γb (unhideAll Γ ms (thaw (hideAll Γ ms) ros Γb)) env Sb S r Fz Rc op :=
    { hop := hop, hcomp := hcomp, hown := hos, href := hrs, hnames := by rw [hnames]; exact hnd,
      harm := ⟨Γa, by rw [hsigs]; exact harm⟩,
      hSin := fun l hl => List.mem_append.mp (hS.mem_iff.mp hl),
      hS := fun l hl => hS.mem_iff.mpr (List.mem_append.mpr (.inr hl)),
      hRc := hRc,
      hRcdet := fun W hW σ1 Rc' Hc' hag hc => (hcok.mono hW).det_ro hc (hag.mono fun l hl => by
        rcases hRc l hl with h | h <;> simp [h]),
      hfns := hcok.fns,
      hre := by
        intro W hW σ1 Eb' Hc' hag hdX hSH hnX hc hI'
        obtain ⟨E1, hf1, hp1⟩ := hthaw W hW σ1 Γb Eb' hI'.foot hw hag
        obtain ⟨E', hf', hp'⟩ := hreb W hW σ1 _ E1 Hc' hf1 (thaw_weaker hw)
          ((hag.mono fun l hl => List.mem_append.mpr (.inr hl))) (htr' _ σ1 Rc Hc' hc)
        have hmem' : ∀ z, z ∈ E' ↔ z ∈ Eb' ∨ z ∈ Fz ∨ z ∈ Hc' := fun z => by
          rw [hp'.mem_iff, List.mem_append, hp1.mem_iff, List.mem_append]; grind
        obtain ⟨hFzn', hHcn', hdFH⟩ := nodup_append_disj.mp hnX
        refine ⟨E', ⟨hf', hp'.nodup_iff.mpr (nodup_append_disj.mpr ⟨hHcn', hp1.nodup_iff.mpr
          (nodup_append_disj.mpr ⟨hI'.nodup, hFzn', fun l h h' => hdX l (by simp [h']) h⟩), ?_⟩), ?_,
          by rw [unhideAll_keys ((thaw_keys (by rw [typed_keys hbody, freeze_keys])).trans hideAll_keys)];
             exact hI.keys⟩, hmem'⟩
        · intro l hl hl'
          rcases List.mem_append.mp (hp1.mem_iff.mp hl') with h | h
          · exact hdX l (by simp [hl]) h
          · exact hdFH l h hl
        · intro l hl hl'
          rcases (hmem' l).mp hl' with h | h | h
          · exact hI'.disj l (hS.mem_iff.mpr (List.mem_append.mpr (.inr hl))) h
          · exact hI.disj l hl (hFz l h)
          · exact hSH l hl h }
  have hdS : Disj S (Fz ++ Hc ++ Eb) := fun l hl h => by
    simp only [List.mem_append] at h
    rcases h with (h | h) | h
    · exact hI.disj l hl (hFz l h)
    · exact hI.disj l hl (hHcE l h)
    · exact hI.disj l hl (hEb l h)
  have hf := FrameOk.capK (τ := τ) (hid := σ.ids + 1) hH (by rw [← hms, ← hrs']; exact hP) hcok
  have hpost := hE _ _ _ _ _ _ _ _ _ _ _ hbody hIb.fresh (hwf : WF _) (hf.ready hRdy)
  have h := hR hs _ _ σ _ _ _ (Fz ++ Hc) [] σ.fresh.2 Eb _ hf hRdy (fun _ h => by simp at h) (hwf : WF _)
    (Agree.of' fun _ _ => rfl)
    (fun l hl => by
      rcases List.mem_append.mp hl with h | h
      · exact hI.alloc l (hFz l h)
      · exact hI.alloc l (hHcE l h))
    (nodup_append_disj.mpr ⟨hFzn, hHcn, fun l h1 h2 => hdHc l h2 (by simp [h1])⟩)
    (fun l hl h => by
      rcases List.mem_append.mp hl with hl | hl
      · exact hdEF l h hl
      · exact hdHc l hl (by simp [h]))
    hI.allocS (fun l hl h => hdS l hl (by simpa only [List.append_assoc] using h)) hpost
  exact post_relabel hwf hI.alloc (fun z => by
      rw [hmemE]; simp only [List.mem_append]; grind)
    (post_after (Moves.freshen hwf fun l hl => by
      simp only [List.mem_append] at hl
      rcases hl with (h | h) | h
      · exact hI.alloc l (hFz l h)
      · exact hI.alloc l (hHcE l h)
      · exact hI.alloc l (hEb l h)) hwf h)

theorem handle_ok [WorldOk F O ι.w] (hE : EvalOk F O n) (hR : RetOk F O n) (hop : O[e]? = some op)
    (hcomp : ∀ τ ∈ op.owns, τ.complete = true)
    (hos : os.length = op.owns.length) (hrs : rs.length = op.refs.length)
    (hcaps : Caps Γ caps ys) (hexcl : Exclusive ys) (hnd : (os ++ rs ++ caps.map Cap.name).Nodup)
    (harm : Typed F O (armCtx os rs op (caps.map Cap.sig)) arm op.ret Γa r)
    (hbody : Typed F O (freeze (hideAll Γ (roots .mut ys)) (roots .ro ys)) body τ Γb (.eff e :: r))
    (hI : Inv F ι σ Γ env E S) (hwf : WF σ) (hRdy : Ready O hs r) :
    Post F ι O σ E S (unhideAll Γ (roots .mut ys) (thaw (hideAll Γ (roots .mut ys)) (roots .ro ys) Γb)) env τ r
      hs (evalS F O n hs σ env (.handle τ body e caps os rs arm)) :=
  handle_core (post := none) hE hR hop hcomp hos hrs hcaps hexcl hnd trivial harm hbody
    (by simp only [evalS]; rfl)
    hI hwf hRdy

/-- A place's type is what its root says. -/
theorem PlaceTy.transfer (h : PlaceTy Γ p τ w y) (hy : lookup y Γ' = lookup y Γ) : PlaceTy Γ' p τ w y := by
  induction h with
  | own hx => exact .own (hy.trans hx)
  | ref hx => exact .ref (hy.trans hx)
  | half hx ht => exact .half (hy.trans hx) ht
  | deref _ ih => exact .deref (ih hy)
  | fst _ ih => exact .fst (ih hy)
  | snd _ ih => exact .snd (ih hy)

theorem Caps.transfer (h : Caps Γ caps ys) (hy : ∀ p ∈ ys, lookup p.2 Γ' = lookup p.2 Γ) : Caps Γ' caps ys := by
  induction h with
  | nil => exact .nil
  | ro hp hc _ ih =>
    exact .ro (hp.transfer (hy _ (List.mem_cons_self ..))) hc (ih fun p hp => hy p (List.mem_cons_of_mem _ hp))
  | «mut» hp hfn hc _ ih =>
    exact .mut (hp.transfer (hy _ (List.mem_cons_self ..))) hfn hc (ih fun p hp => hy p (List.mem_cons_of_mem _ hp))

theorem lookup_thaw : ∀ {Γ Γb : Ctx}, Γb.map Prod.fst = Γ.map Prod.fst →
    lookup z (thaw Γ ys Γb) = if z ∈ ys then lookup z Γ else lookup z Γb
  | [], [], _ => by simp [thaw, lookup]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | (x, s) :: Γ, (x', s') :: Γb, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    rw [thaw_cons]
    have ih := lookup_thaw (z := z) (ys := ys) h
    by_cases hzx : z = x'
    · subst hzx; by_cases hz : z ∈ ys <;> simp [lookup, hz]
    · by_cases hx : x' ∈ ys <;> by_cases hz : z ∈ ys <;> simp [lookup, hzx, hx, hz, ih]

theorem lookup_unhideAll : ∀ {ys : List Var} {Γ Γb : Ctx}, Γb.map Prod.fst = Γ.map Prod.fst →
    lookup z (unhideAll Γ ys Γb) = if z ∈ ys then lookup z Γ else lookup z Γb
  | [], Γ, Γb, _ => by simp [unhideAll]
  | y :: ys, Γ, Γb, h => by
    simp only [unhideAll]
    have hk : (unhideAll (hide Γ y) ys Γb).map Prod.fst = Γ.map Prod.fst :=
      (unhideAll_keys (h.trans hide_keys.symm)).trans hide_keys
    rw [lookup_thaw hk]
    by_cases hzy : z = y
    · subst hzy; simp
    · rw [lookup_unhideAll (Γ := hide Γ y) (h.trans hide_keys.symm), lookup_hide_ne hzy]
      have : z ∉ [y] := by simp [hzy]
      simp only [this, ↓reduceIte, List.mem_cons, hzy, false_or]

/-- After a `handle`, what it lent its arms is rooted where it was. -/
theorem handle_roots (hb : Γb.map Prod.fst = Γ.map Prod.fst) (hy : y ∈ ms ∨ y ∈ ros) :
    lookup y (unhideAll Γ ms (thaw (hideAll Γ ms) ros Γb)) = lookup y Γ := by
  rw [lookup_unhideAll ((thaw_keys (hb.trans hideAll_keys.symm)).trans hideAll_keys)]
  split
  · rfl
  · rename_i hm
    rw [lookup_thaw (hb.trans hideAll_keys.symm), if_pos (hy.resolve_left hm), lookup_hideAll hm]

/-- A `handle` whose arm resumes in its midst: as one whose arm resumes at its end, but for what runs
once the rest of the `handle` ends. -/
theorem handleR_ok [WorldOk F O ι.w] (hF : FnsOk F O) (hE : EvalOk F O n) (hR : RetOk F O n) (hop : O[e]? = some op)
    (hcomp : ∀ τ ∈ op.owns, τ.complete = true)
    (hos : os.length = op.owns.length) (hrs : rs.length = op.refs.length) (hcaps : Caps Γ caps ys)
    (hexcl : Exclusive ys) (hnd : (os ++ rs ++ caps.map Cap.name).Nodup) (hfd : F[f]? = some d) (hown : d.owns.map Prod.snd = [C, τ])
    (hdrefs : d.refs = caps.map Cap.sig) (hretp : d.retp = none) (hcap : d.cap = none) (hret : d.ret = τ)
    (hrow : ∀ l ∈ d.row, l ∈ r) (hC : C.complete = true)
    (harm : Typed F O (armCtx os rs op (caps.map Cap.sig)) arm (.sum (.pair op.ret C) τ) Γa r)
    (hbody : Typed F O (freeze (hideAll Γ (roots .mut ys)) (roots .ro ys)) body τ Γb (.eff e :: r))
    (hI : Inv F ι σ Γ env E S) (hwf : WF σ) (hRdy : Ready O hs r) :
    Post F ι O σ E S (unhideAll Γ (roots .mut ys) (thaw (hideAll Γ (roots .mut ys)) (roots .ro ys) Γb)) env τ r
      hs (evalS F O n hs σ env (.handleR τ body e caps os rs arm C f)) := by
  obtain ⟨hkeys, hfb⟩ := hF d (List.mem_of_getElem? hfd)
  rw [hcap, hretp] at hfb
  have hkb : Γb.map Prod.fst = Γ.map Prod.fst := by rw [typed_keys hbody, freeze_keys, hideAll_keys]
  refine handle_core (post := some (C, τ, f, env, caps)) hE hR hop hcomp hos hrs hcaps hexcl
    hnd ⟨rfl, rfl, hC, d, ys, hfd, hown, hdrefs, hretp, hcap, hret, hrow,
      hcaps.transfer fun p hp => handle_roots hkb (by
        rcases p with ⟨m, y⟩
        cases m
        · exact .inr (mem_roots.mpr hp)
        · exact .inl (mem_roots.mpr hp)), hexcl, hkeys, hfb⟩ harm hbody (by simp only [evalS]; rfl)
    hI hwf hRdy

/-- What is lent is rooted at a live variable. -/
theorem Lends.root_live : Lends Γ lent ts ys → ∀ q ∈ ys, ∀ τ', lookup q.2 Γ ≠ some (.own τ' false)
  | .nil, _, h => by simp at h
  | .cons hp _ _ hrest, q, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact hp.root_live
    · exact hrest.root_live q h

/-- A call, its owned arguments evaluated to `vs` and the places it lends to the holes `hos`: the
callee's body runs, and its activation ends, as `ret_callK` says. -/
theorem call_core [WorldOk F O ι.w] (hfl : FlushOk F (ι.drop k) (flushR F O n)) (hE : EvalOk F O n) {d : Fn} {hos : List Hole} {vs : List Val}
    {Ls : List (List Nat)} (hkeys : ((d.owns.map Prod.fst) ++ (d.refs.map Prod.fst)).Nodup)
    (hbody : Typed F O (fnCtx d) d.body d.ret Γ'' d.row) (hrow : ∀ l ∈ d.row, l ∈ r)
    (hI₁ : Inv F ι σ1 Γ₁ env E₁ S) (hwf : WF σ) (hm₁ : Moves σ E σ1 E₁ Ls.flatten)
    (hvs₀ : Vals F ι σ1 (d.owns.map fun p => p.2.shiftBy k) vs Ls) (hLn : Ls.flatten.Nodup) (hdL : Disj Ls.flatten E₁)
    (hdLS : Disj Ls.flatten S) (hholes : ∀ h ∈ hos, HoleOk F ι σ1 Γ₁ env h) (hpw : hos.Pairwise Apart)
    (hts : hos.map (fun h => (h.mode, h.ty)) = d.refs.map (fun p => (p.2.1, p.2.2.shiftBy k))) (hRdy : Ready O hs r) :
    Post F ι O σ E S Γ₁ env (d.ret.shiftBy k) r hs
      (let (cells, σ2) := allocAll σ1 ((d.owns.map Prod.fst).zip vs)
       ret F O n hs (.callK ((d.owns.map Prod.snd).zip (cells.map Prod.snd)))
         (eval F O n hs σ2 (cells ++ (d.refs.map Prod.fst).zip (hos.map Hole.loc)) d.body)) := by
  have hvs : Vals F (ι.drop k) σ1 (d.owns.map Prod.snd) vs Ls :=
    Vals.unshiftk (by simpa [List.map_map, Function.comp_def] using hvs₀)
  have hwf₁ := hm₁.wf
  obtain ⟨Eo, hfo, hEo, hEomem, hle, hwf₂, hold, hnew, hlenc⟩ :=
    allocAll_ok (names := d.owns.map Prod.fst) hvs (by simp) hwf₁ hLn
  rw [zip_fst_snd] at hfo
  have hcells : (allocAll σ1 ((d.owns.map Prod.fst).zip vs)).1.map Prod.fst = d.owns.map Prod.fst := by
    rw [allocAll_fst]; exact List.map_fst_zip (by rw [hvs.length]; simp)
  have hrtAl := allocAll_rt σ1 ((d.owns.map Prod.fst).zip vs)
  generalize allocAll σ1 ((d.owns.map Prod.fst).zip vs) = al at hfo hEomem hle hwf₂ hold hnew hlenc hcells hrtAl ⊢
  obtain ⟨cells, σ2⟩ := al
  dsimp only at hfo hEomem hle hwf₂ hold hnew hlenc hcells hrtAl ⊢
  have hMin : ∀ l ∈ mutCells (olds hos), l ∈ E₁ := fun l hl => by
    obtain ⟨h, hh, hl⟩ := mem_olds_mut.mp hl
    exact (hole_in hI₁ (hholes h hh)).2 (Hole.excl_mut hl).1 l hl
  have hEoin : ∀ l ∈ Eo, l ∈ Ls.flatten ∨ σ1.next ≤ l := fun l hl => by
    rcases (hEomem l).mp hl with h | h
    · exact .inl h
    · exact .inr h.1
  have hIc := callee_inv (k := k) (d := d) hI₁ hholes hpw (refs_lower hts) hkeys hfo hEo hEoin hdL
    hdLS hwf₁ hold (by rt_tac) (fun h hh _ hL => LT.unshiftk (by rw [holes_shift hts h hh]; exact hL))
  have hlow : ∀ l, σ1.mem l ≠ none → σ2.mem l ≠ none := fun l h => by rw [hold l (hwf₁ l h)]; exact h
  have hapart : ∀ {Y : List Nat}, (∀ l ∈ Y, σ1.mem l ≠ none) → Disj Y Ls.flatten →
      Disj Y (mutCells (olds hos)) → Disj Y (Eo ++ mutCells (olds hos)) := by
    intro Y hY hYL hYM l hl hl'
    rcases List.mem_append.mp hl' with hl' | hl'
    · rcases hEoin l hl' with h | h
      · exact hYL l hl h
      · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hwf₁ l (hY l hl)) h)
    · exact hYM l hl hl'
  generalize hX : E₁.filter (· ∉ mutCells (olds hos)) = X
  have hXE : ∀ l ∈ X, l ∈ E₁ := fun l hl => (mem_keep.mp (hX ▸ hl)).1
  have hXa : ∀ l ∈ X, σ1.mem l ≠ none := fun l hl => hI₁.alloc l (hXE l hl)
  have hXc : Disj X (Eo ++ mutCells (olds hos)) := hapart hXa (fun l hl h => hdL l h (hXE l hl))
    (fun l hl => (mem_keep.mp (hX ▸ hl)).2)
  have hSc : Disj S (Eo ++ mutCells (olds hos)) := hapart hI₁.allocS (fun l hl h => hdLS l h hl)
    (fun l hl h => hI₁.disj l hl (hMin l h))
  have h3 := hE _ _ _ _ _ _ _ _ _ _ _ hbody hIc hwf₂ ⟨hRdy.1, fun l hl => hRdy.2 l (hrow l hl)⟩
  have h4 := ret_callK (n := n) (σf := σ1) (σ0 := σ2) (r := r) (hs := hs) hfl hrow hI₁ hholes hpw hts hkeys
    hvs.owns_complete hbody
    hcells hRdy hwf₂ (by rw [hX]; exact Agree.of' fun l hl => hold l (hwf₁ l (by
      rcases List.mem_append.mp hl with h | h
      · exact hXa l h
      · exact hI₁.allocS l h)))
    (by rw [hX]; exact hXc) (fun l hl => hlow l (hI₁.allocS l hl))
    (by rw [hX]; exact disj_append_right.mpr ⟨fun l hl h => hI₁.disj l hl (hXE l h), hSc⟩) h3
  rw [hX] at h4
  have m1 : Moves σ E σ1 (X ++ mutCells (olds hos) ++ Ls.flatten) [] := hm₁.relabel fun x => by
    have := hMin x
    have := hX ▸ (mem_keep (E := E₁) (M := mutCells (olds hos)) (l := x))
    simp only [List.mem_append, List.not_mem_nil, or_false] at * <;> grind
  have m2 := Moves.grow (E := X ++ mutCells (olds hos) ++ Ls.flatten)
    (E' := X ++ (Eo ++ mutCells (olds hos)))
    hwf₁ hwf₂ hle hold hnew (fun l hl => by
      simp only [List.mem_append] at hl
      rcases hl with (h | h) | h
      · exact hXa l h
      · exact hI₁.alloc l (hMin l h)
      · exact hvs.alloc l h) (fun l => by
      simp only [List.mem_append, hEomem]; grind)
  exact post_after ((m1.trans m2 disj_nil_left hwf).relabel fun x => by simp) hwf h4


/-- A call whose callee's regions are its caller's. -/
theorem call_core0 [WorldOk F O ι.w] (hfl : FlushOk F ι (flushR F O n)) (hE : EvalOk F O n) {d : Fn} {hos : List Hole} {vs : List Val}
    {Ls : List (List Nat)} (hkeys : ((d.owns.map Prod.fst) ++ (d.refs.map Prod.fst)).Nodup)
    (hbody : Typed F O (fnCtx d) d.body d.ret Γ'' d.row) (hrow : ∀ l ∈ d.row, l ∈ r)
    (hI₁ : Inv F ι σ1 Γ₁ env E₁ S) (hwf : WF σ) (hm₁ : Moves σ E σ1 E₁ Ls.flatten)
    (hvs : Vals F ι σ1 (d.owns.map Prod.snd) vs Ls) (hLn : Ls.flatten.Nodup) (hdL : Disj Ls.flatten E₁)
    (hdLS : Disj Ls.flatten S) (hholes : ∀ h ∈ hos, HoleOk F ι σ1 Γ₁ env h) (hpw : hos.Pairwise Apart)
    (hts : hos.map (fun h => (h.mode, h.ty)) = d.refs.map Prod.snd) (hRdy : Ready O hs r) :
    Post F ι O σ E S Γ₁ env d.ret r hs
      (let (cells, σ2) := allocAll σ1 ((d.owns.map Prod.fst).zip vs)
       ret F O n hs (.callK ((d.owns.map Prod.snd).zip (cells.map Prod.snd)))
         (eval F O n hs σ2 (cells ++ (d.refs.map Prod.fst).zip (hos.map Hole.loc)) d.body)) := by
  have := call_core (k := 0) hfl hE hkeys hbody hrow hI₁ hwf hm₁ (by simpa using hvs) hLn hdL hdLS hholes hpw
    (by simpa using hts) hRdy
  rwa [Ty.shiftBy_zero] at this

/-- Frames: each does with what its code gave what its construct says. -/
theorem callRet_eq : callRet (flushR F O n) cells res = ret F O n hs (.callK cells) res := by
  rcases res with ⟨_ | _ | _ | _ | _, _⟩ <;> simp [callRet, ret]

/-- What a `handle` lends its arms is rooted at its variables. -/
theorem Caps.mem_root : Caps Γ caps ys → ∀ c ∈ caps, (c.mode, c.loc.root) ∈ ys := by
  intro h
  induction h with
  | nil => simp
  | ro hp _ _ ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · simp [← hp.root_eq]
    · exact List.mem_cons_of_mem _ (ih c hc)
  | «mut» hp _ _ _ ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · simp [Place.root]
    · exact List.mem_cons_of_mem _ (ih c hc)

/-- What a `handle` lends its arms, lent again as a call lends places. -/
theorem Caps.lends : Caps Γ caps ys →
    Lends Γ (caps.map fun c => (c.mode, c.loc)) (caps.map fun c => (c.mode, c.ty)) ys := by
  intro h
  induction h with
  | nil => exact .nil
  | ro hp hc _ ih => exact .cons hp (fun h => by cases h) (Ty.complete_whole hc) ih
  | «mut» hp _ hc _ ih => exact .cons hp (fun _ => rfl) (Ty.complete_whole hc) ih

theorem Caps.lentApart : Caps Γ caps ys → Exclusive ys → LentApart (caps.map fun c => (c.mode, c.loc)) := by
  intro h hx
  induction h with
  | nil => exact List.Pairwise.nil
  | @ro p τ w y rest ys' x hp _ hc ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hx
    refine List.pairwise_cons.mpr ⟨fun b hb hr => .inl ⟨rfl, ?_⟩, ih htail⟩
    obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hb
    exact (hhead _ (hc.mem_root c hcm) (by simp only at hr ⊢; rw [hp.root_eq, hr])).2
  | @«mut» y τ rest ys' x hp _ _ hc ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hx
    refine List.pairwise_cons.mpr ⟨fun b hb hr => ?_, ih htail⟩
    obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hb
    exact absurd (hhead _ (hc.mem_root c hcm) (by simpa [Place.root] using hr)).1 (by simp)

/-- What an arm carried past its resumption, as the rest of its `handle` ended: function `post`
runs, given it and the `handle`'s value, the `handle`'s places lent to it again, as a call. -/
theorem ret_postR [WorldOk F O ι.w] (hfl : FlushOk F ι (flushR F O n)) (hE : EvalOk F O n) (hP : PostOk F O Γ env τ r (some (C, τ, f, env, cps)))
    (hv : VT F ι σf C v Lv) (hR : Ready O hs r) (hwf : WF σ0)
    (hag : Agree σf σ0 (Lv ++ S)) (halloc : ∀ l ∈ Lv, σf.mem l ≠ none) (hnd : Lv.Nodup) (hd : Disj Lv Ein)
    (hSa : ∀ l ∈ S, σ0.mem l ≠ none) (hSd : Disj S (Lv ++ Ein))
    (hp : Post F ι O σ0 Ein S Γ env τ r hs res) :
    Post F ι O σ0 (Lv ++ Ein) S Γ env τ r hs (ret F O n hs (.postR C f v env cps) res) := by
  obtain ⟨-, -, hC, d, ys, hfd, hown, hdrefs, hretp, hcap, hret, hrow, hcaps, hexcl, hkeys, Γ'', hbody⟩ := hP
  have hLa : ∀ l ∈ Lv, σ0.mem l ≠ none := fun l hl => by
    rw [hag l (List.mem_append.mpr (.inl hl))]; exact halloc l hl
  have hv0 : VT F ι σ0 C v Lv := hv.frame (hag.mono fun l hl => List.mem_append.mpr (.inl hl))
  have hSL : Disj S Lv := fun l hl h => hSd l hl (List.mem_append.mpr (.inl h))
  have hSE : Disj S Ein := fun l hl h => hSd l hl (List.mem_append.mpr (.inr h))
  rcases res with ⟨res, σ1⟩
  cases res with
  | val w =>
    obtain ⟨E₁, Lw, hI₁, hvw, hdw, hdwS, hm₁⟩ := hp
    have hv₁ := hv0.frame (hm₁.keeps hwf hLa hd)
    obtain ⟨hdE, hdLw⟩ := hm₁.apart hwf hLa hd
    obtain ⟨hos, hts, hys, hmap, hholes, -, hpw⟩ := lends_ok hcaps.lends hI₁.foot (hcaps.lentApart hexcl)
    have hmap' : cps.mapM (fun c => resolve σ1 env c.loc) = some (hos.map Hole.loc) := by
      rw [← hmap, List.mapM_map]; rfl
    have hvs : Vals F ι σ1 (d.owns.map Prod.snd) [v, w] [Lv, Lw] := by
      rw [hown]; exact .cons hv₁ (.cons hvw .nil)
    have hts' : hos.map (fun h => (h.mode, h.ty)) = d.refs.map Prod.snd := by
      rw [hts, hdrefs, List.map_map]; rfl
    have hlen : [v, w].length = d.owns.length ∧ (hos.map Hole.loc).length = d.refs.length := by
      refine ⟨by simpa using (congrArg List.length hown).symm, ?_⟩
      have := congrArg List.length hts'
      simpa using this
    have hcore := call_core0 (d := d) (hos := hos) (vs := [v, w]) (Ls := [Lv, Lw]) (σ := σ0)
      (E := Lv ++ Ein) hfl hE hkeys hbody hrow hI₁ hwf
      ((hm₁.widen hLa hd).relabel fun x => by
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_append]; grind)
      hvs (by simpa using nodup_append_disj.mpr ⟨hv₁.nodup, hvw.nodup, fun l h1 h2 => hdLw l h1 h2⟩)
      (fun l hl h => by
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_append] at hl
        rcases hl with hl | hl
        · exact hdE l hl h
        · exact hdw l hl h)
      (fun l hl h => by
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_append] at hl
        rcases hl with hl | hl
        · exact hSL l h hl
        · exact hdwS l hl h)
      hholes hpw hts' hR
    rw [hret] at hcore
    simp only [ret, hmap', hfd, hlen, and_self, ↓reduceIte]
    rw [callRet_eq]
    exact hcore
  | abort j k =>
    obtain ⟨haim, E₁, hI₁, hm₁⟩ := hp
    have hv₁ := hv0.frame (hm₁.keeps hwf hLa hd)
    obtain ⟨hdE, -⟩ := hm₁.apart hwf hLa hd
    obtain ⟨σ3, hdrop, hfg⟩ := dropF hfl hm₁.wf hv₁
    simp only [ret, hdrop]
    refine hfg.post fun σ4 hd4 => ⟨haim, E₁, hI₁.dropped hd4 hm₁.wf hdE (fun l hl h => hSL l h hl), ?_⟩
    exact Moves.thenDrop ((hm₁.widen hLa hd).relabel fun x => by mem_iff) hd4
      (fun l hl => hI₁.alloc l (by simpa using hl)) (fun l hl h => hdE l h (by simpa using hl)) hwf
  | susp j ef vs ls K =>
    obtain ⟨op, X, hos, A, Lw, hc, hop, hcov, haim, hK, hls, hvs, hn, hdw, hdS, hm⟩ := hp
    simp only [ret]
    obtain ⟨hdX, hdL⟩ := hm.apart hwf hLa hd
    have hLS : ∀ l ∈ Lv ++ S, σ0.mem l ≠ none := fun l hl => by
      rcases List.mem_append.mp hl with h | h
      · exact hLa l h
      · exact hSa l h
    have hK' := FramesOk.cons (A := A) (.postR ⟨rfl, rfl, hC, d, ys, hfd, hown, hdrefs, hretp, hcap, hret, hrow, hcaps,
        hexcl, hkeys, Γ'', hbody⟩ hv) (Weaker.refl _)
      ((Agree.trans (hag) ((hm.keeps hwf hLS (fun l hl h => by
        rcases List.mem_append.mp hl with hl | hl
        · exact hd l hl h
        · exact hSE l hl h))))) halloc hnd hdX hK
      (fun _ h => by simp at h) (fun a ha => .inl ha)
    refine ⟨op, Lv ++ X, hos, A, Lw, hc, hop, hcov, haim, hK', hls, hvs, hn, ?_, hdS, ?_⟩
    · intro l hl h
      simp only [List.mem_append] at h
      rcases h with (h | h) | h
      · exact hdL l h hl
      · exact hdw l hl (by simp [h])
      · exact hdw l hl (by simp [h])
    · exact (hm.widen hLa hd).relabel fun x => by simp only [List.mem_append, List.append_assoc]
  | stuck => simp [Post] at hp
  | timeout => simp [ret, Post]
  | ended => simp [ret, Post]

end FlyCore.Ownership
