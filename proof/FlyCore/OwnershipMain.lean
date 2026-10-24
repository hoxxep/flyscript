import FlyCore.OwnershipFiber

/-!
# Ownership: soundness

Every construct evaluates as its typing says (`eval_ok_succ`), every frame does with what its code
gives what its construct says (`ret_ok`), and so, by fuel, every well-typed program (`sound`,
`program_ok`).
-/

namespace FlyCore.Ownership

theorem preTarget_spec : ∀ {hs : HS}, preTarget O hs = some (e, j) →
    Frame.capture e j ∈ hs ∧ ∃ op, O[e]? = some op ∧ op.owns = [] ∧ op.refs = [] ∧ op.ret = .int
  | [], h => by simp [preTarget] at h
  | .capture e' id :: hs, h => by
    simp only [preTarget] at h
    split at h
    · rename_i op hop
      split at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨List.mem_cons_self .., op, hop, hc.2.1, hc.2.2.1, hc.2.2.2⟩
      · obtain ⟨hm, h'⟩ := preTarget_spec h
        exact ⟨List.mem_cons_of_mem _ hm, h'⟩
    · obtain ⟨hm, h'⟩ := preTarget_spec h
      exact ⟨List.mem_cons_of_mem _ hm, h'⟩
  | .abort l id :: hs, h => by
    simp only [preTarget] at h
    obtain ⟨hm, h'⟩ := preTarget_spec h
    exact ⟨List.mem_cons_of_mem _ hm, h'⟩
  | .cancel id :: hs, h => by
    simp only [preTarget] at h
    obtain ⟨hm, h'⟩ := preTarget_spec h
    exact ⟨List.mem_cons_of_mem _ hm, h'⟩

/-- A task stopped before `e`, for another to run: it waits, as if it had given way, to run `e`
once it goes on, its cells as they were. -/
theorem preempt_ok (ht : Typed F O Γ e τ Γ' r) (hI : Inv F ι σ Γ env E S) (hwf : WF σ) (hRdy : Ready O hs r)
    (hp : preTarget O hs = some (e0, j)) :
    Post F ι O σ E S Γ' env τ r hs (.susp j e0 [] [] [.startK env e], σ.fresh.2) := by
  obtain ⟨hm, op, hop, howns, hrefs, hret⟩ := preTarget_spec hp
  have hI1 : Inv F ι σ.fresh.2 Γ env E S := ⟨hI.foot.frame (Agree.of' fun _ _ => rfl), hI.nodup, hI.disj, hI.keys⟩
  have hb : FramesOk F O ι σ.fresh.2 [] op ⟨Γ, env, op.ret, S, r⟩ (E.filter (· ∉ mutCells (olds []))) [] [] :=
    .base hI1 (fun _ h => by simp at h) List.Pairwise.nil hop (by simp [hrefs]) (Weaker.refl _)
  rw [hret] at hb
  have hK : FramesOk F O ι σ.fresh.2 [.startK env e] op ⟨Γ', env, τ, S, r⟩
      ([] ++ E.filter (· ∉ mutCells (olds []))) [] [] :=
    .cons (.startK ht) (Weaker.refl _) Agree.self (fun _ h => by simp at h) List.nodup_nil disj_nil_left hb
      (fun _ h => by simp at h) (fun _ h => by simp at h)
  refine ⟨op, _, [], [], [], .inl hm, hop, hRdy.2, fun _ h => by simp at h, hK, rfl, by rw [howns]; exact .nil,
    List.nodup_nil, disj_nil_left, disj_nil_left, ?_⟩
  simp only [olds, mutCells, List.map_nil, List.flatMap_nil, List.flatten_nil, List.nil_append, List.append_nil]
  exact (Moves.freshen hwf hI.alloc).relabel fun x => by simp

theorem eval_ok_succ (hF : FnsOk F O) (hE : EvalOk F O n) (hR : RetOk F O n) (hK : EvalKOk F O n)
    (hKs : ∀ m, m < n → EvalOk F O m ∧ EvalKOk F O m ∧ RetOk F O m) : EvalOk F O (n + 1) := by
  intro hs σ ι Γ env E S e τ Γ' r _ ht hI hwf hRdy
  have hKo : ∀ m, n = m + 1 → EvalKOk F O m := fun m h => (hKs m (by omega)).2.1
  have hKR : ∀ m, n = m + 1 → EvalKOk F O m ∧ RetOk F O m := fun m h => (hKs m (by omega)).2
  have hfl : ∀ ι, [WorldOk F O ι.w] → FlushOk F ι (flushR F O n) := fun _ _ => flushR_ok hKo
  have hKv : ∀ ι, [WorldOk F O ι.w] → ∀ m, n = m + 1 → EvalOk F O m ∧ FlushOk F ι (flushR F O m) :=
    fun _ _ m h => ⟨(hKs m (by omega)).1, flushR_ok fun k hk => (hKs k (by omega)).2.1⟩
  -- A task may be stopped before anything it does, for another to run.
  rw [eval]
  split
  · rename_i e0 j hpt
    split at hpt
    · exact preempt_ok ht hI hwf hRdy hpt
    · cases hpt
  -- Each step is a point the schedule may stop it at, which it counts.
  have hI1 : Inv F ι σ.fresh.2 Γ env E S := ⟨hI.foot.frame (Agree.of' fun _ _ => rfl), hI.nodup, hI.disj, hI.keys⟩
  refine post_after (Moves.freshen hwf hI.alloc) hwf ?_
  suffices h : ∀ σ, Inv F ι σ Γ env E S → WF σ → Post F ι O σ E S Γ' env τ r hs (evalS F O n hs σ env e) from
    h _ hI1 hwf
  clear hI1 hI hwf
  intro σ hI hwf
  cases ht with
    | atom ha =>
      obtain ⟨v, σ1, E₁, L₁, hev, hI₁, hv₁, hd₁, hdS₁, hm₁⟩ := atom_ok ha hI hwf
      simp only [evalS, hev]
      exact post_val hI₁ hv₁ hd₁ hdS₁ hm₁
    | add ha hb =>
      obtain ⟨v, σ1, E₁, L₁, hev, hI₁, hv₁, -, -, hm₁⟩ := atom_ok ha hI hwf
      cases hv₁ with
      | int =>
      obtain ⟨w, σ2, E₂, L₂, hev2, hI₂, hv₂, -, -, hm₂⟩ := atom_ok hb hI₁ hm₁.wf
      cases hv₂ with
      | int =>
      simp only [evalS, hev, hev2]
      split
      · exact post_val hI₂ .int disj_nil_left disj_nil_left
          ((hm₁.trans hm₂ disj_nil_left hwf).relabel (by simp))
      · simp [Post]
    | new ha =>
      obtain ⟨v, σ1, E₁, L₁, hev, hI₁, hv₁, hd₁, hdS₁, hm₁⟩ := atom_ok ha hI hwf
      simp only [evalS, hev]
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
      refine post_val ⟨hI₁.foot.frame (hag.mono fun l hl => ?_), hI₁.nodup, hI₁.disj, hI₁.keys⟩
        (.box (LT.of_contents (by simp [Store.alloc]) (hv₁.frame (hag.mono fun l hl => ?_)) ?_) hv₁.complete) ?_ ?_
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
    | pair ha hb =>
      exact pair_ok ha hb hI hwf
    | case hx hAB hy h₁ h₂ w₁ w₂ => exact case_ok (hfl _) hE hx hAB hy h₁ h₂ w₁ w₂ hI hwf hRdy
    | caseRef hx hp hun hm hmf h₁ h₂ w₁ w₂ => exact caseRef_ok hE hx hp hun hm hmf h₁ h₂ w₁ w₂ hI hwf hRdy
    | inj ha hAB =>
      obtain ⟨v, σ1, E₁, L₁, hev, hI₁, hv₁, hd₁, hdS₁, hm₁⟩ := atom_ok ha hI hwf
      simp only [evalS, hev]
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
      refine post_val ⟨hI₁.foot.frame (hag.mono fun l hl => ?_), hI₁.nodup, hI₁.disj, hI₁.keys⟩
        (.tag (LT.of_contents (by simp [Store.alloc]) (hv₁.frame (hag.mono fun l hl => ?_)) ?_)
          (by simp only [Ty.complete, Bool.and_eq_true] at hAB; exact hAB.1)
          (by simp only [Ty.complete, Bool.and_eq_true] at hAB; exact hAB.2)) ?_ ?_
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
    | lendClo hfd hcap hown hrefs hretp hdat hp hx hb =>
      exact lendClo_ok hE hfd hcap hown hrefs hretp hdat hp hx hb hI hwf hRdy
    | lendCloMut hfd hcap hown hrefs hretp hdat hp hun hx hb =>
      exact lendCloMut_ok hE hfd hcap hown hrefs hretp hdat hp hun hx hb hI hwf hRdy
    | lam hfd hcap hown hrefs hretp ha hrf =>
      obtain ⟨v, σ1, E₁, L₁, hev, hI₁, hv₁, hd₁, hdS₁, hm₁⟩ := atom_ok ha hI hwf
      simp only [evalS, hfd, hev, hcap]
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
      refine post_val ⟨hI₁.foot.frame (hag.mono fun l hl => ?_), hI₁.nodup, hI₁.disj, hI₁.keys⟩
        (.clo ⟨_, _, _, hfd, hcap, hown, hrefs, hretp, rfl, rfl, hv₁.complete, hrf⟩
          (LT.of_contents (by simp [Store.alloc]) (hv₁.frame (hag.mono fun l hl => ?_)) ?_) hv₁.complete) ?_ ?_
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
      obtain ⟨l, Rb, P, A, B, hres, hRb, hE, hupd⟩ := replace_at hI₁ hp rfl (.inl rfl)
      cases hRb with
      | int hl =>
        simp only [evalS, hev, hres, hl]
        have hnd := seg_nodup (hE.nodup_iff.mp hI₁.nodup)
        have hlE : l ∈ E₁ := hE.mem_iff.mpr (mem_seg.mpr (.inl (by simp)))
        have hlP : l ∉ P := by
          have := hnd.1; rw [nodup_append_disj] at this; exact fun h => this.2.2 l h (by simp)
        have hlAB : l ∉ A ++ B := hnd.2.1 l (by simp)
        have hlS : l ∉ S := fun h => hI₁.disj l h hlE
        have hout : l ∉ A ++ P ++ B ++ S := by
          simp only [List.mem_append, not_or] at hlAB ⊢
          exact ⟨⟨⟨hlAB.1, hlP⟩, hlAB.2⟩, hlS⟩
        obtain ⟨E'', hI'', hE''⟩ := hupd (σ1.set l (some (.int k))) [l] (agree_set hout)
          (.int (n := k) (by simp [Store.set])) (by
            intro x hx; simp at hx; subst hx
            simp only [List.mem_append, not_or] at hout ⊢; exact hout.1) (by
            intro x hx; simp at hx; subst hx; exact hlS)
        refine post_val hI'' .int disj_nil_left disj_nil_left
          ((hm₁.trans (Moves.set hm₁.wf hI₁.alloc hlE) disj_nil_left hwf).relabel (E'' := E'') (L'' := [])
            (fun x => by simp only [List.append_nil, hE''.mem_iff, ← hE.mem_iff]))
    | assign ha hp hsh =>
      obtain ⟨v, σ1, E₁, L₁, hev, hI₁, hv₁, hd₁, hdS₁, hm₁⟩ := atom_ok ha hI hwf
      obtain ⟨l, Rb, P, A, B, hres, hRb, hE, hupd⟩ := replace_at hI₁ hp ha.complete (.inr hsh)
      obtain ⟨w, R', hw, hvw, rfl, hlR'⟩ := hRb.contents ha.complete
      obtain ⟨σ2', hdrop, hfg⟩ := dropF (hfl ι) hm₁.wf hvw
      simp only [evalS, hev, hres, hw, hdrop]
      refine hfg.post fun σ2 hd2 => ?_
      have hkeep := hd2.keep hm₁.wf
      have hfree := hd2.free
      have hlE : l ∈ E₁ := hE.mem_iff.mpr (mem_seg.mpr (.inl (by simp)))
      have hR'E : ∀ x ∈ R', x ∈ E₁ := fun x hx => hE.mem_iff.mpr (mem_seg.mpr (.inl (by simp [hx])))
      obtain ⟨hdR, -⟩ := seg3 (hE.nodup_iff.mp hI₁.nodup)
      have hlAPB : l ∉ A ++ P ++ B := hdR l (by simp)
      have hdR' : Disj R' (A ++ P ++ B) := fun x hx => hdR x (by simp [hx])
      have hlL : l ∉ L₁ := fun h => hd₁ l h hlE
      have hlS : l ∉ S := fun h => hI₁.disj l h hlE
      have hAPB : ∀ x ∈ A ++ P ++ B, x ∈ E₁ := fun x hx => hE.mem_iff.mpr (by
        simp only [List.mem_append] at hx ⊢; rcases hx with (hx | hx) | hx <;> simp [hx])
      let σ3 := σ2.set l (some v)
      have hkeep3 : ∀ x, x ≠ l → x ∉ R' → σ3.mem x = σ1.mem x := by
        intro x hx hxR; simp only [σ3, Store.set, hx, ite_false]; exact hkeep x hxR
      have hag : Agree σ1 σ3 (A ++ P ++ B ++ S) := Agree.trans (hd2.keeps hm₁.wf (fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · exact hI₁.alloc x (hAPB x hx)
          · exact hI₁.allocS x hx) (fun x hx h => by
          rcases List.mem_append.mp hx with hx | hx
          · exact hdR' x h hx
          · exact hI₁.disj x hx (hR'E x h)))
        (Agree.of' fun x hx => by
          have hxl : x ≠ l := by
            rcases List.mem_append.mp hx with hx | hx
            · exact fun h => hlAPB (h ▸ hx)
            · exact fun h => hlS (h ▸ hx)
          simp only [σ3, Store.set, hxl, ite_false])
      have hagL : Agree σ1 σ3 L₁ := Agree.trans (hd2.keeps hm₁.wf hv₁.alloc fun x hx h => hd₁ x hx (hR'E x h))
        (Agree.of' fun x hx => by
          have hxl : x ≠ l := fun h => hlL (h ▸ hx)
          simp only [σ3, Store.set, hxl, ite_false])
      have hLt : LT F ι σ3 l _ (l :: L₁) :=
        LT.of_contents (by simp [σ3, Store.set]) (hv₁.frame hagL) hlL
      have hwf2 : WF σ2 := hd2.wf
      have hm₂ := Moves.ofDropped (E := E₁ ++ L₁) (E' := A ++ (P ++ [l]) ++ B ++ L₁) (D := R') hd2
        (fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · exact hI₁.alloc x hx
          · exact hv₁.alloc x hx)
        (fun x => by rw [List.mem_append, hE.mem_iff]; mem_iff) (by
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
      obtain ⟨E'', hI'', hE''⟩ := hupd σ3 _ hag hLt (disj_cons_left.mpr ⟨hlAPB, fun x hx hx' => hd₁ x hx (hAPB x hx')⟩)
        (disj_cons_left.mpr ⟨hlS, hdS₁⟩)
      refine post_val hI'' .int disj_nil_left disj_nil_left ?_
      have := (hm₁.relabel (E'' := E₁ ++ L₁) (L'' := []) fun x => by mem_iff).trans
        ((hm₂.trans hm₃ disj_nil_left hm₁.wf).relabel (E'' := A ++ (P ++ (l :: L₁)) ++ B) (L'' := [])
          fun x => by mem_iff) disj_nil_left hwf
      exact (by simpa using this : Moves σ E _ (A ++ (P ++ (l :: L₁)) ++ B) []).relabel fun x => by
        simp only [List.append_nil, hE''.mem_iff]
    | let_ hx ha hb =>
      simp only [evalS]
      exact ret_letK (hfl _) hE (lookup_none_of_keys (by rw [typed_keys ha]; exact lookup_none_keys hx))
        (by rw [typed_keys ha]; exact hI.keys) hb hRdy hwf
        (hE _ _ _ _ _ _ _ _ _ _ _ ha hI hwf hRdy)
    | call hfd hretp hcap hrow hargs hlends hexcl =>
      rename_i f d owned k lent ys
      obtain ⟨vs, σ1, E₁, Ls, hevs, hI₁, hvs, hLn, hdL, hdLS, hm₁⟩ := atoms_ok hargs hI hwf
      have hwf₁ := hm₁.wf
      simp only [evalS, hfd, hevs]
      obtain ⟨hos, hts, hys, hmap, hholes, hplain, hpw⟩ := lends_ok hlends hI₁.foot hexcl
      obtain ⟨hkeys, hbody⟩ := hF d (List.mem_of_getElem? hfd)
      rw [hcap, hretp] at hbody
      obtain ⟨Γ'', hbody⟩ := hbody
      have hlen : vs.length = d.owns.length ∧ (hos.map Hole.loc).length = d.refs.length := by
        refine ⟨by rw [hvs.length]; simp, ?_⟩
        have := congrArg List.length hts
        simp only [List.length_map] at this ⊢
        exact this
      simp only [hmap, hlen, and_self, ↓reduceIte]
      exact call_core (hfl _) hE hkeys hbody hrow hI₁ hwf hm₁ hvs hLn hdL hdLS hholes hpw hts hRdy
    | applyOnce hx hrow ha =>
      rename_i x r' A a
      obtain ⟨cx, f, c, τc, Rc, Em, hcx, hσcx, hco, hRc, hcxR, hIm, hdRE, hdRS, hmm⟩ := move_clo hx hI hwf
      obtain ⟨d, xc, pn, hfd, hcap, hown, hrefs, hretp, hret, hrow', hτc⟩ := hco
      replace hrefs : d.refs = [] := by simpa [TyList.toList] using hrefs
      obtain ⟨hkeys0, hbody⟩ := hF d (List.mem_of_getElem? hfd)
      rw [hcap, hretp] at hbody
      obtain ⟨hxc, Γ'', hbody⟩ := hbody
      have hwfm := hmm.wf
      obtain ⟨v, σ1, E₁, L₁, hev, hI₁, hv₁, hdL, hdLS, hm₁⟩ := atom_ok ha hIm hwfm
      have hwf₁ := hm₁.wf
      -- What the closure captured: still there, kept apart from all the argument changed.
      have hRca : ∀ l ∈ Rc, (σ.set cx (some .moved)).mem l ≠ none := fun l hl => (hmm.alloc l).mpr (.inr (.inr hl))
      obtain ⟨hdR1, hdRL⟩ := hm₁.apart hwfm hRca hdRE
      have hag1 := hm₁.keeps hwfm hRca hdRE
      obtain ⟨w, Rw, hw, hvw, rfl, hcRw⟩ := hRc.contents hτc.1
      have hcx' : cx ≠ c := fun e => hcxR (e ▸ List.mem_cons_self ..)
      have hw1 : σ1.mem c = some w := by
        rw [hag1 c (List.mem_cons_self ..)]; simp [Store.set, Ne.symm hcx', hw]
      have hvw1 : VT F ι σ1 τc w Rw := hvw.frame (Agree.ofPre (by rt_tac) hag1 (fun l hl => List.mem_cons_of_mem _ hl)
        fun l hl => by
        rw [hag1 l (List.mem_cons_of_mem _ hl)]
        simp only [Store.set]
        split
        · subst_vars; exact absurd (List.mem_cons_of_mem _ hl) hcxR
        · rfl)
      -- The cell the closure kept what it captured in is freed: the value is the body's.
      have hcE₁ : c ∉ E₁ := fun h => hdR1 c (List.mem_cons_self ..) h
      have hcL₁ : c ∉ L₁ := fun h => hdRL c (List.mem_cons_self ..) h
      have hcS : c ∉ S := fun h => hdRS c (List.mem_cons_self ..) h
      have hag2 : ∀ l, l ≠ c → (σ1.set c none).mem l = σ1.mem l := fun l hl => by simp [Store.set, hl]
      have hI₂ : Inv F ι (σ1.set c none) Γ' env E₁ S :=
        ⟨hI₁.foot.frame <| Agree.of' fun l hl => hag2 l fun e => by
          subst e
          rcases List.mem_append.mp hl with h | h
          · exact hcE₁ h
          · exact hcS h, hI₁.nodup, hI₁.disj, hI₁.keys⟩
      have hvs : Vals F ι (σ1.set c none) [A, τc] [v, w] [L₁, Rw] :=
        .cons (hv₁.frame <| Agree.of' fun l hl => hag2 l fun e => hcL₁ (e ▸ hl))
          (.cons (hvw1.frame <| Agree.of' fun l hl => hag2 l fun e => hcRw (e ▸ hl)) .nil)
      have m1 := (hmm.trans hm₁ hdRE hwf).relabel (E'' := E₁ ++ L₁ ++ (c :: Rw)) (L'' := []) fun x => by
        simp only [List.mem_append, List.not_mem_nil, or_false]; grind
      have m2 := Moves.free (σ := σ1) (σ' := σ1.set c none) (E := E₁ ++ L₁ ++ (c :: Rw)) (E' := E₁ ++ L₁ ++ Rw) (D := [c])
        (WF.set_none hwf₁) rfl (fun l hl => (m1.alloc l).mpr (.inr (.inl hl)))
        (fun x => by simp only [List.mem_append, List.mem_cons, List.mem_singleton]; grind)
        (fun l hl => by simp at hl; subst hl; simp [Store.set]) (fun l hl => hag2 l (by simpa using hl))
        (by
          intro l hl hl'
          simp only [List.mem_singleton] at hl'
          subst hl'
          simp only [List.mem_append] at hl
          rcases hl with (h | h) | h
          · exact hcE₁ h
          · exact hcL₁ h
          · exact hcRw h)
      have hm₂ := (m1.trans m2 disj_nil_left hwf).relabel (E'' := E₁) (L'' := [L₁, Rw].flatten) fun x => by
        simp only [List.mem_append, List.flatten_cons, List.flatten_nil, List.append_nil,
          List.not_mem_nil, or_false]; grind
      have hdLw : Disj L₁ Rw := fun l h1 h2 => hdRL l (List.mem_cons_of_mem _ h2) h1
      have hown' : (cloFn d xc τc .once).owns = [(pn, A), (xc, τc)] := by simp [cloFn, hown]
      have hkeys : (((cloFn d xc τc .once).owns.map Prod.fst) ++ ((cloFn d xc τc .once).refs.map Prod.fst)).Nodup := by
        rw [hown']
        simp only [cloFn, hrefs, List.map_cons, List.map_nil, List.append_nil, List.nodup_cons,
          List.mem_singleton, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true]
        intro e; subst e; exact hxc (by simp [hown])
      have hcore := call_core0 (hfl _) (d := cloFn d xc τc .once) (hos := []) (vs := [v, w]) (Ls := [L₁, Rw]) hE hkeys
        (by simpa [cloFn] using hbody) (fun l hl => hrow l (hrow' ▸ by simpa [cloFn] using hl)) hI₂ hwf hm₂
        (by rw [hown']; exact hvs)
        (by simpa using nodup_append_disj.mpr ⟨hv₁.nodup, hvw1.nodup, hdLw⟩)
        (fun l hl h => by
          simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_append] at hl
          rcases hl with hl | hl
          · exact hdL l hl h
          · exact hdR1 l (List.mem_cons_of_mem _ hl) h)
        (fun l hl h => by
          simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_append] at hl
          rcases hl with hl | hl
          · exact hdLS l hl h
          · exact hdRS l (List.mem_cons_of_mem _ hl) h)
        (fun _ h => by simp at h) List.Pairwise.nil (by simp [cloFn, hrefs]) hRdy
      simp only [evalS, hcx, hσcx, hev, hfd, hcap, hw1]
      rw [show (cloFn d xc τc .once).ret = τ by simp [cloFn, hret]] at hcore
      simpa [hown', cloFn, hrefs, hown] using hcore
    | applyBorrow hk ha hp hw hrow =>
      obtain ⟨v, σ1, E₁, L₁, hev, hI₁, hv₁, hdL, hdLS, hm₁⟩ := atom_ok ha hI hwf
      obtain ⟨ra, τr, Lr, P, la, s, hra, hLr, hpath, hres, -, -, hsl, hso, hexw, hslot, hshp, hty⟩ :=
        place_ok hp hI₁.foot
      obtain ⟨Rt, hRt, hLrPR⟩ := path_split hpath hLr
      cases hRt with
      | @clo _ f c τc _ _ _ _ _ Rc hla hco hc hn =>
      obtain ⟨d, xc, pn, hfd, hcap, hown, hrefs, hretp, hret, hrow', hτc⟩ := hco
      replace hrefs : d.refs = [] := by simpa [TyList.toList] using hrefs
      obtain ⟨hkeys0, hbody⟩ := hF d (List.mem_of_getElem? hfd)
      rw [hcap, hretp] at hbody
      obtain ⟨hxc, Γ'', hbody⟩ := hbody
      rename_i k a A p r' w y
      -- What the closure captured is lent to its body as it is called: `readonly` or `mut`.
      obtain ⟨md, hmd, hmdw⟩ : ∃ md : Mode, (cloFn d xc τc k).refs = [(xc, md, τc)] ∧ (md = .mut → w = true) := by
        cases k with
        | once => exact absurd rfl hk
        | shared => exact ⟨.ro, rfl, fun h => by cases h⟩
        | excl => exact ⟨.mut, rfl, fun _ => hw rfl⟩
      let h : Hole := ⟨md, τc, y, c, P ++ [la], Rc, Lr⟩
      have hco' : CloOk F f τc k A _ r' .nil := ⟨d, xc, pn, hfd, hcap, hown, by simp [hrefs, TyList.toList], hretp, hret, hrow', hτc⟩
      have hhole : HoleOk F ι σ1 Γ' env h := ⟨s, ra, τr, hsl, hra, fun hm => hexw (hmdw hm),
        hpath.trans (.clo hla hco' .here), hLr, by simpa [h] using hLrPR,
        hso, hc, hslot, fun hs => .inr (by
          rcases hshp hs with ⟨rfl, -⟩ | ⟨-, P', rfl⟩
          · cases hpath; exact ⟨[], rfl⟩
          · exact ⟨_, rfl⟩), Ty.complete_whole hτc.1, hty⟩
      have hown' : (cloFn d xc τc k).owns = [(pn, A)] := by
        cases k with
        | once => exact absurd rfl hk
        | _ => simp [cloFn, hown]
      have hcall : ∀ k', k' ≠ .once → cloFn d xc τc k' = cloFn d xc τc k →
          Post F ι O σ E S Γ' env τ r hs (evalS F O n hs σ env (.apply k' p a)) := by
        intro k' hk' hkk
        cases k' with
        | once => exact absurd rfl hk'
        | shared | excl =>
          simp only [evalS, hev, hres, hla, hfd, hcap]
          rw [hkk]
          simp only [hown', hmd, List.length_singleton, and_self, ↓reduceIte]
          have hsame : (cloFn d xc τc k).body = d.body ∧ (cloFn d xc τc k).ret = d.ret ∧
              (cloFn d xc τc k).row = d.row := by cases k <;> simp [cloFn]
          have hkeys : (((cloFn d xc τc k).owns.map Prod.fst) ++ ((cloFn d xc τc k).refs.map Prod.fst)).Nodup := by
            rw [hown', hmd]
            simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.nodup_cons,
              List.mem_singleton, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self, and_true]
            intro e; subst e; exact hxc (by simp [hown])
          have hcore := call_core0 (hfl _) (d := cloFn d xc τc k) (hos := [h]) (vs := [v]) (Ls := [L₁]) hE hkeys
            (by rw [hsame.1, hsame.2.1, hsame.2.2]; exact hbody)
            (fun l hl => hrow l (hrow' ▸ hsame.2.2 ▸ hl)) hI₁ hwf (by simpa using hm₁)
            (by rw [hown']; exact .cons hv₁ .nil) (by simpa using hv₁.nodup) (by simpa using hdL)
            (by simpa using hdLS) (fun h' hh' => by simp at hh'; subst hh'; exact hhole)
            (List.pairwise_singleton _ _) (by rw [hmd]; rfl) hRdy
          rw [hsame.2.1, hret] at hcore
          simpa [h, hown', hmd] using hcore
      exact hcall k hk rfl
    | lendCall hfd hretp hcap hrow hargs hlends hexcl hpairs hmz hx hb =>
      rename_i f d m cs owned Γ₁ lent ys zs x body Γb
      obtain ⟨vs, σ1, E₁, Ls, hevs, hI₁, hvs, hLn, hdL, hdLS, hm₁⟩ := atoms_ok hargs hI hwf
      have hwf₁ := hm₁.wf
      simp only [evalS, hfd, hevs, hretp]
      obtain ⟨hos, hts, hys, hmap, hholes, hplain, hpw⟩ := lends_ok hlends hI₁.foot hexcl
      obtain ⟨hkeys, hbody⟩ := hF d (List.mem_of_getElem? hfd)
      rw [hcap, hretp] at hbody
      obtain ⟨hcne, Γ'', hbody, hcands⟩ := hbody
      -- Each place the callee may pick: the hole lent there, and its root among `zs`.
      have hhole : ∀ c ∈ cs, ∀ mi z, ys[c.1]? = some (mi, z) → ∃ hd : Hole, hos[c.1]? = some hd ∧ hd.mode = mi ∧ hd.root = z := by
        intro c _ mi z hyi
        have : (hos.map fun h => (h.mode, h.root))[c.1]? = some (mi, z) := by rw [hys]; exact hyi
        simp only [List.getElem?_map, Option.map_eq_some_iff, Prod.mk.injEq] at this
        obtain ⟨hd, h1, h2, h3⟩ := this
        exact ⟨hd, h1, h2, h3⟩
      have hcs : ∀ c ∈ cs, ∃ xi mi τi w hd, d.refs[c.1]? = some (xi, mi, τi) ∧ PlaceTy Γ'' c.2 d.ret w xi ∧
          (m = .mut → w = true) ∧ hos[c.1]? = some (hd : Hole) ∧ (m = .mut → hd.mode = .mut ∧ τi.shell = false) ∧
          (m = .mut → ∀ s, lookup hd.root Γ₁ = some s → s.shell = true → hd.path = []) := by
        intro c hc
        obtain ⟨xi, mi, τi, w, hri, hpt, hmw⟩ := hcands c hc
        obtain ⟨z, hz, mi', hyi, hmm⟩ := hpairs.mem_left hc
        obtain ⟨hd, hhi, hdm, hdz⟩ := hhole c hc mi' z hyi
        exact ⟨xi, mi, τi, w, hd, hri, hpt, hmw, hhi, fun h => ⟨hdm ▸ hmm h, (hmz h).2.2.1 c hc _ hri⟩,
          fun h s0 hs0 hsh0 => hplain hd (List.mem_of_getElem? hhi) s0 hs0 hsh0
            (shell_fn_of hs0 (hdz ▸ (hmz h).2.2.2 z hz) hsh0)⟩
      have hzs : Pairs (fun c z => ∃ hd : Hole, hos[c.1]? = some hd ∧ hd.root = z) cs zs :=
        hpairs.imp fun c hc z ⟨mi, hyi, _⟩ => by
          obtain ⟨hd, hhi, -, hz⟩ := hhole c hc mi z hyi
          exact ⟨hd, hhi, hz⟩
      have hlive : ∀ z ∈ zs, ∀ τ', lookup z Γ₁ ≠ some (.own τ' false) := fun z hz => by
        obtain ⟨c, -, mi, hyi, -⟩ := hpairs.mem_right hz
        exact hlends.root_live _ (List.mem_of_getElem? hyi)
      have hlen : vs.length = d.owns.length ∧ (hos.map Hole.loc).length = d.refs.length := by
        refine ⟨by rw [hvs.length]; simp, ?_⟩
        have := congrArg List.length hts
        simp only [List.length_map] at this ⊢
        exact this
      simp only [hmap, hlen, and_self, ↓reduceIte]
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
      have hIc := callee_inv (k := 0) (d := d) hI₁ hholes hpw (by simpa using hts.symm) hkeys hfo hEo hEoin hdL
        hdLS hwf₁ hold (by rt_tac) (fun _ _ _ h => by simpa using h)
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
      have h4 := ret_callLendK (hfl _) (n := n) (σf := σ1) (σ0 := σ2) (r := r) (hs := hs) hE hrow hI₁ hholes hpw hts
        hkeys hvs.owns_complete hbody hcells hcne hcs hzs (fun h => ⟨(hmz h).1, (hmz h).2.1⟩) hlive hx hb hRdy hwf₂ (by rw [hX]; exact Agree.of' fun l hl => hold l (hwf₁ l (by
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
    | ite hc ha hb wa wb =>
      obtain ⟨v, σ1, E₁, L₁, hev, hI₁, hv₁, -, -, hm₁⟩ := atom_ok hc hI hwf
      cases hv₁ with
      | @int k =>
      simp only [evalS, hev]
      split
      · exact post_after (by simpa using hm₁) hwf (post_weaken (hE _ _ _ _ _ _ _ _ _ _ _ hb hI₁ hm₁.wf hRdy) wb)
      · exact post_after (by simpa using hm₁) hwf (post_weaken (hE _ _ _ _ _ _ _ _ _ _ _ ha hI₁ hm₁.wf hRdy) wa)
    | throw_ ha hlab =>
      obtain ⟨v, σ1, E₁, L₁, hev, hI₁, hv₁, -, -, hm₁⟩ := atom_ok ha hI hwf
      cases hv₁ with
      | int =>
      simp only [evalS, hev]
      obtain ⟨f, hf⟩ := hRdy.2 _ hlab
      have hh := find_handles hf
      cases f with
      | capture => simp [Frame.handles] at hh
      | cancel => simp [Frame.handles] at hh
      | abort l i =>
        simp only [hf]
        exact ⟨⟨l, find_mem hf⟩, E₁, hI₁, by simpa using hm₁⟩
    | try_ hx hb hh =>
      simp only [evalS]
      have hk := hI.keys
      rw [← typed_keys hb] at hk
      exact post_after (Moves.freshen hwf hI.alloc) hwf (ret_catchK (hfl _) hE hKR hx hk hh (by intro e h; cases h) hRdy
        (hwf : WF _) hI.allocS hI.disj (hE _ _ _ _ _ _ _ _ _ _ _ hb hI.fresh (hwf : WF _)
          ⟨catch_hsok (by intro e h; cases h) hRdy.1, catch_covers hRdy.2⟩))
    | handleAbort hop howns hrefs hx hb hh =>
      simp only [evalS]
      have hk := hI.keys
      rw [← typed_keys hb] at hk
      exact post_after (Moves.freshen hwf hI.alloc) hwf (ret_catchK (hfl _) hE hKR hx hk hh
        (by intro e' h; cases h; exact ⟨_, hop, howns, hrefs⟩) hRdy (hwf : WF _) hI.allocS hI.disj
        (hE _ _ _ _ _ _ _ _ _ _ _ hb hI.fresh (hwf : WF _)
          ⟨catch_hsok (by intro e' h; cases h; exact ⟨_, hop, howns, hrefs⟩) hRdy.1, catch_covers hRdy.2⟩))
    | while_ hc hb =>
      simp only [evalS]
      exact ret_whileC hE hc hb hRdy hwf (hE _ _ _ _ _ _ _ _ _ _ _ hc hI hwf hRdy)
    | defer hb hd =>
      simp only [evalS]
      exact ret_deferK (hfl _) hE hd hRdy hwf (hE _ _ _ _ _ _ _ _ _ _ _ hb hI hwf hRdy)
    | perform hop hlab hargs hlends hexcl =>
      obtain ⟨vs, σ1, E₁, Ls, hevs, hI₁, hvs, hLn, hdL, hdLS, hm₁⟩ := atoms_ok hargs hI hwf
      obtain ⟨hos, hts, hys, hmap, hholes, hplain, hpw⟩ := lends_ok hlends hI₁.foot hexcl
      simp only [evalS, hop, hevs, hmap]
      obtain ⟨f, hf⟩ := hRdy.2 _ hlab
      have hh := find_handles hf
      cases f with
      | abort l i =>
        -- Unwinding: the operation's argument is an integer, which owns nothing.
        obtain ⟨op', hop', howns, -⟩ := find_abort_op hRdy.1 hf
        rw [hop] at hop'
        cases hop'
        rw [howns] at hvs
        cases hvs with
        | cons hv hnil =>
          cases hnil
          cases hv with
          | int =>
            simp only [hf]
            exact ⟨⟨l, find_mem hf⟩, E₁, hI₁, by simpa using hm₁⟩
      | capture e' i =>
        simp only [Frame.handles, beq_iff_eq] at hh
        subst hh
        simp only [hf]
        have hMin : ∀ l ∈ mutCells (olds hos), l ∈ E₁ := fun l hl => by
          obtain ⟨h, hh, hl⟩ := mem_olds_mut.mp hl
          exact (hole_in hI₁ (hholes h hh)).2 (Hole.excl_mut hl).1 l hl
        refine ⟨_, E₁.filter (· ∉ mutCells (olds hos)), hos, [], Ls, .inl (find_mem hf), hop, hRdy.2,
          fun _ h => by simp at h, .base hI₁ hholes hpw hop hts (Weaker.refl _), rfl, hvs, hLn, ?_, hdLS, ?_⟩
        · intro l hl h
          simp only [List.mem_append] at h
          rcases h with h | h
          · exact hdL l hl (mem_keep.mp h).1
          · exact hdL l hl (hMin l h)
        · exact hm₁.relabel fun x => by
            have := hMin x
            simp only [List.mem_append, mem_keep] at *; grind
      | cancel i =>
        simp only [hf]
        have hMin : ∀ l ∈ mutCells (olds hos), l ∈ E₁ := fun l hl => by
          obtain ⟨h, hh, hl⟩ := mem_olds_mut.mp hl
          exact (hole_in hI₁ (hholes h hh)).2 (Hole.excl_mut hl).1 l hl
        refine ⟨_, E₁.filter (· ∉ mutCells (olds hos)), hos, [], Ls, .inr (.inl (find_mem hf)), hop, hRdy.2,
          fun _ h => by simp at h, .base hI₁ hholes hpw hop hts (Weaker.refl _), rfl, hvs, hLn, ?_, hdLS, ?_⟩
        · intro l hl h
          simp only [List.mem_append] at h
          rcases h with h | h
          · exact hdL l hl (mem_keep.mp h).1
          · exact hdL l hl (hMin l h)
        · exact hm₁.relabel fun x => by
            have := hMin x
            simp only [List.mem_append, mem_keep] at *; grind
    | lend hx hp hm hmf hun hb => exact lend_ok hE hx hp hm hmf hun hb hI hwf hRdy
    | lendIdx hx hp hz hm hmf hun hb => exact lendIdx_ok hE hx hp hz hm hmf hun hb hI hwf hRdy
    | gen hopN hNowns hNrefs hNret hopY hYowns hYrefs hYret hcy hfd hretp hcap hdret hrow hey hdrefs hargs hcaps hexcl
        hb hcb =>
      exact gen_ok hF hE hR hopN hNowns hNrefs hNret hopY hYowns hYrefs hYret hcy hfd hretp hcap hdret hrow hey hdrefs
        hargs hcaps hexcl hb hcb hI hwf hRdy
    | lendField hx hy hty hsl _ hmf hb => exact lendField_ok hE hx hy hty hsl hmf hb hI hwf hRdy
    | scope hop _ howns hrefs hret hopS hSowns hSrefs hSret hne hrT heT hcτ hRt hcaps hb =>
      exact scope_ok hE hR ⟨hop, howns, hrefs, hret, hopS, hSowns, hSrefs, hSret, hne, hrT, heT, hcτ⟩ hRt hcaps hb hI
        hwf hRdy
    | handle hop _ hcomp hos hrs hcaps hexcl hnd harm hbody =>
      exact handle_ok hE hR hop hcomp hos hrs hcaps hexcl hnd harm hbody hI hwf hRdy
    | handleR hop _ hcomp hos hrs hcaps hexcl hnd hfd hown hdrefs hretp hcap hret hrow hC harm hbody =>
      exact handleR_ok hF hE hR hop hcomp hos hrs hcaps hexcl hnd hfd hown hdrefs hretp hcap hret hrow hC harm
        hbody hI hwf hRdy
    | region hx _ hb => exact region_ok hE hR hx hb hI hwf hRdy
    | ralloc hRl hs hd ha => exact ralloc_ok hRl hs hd ha hI hwf
    | rget hp hRl hs hd => exact rget_ok hp hRl hs hd hI hwf
    | rset hp hRl hs hd ha => exact rset_ok hp hRl hs hd ha hI hwf
    | rlnew hRl hs _ => exact rlnew_ok hRl hs hI hwf
    | rpush hp hRl hs hd ha => exact rpush_ok hp hRl hs hd ha hI hwf
    | rnth hp hz hRl hs hd => exact rnth_ok hp hz hRl hs hd hI hwf
    | rlen hp hRl hs => exact rlen_ok hp hRl hs hI hwf
    | vnew hc => exact vnew_ok hc hI hwf
    | vlen hp => exact vlen_ok hp hI hwf
    | vpush ha hp => exact vpush_ok ha hp hI hwf
    | vpop hp hc => exact vpop_ok hp hc hI hwf
    | lendSlice hx hp hlo hhi hm hb => exact lendSlice_any hE hx hp hlo hhi hm hb hI hwf hRdy
    | par hop _ howns hrefs hret hfa hfb hretpa hcapa hretpb hcapb hea heb hrowa hrowb hca hcb hargs hlends =>
      exact par_ok hF hR hK hop howns hrefs hret hfa hfb hretpa hcapa hretpb hcapb hea heb hrowa hrowb
        hca hcb hargs hlends hI hwf hRdy
    | handleV hop htask hrefs hret howns hτ hfa hdowns hdrefs hdret hdrow hdretp hdcap hra hf hrefsd hretd hretpd
        hcapd he hrow hcross hargs =>
      exact handleV_ok hF hE hfl (hKv _) hop htask hrefs hret howns hτ hfa hdowns hdrefs hdret hdrow hdretp
        hdcap hra hf hrefsd hretd hretpd hcapd he hrow hcross hargs hI hwf hRdy
    | resume hx hra ha => exact resumeV_ok hF hK (hKv _) hx hra ha hI hwf hRdy

theorem ret_ok (hF : FnsOk F O) (hE : EvalOk F O n) (hKs : ∀ m, m < n → EvalKOk F O m ∧ RetOk F O m) :
    RetOk F O n := by
  have hKo : ∀ m, n = m + 1 → EvalKOk F O m ∧ RetOk F O m := fun m h => hKs m (by omega)
  intro hs ιi ιo σf f inL outL Xf A σ0 Ein res _ hf hR hA hwf hag halloc hnd hd hSa hSd hp
  have hfl : ∀ ι, [WorldOk F O ι.w] → FlushOk F ι (flushR F O n) := fun _ _ => flushR_ok fun m h => (hKo m h).1
  have hflm : ∀ ι, [WorldOk F O ι.w] → ∀ m, n = m + 1 → FlushOk F ι (flushR F O m) :=
    fun _ _ m h => flushR_ok fun k hk => (hKs k (by omega)).1
  cases hf with
  | letK hx hk hb => exact ret_letK (hfl _) hE hx hk hb hR hwf hp
  | callLendK hrow hI₁ hholes hpw hts hkeys hoc hbody hcells hcne hcs hzs hzm hlive hx hb =>
    exact ret_callLendK (hfl _) hE hrow hI₁ hholes hpw hts hkeys hoc hbody hcells hcne hcs hzs hzm hlive hx hb hR hwf
      hag hd hSa hSd hp
  | scopeK hx hk hτx =>
    have : ∀ τ c, ret F O n hs (.scopeK τ c) res = leave (flushR F O n) τ c res := fun τ c => by
      rcases res with ⟨_ | _ | _ | _ | _, _⟩ <;> simp [ret, leave, Res.done]
    rw [this]
    exact leave_ok' (hfl _) hτx hwf hx hk hp
  | callK hrow hI₁ hholes hpw hts hkeys hoc hbody hcells =>
    exact ret_callK (hfl _) hrow hI₁ hholes hpw hts hkeys hoc hbody hcells hR hwf hag hd hSa hSd hp
  | catchK hx hk hh hl => exact ret_catchK (hfl _) hE hKo hx hk hh hl hR hwf hSa (by simpa using hSd) hp
  | whileC hc hb => exact ret_whileC hE hc hb hR hwf hp
  | whileB hc hb => exact ret_whileB hE hc hb hR hwf hp
  | deferK hd' => exact ret_deferK (hfl _) hE hd' hR hwf hp
  | deferV hv =>
    have : ∀ τ v, ret F O n hs (.deferV τ v) res = cleanV (flushR F O n) τ v res := fun τ v => by
      rcases res with ⟨_ | _ | _ | _ | _, _⟩ <;> simp [ret, cleanV]
    rw [this]
    exact ret_deferV (hfl _) hv hag halloc hnd hd (fun l h1 h2 => hSd l h1 (List.mem_append.mpr (.inl h2)))
      (fun l h1 h2 => hSd l h1 (List.mem_append.mpr (.inr h2))) hSa hwf hp
  | deferA =>
    have : ∀ j k, ret F O n hs (.deferA j k) res = cleanA j k res := fun j k => by
      rcases res with ⟨_ | _ | _ | _ | _, _⟩ <;> simp [ret, cleanA]
    rw [this]
    exact ret_deferA (hA _ (List.mem_singleton_self _)) hp
  | dropK => rw [← dropRet_eq]; exact ret_dropK (hfl _) (hA _ (List.mem_singleton_self _)) hR.2 hwf hp
  | dropKv hv =>
    rw [← dropRet_eq]; exact ret_dropKv (hfl _) hv hR.2 hag halloc hnd hd (fun l h1 h2 => hSd l h1 (List.mem_append.mpr (.inl h2)))
      (fun l h1 h2 => hSd l h1 (List.mem_append.mpr (.inr h2))) hSa hwf hp
  | lendK hSin hSS hre => exact ret_lendK hSin hSS hre hR.2 hwf hag halloc hnd hd hSa hSd hp
  | cloK hSin hSS haX hre => exact ret_cloK hSin hSS haX hre hR.2 hwf hag halloc hnd hd hSa hSd hp
  | capK hH hP hcaps => exact ret_capK (hfl _) hE hKo hH hP hcaps hR hwf hag halloc hnd hd hSa hSd hp
  | armK hH hP hK hro harm hcells => exact ret_armK (hfl _) hKo hH hP hK hro harm hcells hR hA hwf hag halloc hnd hd hSa hSd hp
  | startK hb => simpa using ret_startK hE hb hR hwf (by simpa [Kont.push] using hp)
  | taskK hrow hkeys hoc hbody hcells =>
    simpa using ret_taskK (hfl _) hrow hkeys hoc hbody hcells hR hwf (by simpa [Kont.push] using hp)
  | parS hP hroR hroO hSr hSo hK => exact ret_parS (hfl _) hKo hP hroR hroO hSr hSo hK hR hA hwf hag halloc hnd hd hSa hSd hp
  | parD hP hro hSr hw => exact ret_parD (hfl _) hKo hP hro hSr hw hR hwf hag halloc hnd hd hSa hSd hp
  | parY hop howns hrefs hret =>
    simpa using ret_parY hKo hop howns hrefs hret hR hwf (by simpa using hag) hSa (by simpa using hSd) hp
  | parE hI hro hSo => exact ret_parE hI hro hSo hR hwf hag halloc hnd hd hSa hSd hp
  | regionK => exact ret_regionK hR hwf (by simpa using hag) hSa (by simpa using hSd) (by simpa [Kont.push] using hp)
  | postR hP hv => exact ret_postR (hfl _) hE hP hv hR hwf hag halloc hnd hd hSa hSd hp
  | genC hG hSo hK => exact ret_genC hKo (hflm _) hG hSo hK hR hA hwf hag halloc hnd hd hSa hSd hp
  | genCd hG hc => exact ret_genCd hKo hG hc hR hwf hag halloc hnd hd hSa hSd hp
  | genP hG hSo hKc => exact ret_genP (hfl _) hKo hG hSo hKc hR hA hwf hag halloc hnd hd hSa hSd hp
  | genY hop howns hrefs hret hcy =>
    simpa using ret_genY (hfl _) hKo hop howns hrefs hret hcy hR hwf (by simpa using hag) hSa (by simpa using hSd) hp
  | capD hop hrefs hcτ hrin =>
    simpa using ret_capD (hfl _) hKo hop hrefs hcτ hrin (hA _ (List.mem_singleton_self _)) hR hwf (by simpa using hag)
      hSa (by simpa using hSd) hp
  | genN hop howns hrefs hret hcy =>
    simpa using ret_genN hKo hop howns hrefs hret hcy hR hwf (by simpa using hag) hSa (by simpa using hSd) hp
  | genE hG hIc hdFE hSo ho => exact ret_genE (hfl _) hG hIc hdFE hSo ho hR hA hwf hag halloc hnd hd hSa hSd hp
  | scB hS hcz hT => exact ret_scB hF hKo hS hcz hT hR hA hwf hag halloc hnd hd hSa hSd hp
  | scW hS hcz hbr hbrefs hKb hagb hab hT hdbq hSt hro =>
    exact ret_scW hF hKo hS hcz hbr hbrefs hKb hagb hab hT hdbq hSt hro hR hA hwf hag halloc hnd hd hSa hSd hp
  | scV hS hcz hIb hv hdLE hdLS hT hdq hSt hro =>
    exact ret_scV (hfl _) hF hKo hS hcz hIb hv hdLE hdLS hT hdq hSt hro hR hA hwf hag halloc hnd hd hSa hSd hp
  | scX hop howns hrefs hret hopS hSowns hSrefs hSret =>
    simpa using ret_scX (hfl _) hKo hop howns hrefs hret hopS hSowns hSrefs hSret hR hwf (by simpa using hag) hSa
      (by simpa using hSd) hp
  | scEb hS hT => exact ret_scEb (hfl _) hKo hS hT hR hA hwf hag halloc hnd hd hSa hSd hp
  | scEt hS hI hT hdT hSt hro => exact ret_scEt hKo hS hI hT hdT hR hA hwf hag halloc hnd hd hSa hSd hSt hro hp

/-- Expressions, frames and continuations, at every fuel. -/
theorem sound (hF : FnsOk F O) : ∀ n, EvalOk F O n ∧ RetOk F O n ∧ EvalKOk F O n
  | 0 =>
    have hE : EvalOk F O 0 := by intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; simp [eval, Post]
    have hR : RetOk F O 0 := ret_ok hF hE fun m h => absurd h (by omega)
    ⟨hE, hR, evalK_ok hR (nest_ok hF fun m h => absurd h (by omega))⟩
  | n + 1 =>
    have ⟨hE, hR, hK⟩ := sound hF n
    have hE' := eval_ok_succ hF hE hR hK fun m h => let s := sound hF m; ⟨s.1, s.2.2, s.2.1⟩
    have hR' : RetOk F O (n + 1) := ret_ok hF hE' fun m h =>
      if hm : m = n then hm ▸ ⟨hK, hR⟩ else let s := sound hF m; ⟨s.2.2, s.2.1⟩
    have hN' : NestOk F O (n + 1) := nest_ok hF fun m h =>
      if hm : m = n then hm ▸ ⟨hE, hK, hR⟩ else let s := sound hF m; ⟨s.1, s.2.2, s.2.1⟩
    ⟨hE', hR', evalK_ok hR' hN'⟩
termination_by n => n
decreasing_by all_goals omega

theorem eval_ok (hF : FnsOk F O) (n : Nat) : EvalOk F O n := (sound hF n).1

def Store.empty : Store := { mem := fun _ => none, next := 0 }

/-- The empty store, under the schedule `s` of which task goes on where one gives way, and `p` of
where a running task is stopped for another: with both arbitrary, every interleaving of the tasks'
operations, as when they run on many cores at once. -/
def Store.sched0 (s : Nat → Bool) (p : Nat → Bool := fun _ => false) : Store := { Store.empty with sched := s, pre := p }

theorem Store.sched0_wf : WF (Store.sched0 s p) := fun _ h => absurd rfl h

/-- A well-typed program, run from an empty store with only a handler of failure, under any schedule
of its tasks and with its running tasks stopped for others before any of their operations — every
interleaving of their operations, as on many cores at once — is never stuck: it ends with a value of
its type owning everything allocated, or failing having freed everything. -/
theorem program_ok_sched (hF : FnsOk F O) (ht : Typed F O [] e τ Γ' [.fail]) (s p : Nat → Bool) (n : Nat) :
    match eval F O n [.abort .fail 0] (Store.sched0 s p) [] e with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT F ⟨[], Wstar F O⟩ σ' τ v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none := by
  have hR : Ready O [.abort .fail 0] [.fail] :=
    ⟨.abort (by intro e h; cases h) .nil, fun l hl => by
      simp only [List.mem_singleton] at hl; subst hl; exact find_head⟩
  have h := eval_ok hF n [.abort .fail 0] (Store.sched0 s p) ⟨[], Wstar F O⟩ [] [] [] [] e τ Γ' [.fail] ht
    ⟨.nil, List.nodup_nil, disj_nil_left, List.nodup_nil⟩ Store.sched0_wf hR
  generalize eval F O n [.abort .fail 0] (Store.sched0 s p) [] e = r at h ⊢
  rcases r with ⟨r, σ'⟩
  have hΓ : Γ' = [] := List.eq_nil_of_map_eq_nil (typed_keys ht)
  subst hΓ
  cases r with
  | stuck => exact h
  | timeout => trivial
  | panic => trivial
  | susp j ef vs ls K =>
    obtain ⟨-, -, -, -, -, hc, -⟩ := h
    rcases hc with hc | hc | hc <;> simp at hc
  | val v =>
    obtain ⟨E', L, hI, hv, -, -, hm⟩ := h
    cases hI.foot
    exact ⟨L, hv, fun l => by rw [hm.alloc]; simp [Store.sched0, Store.empty]⟩
  | abort i k =>
    obtain ⟨-, E', hI, hm⟩ := h
    cases hI.foot
    intro l
    have := hm.alloc l
    simp [Store.sched0, Store.empty] at this
    exact this

/-- As `program_ok_sched`, under the schedule that keeps each task running until it gives way. -/
theorem program_ok (hF : FnsOk F O) (ht : Typed F O [] e τ Γ' [.fail]) (n : Nat) :
    match eval F O n [.abort .fail 0] .empty [] e with
    | (.stuck, _) => False
    | (.susp _ _ _ _ _, _) => False
    | (.timeout, _) => True
    | (.panic, _) => True
    | (.val v, σ') => ∃ L, VT F ⟨[], Wstar F O⟩ σ' τ v L ∧ ∀ l, σ'.mem l ≠ none ↔ l ∈ L
    | (.abort _ _, σ') => ∀ l, σ'.mem l = none :=
  program_ok_sched hF ht (fun _ => true) (fun _ => false) n

end FlyCore.Ownership
