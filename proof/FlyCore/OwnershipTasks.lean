import FlyCore.OwnershipSound

/-!
# Ownership: tasks

Two tasks run as one, each giving way to the other wherever it performs the operation they share,
in whatever order the schedule picks. Each keeps its own cells, and reads only what it was lent
`readonly`, which neither changes; while one runs, the other's cells, waiting in its continuation,
are as it left them.
-/

namespace FlyCore.Ownership

/-! ## A task's body, started -/

/-- A task first given its turn runs its body. -/
theorem ret_startK (hE : EvalOk F O n) (hb : Typed F O Γ b τ Γ' r) (hR : Ready O hs r) (hwf : WF σ0)
    (hp : Post F ι O σ0 Ein S Γ env .int r hs res) :
    Post F ι O σ0 Ein S Γ' env τ r hs (ret F O n hs (.startK env b) res) := by
  rcases res with ⟨res, σ1⟩
  cases res with
  | val v =>
    obtain ⟨E₁, L₁, hI₁, hv₁, -, -, hm₁⟩ := hp
    cases hv₁ with
    | int =>
      simp only [ret]
      exact post_after (hm₁.relabel fun x => by simp) hwf (hE _ _ _ _ _ _ _ _ _ _ _ hb hI₁ hm₁.wf hR)
  | abort j k =>
    simp only [ret]
    have ⟨_, _, hI₁, _⟩ := hp
    exact post_out hp (typed_weaker hb hI₁.keys)
  | susp j ef vs ls K => simp only [ret]; exact post_frame hp (.startK hb)
  | stuck => simp [Post] at hp
  | timeout => simp [ret, Post]
  | panic => simp [ret, Post]

/-! ## Giving way -/

/-- A task that gave way, resumed: what its continuation does. -/
theorem yield_resume {e : Nat} (hKk : EvalKOk F O m) (hop : O[e]? = some op) (hrefs : op.refs = []) (hret : op.ret = .int)
    (hK : FramesOk F O ι σs K op top X hos A) (hR : Ready O hs top.r) (hA : ∀ a ∈ A, AimedIn a hs)
    (hwf : WF σr) (hag : Agree σs σr (X ++ top.S)) (hXa : ∀ l ∈ X ++ top.S, σs.mem l ≠ none) (hXn : X.Nodup)
    (hdS : Disj top.S X) :
    Post F ι O σr X top.S top.Γ top.env top.τ top.r hs (evalK F O m hs σr K (.val (.int 0))) := by
  obtain ⟨-, -, -, -, -, -, -, -, hts, -, -, -, -⟩ := hK.base_of
  rw [hrefs] at hts
  obtain rfl : hos = [] := List.map_eq_nil_iff.mp hts
  have h := hKk hs _ σs K top X [] A σr [] (.val (.int 0)) op [] hK hR hA hwf hag hXa hXn rfl
    (fun _ h => by simp at h) (by simp [mutCells]) (by simp [mutCells, Disj])
    (by simp only [mutCells, List.flatMap_nil, List.append_nil]; exact fun l h1 h2 => hdS l h1 h2)
    (.inl ⟨_, rfl, by rw [hret]; exact .int, by simp [Disj]⟩)
  simpa [mutCells] using h

/-- A task running alone as it is dropped: its turns are given back at once. -/
theorem ret_parY (hKo : ∀ m, n = m + 1 → EvalKOk F O m ∧ RetOk F O m) (hop : O[e]? = some op)
    (howns : op.owns = []) (hrefs : op.refs = []) (hret : op.ret = .int)
    (hR : Ready O hs r) (hwf : WF σ0) (hag : Agree σf σ0 S) (hSa : ∀ l ∈ S, σ0.mem l ≠ none) (hSd : Disj S Ein)
    (hp : Post F ι O σ0 Ein S Γ env τ (.eff e :: r) (.capture e hid :: hs) res) :
    Post F ι O σ0 Ein S Γ env τ r hs (ret F O n hs (.parY e hid) res) := by
  have hA : ∀ a, AimedIn a (.capture e hid :: hs) → AimedIn a hs := fun a ⟨l, hl⟩ =>
    ⟨l, (List.mem_cons.mp hl).resolve_left (by simp)⟩
  rcases res with ⟨res, σ1⟩
  have pass : (∀ j ef vs ls K, res = .susp j ef vs ls K → j ≠ hid ∨ ef ≠ e) →
      Post F ι O σ0 Ein S Γ env τ r hs (ret F O n hs (.parY e hid) (res, σ1)) := by
    intro hnot
    have : ret F O n hs (.parY e hid) (res, σ1) = passK (.parY e hid) (res, σ1) := by
      cases res with
      | susp j ef vs ls K => rw [ret.eq_def]; simp [passK, hnot j ef vs ls K rfl]
      | _ => simp [ret, passK]
    rw [this]
    have h := post_pass (Xf := []) (σf := σf) (.parY (hid := hid) hop howns hrefs hret) (fun _ h => h)
      (fun σ1 Eb _ _ hI => ⟨Eb, hI, fun z => by simp⟩) hR.2 hA ?_ hwf hag (fun _ h => by simp at h)
      List.nodup_nil disj_nil_left hSa (by simpa using hSd) hp
    · simpa using h
    · intro j ef vs ls K σ' h hc
      have h1 := hnot j ef vs ls K (congrArg Prod.fst h)
      rcases List.mem_cons.mp hc with h | h
      · simp only [Frame.capture.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp at h1
      · exact h
  cases res with
  | val v => exact pass fun _ _ _ _ _ h => by cases h
  | abort j k => exact pass fun _ _ _ _ _ h => by cases h
  | stuck => exact pass fun _ _ _ _ _ h => by cases h
  | timeout => exact pass fun _ _ _ _ _ h => by cases h
  | panic => exact pass fun _ _ _ _ _ h => by cases h
  | susp j ef vs ls K =>
  by_cases hc : j ≠ hid ∨ ef ≠ e
  · exact pass fun _ _ _ _ _ h => by cases h; exact hc
  simp only [ne_eq, not_or, Decidable.not_not] at hc
  obtain ⟨h1, h2⟩ := hc
  subst j ef
  obtain ⟨op', X, hos, A, Lv, -, hop', -, haim, hK, hls, hvs, hLn, hdLX, hdLS, hm⟩ := hp
  obtain rfl : op = op' := Option.some.inj (hop.symm.trans hop')
  rw [howns] at hvs
  cases hvs
  cases n with
  | zero => simp [ret, Post]
  | succ m =>
  obtain ⟨hKk, hRr⟩ := hKo m rfl
  simp only [ret, ne_eq, not_true_eq_false, or_self, ↓reduceIte]
  have hwf₁ := hm.wf
  obtain ⟨-, -, -, -, -, -, -, -, hts, -, -, hXn, -⟩ := hK.base_of
  rw [hrefs] at hts
  obtain rfl : hos = [] := List.map_eq_nil_iff.mp hts
  simp only [olds, mutCells, List.map_nil, List.flatMap_nil, List.append_nil, List.flatten_nil] at hm hdLX hdLS
  have hSa1 : ∀ l ∈ S, σ1.mem l ≠ none := fun l hl => by
    rw [hm.keeps hwf hSa (fun l h1 h2 => hSd l h1 h2) l hl]; exact hSa l hl
  have hR' : Ready O (.capture e hid :: hs) (.eff e :: r) := (FrameOk.parY (F := F) (ι := ι) (σf := σ1) (Γ := Γ) (env := env) (τ := τ)
    (S := S) (hid := hid) hop howns hrefs hret).ready hR
  have hres := yield_resume (top := ⟨Γ, env, τ, S, .eff e :: r⟩) hKk hop hrefs hret hK hR' haim hwf₁ Agree.self
    (fun l hl => by
      rcases List.mem_append.mp hl with h | h
      · exact (hm.alloc l).mpr (.inr (.inl h))
      · exact hSa1 l h) hXn
    (hm.apart hwf hSa hSd).1
  have h2 := hRr hs _ _ σ1 (.parY e hid) ⟨Γ, env, τ, S, .eff e :: r⟩ ⟨Γ, env, τ, S, r⟩ [] [] σ1 X _
      (.parY hop howns hrefs hret) hR (fun _ h => by simp at h) hwf₁ Agree.self (fun _ h => by simp at h)
      List.nodup_nil disj_nil_left hSa1 (by simpa using (hm.apart hwf hSa hSd).1) hres
  exact post_after hm hwf (by simpa using h2)

/-! ## A task's call -/

/-- A context of `readonly` borrows owns nothing it may change. -/
theorem foot_ro : Foot F ι σ Γ env E S → RoCtx Γ → E = [] := by
  intro h
  induction h with
  | nil => intro _; rfl
  | @cons s a L Γ env E S x _ _ ih =>
    intro hro
    obtain ⟨τ, hτ⟩ := hro (x, s) (List.mem_cons_self ..)
    simp only at hτ
    subst hτ
    rw [ih fun p hp => hro p (List.mem_cons_of_mem _ hp)]
    simp [addE, exclPart, Slot.excl]

theorem refCtx_ro (hro : ∀ x ∈ refs, x.2.1 = .ro) : RoCtx (refCtx refs) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact ⟨q.2.2, by simp [hro q hq]⟩

theorem refCtx_keys {owns : List (Var × Ty)} {refs : List (Var × Mode × Ty)} (hkeys : ((owns.map Prod.fst) ++ (refs.map Prod.fst)).Nodup) :
    ((refCtx refs).map Prod.fst).Nodup := by
  have := (List.nodup_append.mp hkeys).2.1
  simpa [refCtx, Function.comp_def] using this

/-- A task's body ended: the parameters it owns are dropped, and what is left are the places it was
lent `readonly`. -/
theorem ret_taskK {d : Fn} {cells : Env} {ls : List Nat}
    (hrow : ∀ l ∈ d.row, l ∈ r)
    (hkeys : ((d.owns.map Prod.fst) ++ (d.refs.map Prod.fst)).Nodup) (hoc : ∀ o ∈ d.owns, o.2.complete = true)
    (hbody : Typed F O (fnCtx d) d.body d.ret Γ'' d.row) (hcells : cells.map Prod.fst = d.owns.map Prod.fst)
    (hR : Ready O hs r) (hwf : WF σ0)
    (hp : Post F ι O σ0 Ein St Γ'' (cells ++ (d.refs.map Prod.fst).zip ls) d.ret d.row hs res) :
    Post F ι O σ0 Ein St (refCtx d.refs) ((d.refs.map Prod.fst).zip ls) d.ret r hs
      (ret F O n hs (.callK ((d.owns.map Prod.snd).zip (cells.map Prod.snd))) res) := by
  have key : ∀ σ3 Ec' Lw, Inv F ι σ3 Γ'' (cells ++ (d.refs.map Prod.fst).zip ls) Ec' St → Disj Lw Ec' →
      Moves σ0 Ein σ3 Ec' Lw →
      ∃ σ4 Er, dropCells σ3 ((d.owns.map Prod.snd).zip (cells.map Prod.snd)) = some σ4 ∧
        Inv F ι σ4 (refCtx d.refs) ((d.refs.map Prod.fst).zip ls) Er St ∧ Agree σ3 σ4 Lw ∧ Disj Lw Er ∧
        Moves σ0 Ein σ4 Er Lw := by
    intro σ3 Ec' Lw hI₃ hdw hm₃
    have hsh : shape Γ'' = ownCtx d.owns ++ refCtx d.refs := by
      rw [typed_shape hbody (by simpa [fnCtx, List.map_append, List.map_map, Function.comp_def] using hkeys),
        shape_fnCtx]
    obtain ⟨Γa, rfl, hΓa⟩ := shape_split (ownCtx d.owns) hsh (refCtx_refs d.refs)
    have hla : Γa.length = cells.length := by
      rw [← shape_length, hΓa]; simpa [ownCtx] using (congrArg List.length hcells).symm
    obtain ⟨Ea, Sa, Er, Sr, hfa, hfr, rfl, rfl⟩ := hI₃.foot.split hla
    have hnd := nodup_append_disj.mp hI₃.nodup
    obtain ⟨rfl, σ4, hdrop, hn4, hfree4, hkeep4⟩ := dropCells_ok hfa hΓa hnd.1 hm₃.wf hoc
    have hdisj := hI₃.disj
    simp only [List.nil_append] at hdisj ⊢
    refine ⟨σ4, Er, hdrop, ⟨hfr.frame <| Agree.of' fun l hl => hkeep4 l fun h => ?_, hnd.2.1,
      fun l hl h => hdisj l hl (List.mem_append.mpr (.inr h)), refCtx_keys hkeys, by cur_inv⟩,
      Agree.of' fun l hl => hkeep4 l fun h => hdw l hl (List.mem_append.mpr (.inl h)),
      fun l h1 h2 => hdw l h1 (List.mem_append.mpr (.inr h2)), ?_⟩
    · rcases List.mem_append.mp hl with hl | hl
      · exact hnd.2.2 l h hl
      · exact hdisj l hl (List.mem_append.mpr (.inl h))
    have m3 := hm₃.relabel (E'' := Lw ++ Er ++ Ea) (L'' := []) fun x => by
      simp only [List.mem_append, List.not_mem_nil, or_false]; grind
    have m4 := Moves.free (E := Lw ++ Er ++ Ea) (E' := Lw ++ Er) (D := Ea)
      (WF.of_free hm₃.wf hn4 hfree4 hkeep4) hn4 (fun l hl => (m3.alloc l).mpr (.inr (.inl hl)))
      (fun x => by simp only [List.mem_append]) hfree4 hkeep4 (fun l h1 h2 => by
        rcases List.mem_append.mp h1 with h1 | h1
        · exact hdw l h1 (List.mem_append.mpr (.inl h2))
        · exact hnd.2.2 l h2 h1)
    exact (m3.trans m4 disj_nil_left hwf).relabel fun x => by
      simp only [List.mem_append, List.not_mem_nil, or_false, List.append_nil]; grind
  rcases res with ⟨res, σ3⟩
  cases res with
  | val w =>
    obtain ⟨Ec', Lw, hI₃, hvw, hdw, hdS, hm₃⟩ := hp
    obtain ⟨σ4, Er, hdrop, hI₄, hag', hdLE, hm⟩ := key σ3 Ec' Lw hI₃ hdw hm₃
    simp only [ret, hdrop]
    exact ⟨Er, Lw, hI₄, hvw.frame hag', hdLE, hdS, hm⟩
  | abort i k =>
    obtain ⟨haim, Ec', hI₃, hm₃⟩ := hp
    obtain ⟨σ4, Er, hdrop, hI₄, -, -, hm⟩ := key σ3 Ec' [] hI₃ disj_nil_left hm₃
    simp only [ret, hdrop]
    exact ⟨haim, Er, hI₄, hm⟩
  | susp j ef vs ls' K =>
    obtain ⟨op, X', hos', A, Lv, hc, hop, hcov, haim, hK, hls, hvs, hn, hdv, hdSv, hm⟩ := hp
    simp only [ret]
    have hK' := FramesOk.cons (σf := σ3) (A := A) (.taskK (ls := ls) (St := St) hrow hkeys hoc hbody hcells)
      (Weaker.refl _) Agree.self (fun _ h => by simp at h) List.nodup_nil disj_nil_left hK
      (fun _ h => by simp at h) (fun a ha => .inl ha)
    simp only [List.nil_append] at hK'
    exact ⟨op, X', hos', A, Lv, hc, hop, hR.2, haim, hK', hls, hvs, hn, hdv, hdSv, hm⟩
  | stuck => simp [Post] at hp
  | timeout => simp [ret, Post]
  | panic => simp [ret, Post]

/-! ## Frames that pass a suspension on -/

/-- An operation performed under a frame its handler is outside of: the frame joins the
continuation, its cells kept as they were. -/
theorem post_susp {hsin : HS} (hf : FrameOk F O ι ι σf f ⟨Γin, envin, τin, Sin, rin⟩ ⟨Γout, envout, τout, S, r⟩ Xf Af)
    (hcov : Covers hs r) (hA : ∀ a, AimedIn a hsin → AimedIn a hs) (hAf : ∀ a ∈ Af, AimedIn a hs)
    (hc' : Frame.capture ef j ∈ hsin → Frame.capture ef j ∈ hs)
    (hwf : WF σ0) (hag : Agree σf σ0 (Xf ++ S)) (halloc : ∀ l ∈ Xf, σf.mem l ≠ none) (hnd : Xf.Nodup)
    (hd : Disj Xf Ein) (hSa : ∀ l ∈ S, σ0.mem l ≠ none) (hSd : Disj S (Xf ++ Ein))
    (hp : Post F ι O σ0 Ein Sin Γin envin τin rin hsin (.susp j ef vs ls K, σ1)) :
    Post F ι O σ0 (Xf ++ Ein) S Γout envout τout r hs (.susp j ef vs ls (f :: K), σ1) := by
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
  obtain ⟨op, X, hos, A, Lw, hc, hop, -, haim, hK, hls, hvs, hn, hdw, -, hm⟩ := hp
  obtain ⟨hdX, hdL⟩ := hm.apart hwf hXa hd
  have hK' := FramesOk.cons (A := Af ++ A) hf (Weaker.refl _)
    ((Agree.trans (hag) (hm.keeps hwf hXSa hXSd))) halloc hnd hdX hK
    (fun a ha => List.mem_append.mpr (.inl ha)) (fun a ha => .inl (List.mem_append.mpr (.inr ha)))
  refine ⟨op, Xf ++ X, hos, Af ++ A, Lw, hc' hc, hop, hcov, fun a ha => ?_, hK', hls, hvs, hn, ?_,
    fun l hl h => (hm.apart hwf hSa (fun l hl h => hSd l hl (List.mem_append.mpr (.inr h)))).2 l h hl, ?_⟩
  · rcases List.mem_append.mp ha with h | h
    · exact hAf a h
    · exact hA a (haim a h)
  · intro l hl h
    simp only [List.mem_append] at h
    rcases h with (h | h) | h
    · exact hdL l h hl
    · exact hdw l hl (by simp [h])
    · exact hdw l hl (by simp [h])
  · exact (hm.widen hXa hd).relabel fun x => by simp only [List.mem_append, List.append_assoc]

/-! ## The code around two tasks, one of which failed -/

/-- Once the task left is dropped, the activation is the code around's again. -/
theorem ret_parE (hI : Inv F ι σf Γ₁ env E₁ S) (hro : RoCtx Γo) (hSo : ∀ l ∈ So, l ∈ E₁ ∨ l ∈ S)
    (hR : Ready O hs r) (hwf : WF σ0) (hag : Agree σf σ0 (E₁ ++ S)) (halloc : ∀ l ∈ E₁, σf.mem l ≠ none)
    (hnd : E₁.Nodup) (hd : Disj E₁ Ein) (hSa : ∀ l ∈ S, σ0.mem l ≠ none) (hSd : Disj S (E₁ ++ Ein))
    (hp : Post F ι O σ0 Ein So Γo envo τ r hs res) :
    Post F ι O σ0 (E₁ ++ Ein) S Γ₁ env τ r hs (ret F O n hs .parE res) := by
  have hXa : ∀ l ∈ E₁, σ0.mem l ≠ none := fun l hl => by
    rw [hag l (List.mem_append.mpr (.inl hl))]; exact halloc l hl
  have hXSa : ∀ l ∈ E₁ ++ S, σ0.mem l ≠ none := fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · exact hXa l h
    · exact hSa l h
  have hXSd : Disj (E₁ ++ S) Ein := fun l hl h => by
    rcases List.mem_append.mp hl with hl | hl
    · exact hd l hl h
    · exact hSd l hl (List.mem_append.mpr (.inr h))
  have hSE : Disj S Ein := fun l hl h => hSd l hl (List.mem_append.mpr (.inr h))
  -- What is left of the dropped task owns nothing; the code around is as it was.
  have back : ∀ {σ1 Eb L}, Inv F ι σ1 Γo envo Eb So → Moves σ0 Ein σ1 Eb L →
      Eb = [] ∧ Inv F ι σ1 Γ₁ env E₁ S ∧ Moves σ0 (E₁ ++ Ein) σ1 E₁ L := by
    intro σ1 Eb L hIb hm
    obtain rfl := foot_ro hIb.foot hro
    have hag1 : Agree σf σ1 (E₁ ++ S) := (Agree.trans (hag) (hm.keeps hwf hXSa hXSd))
    exact ⟨rfl, ⟨hI.foot.frame hag1, hI.nodup, hI.disj, hI.keys, hag1.cur.trans hI.cur⟩,
      (hm.widen hXa hd).relabel fun x => by simp⟩
  rcases res with ⟨res, σ1⟩
  cases res with
  | val v =>
    obtain ⟨Eb, L, hIb, hv, -, -, hm⟩ := hp
    obtain ⟨rfl, hI1, hm1⟩ := back hIb hm
    simp only [ret]
    obtain ⟨hdE, hdL⟩ := hm.apart hwf hXa hd
    exact ⟨E₁, L, hI1, hv, fun l h1 h2 => hdL l h2 h1, fun l h1 h2 => (hm.apart hwf hSa hSE).2 l h2 h1, hm1⟩
  | abort j k =>
    obtain ⟨haim, Eb, hIb, hm⟩ := hp
    obtain ⟨rfl, hI1, hm1⟩ := back hIb hm
    simp only [ret]
    exact ⟨haim, E₁, hI1, hm1⟩
  | susp j ef vs ls K =>
    simp only [ret]
    exact post_susp (.parE hI hro hSo) hR.2 (fun _ h => h) (fun _ h => by simp at h) id hwf hag halloc hnd hd hSa
      hSd hp
  | stuck => simp [Post] at hp
  | timeout => simp [ret, Post]
  | panic => simp [ret, Post]

/-! ## Two values made a pair -/

/-- Two values, each put in a fresh cell, make a pair owning both. -/
theorem pair_alloc (hI : Inv F ι σ Γ env E S) (hwf : WF σ) (hv : VT F ι σ A v Lv) (hw : VT F ι σ B w Lw)
    (hLn : (Lv ++ Lw).Nodup) (hdL : Disj (Lv ++ Lw) E) (hdLS : Disj (Lv ++ Lw) S) :
    ∃ L, Inv F ι ((σ.alloc v).2.alloc w).2 Γ env E S ∧
      VT F ι ((σ.alloc v).2.alloc w).2 (.pair A B) (.pair (σ.alloc v).1 ((σ.alloc v).2.alloc w).1) L ∧
      Disj L E ∧ Disj L S ∧ Moves σ (Lv ++ Lw ++ E) ((σ.alloc v).2.alloc w).2 E L := by
  let σ3 := (σ.alloc v).2
  let σ4 := (σ3.alloc w).2
  have hn3 : σ3.next = σ.next + 1 := rfl
  have hold3 : ∀ z, σ.mem z ≠ none → σ3.mem z = σ.mem z := fun z hz => by
    simp only [σ3, Store.alloc]; rw [if_neg (fun e => Nat.lt_irrefl _ (e ▸ hwf z hz))]
  have hold4 : ∀ z, σ.mem z ≠ none → σ4.mem z = σ.mem z := fun z hz => by
    simp only [σ4, Store.alloc]
    rw [if_neg (fun e => by have := hwf z hz; simp [σ3, Store.alloc] at e; omega)]
    exact hold3 z hz
  have hb4 : σ4.mem σ.next = some v := by
    simp only [σ4, σ3, Store.alloc]; simp
  have hc4 : σ4.mem (σ.next + 1) = some w := by
    simp only [σ4, σ3, Store.alloc]; simp
  have hfresh : ∀ z, σ.mem z ≠ none → z ≠ σ.next ∧ z ≠ σ.next + 1 := fun z hz =>
    ⟨fun e => Nat.lt_irrefl _ (e ▸ hwf z hz), fun e => by have := hwf z hz; omega⟩
  have hLva := hv.alloc
  have hLwa := hw.alloc
  have hLv1 : LT F ι σ4 σ.next A (σ.next :: Lv) :=
    LT.of_contents hb4 (hv.frame <| Agree.of' fun z hz => hold4 z (hLva z hz)) (fun h => (hfresh _ (hLva _ h)).1 rfl)
      (by simp only [σ4, σ3, Store.alloc]; simp; exact hI.cur)
  have hLw1 : LT F ι σ4 (σ.next + 1) B ((σ.next + 1) :: Lw) :=
    LT.of_contents hc4 (hw.frame <| Agree.of' fun z hz => hold4 z (hLwa z hz)) (fun h => (hfresh _ (hLwa _ h)).2 rfl)
      (by simp only [σ4, σ3, Store.alloc]; simp; exact hI.cur)
  obtain ⟨hnv, hnw, hdvw⟩ := nodup_append_disj.mp hLn
  have hdisj : ∀ x ∈ σ.next :: Lv, x ∉ (σ.next + 1) :: Lw := by
    intro x hx hx'
    rcases List.mem_cons.mp hx with rfl | hx <;> rcases List.mem_cons.mp hx' with e | hx'
    · omega
    · exact (hfresh _ (hLwa _ hx')).1 rfl
    · exact (hfresh _ (hLva _ hx)).2 e
    · exact hdvw x hx hx'
  refine ⟨(σ.next :: Lv) ++ ((σ.next + 1) :: Lw),
    ⟨hI.foot.frame <| Agree.of' fun z hz => hold4 z (hI.foot.alloc z (List.mem_append.mp hz)), hI.nodup, hI.disj, hI.keys, hI.cur⟩,
    .pair hLv1 hLw1 hdisj hv.complete hw.complete, ?_, ?_, ?_⟩
  · intro x hx hx'
    have hxa := hI.alloc x hx'
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with (rfl | hx) | (rfl | hx)
    · exact (hfresh _ hxa).1 rfl
    · exact hdL x (List.mem_append.mpr (.inl hx)) hx'
    · exact (hfresh _ hxa).2 rfl
    · exact hdL x (List.mem_append.mpr (.inr hx)) hx'
  · intro x hx hx'
    have hxa := hI.allocS x hx'
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with (rfl | hx) | (rfl | hx)
    · exact (hfresh _ hxa).1 rfl
    · exact hdLS x (List.mem_append.mpr (.inl hx)) hx'
    · exact (hfresh _ hxa).2 rfl
    · exact hdLS x (List.mem_append.mpr (.inr hx)) hx'
  · have hLE : ∀ l ∈ Lv ++ Lw ++ E, σ.mem l ≠ none := fun l hl => by
      simp only [List.mem_append] at hl
      rcases hl with (h | h) | h
      · exact hLva l h
      · exact hLwa l h
      · exact hI.alloc l h
    have m3 := Moves.allocate (v := v) hwf hLE
    have m4 := m3.trans (Moves.allocate (σ := σ3) (v := w) m3.wf (fun z hz => by
        rw [hold3 z (hLE z hz)]; exact hLE z hz))
      (fun x hx hx' => by
        simp only [List.mem_singleton] at hx; subst hx; exact (hfresh _ (hLE _ hx')).1 rfl) hwf
    exact (m4.relabel (E'' := E) (L'' := (σ.next :: Lv) ++ ((σ.next + 1) :: Lw)) fun x => by
      simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
        show (σ.alloc v).1 = σ.next from rfl, show (σ3.alloc w).1 = σ3.next from rfl, hn3]
      grind)

/-! ## Two tasks, one of them done -/

theorem aimed_uncap : AimedIn a (.capture e hid :: hs) → AimedIn a hs := fun ⟨l, hl⟩ =>
  ⟨l, (List.mem_cons.mp hl).resolve_left (by simp)⟩

/-- Two tasks, the one running `side`, the other done with `w`: the running one gives way to no one,
and once it is done too the pair of what they gave is the value; if it fails, `w` is dropped. -/
theorem ret_parD (hKo : ∀ m, n = m + 1 → EvalKOk F O m ∧ RetOk F O m)
    (hP : ParOk F ι O σf e op Γ₁ env E₁ S τa τb) (hro : RoCtx Γr) (hSr : ∀ l ∈ Sr, l ∈ E₁ ∨ l ∈ S)
    (hw : VT F ι σf (if side then τb else τa) w Lw)
    (hR : Ready O hs r) (hwf : WF σ0) (hag : Agree σf σ0 (E₁ ++ Lw ++ S)) (halloc : ∀ l ∈ E₁ ++ Lw, σf.mem l ≠ none)
    (hnd : (E₁ ++ Lw).Nodup) (hd : Disj (E₁ ++ Lw) Ein) (hSa : ∀ l ∈ S, σ0.mem l ≠ none)
    (hSd : Disj S (E₁ ++ Lw ++ Ein))
    (hp : Post F ι O σ0 Ein Sr Γr envr (if side then τa else τb) (.eff e :: r) (.capture e hid :: hs) res) :
    Post F ι O σ0 (E₁ ++ Lw ++ Ein) S Γ₁ env (.pair τa τb) r hs (ret F O n hs (.parD e hid τa τb side w) res) := by
  have hXa : ∀ l ∈ E₁ ++ Lw, σ0.mem l ≠ none := fun l hl => by
    rw [hag l (List.mem_append.mpr (.inl hl))]; exact halloc l hl
  have hXSa : ∀ l ∈ E₁ ++ Lw ++ S, σ0.mem l ≠ none := fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · exact hXa l h
    · exact hSa l h
  have hXSd : Disj (E₁ ++ Lw ++ S) Ein := fun l hl h => by
    rcases List.mem_append.mp hl with hl | hl
    · exact hd l hl h
    · exact hSd l hl (List.mem_append.mpr (.inr h))
  have hSE : Disj S Ein := fun l hl h => hSd l hl (List.mem_append.mpr (.inr h))
  have agreeM : ∀ {E' L σ1}, Moves σ0 Ein σ1 E' L → Agree σf σ1 (E₁ ++ Lw ++ S) := fun hm => Agree.trans hag (hm.keeps hwf hXSa hXSd)
  have hE1L := nodup_append_disj.mp hnd
  have callerI : ∀ {σ1}, Agree σf σ1 (E₁ ++ S) → Inv F ι σ1 Γ₁ env E₁ S := fun hag1 =>
    ⟨hP.hI.foot.frame hag1, hP.hI.nodup, hP.hI.disj, hP.hI.keys, hag1.cur.trans hP.hI.cur⟩
  have restrict : ∀ {σ1}, Agree σf σ1 (E₁ ++ Lw ++ S) → Agree σf σ1 (E₁ ++ S) := fun hag1 =>
    hag1.mono fun l hl => by simp only [List.mem_append] at hl ⊢; grind
  rcases res with ⟨res, σ1⟩
  cases res with
  | val v =>
    obtain ⟨Eb, L, hIb, hv, -, -, hm⟩ := hp
    obtain rfl := foot_ro hIb.foot hro
    have hwf1 := hm.wf
    have hag1 := agreeM hm
    have hI1 := callerI (restrict hag1)
    have hw1 := hw.frame (hag1.mono fun l hl => by simp [hl])
    obtain ⟨hdXL, -⟩ := (hm.apart hwf hXa hd)
    have hdXL' : Disj (E₁ ++ Lw) L := (hm.apart hwf hXa hd).2
    have hdSL : Disj S L := (hm.apart hwf hSa hSE).2
    have m1 := hm.widen hXa hd
    simp only [ret]
    cases side with
    | true =>
      simp only [↓reduceIte] at hv hw1 ⊢
      obtain ⟨Lp, hI4, hvp, hdp, hdpS, mp⟩ := pair_alloc hI1 hwf1 hv hw1
        (nodup_append_disj.mpr ⟨hv.nodup, hE1L.2.1, fun l h1 h2 => hdXL' l (by simp [h2]) h1⟩)
        (fun l h1 h2 => by
          rcases List.mem_append.mp h1 with h1 | h1
          · exact hdXL' l (by simp [h2]) h1
          · exact hE1L.2.2 l h2 h1)
        (fun l h1 h2 => by
          rcases List.mem_append.mp h1 with h1 | h1
          · exact hdSL l h2 h1
          · exact hSd l h2 (by simp [h1]))
      refine ⟨E₁, Lp, hI4, hvp, hdp, hdpS, ?_⟩
      exact ((m1.relabel (E'' := L ++ Lw ++ E₁) (L'' := []) fun x => by simp only [List.mem_append, List.append_nil, List.not_mem_nil, or_false]; grind).trans
        mp disj_nil_left hwf).relabel fun x => by simp
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hv hw1 ⊢
      obtain ⟨Lp, hI4, hvp, hdp, hdpS, mp⟩ := pair_alloc hI1 hwf1 hw1 hv
        (nodup_append_disj.mpr ⟨hE1L.2.1, hv.nodup, fun l h1 h2 => hdXL' l (by simp [h1]) h2⟩)
        (fun l h1 h2 => by
          rcases List.mem_append.mp h1 with h1 | h1
          · exact hE1L.2.2 l h2 h1
          · exact hdXL' l (by simp [h2]) h1)
        (fun l h1 h2 => by
          rcases List.mem_append.mp h1 with h1 | h1
          · exact hSd l h2 (by simp [h1])
          · exact hdSL l h2 h1)
      refine ⟨E₁, Lp, hI4, hvp, hdp, hdpS, ?_⟩
      exact ((m1.relabel (E'' := Lw ++ L ++ E₁) (L'' := []) fun x => by simp only [List.mem_append, List.append_nil, List.not_mem_nil, or_false]; grind).trans
        mp disj_nil_left hwf).relabel fun x => by simp
  | abort j k =>
    obtain ⟨haim, Eb, hIb, hm⟩ := hp
    obtain rfl := foot_ro hIb.foot hro
    have hag1 := agreeM hm
    have hw1 := hw.frame (hag1.mono fun l hl => by simp [hl])
    obtain ⟨σ3, hdrop, hn, hfree, hkeep⟩ := drop_ok hm.wf _ w Lw hw1
    simp only [ret, hdrop]
    have hI3 : Inv F ι σ3 Γ₁ env E₁ S := callerI <| Agree.trans (restrict hag1) <| Agree.of' fun l hl =>
      hkeep l fun h => by
        rcases List.mem_append.mp hl with hl | hl
        · exact hE1L.2.2 l hl h
        · exact hSd l hl (by simp [h])
    refine ⟨aimed_uncap haim, E₁, hI3, ?_⟩
    have m1 := (hm.widen hXa hd).relabel (E'' := E₁ ++ Lw) (L'' := []) fun x => by simp
    exact (m1.trans (Moves.free (E := E₁ ++ Lw) (E' := E₁) (D := Lw) (WF.of_free hm.wf hn hfree hkeep) hn
      (fun l hl => (m1.alloc l).mpr (.inr (.inl hl))) (fun x => by simp) hfree hkeep hE1L.2.2)
      disj_nil_left hwf).relabel fun x => by simp
  | susp j ef vs ls K =>
    by_cases hc : j ≠ hid ∨ ef ≠ e
    · have : ret F O n hs (.parD e hid τa τb side w) (.susp j ef vs ls K, σ1) =
          (.susp j ef vs ls (.parD e hid τa τb side w :: K), σ1) := by
        rw [ret.eq_def]; simp [hc]
      rw [this]
      exact post_susp (.parD hP hro hSr hw) hR.2 (fun _ h => aimed_uncap h) (fun _ h => by simp at h) (fun h => by
        rcases List.mem_cons.mp h with h | h
        · simp only [Frame.capture.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp at hc
        · exact h) hwf hag halloc hnd hd hSa hSd hp
    simp only [ne_eq, not_or, Decidable.not_not] at hc
    obtain ⟨h1, h2⟩ := hc
    subst j ef
    obtain ⟨op', X, hos, A, Lv, -, hop', -, haim, hK, hls, hvs, hLn, hdLX, hdLS, hm⟩ := hp
    obtain rfl : op = op' := Option.some.inj (hP.hop.symm.trans hop')
    rw [hP.howns] at hvs
    cases hvs
    cases n with
    | zero => rw [ret.eq_def]; simp [Post]
    | succ m =>
    obtain ⟨hKk, hRr⟩ := hKo m rfl
    have : ret F O (m + 1) hs (.parD e hid τa τb side w) (.susp hid e [] ls K, σ1) =
        ret F O m hs (.parD e hid τa τb side w) (evalK F O m (.capture e hid :: hs) σ1 K (.val (.int 0))) := by
      rw [ret.eq_def]; simp
    rw [this]
    obtain ⟨-, -, -, -, -, -, -, -, hts, -, -, hXn, -⟩ := hK.base_of
    rw [hP.hrefs] at hts
    obtain rfl : hos = [] := List.map_eq_nil_iff.mp hts
    simp only [olds, mutCells, List.map_nil, List.flatMap_nil, List.append_nil, List.flatten_nil] at hm
    have hwf1 := hm.wf
    have hag1 := agreeM hm
    have hfa : ∀ l ∈ E₁ ++ S, σf.mem l ≠ none := fun l hl => by
      rcases List.mem_append.mp hl with h | h
      · exact halloc l (by simp [h])
      · rw [← hag l (by simp [h])]; exact hSa l h
    have hSr1 : ∀ l ∈ Sr, σ1.mem l ≠ none := fun l hl => by
      rw [restrict hag1 l (by rcases hSr l hl with h | h <;> simp [h])]
      exact hfa l (by rcases hSr l hl with h | h <;> simp [h])
    have hS1 : ∀ l ∈ S, σ1.mem l ≠ none := fun l hl => by
      rw [restrict hag1 l (by simp [hl])]; exact hfa l (by simp [hl])
    have hdX := (hm.apart hwf hXSa hXSd).1
    have hR' : Ready O (.capture e hid :: hs) (.eff e :: r) :=
      (FrameOk.parD (ι := ι) (σf := σf) (Γr := Γr) (envr := envr) (Sr := Sr) (hid := hid) hP hro hSr hw).ready hR
    have hres := yield_resume (top := ⟨Γr, envr, (if side then τa else τb), Sr, .eff e :: r⟩) hKk hP.hop hP.hrefs
      hP.hret hK hR' haim hwf1 Agree.self
      (fun l hl => by
        rcases List.mem_append.mp hl with h | h
        · exact (hm.alloc l).mpr (.inr (.inl h))
        · exact hSr1 l h) hXn
      (fun l h1 h2 => hdX l (by rcases hSr l h1 with h | h <;> simp [h]) h2)
    have h2 := hRr hs _ _ σf (.parD e hid τa τb side w) ⟨Γr, envr, _, Sr, .eff e :: r⟩ ⟨Γ₁, env, .pair τa τb, S, r⟩
      (E₁ ++ Lw) [] σ1 X _ (.parD hP hro hSr hw) hR (fun _ h => by simp at h) hwf1 hag1 halloc hnd
      (fun l h1 h2 => hdX l (by simp only [List.mem_append] at h1 ⊢; grind) h2) hS1
      (fun l h1 h2 => by
        rcases List.mem_append.mp h2 with h2 | h2
        · exact hSd l h1 (by simp only [List.mem_append] at h2 ⊢; grind)
        · exact hdX l (by simp [h1]) h2) hres
    exact post_after ((hm.widen hXa hd).relabel fun x => by simp) hwf h2
  | stuck => simp [Post] at hp
  | timeout => simp [ret, Post]
  | panic => simp [ret, Post]

/-! ## Two tasks, both running -/

theorem ParOk.transfer (h : ParOk F ι O σf e op Γ₁ env E₁ S τa τb) (hag : Agree σf σ' (E₁ ++ S)) :
    ParOk F ι O σ' e op Γ₁ env E₁ S τa τb :=
  { h with hI := ⟨h.hI.foot.frame hag, h.hI.nodup, h.hI.disj, h.hI.keys, hag.cur.trans h.hI.cur⟩ }

/-- Two tasks, the one running `side`, the other waiting as `Ko`: where the running one gives way,
the schedule says which goes on; once it is done, the other runs alone; if it fails, the other is
dropped, unwinding to a barrier, before the failure goes on. -/
theorem ret_parS (hKo : ∀ m, n = m + 1 → EvalKOk F O m ∧ RetOk F O m)
    (hP : ParOk F ι O σf e op Γ₁ env E₁ S τa τb) (hroR : RoCtx Γr) (hroO : RoCtx Γo)
    (hSr : ∀ l ∈ Sr, l ∈ E₁ ∨ l ∈ S) (hSo : ∀ l ∈ So, l ∈ E₁ ∨ l ∈ S)
    (hK : FramesOk F O ι σf Ko op ⟨Γo, envo, (if side then τb else τa), So, .eff e :: r⟩ X [] AK)
    (hR : Ready O hs r) (hA : ∀ a ∈ AK, AimedIn a hs) (hwf : WF σ0) (hag : Agree σf σ0 (E₁ ++ X ++ S))
    (halloc : ∀ l ∈ E₁ ++ X, σf.mem l ≠ none) (hnd : (E₁ ++ X).Nodup) (hd : Disj (E₁ ++ X) Ein)
    (hSa : ∀ l ∈ S, σ0.mem l ≠ none) (hSd : Disj S (E₁ ++ X ++ Ein))
    (hp : Post F ι O σ0 Ein Sr Γr envr (if side then τa else τb) (.eff e :: r) (.capture e hid :: hs) res) :
    Post F ι O σ0 (E₁ ++ X ++ Ein) S Γ₁ env (.pair τa τb) r hs (ret F O n hs (.parS e hid τa τb side Ko) res) := by
  have hXa : ∀ l ∈ E₁ ++ X, σ0.mem l ≠ none := fun l hl => by
    rw [hag l (List.mem_append.mpr (.inl hl))]; exact halloc l hl
  have hXSa : ∀ l ∈ E₁ ++ X ++ S, σ0.mem l ≠ none := fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · exact hXa l h
    · exact hSa l h
  have hXSd : Disj (E₁ ++ X ++ S) Ein := fun l hl h => by
    rcases List.mem_append.mp hl with hl | hl
    · exact hd l hl h
    · exact hSd l hl (List.mem_append.mpr (.inr h))
  have agreeM : ∀ {E' L σ1}, Moves σ0 Ein σ1 E' L → Agree σf σ1 (E₁ ++ X ++ S) := fun hm => Agree.trans hag (hm.keeps hwf hXSa hXSd)
  have restrict : ∀ {σ1}, Agree σf σ1 (E₁ ++ X ++ S) → Agree σf σ1 (E₁ ++ S) := fun hag1 =>
    hag1.mono fun l hl => by simp only [List.mem_append] at hl ⊢; grind
  have hE1X := nodup_append_disj.mp hnd
  have hSE : Disj S Ein := fun l hl h => hSd l hl (List.mem_append.mpr (.inr h))
  have hfa : ∀ l ∈ E₁ ++ S, σf.mem l ≠ none := fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · exact halloc l (by simp [h])
    · rw [← hag l (by simp [h])]; exact hSa l h
  have inES : ∀ {T : List Nat}, (∀ l ∈ T, l ∈ E₁ ∨ l ∈ S) → ∀ l ∈ T, l ∈ E₁ ++ S := fun hT l hl => by
    rcases hT l hl with h | h <;> simp [h]
  -- The task waiting, resumed where it gave way.
  have resumeO : ∀ {σr} m, EvalKOk F O m → WF σr → Agree σf σr (E₁ ++ X ++ S) →
      Post F ι O σr X So Γo envo (if side then τb else τa) (.eff e :: r) (.capture e hid :: hs)
        (evalK F O m (.capture e hid :: hs) σr Ko (.val (.int 0))) := by
    intro σr m hKk hwfr hagr
    have hR' : Ready O (.capture e hid :: hs) (.eff e :: r) :=
      (FrameOk.parY (F := F) (ι := ι) (σf := σf) (Γ := Γo) (env := envo) (τ := τa) (S := So) (hid := hid) hP.hop hP.howns
        hP.hrefs hP.hret).ready hR
    exact yield_resume (top := ⟨Γo, envo, _, So, .eff e :: r⟩) hKk hP.hop hP.hrefs hP.hret hK hR'
      (fun a ha => let ⟨l, hl⟩ := hA a ha; ⟨l, List.mem_cons_of_mem _ hl⟩) hwfr
      ((hagr.mono fun l hl => by
        rcases List.mem_append.mp hl with h | h
        · simp [h]
        · rcases hSo l h with h | h <;> simp [h]))
      (fun l hl => by
        rcases List.mem_append.mp hl with h | h
        · exact halloc l (by simp [h])
        · exact hfa l (inES hSo l h)) hE1X.2.1
      (fun l h1 h2 => by
        rcases hSo l h1 with h | h
        · exact hE1X.2.2 l h h2
        · exact hSd l h (by simp [h2]))
  rcases res with ⟨res, σ1⟩
  cases res with
  | val v =>
    obtain ⟨Eb, L, hIb, hv, -, -, hm⟩ := hp
    obtain rfl := foot_ro hIb.foot hroR
    cases n with
    | zero => rw [ret.eq_def]; simp [Post]
    | succ m =>
    obtain ⟨hKk, hRr⟩ := hKo m rfl
    have : ret F O (m + 1) hs (.parS e hid τa τb side Ko) (.val v, σ1) =
        ret F O m hs (.parD e hid τa τb (!side) v) (evalK F O m (.capture e hid :: hs) σ1 Ko (.val (.int 0))) := by
      rw [ret.eq_def]
    rw [this]
    have hwf1 := hm.wf
    have hag1 := agreeM hm
    have hres := resumeO m hKk hwf1 hag1
    have hdXL : Disj (E₁ ++ X) L := (hm.apart hwf hXa hd).2
    have hdSL : Disj S L := (hm.apart hwf hSa hSE).2
    have hP1 := hP.transfer (restrict hag1)
    have hv' : VT F ι σ1 (if (!side) = true then τb else τa) v L := by cases side <;> simpa using hv
    have hres' : Post F ι O σ1 X So Γo envo (if (!side) = true then τa else τb) (.eff e :: r) (.capture e hid :: hs)
        (evalK F O m (.capture e hid :: hs) σ1 Ko (.val (.int 0))) := by cases side <;> simpa using hres
    have hE1a : ∀ l ∈ E₁, σ1.mem l ≠ none := fun l hl => by
      rw [restrict hag1 l (by simp [hl])]; exact hfa l (by simp [hl])
    have hS1 : ∀ l ∈ S, σ1.mem l ≠ none := fun l hl => by
      rw [restrict hag1 l (by simp [hl])]; exact hfa l (by simp [hl])
    have h2 := hRr hs _ _ σ1 (.parD e hid τa τb (!side) v) ⟨Γo, envo, _, So, .eff e :: r⟩ ⟨Γ₁, env, .pair τa τb, S, r⟩
      (E₁ ++ L) [] σ1 X _ (.parD hP1 hroO hSo hv') hR (fun _ h => by simp at h) hwf1 Agree.self
      (fun l hl => by
        rcases List.mem_append.mp hl with h | h
        · exact hE1a l h
        · exact hv.alloc l h)
      (nodup_append_disj.mpr ⟨hE1X.1, hv.nodup, fun l h1 h2 => hdXL l (by simp [h1]) h2⟩)
      (fun l h1 h2 => by
        rcases List.mem_append.mp h1 with h1 | h1
        · exact hE1X.2.2 l h1 h2
        · exact hdXL l (by simp [h2]) h1)
      hS1
      (fun l h1 h2 => by
        simp only [List.mem_append] at h2
        rcases h2 with (h2 | h2) | h2
        · exact hSd l h1 (by simp [h2])
        · exact hdSL l h1 h2
        · exact hSd l h1 (by simp [h2])) hres'
    exact post_after ((hm.widen hXa hd).relabel fun x => by simp only [List.mem_append, List.append_nil]; grind) hwf h2
  | abort j k =>
    obtain ⟨haim, Eb, hIb, hm⟩ := hp
    obtain rfl := foot_ro hIb.foot hroR
    cases n with
    | zero => rw [ret.eq_def]; simp [Post]
    | succ m =>
    obtain ⟨hKk, hRr⟩ := hKo m rfl
    have : ret F O (m + 1) hs (.parS e hid τa τb side Ko) (.abort j k, σ1) =
        ret F O m hs .parE (dropRet (if side then τb else τa) (.abort j k) σ1.fresh.1
          (ret F O m (.abort .drop σ1.fresh.1 :: hs) (.parY e hid)
            (evalK F O m (.capture e hid :: .abort .drop σ1.fresh.1 :: hs) σ1.fresh.2 Ko (.abort σ1.fresh.1 0)))) := by
      rw [ret.eq_def]
    rw [this]
    generalize hdd : σ1.fresh.1 = d
    have hwf1 := hm.wf
    have hag1 := agreeM hm
    have hwf2 : WF σ1.fresh.2 := hwf1
    have hag2 : Agree σf σ1.fresh.2 (E₁ ++ X ++ S) := hag1.trans (Agree.of' fun _ _ => rfl)
    have hR2 : Ready O (.abort .drop d :: hs) r := ⟨.abort (by intro e h; cases h) hR.1, fun l hl => covers_cons _ hR.2 l hl⟩
    have hR3 : Ready O (.capture e hid :: .abort .drop d :: hs) (.eff e :: r) :=
      (FrameOk.parY (F := F) (ι := ι) (σf := σf) (Γ := Γo) (env := envo) (τ := τa) (S := So) (hid := hid) hP.hop hP.howns
        hP.hrefs hP.hret).ready hR2
    have hSo2 : ∀ l ∈ So, σ1.fresh.2.mem l ≠ none := fun l hl => by
      show σ1.mem l ≠ none
      rw [restrict hag1 l (inES hSo l hl)]; exact hfa l (inES hSo l hl)
    have hdSoX : Disj So X := fun l h1 h2 => by
      rcases hSo l h1 with h | h
      · exact hE1X.2.2 l h h2
      · exact hSd l h (by simp [h2])
    have h1 := hKk (.capture e hid :: .abort .drop d :: hs) _ σf Ko _ X [] AK σ1.fresh.2 [] (.abort d 0) op [] hK hR3
      (fun a ha => let ⟨l, hl⟩ := hA a ha; ⟨l, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hl)⟩) hwf2
      ((hag2.mono fun l hl => by
        rcases List.mem_append.mp hl with h | h
        · simp [h]
        · rcases hSo l h with h | h <;> simp [h]))
      (fun l hl => by
        rcases List.mem_append.mp hl with h | h
        · exact halloc l (by simp [h])
        · exact hfa l (inES hSo l h)) hE1X.2.1 rfl (fun _ h => by simp at h) (by simp [mutCells])
      (by simp [mutCells, Disj]) (by simpa [mutCells] using hdSoX)
      (.inr ⟨d, 0, rfl, ⟨.drop, List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩, rfl⟩)
    simp only [mutCells, List.flatMap_nil, List.append_nil] at h1
    have h2 := hRr (.abort .drop d :: hs) _ _ σ1.fresh.2 (.parY e hid) ⟨Γo, envo, _, So, .eff e :: r⟩ ⟨Γo, envo, _, So, r⟩
      [] [] σ1.fresh.2 X _ (.parY hP.hop hP.howns hP.hrefs hP.hret) hR2 (fun _ h => by simp at h) hwf2 Agree.self
      (fun _ h => by simp at h) List.nodup_nil disj_nil_left hSo2 (by simpa using hdSoX) h1
    simp only [List.nil_append] at h2
    rw [dropRet_eq (F := F) (O := O) (n := m) (hs := hs)]
    have h3 := ret_dropK (τ' := .pair τa τb) (n := m) (k := k) (aimed_uncap haim) hR.2 hwf2 h2
    have hI2 : Inv F ι σ1.fresh.2 Γ₁ env E₁ S := ⟨hP.hI.foot.frame (restrict hag2), hP.hI.nodup, hP.hI.disj, hP.hI.keys, by cur_inv⟩
    have hE1a : ∀ l ∈ E₁, σ1.fresh.2.mem l ≠ none := fun l hl => by
      show σ1.mem l ≠ none
      rw [restrict hag1 l (by simp [hl])]; exact hfa l (by simp [hl])
    have hS2 : ∀ l ∈ S, σ1.fresh.2.mem l ≠ none := fun l hl => by
      show σ1.mem l ≠ none
      rw [restrict hag1 l (by simp [hl])]; exact hfa l (by simp [hl])
    have h4 := ret_parE (n := m) hI2 hroO hSo hR hwf2 Agree.self hE1a hE1X.1 hE1X.2.2 hS2
      (fun l h1 h2 => by
        rcases List.mem_append.mp h2 with h2 | h2
        · exact hSd l h1 (by simp [h2])
        · exact hSd l h1 (by simp [h2])) h3
    exact post_after (((hm.widen hXa hd).relabel (E'' := E₁ ++ X) (L'' := []) fun x => by simp).trans
      (Moves.freshen hwf1 fun l hl => by
        rcases List.mem_append.mp hl with h | h
        · rw [restrict hag1 l (by simp [h])]; exact hfa l (by simp [h])
        · rw [hag1 l (by simp [h])]; exact halloc l (by simp [h])) disj_nil_left hwf |>.relabel
      fun x => by simp) hwf h4
  | susp j ef vs ls K =>
    by_cases hc : j ≠ hid ∨ ef ≠ e
    · have : ret F O n hs (.parS e hid τa τb side Ko) (.susp j ef vs ls K, σ1) =
          (.susp j ef vs ls (.parS e hid τa τb side Ko :: K), σ1) := by
        rw [ret.eq_def]; simp [hc]
      rw [this]
      exact post_susp (.parS hP hroR hroO hSr hSo hK) hR.2 (fun _ h => aimed_uncap h) hA (fun h => by
        rcases List.mem_cons.mp h with h | h
        · simp only [Frame.capture.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp at hc
        · exact h) hwf hag halloc hnd hd hSa hSd hp
    simp only [ne_eq, not_or, Decidable.not_not] at hc
    obtain ⟨h1, h2⟩ := hc
    subst j ef
    obtain ⟨op', X', hos, A', Lv, -, hop', -, haim, hK', hls, hvs, hLn, hdLX, hdLS, hm⟩ := hp
    obtain rfl : op = op' := Option.some.inj (hP.hop.symm.trans hop')
    rw [hP.howns] at hvs
    cases hvs
    cases n with
    | zero => rw [ret.eq_def]; simp [Post]
    | succ m =>
    obtain ⟨hKk, hRr⟩ := hKo m rfl
    obtain ⟨-, -, -, -, -, -, -, -, hts, -, -, hXn', -⟩ := hK'.base_of
    rw [hP.hrefs] at hts
    obtain rfl : hos = [] := List.map_eq_nil_iff.mp hts
    simp only [olds, mutCells, List.map_nil, List.flatMap_nil, List.append_nil, List.flatten_nil] at hm
    have hwf1 := hm.wf
    have hag1 := agreeM hm
    have hwf2 : WF σ1.fresh.2 := hwf1
    have hag2 : Agree σf σ1.fresh.2 (E₁ ++ X ++ S) := hag1.trans (Agree.of' fun _ _ => rfl)
    have hdX' := (hm.apart hwf hXSa hXSd).1
    have hE1a : ∀ l ∈ E₁, σ1.mem l ≠ none := fun l hl => by
      rw [restrict hag1 l (by simp [hl])]; exact hfa l (by simp [hl])
    have hS1 : ∀ l ∈ S, σ1.mem l ≠ none := fun l hl => by
      rw [restrict hag1 l (by simp [hl])]; exact hfa l (by simp [hl])
    have hSr1 : ∀ l ∈ Sr, σ1.mem l ≠ none := fun l hl => by
      rcases hSr l hl with h | h
      · exact hE1a l h
      · exact hS1 l h
    have hX'a : ∀ l ∈ X', σ1.mem l ≠ none := fun l hl => (hm.alloc l).mpr (.inr (.inl hl))
    have hdSrX' : Disj Sr X' := fun l h1 h2 => hdX' l (by rcases hSr l h1 with h | h <;> simp [h]) h2
    have hR' : Ready O (.capture e hid :: hs) (.eff e :: r) :=
      (FrameOk.parY (F := F) (ι := ι) (σf := σf) (Γ := Γo) (env := envo) (τ := τa) (S := So) (hid := hid) hP.hop hP.howns
        hP.hrefs hP.hret).ready hR
    have hm2 : Moves σ0 (E₁ ++ X ++ Ein) σ1.fresh.2 (E₁ ++ X ++ X') [] :=
      ((hm.widen hXa hd).relabel (E'' := E₁ ++ X ++ X') (L'' := []) fun x => by simp).trans
        (Moves.freshen hwf1 fun l hl => by
          simp only [List.mem_append] at hl
          rcases hl with (h | h) | h
          · exact hE1a l h
          · rw [hag1 l (by simp [h])]; exact halloc l (by simp [h])
          · exact hX'a l h) disj_nil_left hwf |>.relabel fun x => by simp
    have : ret F O (m + 1) hs (.parS e hid τa τb side Ko) (.susp hid e [] ls K, σ1) =
        if σ1.sched σ1.ids = true then
          ret F O m hs (.parS e hid τa τb side Ko) (evalK F O m (.capture e hid :: hs) σ1.fresh.2 K (.val (.int 0)))
        else
          ret F O m hs (.parS e hid τa τb (!side) K) (evalK F O m (.capture e hid :: hs) σ1.fresh.2 Ko (.val (.int 0))) := by
      rw [ret.eq_def]
      simp only [ne_eq, not_true_eq_false, or_self, ↓reduceIte]
      rfl
    rw [this]
    split
    · -- The same task goes on.
      have hres := yield_resume (top := ⟨Γr, envr, _, Sr, .eff e :: r⟩) hKk hP.hop hP.hrefs hP.hret hK' hR' haim hwf2
        (Agree.of' fun _ _ => rfl) (fun l hl => by
          rcases List.mem_append.mp hl with h | h
          · exact hX'a l h
          · exact hSr1 l h) hXn' hdSrX'
      have h2 := hRr hs _ _ σf (.parS e hid τa τb side Ko) ⟨Γr, envr, _, Sr, .eff e :: r⟩ ⟨Γ₁, env, .pair τa τb, S, r⟩
        (E₁ ++ X) AK σ1.fresh.2 X' _ (.parS hP hroR hroO hSr hSo hK) hR hA hwf2 hag2 halloc hnd
        (fun l h1 h2 => hdX' l (by simp only [List.mem_append] at h1 ⊢; grind) h2) hS1
        (fun l h1 h2 => by
          rcases List.mem_append.mp h2 with h2 | h2
          · exact hSd l h1 (by simp only [List.mem_append] at h2 ⊢; grind)
          · exact hdX' l (by simp [h1]) h2) hres
      exact post_after hm2 hwf h2
    · -- The other task goes on, and this one waits where it gave way.
      have hres := resumeO m hKk hwf2 hag2
      have hP1 := hP.transfer (restrict hag1)
      have hK'' : FramesOk F O ι σ1 K op ⟨Γr, envr, (if (!side) = true then τb else τa), Sr, .eff e :: r⟩ X' [] A' := by
        cases side <;> simpa using hK'
      have hres' : Post F ι O σ1.fresh.2 X So Γo envo (if (!side) = true then τa else τb) (.eff e :: r) (.capture e hid :: hs)
          (evalK F O m (.capture e hid :: hs) σ1.fresh.2 Ko (.val (.int 0))) := by cases side <;> simpa using hres
      have h2 := hRr hs _ _ σ1 (.parS e hid τa τb (!side) K) ⟨Γo, envo, _, So, .eff e :: r⟩ ⟨Γ₁, env, .pair τa τb, S, r⟩
        (E₁ ++ X') A' σ1.fresh.2 X _ (.parS hP1 hroO hroR hSo hSr hK'') hR (fun a ha => aimed_uncap (haim a ha)) hwf2
        (Agree.of' fun _ _ => rfl)
        (fun l hl => by
          rcases List.mem_append.mp hl with h | h
          · exact hE1a l h
          · exact hX'a l h)
        (nodup_append_disj.mpr ⟨hE1X.1, hXn', fun l h1 h2 => hdX' l (by simp [h1]) h2⟩)
        (fun l h1 h2 => by
          rcases List.mem_append.mp h1 with h1 | h1
          · exact hE1X.2.2 l h1 h2
          · exact hdX' l (by simp [h2]) h1) hS1
        (fun l h1 h2 => by
          simp only [List.mem_append] at h2
          rcases h2 with (h2 | h2) | h2
          · exact hSd l h1 (by simp [h2])
          · exact hdX' l (by simp [h1]) h2
          · exact hSd l h1 (by simp [h2])) hres'
      exact post_after (hm2.relabel fun x => by simp only [List.mem_append]; grind) hwf h2
  | stuck => simp [Post] at hp
  | timeout => simp [ret, Post]
  | panic => simp [ret, Post]

/-! ## Two tasks started -/

theorem Vals.split : ∀ {ts1 ts2 : List Ty} {vs : List Val} {Ls : List (List Nat)}, Vals F ι σ (ts1 ++ ts2) vs Ls →
    ∃ vs1 vs2 Ls1 Ls2, vs = vs1 ++ vs2 ∧ Ls = Ls1 ++ Ls2 ∧ Vals F ι σ ts1 vs1 Ls1 ∧ Vals F ι σ ts2 vs2 Ls2
  | [], _, vs, Ls, h => ⟨[], vs, [], Ls, rfl, rfl, .nil, h⟩
  | _ :: _, _, _, _, .cons hv hrest => by
    obtain ⟨vs1, vs2, Ls1, Ls2, rfl, rfl, h1, h2⟩ := Vals.split hrest
    exact ⟨_ :: vs1, vs2, _ :: Ls1, Ls2, rfl, rfl, .cons hv h1, h2⟩

theorem lends_ro : Lends Γ lent ts ys → (∀ x ∈ lent, x.1 = .ro) → ∀ x ∈ ts, x.1 = .ro := by
  intro h
  induction h with
  | nil => intro _ x hx; simp at hx
  | cons _ _ _ _ ih =>
    intro hl x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hl _ (List.mem_cons_self ..)
    · exact ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)) x hx

theorem lentApart_ro : ∀ {lent : List (Mode × Place)}, (∀ x ∈ lent, x.1 = .ro) → LentApart lent
  | [], _ => List.Pairwise.nil
  | _ :: rest, h => List.Pairwise.cons (fun b hb _ => .inl ⟨h _ (List.mem_cons_self ..),
      h b (List.mem_cons_of_mem _ hb)⟩) (lentApart_ro fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem mutCells_ro (h : ∀ x ∈ hos, x.mode = .ro) : mutCells (olds hos) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro l hl
  obtain ⟨x, hx, hl⟩ := mem_olds_mut.mp hl
  have := (Hole.excl_mut hl).1
  rw [h x hx] at this
  cases this

theorem mapM_ro {l : List Place} :
    ((l.map fun p => ((Mode.ro), p)).mapM fun x => resolve σ env x.2) = l.mapM (fun p => resolve σ env p) := by
  induction l with
  | nil => rfl
  | cons p l ih => simp [List.mapM_cons, ih]

/-- A task not yet started, as if it had given way just before its body. -/
theorem task_frames {d : Fn} {cells : Env} {ls : List Nat} {e : Nat}
    (hkeys : ((d.owns.map Prod.fst) ++ (d.refs.map Prod.fst)).Nodup) (hoc : ∀ o ∈ d.owns, o.2.complete = true)
    (hbody : Typed F O (fnCtx d) d.body d.ret Γ'' d.row) (hrow : ∀ l ∈ d.row, l ∈ .eff e :: r)
    (hcells : cells.map Prod.fst = d.owns.map Prod.fst)
    (hop : O[e]? = some op) (hrefs : op.refs = []) (hret : op.ret = .int) (he : Label.eff e ∈ d.row)
    (hI : Inv F ι σ (fnCtx d) (cells ++ (d.refs.map Prod.fst).zip ls) Et St) :
    FramesOk F O ι σ [.callK ((d.owns.map Prod.snd).zip (cells.map Prod.snd)),
        .startK (cells ++ (d.refs.map Prod.fst).zip ls) d.body] op
      ⟨refCtx d.refs, (d.refs.map Prod.fst).zip ls, d.ret, St, .eff e :: r⟩ Et [] [] := by
  have hb := FramesOk.base (hos := []) (Γ' := fnCtx d) (r := d.row) hI (fun _ h => by simp at h) List.Pairwise.nil hop
    (by simp [hrefs]) (Weaker.refl _)
  rw [hret] at hb
  simp only [olds, mutCells, List.map_nil, List.flatMap_nil, List.not_mem_nil, not_false_eq_true,
    decide_true] at hb
  have h1 := FramesOk.cons (A := []) (Γ' := Γ'') (.startK (σf := σ) (env := cells ++ (d.refs.map Prod.fst).zip ls)
    (S := St) hbody) (Weaker.refl _) Agree.self (fun _ h => by simp at h) List.nodup_nil disj_nil_left hb
    (fun _ h => by simp at h) (fun _ h => by simp at h)
  have h2 := FramesOk.cons (A := []) (Γ' := refCtx d.refs) (.taskK (r := .eff e :: r) (ls := ls) (St := St) hrow hkeys hoc
    hbody hcells) (Weaker.refl _) Agree.self (fun _ h => by simp at h) List.nodup_nil disj_nil_left h1
    (fun _ h => by simp at h) (fun _ h => by simp at h)
  have hf : List.filter (fun _ => true) Et = Et := List.filter_eq_self.mpr fun _ _ => rfl
  simpa [hf] using h2

/-- `par`: both tasks' arguments taken and their parameters allocated, the first runs, the second
waiting as if it had given way just before its body. -/
theorem par_ok (hF : FnsOk F O) (hR : RetOk F O n) (hKk : EvalKOk F O n)
    (hop : O[e]? = some op) (howns : op.owns = []) (hrefs : op.refs = []) (hret : op.ret = .int)
    (hfa : F[fa]? = some da) (hfb : F[fb]? = some db) (hretpa : da.retp = none) (hcapa : da.cap = none)
    (hretpb : db.retp = none) (hcapb : db.cap = none) (hea : Label.eff e ∈ da.row) (heb : Label.eff e ∈ db.row)
    (hrowa : ∀ l ∈ da.row, l ∈ .eff e :: r) (hrowb : ∀ l ∈ db.row, l ∈ .eff e :: r)
    (hca : da.ret.complete = true) (hcb : db.ret.complete = true)
    (hargs : AtomsTy Γ (oa ++ ob) (da.owns.map Prod.snd ++ db.owns.map Prod.snd) Γ₁)
    (hlends : Lends Γ₁ ((la ++ lb).map fun p => (.ro, p)) (da.refs.map Prod.snd ++ db.refs.map Prod.snd) ys)
    (hI : Inv F ι σ Γ env E S) (hwf : WF σ) (hRdy : Ready O hs r) :
    Post F ι O σ E S Γ₁ env (.pair da.ret db.ret) r hs (evalS F O n hs σ env (.par e fa oa la fb ob lb)) := by
  obtain ⟨vs, σ1, E₁, Ls, hevs, hI₁, hvs, hLn, hdL, hdLS, hm₁⟩ := atoms_ok hargs hI hwf
  have hwf₁ := hm₁.wf
  have hrolent : ∀ x ∈ (la ++ lb).map (fun p => ((Mode.ro), p)), x.1 = .ro := by
    intro x hx; obtain ⟨p, -, rfl⟩ := List.mem_map.mp hx; rfl
  obtain ⟨hos, hts, -, hmap, hholes, -, hpw⟩ := lends_ok hlends hI₁.foot (lentApart_ro hrolent)
  rw [mapM_ro] at hmap
  have hrots := lends_ro hlends hrolent
  have hroa : ∀ x ∈ da.refs, x.2.1 = .ro := fun x hx =>
    hrots x.2 (List.mem_append.mpr (.inl (List.mem_map_of_mem hx)))
  have hrob : ∀ x ∈ db.refs, x.2.1 = .ro := fun x hx =>
    hrots x.2 (List.mem_append.mpr (.inr (List.mem_map_of_mem hx)))
  obtain ⟨hosA, hosB, rfl, htsA, htsB⟩ := List.map_eq_append_iff.mp hts
  obtain ⟨vsA, vsB, LsA, LsB, rfl, rfl, hvA, hvB⟩ := Vals.split hvs
  obtain ⟨hkA, hbA⟩ := hF da (List.mem_of_getElem? hfa)
  rw [hcapa, hretpa] at hbA
  obtain ⟨ΓA, hbA⟩ := hbA
  obtain ⟨hkB, hbB⟩ := hF db (List.mem_of_getElem? hfb)
  rw [hcapb, hretpb] at hbB
  obtain ⟨ΓB, hbB⟩ := hbB
  have hlenA : vsA.length = da.owns.length := by rw [hvA.length]; simp
  have hlenB : vsB.length = db.owns.length := by rw [hvB.length]; simp
  have hlenhA : hosA.length = da.refs.length := by have := congrArg List.length htsA; simpa using this
  have hlenhB : hosB.length = db.refs.length := by have := congrArg List.length htsB; simpa using this
  simp only [evalS, hfa, hfb, hevs, hmap]
  have htA : List.take da.owns.length (vsA ++ vsB) = vsA := by rw [← hlenA]; simp
  have hdA : List.drop da.owns.length (vsA ++ vsB) = vsB := by rw [← hlenA]; simp
  have htH : List.take da.refs.length (List.map Hole.loc (hosA ++ hosB)) = hosA.map Hole.loc := by
    rw [List.map_append, ← hlenhA]; simp
  have hdH : List.drop da.refs.length (List.map Hole.loc (hosA ++ hosB)) = hosB.map Hole.loc := by
    rw [List.map_append, ← hlenhA]; simp
  rw [if_pos ⟨by simp [hlenA, hlenB], by simp [hlenhA, hlenhB]⟩, htA, hdA, htH, hdH]
  have hLn' := nodup_append_disj.mp (by simpa using hLn : (LsA.flatten ++ LsB.flatten).Nodup)
  -- The first task's parameters.
  obtain ⟨EoA, hfoA, hEoA, hEoAm, hleA, hwf₂, holdA, hnewA, -⟩ :=
    allocAll_ok (names := da.owns.map Prod.fst) hvA (by simp) hwf₁ hLn'.1 (by cur_inv)
  rw [zip_fst_snd] at hfoA
  have hcellsA : (allocAll σ1 ((da.owns.map Prod.fst).zip vsA)).1.map Prod.fst = da.owns.map Prod.fst := by
    rw [allocAll_fst]; exact List.map_fst_zip (by rw [hlenA]; simp)
  have hrtA := allocAll_rt σ1 ((da.owns.map Prod.fst).zip vsA)
  have hfbtA := allocAll_fbext σ1 ((da.owns.map Prod.fst).zip vsA)
  have hcutA := allocAll_cur σ1 ((da.owns.map Prod.fst).zip vsA)
  generalize allocAll σ1 ((da.owns.map Prod.fst).zip vsA) = alA at hfoA hEoAm hleA hwf₂ holdA hnewA hcellsA hrtA hfbtA hcutA ⊢
  obtain ⟨cA, σ2⟩ := alA
  dsimp only at hfoA hEoAm hleA hwf₂ holdA hnewA hcellsA hrtA hfbtA ⊢
  -- The second's.
  have hvB2 := hvB.frame <| Agree.of' fun l hl => holdA l (hwf₁ l (hvB.alloc l hl))
  obtain ⟨EoB, hfoB, hEoB, hEoBm, hleB, hwf₃, holdB, hnewB, -⟩ :=
    allocAll_ok (names := db.owns.map Prod.fst) hvB2 (by simp) hwf₂ hLn'.2.1 (hcutA.trans hI₁.cur)
  rw [zip_fst_snd] at hfoB
  have hcellsB : (allocAll σ2 ((db.owns.map Prod.fst).zip vsB)).1.map Prod.fst = db.owns.map Prod.fst := by
    rw [allocAll_fst]; exact List.map_fst_zip (by rw [hlenB]; simp)
  have hrtB := allocAll_rt σ2 ((db.owns.map Prod.fst).zip vsB)
  have hfbtB := allocAll_fbext σ2 ((db.owns.map Prod.fst).zip vsB)
  have hcutB := allocAll_cur σ2 ((db.owns.map Prod.fst).zip vsB)
  generalize allocAll σ2 ((db.owns.map Prod.fst).zip vsB) = alB at hfoB hEoBm hleB hwf₃ holdB hnewB hcellsB hrtB hfbtB hcutB ⊢
  obtain ⟨cB, σ3⟩ := alB
  dsimp only at hfoB hEoBm hleB hwf₃ holdB hnewB hcellsB hrtB hfbtB ⊢
  have hold31 : ∀ l, l < σ1.next → σ3.mem l = σ1.mem l := fun l hl =>
    (holdB l (Nat.lt_of_lt_of_le hl hleA)).trans (holdA l hl)
  have hEoAin : ∀ l ∈ EoA, l ∈ LsA.flatten ∨ σ1.next ≤ l := fun l hl => by
    rcases (hEoAm l).mp hl with h | h
    · exact .inl h
    · exact .inr h.1
  have hEoBin : ∀ l ∈ EoB, l ∈ LsB.flatten ∨ σ1.next ≤ l := fun l hl => by
    rcases (hEoBm l).mp hl with h | h
    · exact .inl h
    · exact .inr (Nat.le_trans hleA h.1)
  have hdLA : Disj LsA.flatten E₁ := fun l h1 h2 => hdL l (by simp [h1]) h2
  have hdLB : Disj LsB.flatten E₁ := fun l h1 h2 => hdL l (by simp [h1]) h2
  have hdLSA : Disj LsA.flatten S := fun l h1 h2 => hdLS l (by simp [h1]) h2
  have hdLSB : Disj LsB.flatten S := fun l h1 h2 => hdLS l (by simp [h1]) h2
  have hpw2 := List.pairwise_append.mp hpw
  have hmodes : ∀ {hs' : List Hole} {refs : List (Var × Mode × Ty)},
      hs'.map (fun h => (h.mode, h.ty)) = refs.map Prod.snd → (∀ x ∈ refs, x.2.1 = .ro) → ∀ h ∈ hs', h.mode = .ro := by
    intro hs' refs hm hro h hh
    have : (h.mode, h.ty) ∈ refs.map Prod.snd := hm ▸ List.mem_map_of_mem hh
    obtain ⟨x, hx, hxe⟩ := List.mem_map.mp this
    have := hro x hx
    rw [hxe] at this
    exact this
  have hmA := mutCells_ro (hmodes htsA hroa)
  have hmB := mutCells_ro (hmodes htsB hrob)
  have hIA := callee_inv (k := 0) (d := da) hI₁ (fun h hh => hholes h (List.mem_append.mpr (.inl hh))) hpw2.1
    (by simpa using htsA.symm) hkA hfoA hEoA hEoAin hdLA hdLSA hwf₁ holdA hrtA hfbtA hcutA rfl (fun _ _ _ h => by simpa using h)
  have hIB := callee_inv (k := 0) (d := db) hI₁ (fun h hh => hholes h (List.mem_append.mpr (.inr hh))) hpw2.2.1
    (by simpa using htsB.symm) hkB hfoB hEoB hEoBin hdLB hdLSB hwf₁ hold31 (hrtB.trans hrtA) (hfbtA.trans hfbtB) (hcutB.trans hcutA) rfl (fun _ _ _ h => by simpa using h)
  rw [hmA, List.append_nil] at hIA
  rw [hmB, List.append_nil] at hIB
  -- Everything at the start of the tasks, where the first is given its turn.
  have hag23 : ∀ l, σ2.mem l ≠ none → σ3.fresh.2.mem l = σ2.mem l := fun l h => holdB l (hwf₂ l h)
  have hIA4 : Inv F ι σ3.fresh.2 (fnCtx da) (cA ++ (da.refs.map Prod.fst).zip (hosA.map Hole.loc)) EoA
      (roCells (olds hosA)) :=
    ⟨hIA.foot.frame (Agree.of (fun l hl => hag23 l (hIA.foot.alloc l (List.mem_append.mp hl))) hrtB), hIA.nodup,
      hIA.disj, hIA.keys, hcutB.trans hIA.cur⟩
  have hIB4 : Inv F ι σ3.fresh.2 (fnCtx db) (cB ++ (db.refs.map Prod.fst).zip (hosB.map Hole.loc)) EoB
      (roCells (olds hosB)) :=
    ⟨hIB.foot.frame <| Agree.of' fun _ _ => rfl, hIB.nodup, hIB.disj, hIB.keys, hIB.cur⟩
  have hag14 : Agree σ1 σ3.fresh.2 (E₁ ++ S) :=
    Agree.of (fun l hl => hold31 l (hwf₁ l (hI₁.foot.alloc l (List.mem_append.mp hl)))) (hrtB.trans hrtA)
      (hfbtA.trans hfbtB) (hcutB.trans hcutA)
  have hP4 : ParOk F ι O σ3.fresh.2 e op Γ₁ env E₁ S da.ret db.ret :=
    ⟨hop, howns, hrefs, hret, ⟨hI₁.foot.frame hag14, hI₁.nodup, hI₁.disj, hI₁.keys, hag14.cur.trans hI₁.cur⟩, hca, hcb⟩
  have hSt : ∀ {hs' : List Hole}, (∀ h ∈ hs', HoleOk F ι σ1 Γ₁ env h) → ∀ l ∈ roCells (olds hs'), l ∈ E₁ ∨ l ∈ S := by
    intro hs' hh l hl
    obtain ⟨h, hmem, hlo⟩ := mem_olds_ro.mp hl
    exact (hole_in hI₁ (hh h hmem)).1 l (List.mem_append.mpr (.inr (sharedPart_sub hlo)))
  have hStA := hSt fun h hh => hholes h (List.mem_append.mpr (.inl hh))
  have hStB := hSt fun h hh => hholes h (List.mem_append.mpr (.inr hh))
  have hKA := task_frames (r := r) hkA hvA.owns_complete hbA hrowa hcellsA hop hrefs hret hea hIA4
  have hKB := task_frames (r := r) hkB hvB.owns_complete hbB hrowb hcellsB hop hrefs hret heb hIB4
  have hframe := FrameOk.parS (σf := σ3.fresh.2) (side := true) (hid := σ3.fresh.1) (Γr := refCtx da.refs)
    (envr := (da.refs.map Prod.fst).zip (hosA.map Hole.loc)) hP4 (refCtx_ro hroa) (refCtx_ro hrob) hStA hStB
    (by simpa using hKB)
  have hwf4 : WF σ3.fresh.2 := hwf₃
  have hres := yield_resume (top := ⟨refCtx da.refs, (da.refs.map Prod.fst).zip (hosA.map Hole.loc), da.ret,
      roCells (olds hosA), .eff e :: r⟩) hKk hop hrefs hret hKA (hframe.ready hRdy) (fun _ h => by simp at h) hwf4
    Agree.self (fun l hl => hIA4.foot.alloc l (List.mem_append.mp hl)) hEoA hIA4.disj
  -- Where each cell is: the code around's, the arguments moved into the tasks, the new ones.
  have hE1a : ∀ l ∈ E₁, σ1.mem l ≠ none := hI₁.alloc
  have hSa1 : ∀ l ∈ S, σ1.mem l ≠ none := hI₁.allocS
  have hLa : ∀ l ∈ LsA.flatten ++ LsB.flatten, σ1.mem l ≠ none := fun l hl => hvs.alloc l (by simpa using hl)
  have hlt : ∀ l, σ1.mem l ≠ none → l < σ1.next := hwf₁
  have hdE1B : Disj E₁ EoB := fun l h1 h2 => by
    rcases (hEoBm l).mp h2 with h | h
    · exact hdLB l h h1
    · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hlt l (hE1a l h1)) (Nat.le_trans hleA h.1))
  have hdE1A : Disj E₁ EoA := fun l h1 h2 => by
    rcases (hEoAm l).mp h2 with h | h
    · exact hdLA l h h1
    · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hlt l (hE1a l h1)) h.1)
  have hdBA : Disj EoB EoA := fun l h1 h2 => by
    rcases (hEoBm l).mp h1 with h | h <;> rcases (hEoAm l).mp h2 with h' | h'
    · exact hLn'.2.2 l h' h
    · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hlt l (hLa l (by simp [h]))) h'.1)
    · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hlt l (hLa l (by simp [h']))) (Nat.le_trans hleA h.1))
    · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h'.2 h.1)
  have hdSA : Disj S EoA := fun l h1 h2 => by
    rcases (hEoAm l).mp h2 with h | h
    · exact hdLSA l h h1
    · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hlt l (hSa1 l h1)) h.1)
  have hdSB : Disj S EoB := fun l h1 h2 => by
    rcases (hEoBm l).mp h2 with h | h
    · exact hdLSB l h h1
    · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hlt l (hSa1 l h1)) (Nat.le_trans hleA h.1))
  have hS4 : ∀ l ∈ S, σ3.fresh.2.mem l ≠ none := fun l hl => by
    rw [hag14 l (by simp [hl])]; exact hSa1 l hl
  have h := hR hs _ _ σ3.fresh.2 (.parS e σ3.fresh.1 da.ret db.ret true _) _ ⟨Γ₁, env, .pair da.ret db.ret, S, r⟩
    (E₁ ++ EoB) [] σ3.fresh.2 EoA _ hframe hRdy (fun _ h => by simp at h) hwf4 Agree.self
    (fun l hl => by
      rcases List.mem_append.mp hl with h | h
      · rw [hag14 l (by simp [h])]; exact hE1a l h
      · exact hIB4.alloc l h)
    (nodup_append_disj.mpr ⟨hI₁.nodup, hEoB, hdE1B⟩)
    (fun l h1 h2 => by
      rcases List.mem_append.mp h1 with h1 | h1
      · exact hdE1A l h1 h2
      · exact hdBA l h1 h2) hS4
    (fun l h1 h2 => by
      simp only [List.mem_append] at h2
      rcases h2 with (h2 | h2) | h2
      · exact hI₁.disj l h1 h2
      · exact hdSB l h1 h2
      · exact hdSA l h1 h2) (by simpa using hres)
  have m1 := hm₁.relabel (E'' := E₁ ++ (LsA.flatten ++ LsB.flatten)) (L'' := []) fun x => by simp
  have m2 := Moves.grow (σ := σ1) (σ' := σ3) (E := E₁ ++ (LsA.flatten ++ LsB.flatten)) (E' := E₁ ++ EoB ++ EoA)
    (hfb := hfbtA.trans hfbtB) (hcur := hcutB.trans hcutA)
    hwf₁ hwf₃ (Nat.le_trans hleA hleB) hold31
    (fun l h1 h2 => by
      by_cases h3 : l < σ2.next
      · rw [holdB l h3]; exact hnewA l h1 h3
      · exact hnewB l (Nat.le_of_not_lt h3) h2)
    (fun l hl => by
      rcases List.mem_append.mp hl with h | h
      · exact hE1a l h
      · exact hLa l h)
    (fun l => by
      simp only [List.mem_append, hEoAm, hEoBm]
      constructor
      · rintro ((h | h | h) | h | h)
        · exact .inl (.inl h)
        · exact .inl (.inr (.inr h))
        · exact .inr ⟨Nat.le_trans hleA h.1, h.2⟩
        · exact .inl (.inr (.inl h))
        · exact .inr ⟨h.1, Nat.lt_of_lt_of_le h.2 hleB⟩
      · rintro ((h | h | h) | ⟨h1, h2⟩)
        · exact .inl (.inl h)
        · exact .inr (.inl h)
        · exact .inl (.inr (.inl h))
        · by_cases h3 : l < σ2.next
          · exact .inr (.inr ⟨h1, h3⟩)
          · exact .inl (.inr (.inr ⟨Nat.le_of_not_lt h3, h2⟩))) (hrtB.trans hrtA)
  have m3 := Moves.freshen (σ := σ3) (E := E₁ ++ EoB ++ EoA) hwf₃ fun l hl => (m2.alloc l).mpr (.inr (.inl hl))
  exact post_after (((m1.trans m2 disj_nil_left hwf).trans m3 disj_nil_left hwf).relabel fun x => by simp) hwf h

end FlyCore.Ownership
