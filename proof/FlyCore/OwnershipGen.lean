import FlyCore.OwnershipVec

/-!
# Ownership: generators

A generator's producer runs as its consumer asks for values: each side, while the other runs, waits
as a continuation the generator's frame keeps, its cells the frame's own, as a task waits; and the
consumer's activation, which the generator froze the producer's loans in, is rebuilt once it ends.
When either side ends, the other is dropped where it waits, its scopes dropping what they own.
-/

namespace FlyCore.Ownership

/-- A continuation resumed with a value of its operation's result, owning `Lv`. -/
theorem value_resume (hKk : EvalKOk F O m) (hrefs : op.refs = [])
    (hK : FramesOk F O ι σs K op top X hos A) (hR : Ready O hs top.r) (hA : ∀ a ∈ A, AimedIn a hs)
    (hwf : WF σr) (hag : Agree σs σr (X ++ top.S)) (hXa : ∀ l ∈ X ++ top.S, σs.mem l ≠ none) (hXn : X.Nodup)
    (hdS : Disj top.S (X ++ Lv)) (hv : VT F ι σr op.ret v Lv) (hdv : Disj Lv X) :
    Post F ι O σr (X ++ Lv) top.S top.Γ top.env top.τ top.r hs (evalK F O m hs σr K (.val v)) := by
  obtain ⟨-, -, -, -, -, -, -, -, hts, -, -, -, -⟩ := hK.base_of
  rw [hrefs] at hts
  obtain rfl : hos = [] := List.map_eq_nil_iff.mp hts
  have h := hKk hs _ σs K top X [] A σr [] (.val v) op Lv hK hR hA hwf hag hXa hXn rfl
    (fun _ h => by simp at h) (by simp [mutCells]) (by simp [mutCells, Disj])
    (by simpa [mutCells] using hdS) (.inl ⟨_, rfl, hv, by simpa [mutCells] using hdv⟩)
  simpa [mutCells] using h

/-! ## Dropping one side -/

/-- A producer being dropped: each value it yields is dropped, and it goes on at once. -/
theorem ret_genY (hKo : ∀ m, n = m + 1 → EvalKOk F O m ∧ RetOk F O m) (hop : O[eY]? = some op)
    (howns : op.owns = [τy]) (hrefs : op.refs = []) (hret : op.ret = .int) (hcy : τy.complete = true)
    (hR : Ready O hs r) (hwf : WF σ0) (hag : Agree σf σ0 S) (hSa : ∀ l ∈ S, σ0.mem l ≠ none) (hSd : Disj S Ein)
    (hp : Post F ι O σ0 Ein S Γ env τ (.eff eY :: r) (.capture eY hid :: hs) res) :
    Post F ι O σ0 Ein S Γ env τ r hs (ret F O n hs (.genY eY hid τy) res) := by
  rcases res with ⟨res, σ1⟩
  have pass : (∀ j ef vs ls K, res = .susp j ef vs ls K → j ≠ hid ∨ ef ≠ eY) →
      Post F ι O σ0 Ein S Γ env τ r hs (ret F O n hs (.genY eY hid τy) (res, σ1)) := by
    intro hnot
    have : ret F O n hs (.genY eY hid τy) (res, σ1) = passK (.genY eY hid τy) (res, σ1) := by
      cases res with
      | susp j ef vs ls K => rw [ret.eq_def]; simp [passK, hnot j ef vs ls K rfl]
      | _ => simp [ret, passK]
    rw [this]
    have h := post_pass (Xf := []) (σf := σf) (.genY (hid := hid) hop howns hrefs hret hcy) (fun _ h => h)
      (fun σ1 Eb _ _ hI => ⟨Eb, hI, fun z => by simp⟩) hR.2 (fun a ha => aimed_uncap ha) ?_ hwf hag
      (fun _ h => by simp at h) List.nodup_nil disj_nil_left hSa (by simpa using hSd) hp
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
  by_cases hc : j ≠ hid ∨ ef ≠ eY
  · exact pass fun _ _ _ _ _ h => by cases h; exact hc
  simp only [ne_eq, not_or, Decidable.not_not] at hc
  obtain ⟨h1, h2⟩ := hc
  subst j ef
  obtain ⟨op', X, hos, A, Lv, -, hop', -, haim, hK, hls, hvs, hLn, hdLX, hdLS, hm⟩ := hp
  obtain rfl : op = op' := Option.some.inj (hop.symm.trans hop')
  rw [howns] at hvs
  cases hvs with
  | cons hv hrest =>
  cases hrest
  rename_i v L
  obtain ⟨-, -, -, -, -, -, -, -, hts, -, -, hXn, -⟩ := hK.base_of
  rw [hrefs] at hts
  obtain rfl : hos = [] := List.map_eq_nil_iff.mp hts
  simp only [olds, mutCells, List.map_nil, List.flatMap_nil, List.append_nil, List.flatten_cons,
    List.flatten_nil] at hm hdLX hdLS hLn
  cases n with
  | zero => simp [ret, Post]
  | succ m =>
  obtain ⟨hKk, hRr⟩ := hKo m rfl
  have hwf₁ := hm.wf
  obtain ⟨σ2, hdrop, hnext, hfree, hkeep⟩ := drop_ok hwf₁ τy v L hv
  have hrt2 : σ2.rt = σ1.rt := drop_rt hdrop
  simp only [ret, ne_eq, not_true_eq_false, or_self, ↓reduceIte, hdrop]
  have hwf2 : WF σ2 := WF.of_free hwf₁ hnext hfree hkeep
  have hSa1 : ∀ l ∈ S, σ1.mem l ≠ none := fun l hl => by
    rw [hm.keeps hwf hSa (fun l h1 h2 => hSd l h1 h2) l hl]; exact hSa l hl
  have hXa1 : ∀ l ∈ X, σ1.mem l ≠ none := fun l hl => (hm.alloc l).mpr (.inr (.inl hl))
  have hag12 : Agree σ1 σ2 (X ++ S) := Agree.of (fun l hl => hkeep l fun h => by
    rcases List.mem_append.mp hl with hl | hl
    · exact hdLX l h hl
    · exact hdLS l h hl) hrt2
  have hm2 : Moves σ1 (X ++ L) σ2 X [] := Moves.free hwf2 hnext (fun l hl => by
      rcases List.mem_append.mp hl with h | h
      · exact hXa1 l h
      · exact hv.alloc l h) (fun l => by simp only [List.mem_append]) hfree hkeep (fun l h1 h2 => hdLX l h2 h1) hrt2
  have hR' : Ready O (.capture eY hid :: hs) (.eff eY :: r) :=
    (FrameOk.genY (F := F) (ι := ι) (σf := σ2) (Γ := Γ) (env := env) (τ := τ) (S := S) (hid := hid) hop howns hrefs
      hret hcy).ready hR
  have hres := yield_resume (top := ⟨Γ, env, τ, S, .eff eY :: r⟩) hKk hop hrefs hret hK hR' haim hwf2 hag12
    (fun l hl => by
      rcases List.mem_append.mp hl with h | h
      · exact hXa1 l h
      · exact hSa1 l h) hXn (fun l h1 h2 => (hm.apart hwf hSa hSd).1 l h1 h2)
  have hSa2 : ∀ l ∈ S, σ2.mem l ≠ none := fun l hl => by
    rw [hag12 l (List.mem_append.mpr (.inr hl))]; exact hSa1 l hl
  have h2 := hRr hs _ _ σ2 (.genY eY hid τy) ⟨Γ, env, τ, S, .eff eY :: r⟩ ⟨Γ, env, τ, S, r⟩ [] [] σ2 X _
      (.genY hop howns hrefs hret hcy) hR (fun _ h => by simp at h) hwf2 Agree.self (fun _ h => by simp at h)
      List.nodup_nil disj_nil_left hSa2 (fun l h1 h2 => (hm.apart hwf hSa hSd).1 l h1 (by simpa using h2)) hres
  have hm' : Moves σ0 Ein σ1 (X ++ L) [] := hm.relabel fun x => by simp only [List.mem_append, List.not_mem_nil, or_false]
  exact post_after (hm'.trans hm2 disj_nil_left hwf) hwf (by simpa using h2)


/-- `#Done`, in a cell of its own. -/
theorem done_vt (hb : σ.mem b = some (.int 0)) (hcy : τy.complete = true) :
    VT F ι σ (.sum .int τy) (.tag .int τy true b) [b] :=
  .tag (.int hb) rfl hcy

/-- A consumer being dropped: whatever it asks is answered `#Done`. -/
theorem ret_genN (hKo : ∀ m, n = m + 1 → EvalKOk F O m ∧ RetOk F O m) (hop : O[eN]? = some op)
    (howns : op.owns = []) (hrefs : op.refs = []) (hret : op.ret = .sum .int τy) (hcy : τy.complete = true)
    (hR : Ready O hs r) (hwf : WF σ0) (hag : Agree σf σ0 S) (hSa : ∀ l ∈ S, σ0.mem l ≠ none) (hSd : Disj S Ein)
    (hp : Post F ι O σ0 Ein S Γ env τ (.eff eN :: r) (.capture eN hid :: hs) res) :
    Post F ι O σ0 Ein S Γ env τ r hs (ret F O n hs (.genN eN hid τy) res) := by
  rcases res with ⟨res, σ1⟩
  have pass : (∀ j ef vs ls K, res = .susp j ef vs ls K → j ≠ hid ∨ ef ≠ eN) →
      Post F ι O σ0 Ein S Γ env τ r hs (ret F O n hs (.genN eN hid τy) (res, σ1)) := by
    intro hnot
    have : ret F O n hs (.genN eN hid τy) (res, σ1) = passK (.genN eN hid τy) (res, σ1) := by
      cases res with
      | susp j ef vs ls K => rw [ret.eq_def]; simp [passK, hnot j ef vs ls K rfl]
      | _ => simp [ret, passK]
    rw [this]
    have h := post_pass (Xf := []) (σf := σf) (.genN (hid := hid) hop howns hrefs hret hcy) (fun _ h => h)
      (fun σ1 Eb _ _ hI => ⟨Eb, hI, fun z => by simp⟩) hR.2 (fun a ha => aimed_uncap ha) ?_ hwf hag
      (fun _ h => by simp at h) List.nodup_nil disj_nil_left hSa (by simpa using hSd) hp
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
  by_cases hc : j ≠ hid ∨ ef ≠ eN
  · exact pass fun _ _ _ _ _ h => by cases h; exact hc
  simp only [ne_eq, not_or, Decidable.not_not] at hc
  obtain ⟨h1, h2⟩ := hc
  subst j ef
  obtain ⟨op', X, hos, A, Lv, -, hop', -, haim, hK, hls, hvs, hLn, hdLX, hdLS, hm⟩ := hp
  obtain rfl : op = op' := Option.some.inj (hop.symm.trans hop')
  rw [howns] at hvs
  cases hvs
  obtain ⟨-, -, -, -, -, -, -, -, hts, -, -, hXn, -⟩ := hK.base_of
  rw [hrefs] at hts
  obtain rfl : hos = [] := List.map_eq_nil_iff.mp hts
  simp only [olds, mutCells, List.map_nil, List.flatMap_nil, List.append_nil, List.flatten_nil] at hm
  cases n with
  | zero => simp [ret, Post]
  | succ m =>
  obtain ⟨hKk, hRr⟩ := hKo m rfl
  have hwf₁ := hm.wf
  simp only [ret, ne_eq, not_true_eq_false, or_self, ↓reduceIte]
  generalize hb : (σ1.alloc (.int 0)).1 = b
  have hbn : b = σ1.next := hb.symm
  generalize hσ2 : (σ1.alloc (.int 0)).2 = σ2
  have hm2 : Moves σ1 X σ2 (X ++ [b]) [] := by
    rw [← hσ2, hbn]
    exact (Moves.allocate hwf₁ (fun l hl => (hm.alloc l).mpr (.inr (.inl hl)))).relabel fun x => by simp
  have hwf2 : WF σ2 := hm2.wf
  have hfresh : ∀ l, σ1.mem l ≠ none → l ≠ b := fun l h e => by
    subst e; rw [hbn] at h; exact Nat.lt_irrefl _ (hwf₁ _ h)
  have hSa1 : ∀ l ∈ S, σ1.mem l ≠ none := fun l hl => by
    rw [hm.keeps hwf hSa (fun l h1 h2 => hSd l h1 h2) l hl]; exact hSa l hl
  have hXa1 : ∀ l ∈ X, σ1.mem l ≠ none := fun l hl => (hm.alloc l).mpr (.inr (.inl hl))
  have hold : ∀ l, σ1.mem l ≠ none → σ2.mem l = σ1.mem l := fun l h => by
    rw [← hσ2]; simp only [Store.alloc]; rw [if_neg (fun e => hfresh l h (by rw [hbn]; exact e))]
  have hag12 : Agree σ1 σ2 (X ++ S) := Agree.of' (fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · exact hold l (hXa1 l h)
    · exact hold l (hSa1 l h)) (by rw [← hσ2]; rfl)
  have hbm : σ2.mem b = some (.int 0) := by rw [← hσ2, hbn]; simp [Store.alloc]
  have hdSX : Disj S X := (hm.apart hwf hSa hSd).1
  have hR' : Ready O (.capture eN hid :: hs) (.eff eN :: r) :=
    (FrameOk.genN (F := F) (ι := ι) (σf := σ2) (Γ := Γ) (env := env) (τ := τ) (S := S) (hid := hid) hop howns hrefs
      hret hcy).ready hR
  have hres := value_resume (top := ⟨Γ, env, τ, S, .eff eN :: r⟩) (Lv := [b]) hKk hrefs hK hR' haim hwf2 hag12
    (fun l hl => by
      rcases List.mem_append.mp hl with h | h
      · exact hXa1 l h
      · exact hSa1 l h) hXn
    (fun l h1 h2 => by
      rcases List.mem_append.mp h2 with h2 | h2
      · exact hdSX l h1 h2
      · simp at h2; exact hfresh l (hSa1 l h1) h2)
    (by rw [hret]; exact done_vt hbm hcy)
    (fun l h1 h2 => by simp at h1; subst h1; exact hfresh _ (hXa1 _ h2) rfl)
  have hSa2 : ∀ l ∈ S, σ2.mem l ≠ none := fun l hl => by rw [hold l (hSa1 l hl)]; exact hSa1 l hl
  have h2 := hRr hs _ _ σ2 (.genN eN hid τy) ⟨Γ, env, τ, S, .eff eN :: r⟩ ⟨Γ, env, τ, S, r⟩ [] [] σ2 (X ++ [b]) _
      (.genN hop howns hrefs hret hcy) hR (fun _ h => by simp at h) hwf2 Agree.self (fun _ h => by simp at h)
      List.nodup_nil disj_nil_left hSa2 (fun l h1 h2 => by
        simp only [List.nil_append, List.mem_append, List.mem_singleton] at h2
        rcases h2 with h2 | rfl
        · exact hdSX l h1 h2
        · exact hfresh _ (hSa1 _ h1) rfl) hres
  exact post_after (hm.trans hm2 disj_nil_left hwf) hwf (by simpa using h2)


/-- A frame with cells of its own that puts an unwinding barrier in force joins a continuation taken
through it. -/
theorem post_susp_abort (hf : FrameOk F O ι ι σf f ⟨Γin, envin, τin, Sin, rin⟩ ⟨Γout, envout, τout, S, r⟩ Xf Af)
    (hpush : ∀ hs, f.push hs = .abort l c :: hs) (hcov : Covers hs r) (hAf : ∀ a ∈ Af, AimedIn a hs)
    (hwf : WF σ0) (hag : Agree σf σ0 (Xf ++ S)) (halloc : ∀ l ∈ Xf, σf.mem l ≠ none) (hnd : Xf.Nodup)
    (hd : Disj Xf Ein) (hSa : ∀ l ∈ S, σ0.mem l ≠ none) (hSd : Disj S (Xf ++ Ein))
    (hp : Post F ι O σ0 Ein Sin Γin envin τin rin (.abort l c :: hs) (.susp j ef vs ls K, σ1)) :
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
  have hK' := FramesOk.cons (A := Af ++ A.filter (· ≠ c)) hf (Weaker.refl _)
    ((Agree.trans (hag) (hm.keeps hwf hXSa hXSd))) halloc hnd hdX hK
    (fun a ha => List.mem_append.mpr (.inl ha))
    (fun a ha => by
      by_cases hac : a = c
      · subst hac; exact .inr ⟨l, by simp [hpush]⟩
      · exact .inl (List.mem_append.mpr (.inr (List.mem_filter.mpr ⟨ha, by simpa using hac⟩))))
  refine ⟨op, Xf ++ X, hos, Af ++ A.filter (· ≠ c), Lw, ?_, hop, hcov, fun a ha => ?_, hK', hls, hvs, hn, ?_,
    fun l hl h => (hm.apart hwf hSa (fun l hl h => hSd l hl (List.mem_append.mpr (.inr h)))).2 l h hl, ?_⟩
  · rcases List.mem_cons.mp hc with h | h
    · cases h
    · exact h
  · rcases List.mem_append.mp ha with ha | ha
    · exact hAf a ha
    · obtain ⟨ha, hne⟩ := List.mem_filter.mp ha
      exact aimed_pop (haim a ha) (by simpa using hne)
  · intro l hl h
    simp only [List.mem_append] at h
    rcases h with (h | h) | h
    · exact hdL l h hl
    · exact hdw l hl (by simp [h])
    · exact hdw l hl (by simp [h])
  · exact (hm.widen hXa hd).relabel fun x => by simp only [List.mem_append, List.append_assoc]

theorem GenOk.transfer (hG : GenOk F ι O σf eN eY opN opY τy τb cz Γin Γout env Sin S Fz Rc)
    (hag : Agree σf σ' (Fz ++ S)) : GenOk F ι O σ' eN eY opN opY τy τb cz Γin Γout env Sin S Fz Rc :=
  { hG with
    hRcdet := fun σ1 Rc' Hc hag' => hG.hRcdet σ1 Rc' Hc (Agree.trans hag hag')
    hre := fun σ1 Eb Hc hag' => hG.hre σ1 Eb Hc (Agree.trans hag hag') }

/-- The activation around a generator rebuilt, once both sides are done, from its consumer's as it
ended and the trees its producer left at the places lent `mut`. -/
theorem GenOk.rebuild (hG : GenOk F ι O σf eN eY opN opY τy τb cz Γin Γout env Sin S Fz Rc)
    (hag : Agree σf σ1 (Fz ++ S)) (hc : CapsOk F ι σ1 cz Rc' Hc) (hdX : Disj (Fz ++ Hc) Eb) (hSH : Disj S Hc)
    (hnX : (Fz ++ Hc).Nodup) (hI : Inv F ι σ1 Γin env Eb Sin) :
    ∃ E', Inv F ι σ1 Γout env E' S ∧ ∀ z, z ∈ E' ↔ z ∈ Eb ∨ z ∈ Fz ∨ z ∈ Hc := by
  obtain rfl := hG.hRcdet σ1 Rc' Hc hag hc
  exact hG.hre σ1 Eb Hc hag hdX hSH hnX hc hI

theorem agree_after (hag : Agree σf σ0 (Xf ++ S)) (hm : Moves σ0 Ein σ1 E1 L) (hwf : WF σ0)
    (hXa : ∀ l ∈ Xf ++ S, σ0.mem l ≠ none) (hd : Disj (Xf ++ S) Ein) : Agree σf σ1 (Xf ++ S) :=
  Agree.trans hag (hm.keeps hwf hXa hd)

/-- A producer dropped as its consumer ended with `o`: what it left at the places lent `mut`, and the
consumer's activation as it ended, rebuild the activation around, and `o` goes on in it; if the
dropping unwinds past the barrier, `o`'s value is dropped. -/
theorem ret_genE (hG : GenOk F ι O σf eN eY opN opY τy τb cz Γin Γout env Sin S Fz Rc)
    (hIc : Inv F ι σf Γin env Eb Sin) (hdFE : Disj Fz Eb) (hSo : ∀ l ∈ So, l ∈ Fz ∨ l ∈ S)
    (ho : OutOk F ι σf τb o Lo) (hR : Ready O hs r) (hA : ∀ a ∈ o.aims, AimedIn a hs) (hwf : WF σ0)
    (hag : Agree σf σ0 (Fz ++ Eb ++ Lo ++ S)) (halloc : ∀ l ∈ Fz ++ Eb ++ Lo, σf.mem l ≠ none)
    (hnd : (Fz ++ Eb ++ Lo).Nodup) (hd : Disj (Fz ++ Eb ++ Lo) Ein) (hSa : ∀ l ∈ S, σ0.mem l ≠ none)
    (hSd : Disj S (Fz ++ Eb ++ Lo ++ Ein))
    (hp : Post F ι O σ0 Ein So (capsLvlΓ cz) (capsLvlEnv cz) .int r (.abort .drop d :: hs) res) :
    Post F ι O σ0 (Fz ++ Eb ++ Lo ++ Ein) S Γout env τb r hs (ret F O n hs (.genE τb o d) res) := by
  have hXa : ∀ l ∈ Fz ++ Eb ++ Lo, σ0.mem l ≠ none := fun l hl => by
    rw [hag l (List.mem_append.mpr (.inl hl))]; exact halloc l hl
  have hXSa : ∀ l ∈ Fz ++ Eb ++ Lo ++ S, σ0.mem l ≠ none := fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · exact hXa l h
    · exact hSa l h
  have hXSd : Disj (Fz ++ Eb ++ Lo ++ S) Ein := fun l hl h => by
    rcases List.mem_append.mp hl with hl | hl
    · exact hd l hl h
    · exact hSd l hl (List.mem_append.mpr (.inr h))
  have hnd3 := nodup_append_disj.mp hnd
  have hnd2 := nodup_append_disj.mp hnd3.1
  -- What is left of the dropped producer is what it left at the places lent `mut`; with the
  -- consumer's activation, the activation around.
  have back : ∀ {σ1 Ep L}, Inv F ι σ1 (capsLvlΓ cz) (capsLvlEnv cz) Ep So → Moves σ0 Ein σ1 Ep L →
      Agree σf σ1 (Fz ++ Eb ++ Lo ++ S) ∧ ∃ E', Inv F ι σ1 Γout env E' S ∧ (∀ z, z ∈ E' ↔ z ∈ Eb ∨ z ∈ Fz ∨ z ∈ Ep) ∧
        Disj Lo E' ∧ Moves σ0 (Fz ++ Eb ++ Lo ++ Ein) σ1 (E' ++ Lo) L := by
    intro σ1 Ep L hIb hm
    have hag1 : Agree σf σ1 (Fz ++ Eb ++ Lo ++ S) := Agree.trans hag (hm.keeps hwf hXSa hXSd)
    have hdX := (hm.apart hwf hXSa hXSd).1
    have hc := Foot.capsOk hG.hfns hIb.foot
    have hIc1 : Inv F ι σ1 Γin env Eb Sin := ⟨hIc.foot.frame (hag1.mono fun l hl => by
        rcases List.mem_append.mp hl with h | h
        · simp [h]
        · rcases hG.hSin l h with h | h <;> simp [h]), hIc.nodup, hIc.disj, hIc.keys, hag1.cur.trans hIc.cur⟩
    obtain ⟨E', hIo, hE'⟩ := hG.rebuild (hag1.mono fun l hl => by rcases List.mem_append.mp hl with h | h <;> simp [h])
      hc (fun l h1 h2 => by
        rcases List.mem_append.mp h1 with h1 | h1
        · exact hdFE l h1 h2
        · exact hdX l (by simp [h2]) h1)
      (fun l h1 h2 => hdX l (by simp [h1]) h2)
      (nodup_append_disj.mpr ⟨hnd2.1, hIb.nodup, fun l h1 h2 => hdX l (by simp [h1]) h2⟩) hIc1
    refine ⟨hag1, E', hIo, hE', fun l h1 h2 => ?_, ?_⟩
    · rcases (hE' l).mp h2 with h | h | h
      · exact hnd3.2.2 l (by simp [h]) h1
      · exact hnd3.2.2 l (by simp [h]) h1
      · exact hdX l (by simp [h1]) h
    · exact (hm.widen hXa hd).relabel fun x => by
        simp only [List.mem_append, hE']; grind
  have hdLS : Disj Lo S := fun l h1 h2 => hSd l h2 (by simp [h1])
  -- `o` goes on.
  have finish : ∀ {σ1 E'}, Agree σf σ1 (Fz ++ Eb ++ Lo ++ S) → Inv F ι σ1 Γout env E' S → Disj Lo E' →
      Moves σ0 (Fz ++ Eb ++ Lo ++ Ein) σ1 (E' ++ Lo) [] →
      Post F ι O σ0 (Fz ++ Eb ++ Lo ++ Ein) S Γout env τb r hs (o.res, σ1) := by
    intro σ1 E' hag1 hI1 hdLE hm1
    cases o with
    | val v =>
      exact ⟨E', Lo, hI1, (show VT F ι σf τb v Lo from ho).frame (hag1.mono fun l hl => by simp [hl]),
        hdLE, hdLS, hm1.relabel fun x => by simp⟩
    | abort j k =>
      obtain rfl : Lo = [] := ho
      exact ⟨hA j (by simp [Outcome.aims]), E', hI1, hm1.relabel fun x => by simp⟩
  rcases res with ⟨res, σ1⟩
  cases res with
  | val w =>
    obtain ⟨Ep, L, hIb, hw, -, -, hm⟩ := hp
    obtain rfl : L = [] := by cases hw; rfl
    obtain ⟨hag1, E', hIo, -, hdLE, hm1⟩ := back hIb hm
    simp only [ret]
    exact finish hag1 hIo hdLE hm1
  | abort j k =>
    obtain ⟨haim, Ep, hIb, hm⟩ := hp
    obtain ⟨hag1, E', hIo, -, hdLE, hm1⟩ := back hIb hm
    rw [ret.eq_def]
    simp only
    split
    · exact finish hag1 hIo hdLE hm1
    · rename_i hne
      have haim' := aimed_pop haim hne
      cases o with
      | abort j' k' =>
        obtain rfl : Lo = [] := ho
        exact ⟨haim', E', hIo, hm1.relabel fun x => by simp⟩
      | val u =>
        have hu : VT F ι σ1 τb u Lo := (show VT F ι σf τb u Lo from ho).frame (hag1.mono fun l hl => by simp [hl])
        obtain ⟨σ2, hdrop, hn, hfree, hkeep⟩ := drop_ok hm1.wf _ u Lo hu
        simp only [hdrop]
        refine ⟨haim', E', ⟨hIo.foot.frame (Agree.of' fun l hl => hkeep l fun h => ?_), hIo.nodup, hIo.disj, hIo.keys, by cur_inv⟩, ?_⟩
        · rcases List.mem_append.mp hl with hl | hl
          · exact hdLE l h hl
          · exact hdLS l h hl
        · exact (hm1.relabel (E'' := E' ++ Lo) (L'' := []) fun x => by simp).trans
            (Moves.free (E := E' ++ Lo) (E' := E') (D := Lo) (WF.of_free hm1.wf hn hfree hkeep) hn
              (fun l hl => (hm1.alloc l).mpr (.inr (.inl hl)))
              (fun x => by simp) hfree hkeep (fun l h1 h2 => hdLE l h2 h1)) disj_nil_left hwf |>.relabel
            fun x => by simp
  | susp j ef vs ls K =>
    simp only [ret]
    exact post_susp_abort (.genE hG hIc hdFE hSo ho) (fun _ => rfl) hR.2 hA hwf hag halloc hnd hd hSa hSd hp
  | stuck => simp [Post] at hp
  | timeout => simp [ret, Post]
  | panic => simp [ret, Post]

/-! ## The consumer, its producer ended -/

/-- A consumer whose producer has ended: what it asks is answered `#Done`; once it ends, the
activation is rebuilt from what the producer left at the places lent `mut`, which the frame keeps. -/
theorem ret_genCd (hKo : ∀ m, n = m + 1 → EvalKOk F O m ∧ RetOk F O m)
    (hG : GenOk F ι O σf eN eY opN opY τy τb cz Γin Γout env Sin S Fz Rc) (hc : CapsOk F ι σf cz Rc Hc)
    (hR : Ready O hs r) (hwf : WF σ0) (hag : Agree σf σ0 (Fz ++ Hc ++ S)) (halloc : ∀ l ∈ Fz ++ Hc, σf.mem l ≠ none)
    (hnd : (Fz ++ Hc).Nodup) (hd : Disj (Fz ++ Hc) Ein) (hSa : ∀ l ∈ S, σ0.mem l ≠ none)
    (hSd : Disj S (Fz ++ Hc ++ Ein))
    (hp : Post F ι O σ0 Ein Sin Γin env τb (.eff eN :: r) (.capture eN hid :: hs) res) :
    Post F ι O σ0 (Fz ++ Hc ++ Ein) S Γout env τb r hs (ret F O n hs (.genC eN eY hid τy τb none) res) := by
  -- The activation rebuilt from what the producer left, which the frame keeps.
  have hre' : ∀ σ1 Eb, Agree σf σ1 (Fz ++ Hc ++ S) → Disj (Fz ++ Hc) Eb → Inv F ι σ1 Γin env Eb Sin →
      ∃ E', Inv F ι σ1 Γout env E' S ∧ ∀ z, z ∈ E' ↔ z ∈ Eb ∨ z ∈ Fz ++ Hc := by
    intro σ1 Eb hag1 hdX hI'
    obtain ⟨E', hIo, hE'⟩ := hG.rebuild (hag1.mono fun l hl => by rcases List.mem_append.mp hl with h | h <;> simp [h])
      (hc.frame (hag1.mono fun l hl => by
        rcases List.mem_append.mp hl with h | h
        · rcases hG.hRc l h with h | h <;> simp [h]
        · simp [h])) hdX (fun l h1 h2 => hSd l h1 (by simp [h2])) hnd hI'
    exact ⟨E', hIo, fun z => by rw [hE']; simp only [List.mem_append]; try grind⟩
  have hframe : ∀ {σ'}, Agree σf σ' (Fz ++ Hc ++ S) →
      FrameOk F O ι ι σ' (.genC eN eY hid τy τb none) ⟨Γin, env, τb, Sin, .eff eN :: r⟩ ⟨Γout, env, τb, S, r⟩
        (Fz ++ Hc) [] := fun hag' =>
    .genCd (hG.transfer (hag'.mono fun l hl => by rcases List.mem_append.mp hl with h | h <;> simp [h]))
      (hc.frame (hag'.mono fun l hl => by
        rcases List.mem_append.mp hl with h | h
        · rcases hG.hRc l h with h | h <;> simp [h]
        · simp [h]))
  have hSin' : ∀ l ∈ Sin, l ∈ Fz ++ Hc ∨ l ∈ S := fun l hl => (hG.hSin l hl).imp_left fun h => by simp [h]
  generalize hW : Fz ++ Hc = W at hag halloc hnd hd hSd hre' hframe hSin' ⊢
  have hXa : ∀ l ∈ W, σ0.mem l ≠ none := fun l hl => by
    rw [hag l (List.mem_append.mpr (.inl hl))]; exact halloc l hl
  have hXSa : ∀ l ∈ W ++ S, σ0.mem l ≠ none := fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · exact hXa l h
    · exact hSa l h
  have hXSd : Disj (W ++ S) Ein := fun l hl h => by
    rcases List.mem_append.mp hl with hl | hl
    · exact hd l hl h
    · exact hSd l hl (List.mem_append.mpr (.inr h))
  rcases res with ⟨res, σ1⟩
  have pass : (∀ j ef vs ls K, res = .susp j ef vs ls K → j ≠ hid ∨ ef ≠ eN) →
      Post F ι O σ0 (W ++ Ein) S Γout env τb r hs (ret F O n hs (.genC eN eY hid τy τb none) (res, σ1)) := by
    intro hnot
    have : ret F O n hs (.genC eN eY hid τy τb none) (res, σ1) = passK (.genC eN eY hid τy τb none) (res, σ1) := by
      cases res with
      | susp j ef vs ls K => rw [ret.eq_def]; simp [passK, hnot j ef vs ls K rfl]
      | _ => simp [ret, passK]
    rw [this]
    refine post_pass (hframe Agree.self) hG.hS hre' hR.2 (fun a ha => aimed_uncap ha) ?_ hwf hag halloc hnd hd
      hSa hSd hp
    intro j ef vs ls K σ' h hc
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
  by_cases hc : j ≠ hid ∨ ef ≠ eN
  · exact pass fun _ _ _ _ _ h => by cases h; exact hc
  simp only [ne_eq, not_or, Decidable.not_not] at hc
  obtain ⟨h1, h2⟩ := hc
  subst j ef
  obtain ⟨op', X, hos, A, Lv, -, hop', -, haim, hK, hls, hvs, hLn, hdLX, hdLS, hm⟩ := hp
  obtain rfl : opN = op' := Option.some.inj (hG.hopN.symm.trans hop')
  rw [hG.hNowns] at hvs
  cases hvs
  obtain ⟨-, -, -, -, -, -, -, -, hts, -, -, hXn, -⟩ := hK.base_of
  rw [hG.hNrefs] at hts
  obtain rfl : hos = [] := List.map_eq_nil_iff.mp hts
  simp only [olds, mutCells, List.map_nil, List.flatMap_nil, List.append_nil, List.flatten_nil] at hm
  cases n with
  | zero => simp [ret, Post]
  | succ m =>
  obtain ⟨hKk, hRr⟩ := hKo m rfl
  have hwf₁ := hm.wf
  simp only [ret, ne_eq, not_true_eq_false, or_self, ↓reduceIte]
  generalize hb : (σ1.alloc (.int 0)).1 = b
  have hbn : b = σ1.next := hb.symm
  generalize hσ2 : (σ1.alloc (.int 0)).2 = σ2
  have hm2 : Moves σ1 X σ2 (X ++ [b]) [] := by
    rw [← hσ2, hbn]
    exact (Moves.allocate hwf₁ (fun l hl => (hm.alloc l).mpr (.inr (.inl hl)))).relabel fun x => by simp
  have hwf2 : WF σ2 := hm2.wf
  have hfresh : ∀ l, σ1.mem l ≠ none → l ≠ b := fun l h e => by
    subst e; rw [hbn] at h; exact Nat.lt_irrefl _ (hwf₁ _ h)
  have hag1 := agree_after hag hm hwf hXSa hXSd
  have hFS1 : ∀ l ∈ W ++ S, σ1.mem l ≠ none := fun l hl => by
    rw [hag1 l hl, ← hag l hl]; exact hXSa l hl
  have hS1 : ∀ l ∈ Sin, σ1.mem l ≠ none := fun l hl => hFS1 l (by
    rcases hSin' l hl with h | h <;> simp [h])
  have hXa1 : ∀ l ∈ X, σ1.mem l ≠ none := fun l hl => (hm.alloc l).mpr (.inr (.inl hl))
  have hold : ∀ l, σ1.mem l ≠ none → σ2.mem l = σ1.mem l := fun l h => by
    rw [← hσ2]; simp only [Store.alloc]; rw [if_neg (fun e => hfresh l h (by rw [hbn]; exact e))]
  have hrt2 : σ2.rt = σ1.rt := by rw [← hσ2]; rfl
  have hag12 : Agree σ1 σ2 (X ++ Sin) := Agree.of (fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · exact hold l (hXa1 l h)
    · exact hold l (hS1 l h)) hrt2
  have hbm : σ2.mem b = some (.int 0) := by rw [← hσ2, hbn]; simp [Store.alloc]
  have hdFX : Disj (W ++ S) X := (hm.apart hwf hXSa hXSd).1
  have hdSinX : Disj Sin X := fun l h1 h2 => hdFX l (by rcases hSin' l h1 with h | h <;> simp [h]) h2
  have hR' : Ready O (.capture eN hid :: hs) (.eff eN :: r) := (hframe Agree.self).ready hR
  have hres := value_resume (top := ⟨Γin, env, τb, Sin, .eff eN :: r⟩) (Lv := [b]) hKk hG.hNrefs hK hR' haim hwf2 hag12
    (fun l hl => by
      rcases List.mem_append.mp hl with h | h
      · exact hXa1 l h
      · exact hS1 l h) hXn
    (fun l h1 h2 => by
      rcases List.mem_append.mp h2 with h2 | h2
      · exact hdSinX l h1 h2
      · simp at h2; exact hfresh l (hS1 l h1) h2)
    (by rw [hG.hNret]; exact done_vt hbm hG.hcy)
    (fun l h1 h2 => by simp at h1; subst h1; exact hfresh _ (hXa1 _ h2) rfl)
  have hag2 : Agree σf σ2 (W ++ S) := Agree.trans hag1 (Agree.of (fun l hl => hold l (hFS1 l hl)) hrt2)
  have hFS2 : ∀ l ∈ W ++ S, σ2.mem l ≠ none := fun l hl => by rw [hold l (hFS1 l hl)]; exact hFS1 l hl
  have h2 := hRr hs _ _ σ2 (.genC eN eY hid τy τb none) ⟨Γin, env, τb, Sin, .eff eN :: r⟩ ⟨Γout, env, τb, S, r⟩
      W [] σ2 (X ++ [b]) _ (hframe hag2) hR (fun _ h => by simp at h) hwf2 Agree.self
      (fun l hl => hFS2 l (by simp [hl])) hnd
      (fun l h1 h2 => by
        rcases List.mem_append.mp h2 with h2 | h2
        · exact hdFX l (by simp [h1]) h2
        · simp at h2; exact hfresh l (hFS1 l (by simp [h1])) h2)
      (fun l hl => hFS2 l (by simp [hl]))
      (fun l h1 h2 => by
        simp only [List.mem_append, List.mem_singleton] at h2
        rcases h2 with h2 | h2 | h2
        · exact hSd l h1 (by simp [h2])
        · exact hdFX l (by simp [h1]) h2
        · exact hfresh l (hFS1 l (by simp [h1])) h2) hres
  have hm' := (hm.widen hXa hd).trans (hm2.widen (X := W) (fun l hl => hFS1 l (by simp [hl]))
    (fun l h1 h2 => hdFX l (by simp [h1]) h2)) disj_nil_left hwf
  exact post_after (hm'.relabel (E'' := W ++ (X ++ [b])) (L'' := []) fun x => by simp) hwf (by simpa using h2)




/-! ## The consumer, its producer waiting -/

/-- A consumer whose producer waits as `Kq`: what it asks resumes the producer; once it ends, with a
value or unwinding, the producer is dropped, and the activation then rebuilt from the consumer's and
what the producer left at the places lent `mut`. -/
theorem ret_genC (hKo : ∀ m, n = m + 1 → EvalKOk F O m ∧ RetOk F O m)
    (hG : GenOk F ι O σf eN eY opN opY τy τb cz Γin Γout env Sin S Fz Rc) (hSo : ∀ l ∈ So, l ∈ Fz ∨ l ∈ S)
    (hK : FramesOk F O ι σf Kq opY ⟨capsLvlΓ cz, capsLvlEnv cz, .int, So, .eff eY :: r⟩ Xp [] AK)
    (hR : Ready O hs r) (hA : ∀ a ∈ AK, AimedIn a hs) (hwf : WF σ0) (hag : Agree σf σ0 (Fz ++ Xp ++ S))
    (halloc : ∀ l ∈ Fz ++ Xp, σf.mem l ≠ none) (hnd : (Fz ++ Xp).Nodup) (hd : Disj (Fz ++ Xp) Ein)
    (hSa : ∀ l ∈ S, σ0.mem l ≠ none) (hSd : Disj S (Fz ++ Xp ++ Ein))
    (hp : Post F ι O σ0 Ein Sin Γin env τb (.eff eN :: r) (.capture eN hid :: hs) res) :
    Post F ι O σ0 (Fz ++ Xp ++ Ein) S Γout env τb r hs (ret F O n hs (.genC eN eY hid τy τb (some Kq)) res) := by
  have hXa : ∀ l ∈ Fz ++ Xp, σ0.mem l ≠ none := fun l hl => by
    rw [hag l (List.mem_append.mpr (.inl hl))]; exact halloc l hl
  have hXSa : ∀ l ∈ Fz ++ Xp ++ S, σ0.mem l ≠ none := fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · exact hXa l h
    · exact hSa l h
  have hXSd : Disj (Fz ++ Xp ++ S) Ein := fun l hl h => by
    rcases List.mem_append.mp hl with hl | hl
    · exact hd l hl h
    · exact hSd l hl (List.mem_append.mpr (.inr h))
  have hFX := nodup_append_disj.mp hnd
  have hfa : ∀ l ∈ Fz ++ Xp ++ S, σf.mem l ≠ none := fun l hl => by rw [← hag l hl]; exact hXSa l hl
  have inFS : ∀ {l}, l ∈ Fz ∨ l ∈ S → l ∈ Fz ++ Xp ++ S := fun h => by rcases h with h | h <;> simp [h]
  have hdSoX : Disj So Xp := fun l h1 h2 => by
    rcases hSo l h1 with h | h
    · exact hFX.2.2 l h h2
    · exact hSd l h (by simp [h2])
  have hSoa : ∀ l ∈ Xp ++ So, σf.mem l ≠ none := fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · exact hfa l (by simp [h])
    · exact hfa l (inFS (hSo l h))
  -- The producer dropped, the consumer having ended with `o`, its activation `Eb`.
  have dropP : ∀ m σ1 Eb Lo (o : Outcome), EvalKOk F O m → RetOk F O m → WF σ1 →
      Agree σf σ1 (Fz ++ Xp ++ S) → Inv F ι σ1 Γin env Eb Sin → Disj (Fz ++ Xp) Eb →
      OutOk F ι σ1 τb o Lo → (∀ a ∈ o.aims, AimedIn a hs) → Disj Lo (Fz ++ Eb ++ Xp) → Disj Lo S → Lo.Nodup →
      Post F ι O σ1 (Fz ++ Eb ++ Lo ++ Xp) S Γout env τb r hs
        (ret F O m hs (.genE τb o σ1.fresh.1) (ret F O m (.abort .drop σ1.fresh.1 :: hs) (.genY eY hid τy)
          (evalK F O m (.capture eY hid :: .abort .drop σ1.fresh.1 :: hs) σ1.fresh.2 Kq (.abort σ1.fresh.1 0)))) := by
    intro m σ1 Eb Lo o hKk hRr hwf1 hag1 hIc hdXE ho haims hdLo hdLoS hLon
    generalize hdd : σ1.fresh.1 = d
    have hwf2 : WF σ1.fresh.2 := hwf1
    have hag2 : Agree σf σ1.fresh.2 (Fz ++ Xp ++ S) := hag1.trans (Agree.of' fun _ _ => rfl)
    have hR2 : Ready O (.abort .drop d :: hs) r := ⟨.abort (by intro e h; cases h) hR.1, fun l hl => covers_cons _ hR.2 l hl⟩
    have hR3 : Ready O (.capture eY hid :: .abort .drop d :: hs) (.eff eY :: r) :=
      (FrameOk.genY (F := F) (ι := ι) (σf := σf) (Γ := capsLvlΓ cz) (env := capsLvlEnv cz) (τ := .int) (S := So)
        (hid := hid) hG.hopY hG.hYowns hG.hYrefs hG.hYret hG.hcy).ready hR2
    have h1 := hKk (.capture eY hid :: .abort .drop d :: hs) _ σf Kq _ Xp [] AK σ1.fresh.2 [] (.abort d 0) opY [] hK hR3
      (fun a ha => let ⟨l, hl⟩ := hA a ha; ⟨l, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hl)⟩) hwf2
      (hag2.mono fun l hl => by
        rcases List.mem_append.mp hl with h | h
        · simp [h]
        · exact inFS (hSo l h)) hSoa hFX.2.1 rfl (fun _ h => by simp at h) (by simp [mutCells])
      (by simp [mutCells, Disj]) (by simpa [mutCells] using hdSoX)
      (.inr ⟨d, 0, rfl, ⟨.drop, List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩, rfl⟩)
    simp only [mutCells, List.flatMap_nil, List.append_nil] at h1
    have hSo2 : ∀ l ∈ So, σ1.fresh.2.mem l ≠ none := fun l hl => by
      rw [hag2 l (inFS (hSo l hl))]; exact hfa l (inFS (hSo l hl))
    have h2 := hRr (.abort .drop d :: hs) _ _ σ1.fresh.2 (.genY eY hid τy) ⟨capsLvlΓ cz, capsLvlEnv cz, .int, So, .eff eY :: r⟩
      ⟨capsLvlΓ cz, capsLvlEnv cz, .int, So, r⟩ [] [] σ1.fresh.2 Xp _ (.genY hG.hopY hG.hYowns hG.hYrefs hG.hYret hG.hcy)
      hR2 (fun _ h => by simp at h) hwf2 Agree.self (fun _ h => by simp at h) List.nodup_nil disj_nil_left hSo2
      (by simpa using hdSoX) h1
    simp only [List.nil_append] at h2
    have hEba : ∀ l ∈ Eb, σ1.fresh.2.mem l ≠ none := fun l hl => hIc.alloc l hl
    have hLoa : ∀ l ∈ Lo, σ1.fresh.2.mem l ≠ none := fun l hl => by
      cases o with
      | val v => exact (show VT F ι σ1 τb v Lo from ho).alloc l hl
      | abort _ _ => obtain rfl : Lo = [] := ho; simp at hl
    have hFz2 : ∀ l ∈ Fz, σ1.fresh.2.mem l ≠ none := fun l hl => by
      rw [hag2 l (by simp [hl])]; exact hfa l (by simp [hl])
    have hS2 : ∀ l ∈ S, σ1.fresh.2.mem l ≠ none := fun l hl => by
      rw [hag2 l (by simp [hl])]; exact hfa l (by simp [hl])
    have hIc2 : Inv F ι σ1.fresh.2 Γin env Eb Sin :=
      ⟨hIc.foot.frame (Agree.of' fun _ _ => rfl), hIc.nodup, hIc.disj, hIc.keys, hIc.cur⟩
    have ho2 : OutOk F ι σ1.fresh.2 τb o Lo := by
      cases o with
      | val v => exact (show VT F ι σ1 τb v Lo from ho).frame (Agree.of' fun _ _ => rfl)
      | abort _ _ => exact ho
    have hdSE : Disj S Eb := fun l h1 h2 => hIc.disj l (hG.hS l h1) h2
    have hG2 := hG.transfer (hag2.mono fun l hl => by rcases List.mem_append.mp hl with h | h <;> simp [h])
    have h4 := ret_genE (n := m) hG2 hIc2 (fun l h1 h2 => hdXE l (by simp [h1]) h2) hSo ho2 hR haims hwf2 Agree.self
      (fun l hl => by
        simp only [List.mem_append] at hl
        rcases hl with (h | h) | h
        · exact hFz2 l h
        · exact hEba l h
        · exact hLoa l h)
      (by
        refine nodup_append_disj.mpr ⟨nodup_append_disj.mpr ⟨hFX.1, hIc.nodup, fun l h1 h2 => hdXE l (by simp [h1]) h2⟩,
          hLon, fun l h1 h2 => ?_⟩
        rcases List.mem_append.mp h1 with h1 | h1
        · exact hdLo l h2 (by simp [h1])
        · exact hdLo l h2 (by simp [h1]))
      (fun l h1 h2 => by
        simp only [List.mem_append] at h1
        rcases h1 with (h1 | h1) | h1
        · exact hFX.2.2 l h1 h2
        · exact hdXE l (by simp [h2]) h1
        · exact hdLo l h1 (by simp [h2])) hS2
      (fun l h1 h2 => by
        simp only [List.mem_append] at h2
        rcases h2 with ((h2 | h2) | h2) | h2
        · exact hSd l h1 (by simp [h2])
        · exact hdSE l h1 h2
        · exact hdLoS l h2 h1
        · exact hSd l h1 (by simp [h2])) h2
    exact post_after (Moves.freshen hwf1 fun l hl => by
      simp only [List.mem_append] at hl
      rcases hl with ((h | h) | h) | h
      · rw [hag1 l (by simp [h])]; exact hfa l (by simp [h])
      · exact hIc.alloc l h
      · cases o with
        | val v => exact (show VT F ι σ1 τb v Lo from ho).alloc l h
        | abort _ _ => obtain rfl : Lo = [] := ho; simp at h
      · rw [hag1 l (by simp [h])]; exact hfa l (by simp [h])) hwf1 h4
  rcases res with ⟨res, σ1⟩
  cases res with
  | val v =>
    obtain ⟨E', L, hI', hv, hdLE, hdLS, hm⟩ := hp
    have hag1 := agree_after hag hm hwf hXSa hXSd
    obtain ⟨hdE, hdL⟩ := hm.apart hwf hXSa hXSd
    cases n with
    | zero => rw [ret.eq_def]; simp [Post]
    | succ m =>
    obtain ⟨hKk, hRr⟩ := hKo m rfl
    have : ret F O (m + 1) hs (.genC eN eY hid τy τb (some Kq)) (.val v, σ1) =
        ret F O m hs (.genE τb (.val v) σ1.fresh.1) (ret F O m (.abort .drop σ1.fresh.1 :: hs) (.genY eY hid τy)
          (evalK F O m (.capture eY hid :: .abort .drop σ1.fresh.1 :: hs) σ1.fresh.2 Kq (.abort σ1.fresh.1 0))) := by
      rw [ret.eq_def]
    rw [this]
    have h := dropP m σ1 E' L (.val v) hKk hRr hm.wf hag1 hI' (fun l h1 h2 => hdE l (List.mem_append.mpr (.inl h1)) h2) hv
      (fun _ h => by simp [Outcome.aims] at h)
      (fun l h1 h2 => by
        simp only [List.mem_append] at h2
        rcases h2 with (h2 | h2) | h2
        · exact hdL l (by simp [h2]) h1
        · exact hdLE l h1 h2
        · exact hdL l (by simp [h2]) h1)
      (fun l h1 h2 => hdL l (by simp [h2]) h1) hv.nodup
    refine post_after ((hm.widen hXa hd).relabel fun x => ?_) hwf h
    simp only [List.mem_append, List.not_mem_nil, or_false]
    grind
  | abort j k =>
    obtain ⟨haim, E', hI', hm⟩ := hp
    have hag1 := agree_after hag hm hwf hXSa hXSd
    obtain ⟨hdE, -⟩ := hm.apart hwf hXSa hXSd
    cases n with
    | zero => rw [ret.eq_def]; simp [Post]
    | succ m =>
    obtain ⟨hKk, hRr⟩ := hKo m rfl
    have : ret F O (m + 1) hs (.genC eN eY hid τy τb (some Kq)) (.abort j k, σ1) =
        ret F O m hs (.genE τb (.abort j k) σ1.fresh.1) (ret F O m (.abort .drop σ1.fresh.1 :: hs) (.genY eY hid τy)
          (evalK F O m (.capture eY hid :: .abort .drop σ1.fresh.1 :: hs) σ1.fresh.2 Kq (.abort σ1.fresh.1 0))) := by
      rw [ret.eq_def]
    rw [this]
    have h := dropP m σ1 E' [] (.abort j k) hKk hRr hm.wf hag1 hI' (fun l h1 h2 => hdE l (List.mem_append.mpr (.inl h1)) h2) rfl
      (fun a ha => by simp [Outcome.aims] at ha; subst ha; exact aimed_uncap haim)
      disj_nil_left disj_nil_left List.nodup_nil
    refine post_after ((hm.widen hXa hd).relabel fun x => ?_) hwf h
    simp only [List.mem_append, List.not_mem_nil, or_false, List.append_nil]
    grind
  | susp j ef vs ls K =>
    by_cases hc : j ≠ hid ∨ ef ≠ eN
    · have : ret F O n hs (.genC eN eY hid τy τb (some Kq)) (.susp j ef vs ls K, σ1) =
          (.susp j ef vs ls (.genC eN eY hid τy τb (some Kq) :: K), σ1) := by
        rw [ret.eq_def]; simp [hc]
      rw [this]
      refine post_susp (.genC hG hSo hK) hR.2 (fun a ha => aimed_uncap ha) hA ?_ hwf hag halloc hnd hd hSa hSd hp
      intro h
      rcases List.mem_cons.mp h with h | h
      · simp only [Frame.capture.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp at hc
      · exact h
    simp only [ne_eq, not_or, Decidable.not_not] at hc
    obtain ⟨h1, h2⟩ := hc
    subst j ef
    obtain ⟨op', X, hos, A, Lv, -, hop', -, haim, hKc, hls, hvs, hLn, hdLX, hdLS, hm⟩ := hp
    obtain rfl : opN = op' := Option.some.inj (hG.hopN.symm.trans hop')
    rw [hG.hNowns] at hvs
    cases hvs
    obtain ⟨-, -, -, -, -, -, -, -, hts, -, -, hXn, -⟩ := hKc.base_of
    rw [hG.hNrefs] at hts
    obtain rfl : hos = [] := List.map_eq_nil_iff.mp hts
    simp only [olds, mutCells, List.map_nil, List.flatMap_nil, List.append_nil, List.flatten_nil] at hm
    cases n with
    | zero => rw [ret.eq_def]; simp [Post]
    | succ m =>
    obtain ⟨hKk, hRr⟩ := hKo m rfl
    have : ret F O (m + 1) hs (.genC eN eY hid τy τb (some Kq)) (.susp hid eN [] ls K, σ1) =
        ret F O m hs (.genP eN eY hid τy τb K) (evalK F O m (.capture eY hid :: hs) σ1 Kq (.val (.int 0))) := by
      rw [ret.eq_def]; simp
    rw [this]
    have hwf1 := hm.wf
    have hag1 := agree_after hag hm hwf hXSa hXSd
    obtain ⟨hdE, -⟩ := hm.apart hwf hXSa hXSd
    have hR3 : Ready O (.capture eY hid :: hs) (.eff eY :: r) :=
      (FrameOk.genY (F := F) (ι := ι) (σf := σf) (Γ := capsLvlΓ cz) (env := capsLvlEnv cz) (τ := .int) (S := So)
        (hid := hid) hG.hopY hG.hYowns hG.hYrefs hG.hYret hG.hcy).ready hR
    have hres := yield_resume (top := ⟨capsLvlΓ cz, capsLvlEnv cz, .int, So, .eff eY :: r⟩) hKk hG.hopY hG.hYrefs
      hG.hYret hK hR3 (fun a ha => let ⟨l, hl⟩ := hA a ha; ⟨l, List.mem_cons_of_mem _ hl⟩) hwf1
      (hag1.mono fun l hl => by
        rcases List.mem_append.mp hl with h | h
        · simp [h]
        · exact inFS (hSo l h)) hSoa hFX.2.1 hdSoX
    have hG1 := hG.transfer (hag1.mono fun l hl => by rcases List.mem_append.mp hl with h | h <;> simp [h])
    have hFXa1 : ∀ l ∈ Fz ++ Xp ++ S, σ1.mem l ≠ none := fun l hl => by rw [hag1 l hl]; exact hfa l hl
    have hXa1 : ∀ l ∈ X, σ1.mem l ≠ none := fun l hl => (hm.alloc l).mpr (.inr (.inl hl))
    have h2 := hRr hs _ _ σ1 (.genP eN eY hid τy τb K) ⟨capsLvlΓ cz, capsLvlEnv cz, .int, So, .eff eY :: r⟩
      ⟨Γout, env, τb, S, r⟩ (Fz ++ X) A σ1 Xp _ (.genP hG1 hSo hKc) hR (fun a ha => aimed_uncap (haim a ha)) hwf1
      Agree.self
      (fun l hl => by
        rcases List.mem_append.mp hl with h | h
        · exact hFXa1 l (by simp [h])
        · exact hXa1 l h)
      (nodup_append_disj.mpr ⟨hFX.1, hXn, fun l h1 h2 => hdE l (by simp [h1]) h2⟩)
      (fun l h1 h2 => by
        rcases List.mem_append.mp h1 with h1 | h1
        · exact hFX.2.2 l h1 h2
        · exact hdE l (by simp [h2]) h1)
      (fun l hl => hFXa1 l (by simp [hl]))
      (fun l h1 h2 => by
        simp only [List.mem_append] at h2
        rcases h2 with (h2 | h2) | h2
        · exact hSd l h1 (by simp [h2])
        · exact hdE l (by simp [h1]) h2
        · exact hSd l h1 (by simp [h2])) hres
    refine post_after ((hm.widen hXa hd).relabel fun x => ?_) hwf h2
    simp only [List.mem_append, List.not_mem_nil, or_false]
    grind
  | stuck => simp [Post] at hp
  | timeout => rw [ret.eq_def]; simp [Post]
  | panic => rw [ret.eq_def]; simp [Post]

/-! ## The producer, its consumer waiting -/

/-- `#Some(v)`, `v` moved into a cell of its own. -/
theorem some_vt (hb : σ.mem b = some v) (hv : VT F ι σ τy v L) (hbL : b ∉ L) :
    VT F ι σ (.sum .int τy) (.tag .int τy false b) (b :: L) :=
  .tag (LT.of_contents hb hv hbL) rfl hv.complete

/-- A producer whose consumer waits as `Kc` for what it asked: what it yields answers it; once it
ends, its consumer's asking is answered `#Done`, the frame keeping what it left at the places lent
`mut`; if it fails, its consumer is dropped and the activation rebuilt, before the failure goes on. -/
theorem ret_genP (hKo : ∀ m, n = m + 1 → EvalKOk F O m ∧ RetOk F O m)
    (hG : GenOk F ι O σf eN eY opN opY τy τb cz Γin Γout env Sin S Fz Rc) (hSo : ∀ l ∈ So, l ∈ Fz ∨ l ∈ S)
    (hKc : FramesOk F O ι σf Kc opN ⟨Γin, env, τb, Sin, .eff eN :: r⟩ Xc [] AK)
    (hR : Ready O hs r) (hA : ∀ a ∈ AK, AimedIn a hs) (hwf : WF σ0) (hag : Agree σf σ0 (Fz ++ Xc ++ S))
    (halloc : ∀ l ∈ Fz ++ Xc, σf.mem l ≠ none) (hnd : (Fz ++ Xc).Nodup) (hd : Disj (Fz ++ Xc) Ein)
    (hSa : ∀ l ∈ S, σ0.mem l ≠ none) (hSd : Disj S (Fz ++ Xc ++ Ein))
    (hp : Post F ι O σ0 Ein So (capsLvlΓ cz) (capsLvlEnv cz) .int (.eff eY :: r) (.capture eY hid :: hs) res) :
    Post F ι O σ0 (Fz ++ Xc ++ Ein) S Γout env τb r hs (ret F O n hs (.genP eN eY hid τy τb Kc) res) := by
  have hXa : ∀ l ∈ Fz ++ Xc, σ0.mem l ≠ none := fun l hl => by
    rw [hag l (List.mem_append.mpr (.inl hl))]; exact halloc l hl
  have hXSa : ∀ l ∈ Fz ++ Xc ++ S, σ0.mem l ≠ none := fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · exact hXa l h
    · exact hSa l h
  have hXSd : Disj (Fz ++ Xc ++ S) Ein := fun l hl h => by
    rcases List.mem_append.mp hl with hl | hl
    · exact hd l hl h
    · exact hSd l hl (List.mem_append.mpr (.inr h))
  have hFX := nodup_append_disj.mp hnd
  have hfa : ∀ l ∈ Fz ++ Xc ++ S, σf.mem l ≠ none := fun l hl => by rw [← hag l hl]; exact hXSa l hl
  have inFS : ∀ {l}, l ∈ Fz ∨ l ∈ S → l ∈ Fz ++ Xc ++ S := fun h => by rcases h with h | h <;> simp [h]
  have hdSinX : Disj Sin Xc := fun l h1 h2 => by
    rcases hG.hSin l h1 with h | h
    · exact hFX.2.2 l h h2
    · exact hSd l h (by simp [h2])
  have hSina : ∀ l ∈ Xc ++ Sin, σf.mem l ≠ none := fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · exact hfa l (by simp [h])
    · exact hfa l (inFS (hG.hSin l h))
  have hRc : Ready O (.capture eN hid :: hs) (.eff eN :: r) := (FrameOk.genN (F := F) (ι := ι) (σf := σf) (Γ := Γin) (env := env) (τ := τb) (S := Sin) (hid := hid) hG.hopN
      hG.hNowns hG.hNrefs hG.hNret hG.hcy).ready hR
  -- The consumer resumed with what it asked, `w`, owning `Lw`.
  have resumeC : ∀ m σ2 w Lw, EvalKOk F O m → WF σ2 → Agree σf σ2 (Fz ++ Xc ++ S) →
      VT F ι σ2 (.sum .int τy) w Lw → Disj Lw (Fz ++ Xc ++ S) →
      Post F ι O σ2 (Xc ++ Lw) Sin Γin env τb (.eff eN :: r) (.capture eN hid :: hs)
        (evalK F O m (.capture eN hid :: hs) σ2 Kc (.val w)) := by
    intro m σ2 w Lw hKk hwf2 hag2 hw hdw
    exact value_resume (top := ⟨Γin, env, τb, Sin, .eff eN :: r⟩) hKk hG.hNrefs hKc hRc
      (fun a ha => let ⟨l, hl⟩ := hA a ha; ⟨l, List.mem_cons_of_mem _ hl⟩) hwf2
      (hag2.mono fun l hl => by
        rcases List.mem_append.mp hl with h | h
        · simp [h]
        · exact inFS (hG.hSin l h)) hSina hFX.2.1
      (fun l h1 h2 => by
        rcases List.mem_append.mp h2 with h2 | h2
        · exact hdSinX l h1 h2
        · exact hdw l h2 (inFS (hG.hSin l h1)))
      (by rw [hG.hNret]; exact hw) (fun l h1 h2 => hdw l h1 (by simp [h2]))
  rcases res with ⟨res, σ1⟩
  cases res with
  | val u =>
    obtain ⟨Ep, L, hIb, hu, -, -, hm⟩ := hp
    obtain rfl : L = [] := by cases hu; rfl
    cases n with
    | zero => rw [ret.eq_def]; simp [Post]
    | succ m =>
    obtain ⟨hKk, hRr⟩ := hKo m rfl
    have : ret F O (m + 1) hs (.genP eN eY hid τy τb Kc) (.val u, σ1) =
        ret F O m hs (.genC eN eY hid τy τb none) (evalK F O m (.capture eN hid :: hs) (σ1.alloc (.int 0)).2 Kc
          (.val (.tag .int τy true (σ1.alloc (.int 0)).1))) := by
      rw [ret.eq_def]
    rw [this]
    have hwf1 := hm.wf
    have hag1 := agree_after hag hm hwf hXSa hXSd
    obtain ⟨hdE, -⟩ := hm.apart hwf hXSa hXSd
    -- What the producer left at the places lent it, which the frame now keeps.
    have hG1 := hG.transfer (hag1.mono fun l hl => by rcases List.mem_append.mp hl with h | h <;> simp [h])
    have hc := Foot.capsOk hG.hfns hIb.foot
    rw [hG1.hRcdet σ1 So Ep Agree.self hc] at hc
    generalize hb : (σ1.alloc (.int 0)).1 = b
    have hbn : b = σ1.next := hb.symm
    generalize hσ2 : (σ1.alloc (.int 0)).2 = σ2
    have hfresh : ∀ l, σ1.mem l ≠ none → l ≠ b := fun l h e => by
      subst e; rw [hbn] at h; exact Nat.lt_irrefl _ (hwf1 _ h)
    have hold : ∀ l, σ1.mem l ≠ none → σ2.mem l = σ1.mem l := fun l h => by
      rw [← hσ2]; simp only [Store.alloc]; rw [if_neg (fun e => hfresh l h (by rw [hbn]; exact e))]
    have hrt2 : σ2.rt = σ1.rt := by rw [← hσ2]; rfl
    have hwf2 : WF σ2 := by rw [← hσ2]; exact hwf1.alloc
    have hFa1 : ∀ l ∈ Fz ++ Xc ++ S, σ1.mem l ≠ none := fun l hl => by rw [hag1 l hl]; exact hfa l hl
    have hEa1 : ∀ l ∈ Ep, σ1.mem l ≠ none := fun l hl => hIb.alloc l hl
    have hag12 : ∀ T : List Nat, (∀ l ∈ T, σ1.mem l ≠ none) → Agree σ1 σ2 T := fun T hT =>
      Agree.of (fun l hl => hold l (hT l hl)) hrt2
    have hag2 : Agree σf σ2 (Fz ++ Xc ++ S) := hag1.trans (hag12 _ hFa1)
    have hbm : σ2.mem b = some (.int 0) := by rw [← hσ2, hbn]; simp [Store.alloc]
    have hres := resumeC m σ2 _ [b] hKk hwf2 hag2 (done_vt hbm hG.hcy)
      (fun l h1 h2 => by simp at h1; subst h1; exact hfresh _ (hFa1 _ h2) rfl)
    have hFEa : ∀ l ∈ Fz ++ Ep, σ1.mem l ≠ none := fun l hl => by
      rcases List.mem_append.mp hl with h | h
      · exact hFa1 l (by simp [h])
      · exact hEa1 l h
    have h2 := hRr hs _ _ σ1 (.genC eN eY hid τy τb none) ⟨Γin, env, τb, Sin, .eff eN :: r⟩ ⟨Γout, env, τb, S, r⟩
      (Fz ++ Ep) [] σ2 (Xc ++ [b]) _ (.genCd hG1 hc) hR (fun _ h => by simp at h) hwf2
      (hag12 _ fun l hl => by
        rcases List.mem_append.mp hl with h | h
        · exact hFEa l h
        · exact hFa1 l (by simp [h]))
      hFEa (nodup_append_disj.mpr ⟨hFX.1, hIb.nodup, fun l h1 h2 => hdE l (by simp [h1]) h2⟩)
      (fun l h1 h2 => by
        simp only [List.mem_append, List.mem_singleton] at h1 h2
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exact hFX.2.2 l h1 h2
        · exact hfresh l (hFa1 l (by simp [h1])) h2
        · exact hdE l (by simp [h2]) h1
        · exact hfresh l (hEa1 l h1) h2)
      (fun l hl => by rw [hold l (hFa1 l (by simp [hl]))]; exact hFa1 l (by simp [hl]))
      (fun l h1 h2 => by
        simp only [List.mem_append, List.mem_singleton] at h2
        rcases h2 with (h2 | h2) | h2 | h2
        · exact hSd l h1 (by simp [h2])
        · exact hdE l (by simp [h1]) h2
        · exact hSd l h1 (by simp [h2])
        · exact hfresh l (hFa1 l (by simp [h1])) h2) hres
    have hm2 : Moves σ1 (Fz ++ Xc ++ Ep) σ2 (Fz ++ Xc ++ Ep ++ [b]) [] := by
      rw [← hσ2, hbn]
      exact (Moves.allocate hwf1 (fun l hl => by
        rcases List.mem_append.mp hl with h | h
        · exact hFa1 l (List.mem_append.mpr (.inl h))
        · exact hEa1 l h)).relabel fun x => by
          simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false]
    have hm' := (hm.widen hXa hd).trans hm2 disj_nil_left hwf
    exact post_after (hm'.relabel fun x => by
      simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false, List.append_nil]; grind) hwf h2
  | abort j k =>
    obtain ⟨haim, Ep, hIb, hm⟩ := hp
    cases n with
    | zero => rw [ret.eq_def]; simp [Post]
    | succ m =>
    obtain ⟨hKk, hRr⟩ := hKo m rfl
    have : ret F O (m + 1) hs (.genP eN eY hid τy τb Kc) (.abort j k, σ1) =
        ret F O m hs .lendK (dropRet τb (.abort j k) σ1.fresh.1 (ret F O m (.abort .drop σ1.fresh.1 :: hs) (.genN eN hid τy)
          (evalK F O m (.capture eN hid :: .abort .drop σ1.fresh.1 :: hs) σ1.fresh.2 Kc (.abort σ1.fresh.1 0)))) := by
      rw [ret.eq_def]
    rw [this]
    generalize hdd : σ1.fresh.1 = d
    have hwf1 := hm.wf
    have hag1 := agree_after hag hm hwf hXSa hXSd
    obtain ⟨hdE, -⟩ := hm.apart hwf hXSa hXSd
    have hwf2 : WF σ1.fresh.2 := hwf1
    have hag2 : Agree σf σ1.fresh.2 (Fz ++ Xc ++ S) := hag1.trans (Agree.of' fun _ _ => rfl)
    have hR2 : Ready O (.abort .drop d :: hs) r := ⟨.abort (by intro e h; cases h) hR.1, fun l hl => covers_cons _ hR.2 l hl⟩
    have hR3 : Ready O (.capture eN hid :: .abort .drop d :: hs) (.eff eN :: r) :=
      (FrameOk.genN (F := F) (ι := ι) (σf := σf) (Γ := Γin) (env := env) (τ := τb) (S := Sin) (hid := hid) hG.hopN
        hG.hNowns hG.hNrefs hG.hNret hG.hcy).ready hR2
    have h1 := hKk (.capture eN hid :: .abort .drop d :: hs) _ σf Kc _ Xc [] AK σ1.fresh.2 [] (.abort d 0) opN [] hKc hR3
      (fun a ha => let ⟨l, hl⟩ := hA a ha; ⟨l, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hl)⟩) hwf2
      (hag2.mono fun l hl => by
        rcases List.mem_append.mp hl with h | h
        · simp [h]
        · exact inFS (hG.hSin l h)) hSina hFX.2.1 rfl (fun _ h => by simp at h) (by simp [mutCells])
      (by simp [mutCells, Disj]) (by simpa [mutCells] using hdSinX)
      (.inr ⟨d, 0, rfl, ⟨.drop, List.mem_cons_of_mem _ (List.mem_cons_self ..)⟩, rfl⟩)
    simp only [mutCells, List.flatMap_nil, List.append_nil] at h1
    have hSin2 : ∀ l ∈ Sin, σ1.fresh.2.mem l ≠ none := fun l hl => by
      rw [hag2 l (inFS (hG.hSin l hl))]; exact hfa l (inFS (hG.hSin l hl))
    have h2 := hRr (.abort .drop d :: hs) _ _ σ1.fresh.2 (.genN eN hid τy) ⟨Γin, env, τb, Sin, .eff eN :: r⟩
      ⟨Γin, env, τb, Sin, r⟩ [] [] σ1.fresh.2 Xc _ (.genN hG.hopN hG.hNowns hG.hNrefs hG.hNret hG.hcy) hR2
      (fun _ h => by simp at h) hwf2 Agree.self (fun _ h => by simp at h) List.nodup_nil disj_nil_left hSin2
      (by simpa using hdSinX) h1
    simp only [List.nil_append] at h2
    rw [dropRet_eq (F := F) (O := O) (n := m) (hs := hs)]
    have h3 := ret_dropK (τ' := τb) (n := m) (k := k) (aimed_uncap haim) hR.2 hwf2 h2
    have hFa1 : ∀ l ∈ Fz ++ Xc ++ S, σ1.mem l ≠ none := fun l hl => by rw [hag1 l hl]; exact hfa l hl
    have hEa1 : ∀ l ∈ Ep, σ1.mem l ≠ none := fun l hl => hIb.alloc l hl
    have hFEa : ∀ l ∈ Fz ++ Ep, σ1.fresh.2.mem l ≠ none := fun l hl => by
      rcases List.mem_append.mp hl with h | h
      · exact hFa1 l (by simp [h])
      · exact hEa1 l h
    have hS2 : ∀ l ∈ S, σ1.fresh.2.mem l ≠ none := fun l hl => hFa1 l (by simp [hl])
    have hnFE : (Fz ++ Ep).Nodup :=
      nodup_append_disj.mpr ⟨hFX.1, hIb.nodup, fun l h1 h2 => hdE l (by simp [h1]) h2⟩
    -- The activation rebuilt from the consumer's, as it was dropped, and what the producer left.
    have hG2 := hG.transfer (hag2.mono fun l hl => by rcases List.mem_append.mp hl with h | h <;> simp [h])
    have hc2 : CapsOk F ι σ1.fresh.2 cz So Ep := (Foot.capsOk hG.hfns hIb.foot).frame (Agree.of' fun _ _ => rfl)
    have hre' : ∀ σ3 Eb, Agree σ1.fresh.2 σ3 (Fz ++ Ep ++ S) → Disj (Fz ++ Ep) Eb → Inv F ι σ3 Γin env Eb Sin →
        ∃ E', Inv F ι σ3 Γout env E' S ∧ ∀ z, z ∈ E' ↔ z ∈ Eb ∨ z ∈ Fz ++ Ep := by
      intro σ3 Eb hag3 hdX hI'
      obtain ⟨E', hIo, hE'⟩ := hG2.rebuild (hag3.mono fun l hl => by rcases List.mem_append.mp hl with h | h <;> simp [h])
        (hc2.frame (hag3.mono fun l hl => by
          rcases List.mem_append.mp hl with h | h
          · rcases hSo l h with h | h <;> simp [h]
          · simp [h])) hdX (fun l h1 h2 => hdE l (by simp [h1]) h2) hnFE hI'
      exact ⟨E', hIo, fun z => by rw [hE']; simp only [List.mem_append]; try grind⟩
    have h4 := ret_lendK (n := m) (σf := σ1.fresh.2) (Xf := Fz ++ Ep)
      (fun l hl => (hG.hSin l hl).imp_left fun h => by simp [h]) hG.hS hre' hR.2 hwf2 Agree.self hFEa hnFE
      (fun l h1 h2 => by
        rcases List.mem_append.mp h1 with h1 | h1
        · exact hFX.2.2 l h1 h2
        · exact hdE l (by simp [h2]) h1) hS2
      (fun l h1 h2 => by
        simp only [List.mem_append] at h2
        rcases h2 with (h2 | h2) | h2
        · exact hSd l h1 (by simp [h2])
        · exact hdE l (by simp [h1]) h2
        · exact hSd l h1 (by simp [h2])) h3
    have hm' : Moves σ0 (Fz ++ Xc ++ Ein) σ1.fresh.2 (Fz ++ Ep ++ Xc) [] :=
      ((hm.widen hXa hd).relabel (E'' := Fz ++ Ep ++ Xc) (L'' := []) fun x => by
        simp only [List.mem_append, List.not_mem_nil, or_false]; grind).trans
        (Moves.freshen hwf1 fun l hl => by
          rcases List.mem_append.mp hl with h | h
          · exact hFEa l h
          · exact hFa1 l (by simp [h])) disj_nil_left hwf |>.relabel
        fun x => by simp
    exact post_after hm' hwf h4
  | susp j ef vs ls K =>
    by_cases hc : j ≠ hid ∨ ef ≠ eY
    · have : ret F O n hs (.genP eN eY hid τy τb Kc) (.susp j ef vs ls K, σ1) =
          (.susp j ef vs ls (.genP eN eY hid τy τb Kc :: K), σ1) := by
        rw [ret.eq_def]; simp [hc]
      rw [this]
      refine post_susp (.genP hG hSo hKc) hR.2 (fun a ha => aimed_uncap ha) hA ?_ hwf hag halloc hnd hd hSa hSd hp
      intro h
      rcases List.mem_cons.mp h with h | h
      · simp only [Frame.capture.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp at hc
      · exact h
    simp only [ne_eq, not_or, Decidable.not_not] at hc
    obtain ⟨h1, h2⟩ := hc
    subst j ef
    obtain ⟨op', X, hos, A, Lv, -, hop', -, haim, hK, hls, hvs, hLn, hdLX, hdLS, hm⟩ := hp
    obtain rfl : opY = op' := Option.some.inj (hG.hopY.symm.trans hop')
    rw [hG.hYowns] at hvs
    cases hvs with
    | cons hv hrest =>
    cases hrest
    rename_i v L
    obtain ⟨-, -, -, -, -, -, -, -, hts, -, -, hXn, -⟩ := hK.base_of
    rw [hG.hYrefs] at hts
    obtain rfl : hos = [] := List.map_eq_nil_iff.mp hts
    simp only [olds, mutCells, List.map_nil, List.flatMap_nil, List.append_nil, List.flatten_cons,
      List.flatten_nil] at hm hdLX hdLS hLn
    cases n with
    | zero => rw [ret.eq_def]; simp [Post]
    | succ m =>
    obtain ⟨hKk, hRr⟩ := hKo m rfl
    have : ret F O (m + 1) hs (.genP eN eY hid τy τb Kc) (.susp hid eY [v] ls K, σ1) =
        ret F O m hs (.genC eN eY hid τy τb (some K)) (evalK F O m (.capture eN hid :: hs) (σ1.alloc v).2 Kc
          (.val (.tag .int τy false (σ1.alloc v).1))) := by
      rw [ret.eq_def]; simp
    rw [this]
    have hwf1 := hm.wf
    have hag1 := agree_after hag hm hwf hXSa hXSd
    obtain ⟨hdE, hdL⟩ := hm.apart hwf hXSa hXSd
    generalize hb : (σ1.alloc v).1 = b
    have hbn : b = σ1.next := hb.symm
    generalize hσ2 : (σ1.alloc v).2 = σ2
    have hfresh : ∀ l, σ1.mem l ≠ none → l ≠ b := fun l h e => by
      subst e; rw [hbn] at h; exact Nat.lt_irrefl _ (hwf1 _ h)
    have hold : ∀ l, σ1.mem l ≠ none → σ2.mem l = σ1.mem l := fun l h => by
      rw [← hσ2]; simp only [Store.alloc]; rw [if_neg (fun e => hfresh l h (by rw [hbn]; exact e))]
    have hrt2 : σ2.rt = σ1.rt := by rw [← hσ2]; rfl
    have hwf2 : WF σ2 := by rw [← hσ2]; exact hwf1.alloc
    have hFa1 : ∀ l ∈ Fz ++ Xc ++ S, σ1.mem l ≠ none := fun l hl => by rw [hag1 l hl]; exact hfa l hl
    have hXa1 : ∀ l ∈ X, σ1.mem l ≠ none := fun l hl => (hm.alloc l).mpr (.inr (.inl hl))
    have hLa1 : ∀ l ∈ L, σ1.mem l ≠ none := hv.alloc
    have hag12 : ∀ T : List Nat, (∀ l ∈ T, σ1.mem l ≠ none) → Agree σ1 σ2 T := fun T hT =>
      Agree.of (fun l hl => hold l (hT l hl)) hrt2
    have hbm : σ2.mem b = some v := by rw [← hσ2, hbn]; simp [Store.alloc]
    have hbL : b ∉ L := fun h => hfresh b (hLa1 b h) rfl
    have hw := some_vt hbm (hv.frame (hag12 L hLa1)) hbL
    have hres := resumeC m σ2 _ (b :: L) hKk hwf2 (hag1.trans (hag12 _ hFa1)) hw
      (fun l h1 h2 => by
        rcases List.mem_cons.mp h1 with rfl | h1
        · exact hfresh _ (hFa1 _ h2) rfl
        · exact hdL l h2 h1)
    have hG1 := hG.transfer (hag1.mono fun l hl => by rcases List.mem_append.mp hl with h | h <;> simp [h])
    have hSo1 : ∀ l ∈ So, l ∈ Fz ∨ l ∈ S := hSo
    have h2 := hRr hs _ _ σ1 (.genC eN eY hid τy τb (some K)) ⟨Γin, env, τb, Sin, .eff eN :: r⟩ ⟨Γout, env, τb, S, r⟩
      (Fz ++ X) A σ2 (Xc ++ (b :: L)) _ (.genC hG1 hSo1 hK) hR (fun a ha => aimed_uncap (haim a ha)) hwf2
      (hag12 _ fun l hl => by
        simp only [List.mem_append] at hl
        rcases hl with (h | h) | h
        · exact hFa1 l (by simp [h])
        · exact hXa1 l h
        · exact hFa1 l (by simp [h]))
      (fun l hl => by
        rcases List.mem_append.mp hl with h | h
        · exact hFa1 l (by simp [h])
        · exact hXa1 l h)
      (nodup_append_disj.mpr ⟨hFX.1, hXn, fun l h1 h2 => hdE l (by simp [h1]) h2⟩)
      (fun l h1 h2 => by
        simp only [List.mem_append, List.mem_cons] at h1 h2
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | rfl | h2
        · exact hFX.2.2 l h1 h2
        · exact hfresh _ (hFa1 _ (by simp [h1])) rfl
        · exact hdL l (by simp [h1]) h2
        · exact hdE l (by simp [h2]) h1
        · exact hfresh _ (hXa1 _ h1) rfl
        · exact hdLX l h2 h1)
      (fun l hl => by rw [hold l (hFa1 l (by simp [hl]))]; exact hFa1 l (by simp [hl]))
      (fun l h1 h2 => by
        simp only [List.mem_append, List.mem_cons] at h2
        rcases h2 with (h2 | h2) | h2 | rfl | h2
        · exact hSd l h1 (by simp [h2])
        · exact hdE l (by simp [h1]) h2
        · exact hSd l h1 (by simp [h2])
        · exact hfresh _ (hFa1 _ (by simp [h1])) rfl
        · exact hdL l (by simp [h1]) h2) hres
    have hm2 : Moves σ1 (Fz ++ Xc ++ X ++ L) σ2 (Fz ++ Xc ++ X ++ L ++ [b]) [] := by
      rw [← hσ2, hbn]
      exact (Moves.allocate hwf1 (fun l hl => by
        simp only [List.mem_append] at hl
        rcases hl with ((h | h) | h) | h
        · exact hFa1 l (by simp [h])
        · exact hFa1 l (by simp [h])
        · exact hXa1 l h
        · exact hLa1 l h)).relabel fun x => by
          simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false]
    have hm' := ((hm.widen hXa hd).relabel (E'' := Fz ++ Xc ++ X ++ L) (L'' := []) fun x => by
      simp only [List.mem_append, List.not_mem_nil, or_false] <;> grind).trans hm2 disj_nil_left hwf
    exact post_after (hm'.relabel fun x => by
      simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, List.append_nil]; grind)
      hwf h2
  | stuck => simp [Post] at hp
  | timeout => rw [ret.eq_def]; simp [Post]
  | panic => rw [ret.eq_def]; simp [Post]


theorem zip_refs_at : ∀ {caps : List (Cap Place)} {ls : List Nat}, ls.length = caps.length →
    ((caps.map Cap.sig).map Prod.fst).zip ls = capsLvlEnv (List.zipWith Cap.at caps ls)
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    have ih := zip_refs_at h
    simp only [capsLvlEnv] at ih
    simp only [capsLvlEnv, List.map_cons, List.zipWith_cons_cons, List.zip_cons_cons, Cap.at, Cap.sig, ih]

/-! ## A generator started -/

/-- `gen`: the producer's arguments taken, its parameters allocated and the places it is lent
resolved, it waits as if it had yielded just before its body; the consumer runs with the places lent
`mut` out of reach and those lent `readonly` frozen. -/
theorem gen_ok (hF : FnsOk F O) (hE : EvalOk F O n) (hR : RetOk F O n)
    (hopN : O[eN]? = some opN) (hNowns : opN.owns = []) (hNrefs : opN.refs = []) (hNret : opN.ret = .sum .int τy)
    (hopY : O[eY]? = some opY) (hYowns : opY.owns = [τy]) (hYrefs : opY.refs = []) (hYret : opY.ret = .int)
    (hcy : τy.complete = true) (hfd : F[f]? = some d) (hretp : d.retp = none) (hcap : d.cap = none)
    (hdret : d.ret = .int) (hrow : ∀ l ∈ d.row, l ∈ .eff eY :: r) (hey : Label.eff eY ∈ d.row)
    (hdrefs : d.refs = caps.map Cap.sig) (hargs : AtomsTy Γ owned (d.owns.map Prod.snd) Γ₁)
    (hcaps : Caps Γ₁ caps ys) (hexcl : Exclusive ys)
    (hb : Typed F O (freeze (hideAll Γ₁ (roots .mut ys)) (roots .ro ys)) body τb Γb (.eff eN :: r))
    (hcb : τb.complete = true) (hI : Inv F ι σ Γ env E S) (hwf : WF σ) (hRdy : Ready O hs r) :
    Post F ι O σ E S (unhideAll Γ₁ (roots .mut ys) (thaw (hideAll Γ₁ (roots .mut ys)) (roots .ro ys) Γb)) env τb r
      hs (evalS F O n hs σ env (.gen eN eY τy τb f owned caps body)) := by
  obtain ⟨vs, σ1, E₁, Ls, hevs, hI₁, hvs, hLn, hdL, hdLS, hm₁⟩ := atoms_ok hargs hI hwf
  have hwf₁ := hm₁.wf
  obtain ⟨ls, Rc, Hc, hmap, hlen, hcok, hcin, htr, htr'⟩ := caps_ok hcaps hI₁.foot
  obtain ⟨hkeys, hbody⟩ := hF d (List.mem_of_getElem? hfd)
  rw [hcap, hretp] at hbody
  obtain ⟨Γ'', hbody⟩ := hbody
  have hlen' : vs.length = d.owns.length ∧ ls.length = d.refs.length :=
    ⟨by rw [hvs.length]; simp, by rw [hdrefs, List.length_map]; exact hlen⟩
  simp only [evalS, hfd, hevs, hmap]
  rw [if_pos hlen']
  -- The producer's parameters.
  obtain ⟨Eo, hfo, hEo, hEom, hle, hwf₂, hold, hnew, -⟩ :=
    allocAll_ok (names := d.owns.map Prod.fst) hvs (by simp) hwf₁ hLn
  rw [zip_fst_snd] at hfo
  have hcells : (allocAll σ1 ((d.owns.map Prod.fst).zip vs)).1.map Prod.fst = d.owns.map Prod.fst := by
    rw [allocAll_fst]; exact List.map_fst_zip (by rw [hvs.length]; simp)
  have hrt := allocAll_rt σ1 ((d.owns.map Prod.fst).zip vs)
  have hfbt := allocAll_fbext σ1 ((d.owns.map Prod.fst).zip vs)
  have hcut := allocAll_cur σ1 ((d.owns.map Prod.fst).zip vs)
  generalize allocAll σ1 ((d.owns.map Prod.fst).zip vs) = al at hfo hEom hle hwf₂ hold hnew hcells hrt hfbt hcut ⊢
  obtain ⟨cP, σ2⟩ := al
  dsimp only at hfo hEom hle hwf₂ hold hnew hcells hrt ⊢
  generalize hσ3 : σ2.fresh = fr
  obtain ⟨hid, σ3⟩ := fr
  have hσ3' : σ3 = { σ2 with ids := σ2.ids + 1 } := by
    have := congrArg Prod.snd hσ3; simpa [Store.fresh] using this.symm
  have hmem3 : σ3.mem = σ2.mem := by rw [hσ3']
  have hnext3 : σ3.next = σ2.next := by rw [hσ3']
  have hrt3 : σ3.rt = σ2.rt := by rw [hσ3']
  have hwf3 : WF σ3 := fun l h => by rw [hnext3]; exact hwf₂ l (by rw [← hmem3]; exact h)
  have hold13 : ∀ l, σ1.mem l ≠ none → σ3.mem l = σ1.mem l := fun l h => by
    rw [hmem3]; exact hold l (hwf₁ l h)
  have hrt13 : σ3.rt = σ1.rt := hrt3.trans hrt
  have hag13 : ∀ L, (∀ l ∈ L, σ1.mem l ≠ none) → Agree σ1 σ3 L := fun L hL =>
    Agree.of (fun l hl => hold13 l (hL l hl)) hrt13
  -- The variables lent `mut` out of reach, their trees the producer's; those lent `readonly` frozen.
  obtain ⟨hmn, hrm⟩ := hexcl.roots_ok
  generalize hms : roots .mut ys = ms at hb hmn hrm htr htr' ⊢
  generalize hrs' : roots .ro ys = ros at hb hrm ⊢
  obtain ⟨Eh, hfh, hEh, hreb⟩ := hI₁.foot.hiddenAll hI₁.keys htr hmn
  have hkh : ((hideAll Γ₁ ms).map Prod.fst).Nodup := by rw [hideAll_keys]; exact hI₁.keys
  obtain ⟨Eb, Sb, Fz, hfb, hEp, hS, hent, hthaw⟩ := hfh.handle hkh (ys := ros) (by
    intro y hy τ' h
    rw [lookup_hideAll (hrm y hy)] at h
    rw [← hrs', mem_roots] at hy
    exact hcaps.roots_live _ hy τ' h)
  have hEall : E₁.Perm (Hc ++ (Eb ++ Fz)) := hEh.trans (hEp.append_left Hc)
  obtain ⟨hHcn, hEbFzn, hdHc⟩ := nodup_append_disj.mp (hEall.nodup_iff.mp hI₁.nodup)
  obtain ⟨hEbn, hFzn, hdEF⟩ := nodup_append_disj.mp hEbFzn
  have hmemE : ∀ l, l ∈ E₁ ↔ l ∈ Hc ∨ l ∈ Eb ∨ l ∈ Fz := fun l => by
    rw [hEall.mem_iff]; simp
  have hEb : ∀ l ∈ Eb, l ∈ E₁ := fun l h => (hmemE l).mpr (.inr (.inl h))
  have hFz : ∀ l ∈ Fz, l ∈ E₁ := fun l h => (hmemE l).mpr (.inr (.inr h))
  have hHcE : ∀ l ∈ Hc, l ∈ E₁ := fun l h => (hmemE l).mpr (.inl h)
  have hSb1 : ∀ l ∈ Sb, σ1.mem l ≠ none := fun l hl => by
    rcases List.mem_append.mp (hS.mem_iff.mp hl) with h | h
    · exact hI₁.alloc l (hFz l h)
    · exact hI₁.allocS l h
  have hIc : Inv F ι σ3 (freeze (hideAll Γ₁ ms) ros) env Eb Sb := by
    refine ⟨hfb.frame (hag13 _ fun l hl => by
      rcases List.mem_append.mp hl with h | h
      · exact hI₁.alloc l (hEb l h)
      · exact hSb1 l h), hEbn, fun l hl hl' => ?_, by rw [freeze_keys]; exact hkh,
      (hag13 [] (by simp)).cur.trans hI₁.cur⟩
    rcases List.mem_append.mp (hS.mem_iff.mp hl) with h | h
    · exact hdEF l hl' h
    · exact hI₁.disj l h (hEb l hl')
  -- What the producer is lent `readonly` is frozen, or read already.
  have hRc : ∀ l ∈ Rc, l ∈ Fz ∨ l ∈ S := by
    intro l hl
    obtain ⟨y, hy, s', a', L', he, hlL⟩ := hcin l hl
    have hyr : y ∈ ros := by rw [← hrs', mem_roots]; exact hy
    exact hent y s' a' L' (he.to_hidden (hrm y hyr)) hyr l hlL
  -- Where each cell is.
  have hlt : ∀ l, σ1.mem l ≠ none → l < σ1.next := hwf₁
  have hdE1o : Disj E₁ Eo := fun l h1 h2 => by
    rcases (hEom l).mp h2 with h | h
    · exact hdL l h h1
    · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hlt l (hI₁.alloc l h1)) h.1)
  have hdSo : Disj S Eo := fun l h1 h2 => by
    rcases (hEom l).mp h2 with h | h
    · exact hdLS l h h1
    · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hlt l (hI₁.allocS l h1)) h.1)
  have hRH1 : ∀ l ∈ Rc ++ Hc, σ1.mem l ≠ none := hcok.alloc
  have hcok3 : CapsOk F ι σ3 (List.zipWith Cap.at caps ls) Rc Hc := hcok.frame (hag13 _ hRH1)
  -- The producer's activation: its parameters, and the places lent it.
  have hsigs : (List.zipWith Cap.at caps ls).map Cap.sig = d.refs := by rw [hdrefs]; exact zipWith_at_sig hlen
  have henv : (d.refs.map Prod.fst).zip ls = capsLvlEnv (List.zipWith Cap.at caps ls) := by
    rw [hdrefs]; exact zip_refs_at hlen
  have hctx : refCtx d.refs = capsLvlΓ (List.zipWith Cap.at caps ls) := by
    simp only [capsLvlΓ, hsigs]; rfl
  have hfp := hfo.append (hcok.foot.frame (Agree.of (fun l hl => hold l (hwf₁ l (hRH1 l (by
    rcases List.mem_append.mp hl with h | h <;> simp [h])))) hrt))
  rw [hsigs, List.nil_append] at hfp
  have hIp3 : Inv F ι σ3 (fnCtx d) (cP ++ (d.refs.map Prod.fst).zip ls) (Eo ++ Hc) Rc := by
    refine ⟨?_, nodup_append_disj.mpr ⟨hEo, hHcn, fun l h1 h2 => hdE1o l (hHcE l h2) h1⟩, ?_, ?_, by cur_inv⟩
    · rw [henv, fnCtx_eq]
      exact (hfp.frame (Agree.of (fun l _ => by rw [hmem3]) hrt3) :)
    · intro l hl h
      rcases List.mem_append.mp h with h | h
      · rcases hRc l hl with h' | h'
        · exact hdE1o l (hFz l h') h
        · exact hdSo l h' h
      · rcases hRc l hl with h' | h'
        · exact hdHc l h (by simp [h'])
        · exact hI₁.disj l h' (hHcE l h)
    · rw [fnCtx_eq]; simpa [ownCtx, refCtx, Function.comp_def] using hkeys
  have hKp := task_frames (r := r) (e := eY) hkeys hvs.owns_complete hbody hrow hcells hopY hYrefs hYret hey hIp3
  have hKp' : FramesOk F O ι σ3 [.callK ((d.owns.map Prod.snd).zip (cP.map Prod.snd)),
        .startK (cP ++ (d.refs.map Prod.fst).zip ls) d.body] opY
      ⟨capsLvlΓ (List.zipWith Cap.at caps ls), capsLvlEnv (List.zipWith Cap.at caps ls), .int, Rc, .eff eY :: r⟩
      (Eo ++ Hc) [] [] := by
    rw [← hctx, ← henv, ← hdret]; exact hKp
  -- How the activation is rebuilt.
  have hw := typed_weaker hb (by rw [freeze_keys]; exact hkh)
  have hFS1 : ∀ l ∈ Fz ++ S, σ1.mem l ≠ none := fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · exact hI₁.alloc l (hFz l h)
    · exact hI₁.allocS l h
  have hG : GenOk F ι O σ3 eN eY opN opY τy τb (List.zipWith Cap.at caps ls) Γb
      (unhideAll Γ₁ ms (thaw (hideAll Γ₁ ms) ros Γb)) env Sb S Fz Rc :=
    { hopN := hopN, hNowns := hNowns, hNrefs := hNrefs, hNret := hNret, hopY := hopY, hYowns := hYowns,
      hYrefs := hYrefs, hYret := hYret, hcy := hcy, hcb := hcb,
      hSin := fun l hl => List.mem_append.mp (hS.mem_iff.mp hl),
      hS := fun l hl => hS.mem_iff.mpr (List.mem_append.mpr (.inr hl)),
      hRc := hRc,
      hRcdet := fun σ' Rc' Hc' hag hc => hcok3.det_ro hc (hag.mono fun l hl => by
        rcases hRc l hl with h | h <;> simp [h]),
      hfns := hcok.fns,
      hre := by
        intro σ' Eb' Hc' hag hdX hSH hnX hc hI'
        have hag' : Agree σ1 σ' (Fz ++ S) := (hag13 _ hFS1).trans hag
        obtain ⟨E1, hf1, hp1⟩ := hthaw σ' Γb Eb' hI'.foot hw hag'
        obtain ⟨E', hf', hp'⟩ := hreb σ' _ E1 Hc' hf1 (thaw_weaker hw)
          ((hag'.mono fun l hl => List.mem_append.mpr (.inr hl))) (htr' σ' Rc Hc' hc)
        have hmem' : ∀ z, z ∈ E' ↔ z ∈ Eb' ∨ z ∈ Fz ∨ z ∈ Hc' := fun z => by
          rw [hp'.mem_iff, List.mem_append, hp1.mem_iff, List.mem_append]; grind
        obtain ⟨hFzn', hHcn', hdFH⟩ := nodup_append_disj.mp hnX
        refine ⟨E', ⟨hf', hp'.nodup_iff.mpr (nodup_append_disj.mpr ⟨hHcn', hp1.nodup_iff.mpr
          (nodup_append_disj.mpr ⟨hI'.nodup, hFzn', fun l h h' => hdX l (by simp [h']) h⟩), ?_⟩), ?_,
          by rw [unhideAll_keys ((thaw_keys (by rw [typed_keys hb, freeze_keys])).trans hideAll_keys)];
             exact hI₁.keys, by cur_inv⟩, hmem'⟩
        · intro l hl hl'
          rcases List.mem_append.mp (hp1.mem_iff.mp hl') with h | h
          · exact hdX l (by simp [hl]) h
          · exact hdFH l h hl
        · intro l hl hl'
          rcases (hmem' l).mp hl' with h | h | h
          · exact hI'.disj l (hS.mem_iff.mpr (List.mem_append.mpr (.inr hl))) h
          · exact hI₁.disj l hl (hFz l h)
          · exact hSH l hl h }
  have hframe := FrameOk.genC (σf := σ3) (hid := hid) hG hRc hKp'
  have h1 := hE (.capture eN hid :: hs) σ3 ι _ env Eb Sb body τb Γb (.eff eN :: r) hb hIc hwf3 (hframe.ready hRdy)
  have hX3 : ∀ l ∈ E₁, σ3.mem l ≠ none := fun l hl => by
    rw [hold13 l (hI₁.alloc l hl)]; exact hI₁.alloc l hl
  have hEo3 : ∀ l ∈ Eo, σ3.mem l ≠ none := fun l hl => hIp3.alloc l (by simp [hl])
  have hS3 : ∀ l ∈ S, σ3.mem l ≠ none := fun l hl => by
    rw [hold13 l (hI₁.allocS l hl)]; exact hI₁.allocS l hl
  have h2 := hR hs ι ι σ3 _ _ ⟨unhideAll Γ₁ ms (thaw (hideAll Γ₁ ms) ros Γb), env, τb, S, r⟩ (Fz ++ (Eo ++ Hc)) []
    σ3 Eb _ hframe hRdy (fun _ h => by simp at h) hwf3 Agree.self
    (fun l hl => by
      simp only [List.mem_append] at hl
      rcases hl with h | h | h
      · exact hX3 l (hFz l h)
      · exact hEo3 l h
      · exact hX3 l (hHcE l h))
    (nodup_append_disj.mpr ⟨hFzn, nodup_append_disj.mpr ⟨hEo, hHcn, fun l h1 h2 => hdE1o l (hHcE l h2) h1⟩,
      fun l h1 h2 => by
        rcases List.mem_append.mp h2 with h2 | h2
        · exact hdE1o l (hFz l h1) h2
        · exact hdHc l h2 (by simp [h1])⟩)
    (fun l h1 h2 => by
      simp only [List.mem_append] at h1
      rcases h1 with h1 | h1 | h1
      · exact hdEF l h2 h1
      · exact hdE1o l (hEb l h2) h1
      · exact hdHc l h1 (by simp [h2])) hS3
    (fun l h1 h2 => by
      simp only [List.mem_append] at h2
      rcases h2 with (h2 | h2 | h2) | h2
      · exact hI₁.disj l h1 (hFz l h2)
      · exact hdSo l h1 h2
      · exact hI₁.disj l h1 (hHcE l h2)
      · exact hI₁.disj l h1 (hEb l h2)) h1
  have m1 := hm₁.relabel (E'' := E₁ ++ Ls.flatten) (L'' := []) fun x => by simp
  have m2 := Moves.grow (σ := σ1) (σ' := σ2) (E := E₁ ++ Ls.flatten) (E' := E₁ ++ Eo)
    hwf₁ hwf₂ hle hold (fun l h1 h2 => hnew l h1 h2)
    (fun l hl => by
      rcases List.mem_append.mp hl with h | h
      · exact hI₁.alloc l h
      · exact hvs.alloc l h)
    (fun l => by
      simp only [List.mem_append, hEom]
      constructor
      · rintro (h | h | h)
        · exact .inl (.inl h)
        · exact .inl (.inr h)
        · exact .inr h
      · rintro ((h | h) | h)
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr h)) hrt
  have m3 : Moves σ2 (E₁ ++ Eo) σ3 (E₁ ++ Eo) [] := by
    have := Moves.freshen (σ := σ2) (E := E₁ ++ Eo) hwf₂ fun l hl => (m2.alloc l).mpr (.inr (.inl hl))
    rw [hσ3] at this
    exact this
  exact post_after (((m1.trans m2 disj_nil_left hwf).trans m3 disj_nil_left hwf).relabel fun x => by
    simp only [List.mem_append, List.append_nil, List.not_mem_nil, or_false, hmemE]; grind) hwf h2

end FlyCore.Ownership
