import FlyCore.OwnershipGen

/-!
# Ownership: scopes that start tasks as they run

A scope's body starts tasks, each a closure called once that took what it captured by moving it, and
the body and every task give way to each other; the scope ends once all have. A failure drops what
is left, the body and every task, each where it waits.
-/

namespace FlyCore.Ownership

theorem dropK_fn_row : ∀ {n : Nat} {σ : Store} {k : Kind} {A B : Ty} {r r' : Row} {v : Val},
    dropK n σ (.fn k A B r R) v = dropK n σ (.fn k A B r' R') v
  | 0, _, _, _, _, _, _, v => by cases v <;> simp [dropK]
  | _ + 1, _, _, _, _, _, _, v => by cases v <;> simp [dropK]

theorem drop_fn_row : drop σ (.fn k A B r R) v = drop σ (.fn k A B r' R') v := by
  simp only [drop]; exact dropK_fn_row

theorem konts_fn_row : konts σ (.fn k A B r R) v = konts σ (.fn k A B r' R') v := by
  simp only [konts]
  cases σ.next <;> cases v <;> simp [kontsK]

theorem aimed_uncap2 : AimedIn a (.capture e hid :: .capture eS hid :: hs) → AimedIn a hs :=
  fun h => aimed_uncap (aimed_uncap h)

/-! ## Dropping a body or a task -/

/-- A scope's body or task being dropped: it goes on at once where it gives way, and each task it
starts is dropped. -/
theorem ret_scX [WorldOk F O ι.w] (hfl : FlushOk F ι (flushR F O n)) (hKo : ∀ m, n = m + 1 → EvalKOk F O m ∧ RetOk F O m) (hop : O[e]? = some op)
    (howns : op.owns = []) (hrefs : op.refs = []) (hret : op.ret = .int) (hopS : O[eS]? = some opS)
    (hSowns : opS.owns = [.fn .once .int .int rT R]) (hSrefs : opS.refs = []) (hSret : opS.ret = .int)
    (hR : Ready O hs r) (hwf : WF σ0) (hag : Agree σf σ0 S) (hSa : ∀ l ∈ S, σ0.mem l ≠ none) (hSd : Disj S Ein)
    (hp : Post F ι O σ0 Ein S Γ env τ (.eff e :: .eff eS :: r) (.capture e hid :: .capture eS hid :: hs) res) :
    Post F ι O σ0 Ein S Γ env τ r hs (ret F O n hs (.scX e eS hid) res) := by
  have hfr : ∀ {σ'}, FrameOk F O ι ι σ' (.scX e eS hid) ⟨Γ, env, τ, S, .eff e :: .eff eS :: r⟩ ⟨Γ, env, τ, S, r⟩ [] [] :=
    .scX hop howns hrefs hret hopS hSowns hSrefs hSret
  rcases res with ⟨res, σ1⟩
  have pass : (∀ j ef vs ls K, res = .susp j ef vs ls K → j ≠ hid ∨ (ef ≠ e ∧ ef ≠ eS)) →
      Post F ι O σ0 Ein S Γ env τ r hs (ret F O n hs (.scX e eS hid) (res, σ1)) := by
    intro hnot
    have : ret F O n hs (.scX e eS hid) (res, σ1) = passK (.scX e eS hid) (res, σ1) := by
      cases res with
      | susp j ef vs ls K => rw [ret.eq_def]; simp [passK, hnot j ef vs ls K rfl]
      | _ => simp [ret, passK]
    rw [this]
    have h := post_pass (Xf := []) (σf := σf) hfr (fun _ h => h)
      (fun σ1 Eb _ _ hI => ⟨Eb, hI, fun z => by simp⟩) hR.2 (fun a ha => aimed_uncap2 ha) ?_ hwf hag
      (fun _ h => by simp at h) List.nodup_nil disj_nil_left hSa (by simpa using hSd) hp
    · simpa using h
    · intro j ef vs ls K σ' h hc
      have h1 := hnot j ef vs ls K (congrArg Prod.fst h)
      rcases hc.of_cons_capture with ⟨rfl, rfl⟩ | hc
      · simp at h1
      rcases hc.of_cons_capture with ⟨rfl, rfl⟩ | hc
      · simp at h1
      · exact hc
  cases res with
  | val v => exact pass fun _ _ _ _ _ h => by cases h
  | abort j k => exact pass fun _ _ _ _ _ h => by cases h
  | stuck => exact pass fun _ _ _ _ _ h => by cases h
  | timeout => exact pass fun _ _ _ _ _ h => by cases h
  | ended => exact pass fun _ _ _ _ _ h => by cases h
  | susp j ef vs ls K =>
  by_cases hc : j ≠ hid ∨ (ef ≠ e ∧ ef ≠ eS)
  · exact pass fun _ _ _ _ _ h => by cases h; exact hc
  have hj : j = hid := by
    by_cases h : j = hid
    · exact h
    · exact absurd (.inl h) hc
  have hef : ef = e ∨ ef = eS := by
    by_cases h1 : ef = e
    · exact .inl h1
    by_cases h2 : ef = eS
    · exact .inr h2
    exact absurd (.inr ⟨h1, h2⟩) hc
  subst hj
  obtain ⟨op', X, hos, A, Lv, -, hop', -, haim, hK, hls, hvs, hLn, hdLX, hdLS, hm⟩ := hp
  have hSa1 : ∀ l ∈ S, σ1.mem l ≠ none := fun l hl => by
    rw [hm.keeps hwf hSa (fun l h1 h2 => hSd l h1 h2) l hl]; exact hSa l hl
  have hwf₁ := hm.wf
  have hR' : Ready O (.capture e j :: .capture eS j :: hs) (.eff e :: .eff eS :: r) := (hfr (σ' := σ1)).ready hR
  cases n with
  | zero =>
    rw [ret.eq_def]; simp only [ne_eq, not_true_eq_false, false_or, Bool.not_eq_true]
    split <;> simp_all [Post]
  | succ m =>
  obtain ⟨hKk, hRr⟩ := hKo m rfl
  by_cases hS : ef = eS
  · -- A task started: it is dropped at once.
    subst hS
    obtain rfl : opS = op' := Option.some.inj (hopS.symm.trans hop')
    rw [hSowns] at hvs
    cases hvs with
    | cons hv hrest =>
    cases hrest
    rename_i w L
    obtain ⟨-, -, -, -, -, -, -, -, hts, -, -, hXn, -⟩ := hK.base_of
    rw [hSrefs] at hts
    obtain rfl : hos = [] := List.map_eq_nil_iff.mp hts
    simp only [olds, mutCells, List.map_nil, List.flatMap_nil, List.append_nil, List.flatten_cons,
      List.flatten_nil] at hm hdLX hdLS hLn
    obtain ⟨σ2', hdrop, hfg⟩ := dropF hfl hwf₁ hv
    have hdrop' : drop σ1 (.fn .once .int .int [] .nil) w = some σ2' := by rw [drop_fn_row]; exact hdrop
    have : ret F O (m + 1) hs (.scX e ef j) (.susp j ef [w] ls K, σ1) =
        andThen (flushR F O (m + 1) (konts σ1 (.fn .once .int .int [] .nil) w) σ2') fun σ2 =>
          ret F O m hs (.scX e ef j) (evalK F O m (.capture e j :: .capture ef j :: hs) σ2 K (.val (.int 0))) := by
      rw [ret.eq_def]; simp [hdrop']
    rw [this, konts_fn_row]
    refine hfg.post fun σ2 hd2 => ?_
    have hwf2 : WF σ2 := hd2.wf
    have hXa1 : ∀ l ∈ X, σ1.mem l ≠ none := fun l hl => (hm.alloc l).mpr (.inr (.inl hl))
    have hag12 : Agree σ1 σ2 (X ++ S) := hd2.keeps hwf₁ (fun l hl => by
        rcases List.mem_append.mp hl with hl | hl
        · exact hXa1 l hl
        · exact hSa1 l hl) fun l hl h => by
      rcases List.mem_append.mp hl with hl | hl
      · exact hdLX l h hl
      · exact hdLS l h hl
    have hm2 : Moves σ1 (X ++ L) σ2 X [] :=
      (hd2.widen (X := X) hXa1 (fun l h1 h2 => hdLX l h2 h1)).relabel fun x => by simp
    have hres := yield_resume (top := ⟨Γ, env, τ, S, .eff e :: .eff ef :: r⟩) hKk hopS hSrefs hSret hK hR' haim hwf2
      hag12 (fun l hl => by
        rcases List.mem_append.mp hl with h | h
        · exact hXa1 l h
        · exact hSa1 l h) hXn (fun l h1 h2 => (hm.apart hwf hSa hSd).1 l h1 h2)
    have hSa2 : ∀ l ∈ S, σ2.mem l ≠ none := fun l hl => by
      rw [hag12 l (List.mem_append.mpr (.inr hl))]; exact hSa1 l hl
    have h2 := hRr hs _ _ σ2 (.scX e ef j) ⟨Γ, env, τ, S, .eff e :: .eff ef :: r⟩ ⟨Γ, env, τ, S, r⟩ [] [] σ2 X _
        hfr hR (fun _ h => by simp at h) hwf2 Agree.self (fun _ h => by simp at h)
        List.nodup_nil disj_nil_left hSa2 (fun l h1 h2 => (hm.apart hwf hSa hSd).1 l h1 (by simpa using h2)) hres
    have hm' : Moves σ0 Ein σ1 (X ++ L) [] := hm.relabel fun x => by simp only [List.mem_append, List.not_mem_nil, or_false]
    exact post_after (hm'.trans hm2 disj_nil_left hwf) hwf (by simpa using h2)
  · -- It gave way: it goes on at once.
    obtain rfl : ef = e := hef.resolve_right hS
    obtain rfl : op = op' := Option.some.inj (hop.symm.trans hop')
    rw [howns] at hvs
    cases hvs
    obtain ⟨-, -, -, -, -, -, -, -, hts, -, -, hXn, -⟩ := hK.base_of
    rw [hrefs] at hts
    obtain rfl : hos = [] := List.map_eq_nil_iff.mp hts
    simp only [olds, mutCells, List.map_nil, List.flatMap_nil, List.append_nil, List.flatten_nil] at hm hdLX hdLS
    have : ret F O (m + 1) hs (.scX ef eS j) (.susp j ef [] ls K, σ1) =
        ret F O m hs (.scX ef eS j) (evalK F O m (.capture ef j :: .capture eS j :: hs) σ1 K (.val (.int 0))) := by
      rw [ret.eq_def]; simp [hS]
    rw [this]
    have hres := yield_resume (top := ⟨Γ, env, τ, S, .eff ef :: .eff eS :: r⟩) hKk hop hrefs hret hK hR' haim hwf₁
      Agree.self (fun l hl => by
        rcases List.mem_append.mp hl with h | h
        · exact (hm.alloc l).mpr (.inr (.inl h))
        · exact hSa1 l h) hXn (hm.apart hwf hSa hSd).1
    have h2 := hRr hs _ _ σ1 (.scX ef eS j) ⟨Γ, env, τ, S, .eff ef :: .eff eS :: r⟩ ⟨Γ, env, τ, S, r⟩ [] [] σ1 X _
        hfr hR (fun _ h => by simp at h) hwf₁ Agree.self (fun _ h => by simp at h)
        List.nodup_nil disj_nil_left hSa1 (by simpa using (hm.apart hwf hSa hSd).1) hres
    exact post_after hm hwf (by simpa using h2)

/-! ## A scope's waiting tasks -/

theorem TasksOk.transfer : TasksOk F O ι σf e eS r S Q X A → Agree σf σ' (X ++ S) → TasksOk F O ι σ' e eS r S Q X A
  | .nil, _ => .nil
  | .cons hK hro hag ha hSt hdS h1 h2 hd hT, hag' =>
    .cons hK hro (hag.trans (hag'.mono fun l hl => by
        rcases List.mem_append.mp hl with h | h
        · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inl h)))
        · exact List.mem_append.mpr (.inr (hSt l h)))) ha hSt hdS h1 h2 hd
      (hT.transfer (hag'.mono fun l hl => by
        rcases List.mem_append.mp hl with h | h
        · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr h)))
        · exact List.mem_append.mpr (.inr h)))

theorem TasksOk.append : TasksOk F O ι σf e eS r S Q X A →
    FramesOk F O ι σt K op0 ⟨Γt, envt, .int, St, .eff e :: .eff eS :: r⟩ Xk [] AK → RoCtx Γt → Agree σt σf (Xk ++ St) →
    (∀ l ∈ Xk ++ St, σt.mem l ≠ none) → (∀ l ∈ St, l ∈ S) → Disj St Xk →
    op0.ret = .int → op0.refs = [] → Disj X Xk →
    TasksOk F O ι σf e eS r S (Q ++ [K]) (X ++ Xk) (A ++ AK)
  | .nil, hK, hro, hag, ha, hSt, hdS, h1, h2, _ => by simpa using TasksOk.cons hK hro hag ha hSt hdS h1 h2 disj_nil_right .nil
  | .cons hK' hro' hag' ha' hSt' hdS' h1' h2' hd' hT, hK, hro, hag, ha, hSt, hdS, h1, h2, hd => by
    have := TasksOk.cons hK' hro' hag' ha' hSt' hdS' h1' h2' (fun l hl h => by
        rcases List.mem_append.mp h with h | h
        · exact hd' l hl h
        · exact hd l (List.mem_append.mpr (.inl hl)) h)
      (hT.append hK hro hag ha hSt hdS h1 h2 (fun l hl h => hd l (List.mem_append.mpr (.inr hl)) h))
    simpa [List.append_assoc] using this

theorem TasksOk.alloc : TasksOk F O ι σf e eS r S Q Xq Aq → ∀ l ∈ Xq, σf.mem l ≠ none
  | .nil => fun _ h => by simp at h
  | .cons _ _ hag ha _ _ _ _ _ hT => fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · rw [hag l (List.mem_append.mpr (.inl h))]; exact ha l (List.mem_append.mpr (.inl h))
    · exact hT.alloc l h

theorem ScCaps.transfer (h : ScCaps F ι σf cz R S Rc) (hag : Agree σf σ' S) : ScCaps F ι σ' cz R S Rc :=
  ⟨h.hc.frame (hag.mono fun l hl => h.hRc l (by simpa using hl)), h.hRc, h.hR, h.hro⟩

theorem agree_S (hag : Agree σ σ' (X ++ S)) : Agree σ σ' S := hag.mono fun l hl => List.mem_append.mpr (.inr hl)

/-- A waiting task, whose cells are among `Xq` and whose borrows among `S`, agrees with the store. -/
theorem agree_task (hagt : Agree σt σf (X ++ St)) (hSt : ∀ l ∈ St, l ∈ S) (hX : ∀ l ∈ X, l ∈ Xq)
    (hag : Agree σf σ1 (Xq ++ S)) : Agree σt σ1 (X ++ St) :=
  hagt.trans (hag.mono fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · exact List.mem_append.mpr (.inl (hX l h))
    · exact List.mem_append.mpr (.inr (hSt l h)))

/-! ## A task started -/

/-- Places lent only read, known by other names. -/
theorem CapsOk.rename : ∀ {cz : List (Cap Nat)} {Rc : List Nat} {ns : List Var}, CapsOk F ι σ cz Rc [] →
    (∀ c ∈ cz, c.mode = .ro) → ns.length = cz.length →
    CapsOk F ι σ (List.zipWith (fun n c => (⟨n, c.mode, c.ty, c.loc⟩ : Cap Nat)) ns cz) Rc []
  | [], _, [], h, _, _ => by cases h; exact .nil
  | [], _, _ :: _, _, _, h => by simp at h
  | _ :: _, _, [], _, _, h => by simp at h
  | ⟨x, m, τ, a⟩ :: cz, _, n :: ns, h, hro, hlen => by
    obtain rfl : m = .ro := hro _ (List.mem_cons_self ..)
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    cases h with
    | ro hL hc => exact .ro hL (CapsOk.rename hc (fun c hc => hro c (List.mem_cons_of_mem _ hc)) hlen)

theorem rename_sig : ∀ {refs : List (Var × Mode × Ty)} {cz : List (Cap Nat)},
    refs.map Prod.snd = cz.map (fun c => (Mode.ro, c.ty)) → (∀ c ∈ cz, c.mode = .ro) →
    (List.zipWith (fun n c => (⟨n, c.mode, c.ty, c.loc⟩ : Cap Nat)) (refs.map Prod.fst) cz).map Cap.sig = refs
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | ⟨x, m, τ⟩ :: refs, c :: cz, h, hro => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, h⟩ := h
    simp only [List.map_cons, List.zipWith_cons_cons, Cap.sig, hro c (List.mem_cons_self ..), List.cons.injEq,
      true_and]
    exact rename_sig h fun c' hc' => hro c' (List.mem_cons_of_mem _ hc')

theorem rename_env : ∀ {ns : List Var} {cz : List (Cap Nat)},
    (List.zipWith (fun n c => (⟨n, c.mode, c.ty, c.loc⟩ : Cap Nat)) ns cz).map (fun c => (c.name, c.loc)) =
      ns.zip (cz.map Cap.loc)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: ns, _ :: cz => by simp [List.zipWith_cons_cons, rename_env (ns := ns) (cz := cz)]

/-- A spawned task's root, which takes its panic up (§5.7), over the frames of its call. -/
theorem FramesOk.spawnRoot (sp : Bool) (h : FramesOk F O ι σ K op ⟨Γ, env, .int, S, r⟩ X [] []) :
    FramesOk F O ι σ ((if sp then [.spawnK] else []) ++ K) op ⟨Γ, env, .int, S, r⟩ X [] [] := by
  cases sp
  · simpa using h
  · have := FramesOk.cons (f := .spawnK) (σf := σ) (A := []) .spawnK (Weaker.refl _) Agree.self
      (fun _ h => by simp at h) List.nodup_nil disj_nil_left h (fun _ h => by simp at h) (fun _ h => by simp at h)
    simpa using this

/-- A closure called once, started as a task: what it captured moved to a parameter of its code,
the task waits to be called with `0`, lent the scope's places; its cells the closure's, those it
captured moved. -/
theorem mkTask_ok (sp : Bool) (hF : FnsOk F O) (hS : ScOk O e eS op opS rT R r τ) (hcz : ScCaps F ι σ cz R S Rc)
    (hv : VT F ι σ (.fn .once .int .int rT R) w L) (hwf : WF σ) (hdLS : Disj L S) :
    ∃ Kt σ' X Γt envt, mkTask F cz σ sp w = some (Kt, σ') ∧
      FramesOk F O ι σ' Kt op ⟨Γt, envt, .int, Rc, .eff e :: .eff eS :: r⟩ X [] [] ∧ RoCtx Γt ∧
        Moves σ L σ' X [] := by
  cases hv with
  | @clo f τc _ _ _ _ _ c R0 hco hLc hcτ =>
  obtain ⟨d, xc, pn, hfd, hcap, hown, hrefs, hretp, hret, hrow, hτc⟩ := hco
  rw [hcz.hR] at hrefs
  obtain ⟨w', Rw, hw, hvw, rfl, hcRw⟩ := hLc.contents hcτ
  obtain ⟨hkeys0, hbody⟩ := hF d (List.mem_of_getElem? hfd)
  rw [hcap, hretp] at hbody
  obtain ⟨hxc, Γ'', hbody⟩ := hbody
  have hown' : (cloFn d xc τc .once).owns = [(pn, .int), (xc, τc)] := by simp [cloFn, hown]
  have hrefs' : (cloFn d xc τc .once).refs = d.refs := by simp [cloFn]
  have hlen : d.refs.length = cz.length := by
    have := congrArg List.length hrefs; simpa using this
  -- The places lent, by the names the code knows them by.
  have hrefs2 : d.refs.map Prod.snd = cz.map (fun c => (Mode.ro, c.ty)) := by
    rw [List.map_map] at hrefs; exact hrefs
  generalize hcrs : List.zipWith (fun n c => (⟨n, c.mode, c.ty, c.loc⟩ : Cap Nat)) (d.refs.map Prod.fst) cz = crs
  have hsig : crs.map Cap.sig = d.refs := by rw [← hcrs]; exact rename_sig hrefs2 hcz.hro
  have henv : crs.map (fun c => (c.name, c.loc)) = (d.refs.map Prod.fst).zip (cz.map Cap.loc) := by
    rw [← hcrs]; exact rename_env
  -- What the closure captured, moved out of its cell.
  have hold1 : ∀ l, l ≠ c → (σ.set c none).mem l = σ.mem l := fun l hl => by simp [Store.set, hl]
  have hvs : Vals F ι (σ.set c none) [.int, τc] [.int 0, w'] [[], Rw] :=
    .cons .int (.cons (hvw.frame (Agree.of' fun l hl => hold1 l fun e => hcRw (e ▸ hl))) .nil)
  have hwf1 : WF (σ.set c none) := WF.set_none hwf
  obtain ⟨Eo, hfo, hEo, hEom, hle, hwf₂, hold, hnew, -⟩ :=
    allocAll_ok (names := [pn, xc]) hvs (by simp) hwf1 (by simpa using hvw.nodup)
  have hcells := allocAll_fst (σ.set c none) ([pn, xc].zip [.int 0, w'])
  have hrt := allocAll_rt (σ.set c none) ([pn, xc].zip [.int 0, w'])
  have hmk : mkTask F cz σ sp (.clo f c τc) = some ((if sp then [.spawnK] else []) ++ [.callK (((cloFn d xc τc .once).owns.map Prod.snd).zip
      ((allocAll (σ.set c none) ([pn, xc].zip [.int 0, w'])).1.map Prod.snd)),
      .startK ((allocAll (σ.set c none) ([pn, xc].zip [.int 0, w'])).1 ++
        ((cloFn d xc τc .once).refs.map Prod.fst).zip (cz.map Cap.loc)) (cloFn d xc τc .once).body],
      (allocAll (σ.set c none) ([pn, xc].zip [.int 0, w'])).2) := by
    simp only [mkTask, hfd, hw, hcap, hown', hrefs', hlen, List.length_cons, List.length_nil, and_self, ↓reduceIte,
      List.map_cons, List.map_nil]
  generalize allocAll (σ.set c none) ([pn, xc].zip [.int 0, w']) = al at hfo hEom hle hwf₂ hold hnew hcells hrt hmk
  obtain ⟨cP, σ2⟩ := al
  dsimp only at hfo hEom hle hwf₂ hold hnew hcells hrt
  have hRcS : ∀ l ∈ Rc, l ∈ S := hcz.hRc
  have hRca : ∀ l ∈ Rc, σ.mem l ≠ none := fun l hl => hcz.hc.alloc l (by simp [hl])
  have hcL : ∀ l ∈ Rc, l ∉ c :: Rw := fun l hl h => hdLS l h (hRcS l hl)
  have hag2 : Agree σ σ2 (Rc ++ []) := Agree.of (fun l hl => by
      have hl' : l ∈ Rc := by simpa using hl
      rw [hold l (hwf l (hRca l hl'))]
      exact hold1 l fun e => hcL l hl' (e ▸ List.mem_cons_self ..)) (by rw [hrt]; rfl)
  have hcfoot := (hcz.hc.rename (ns := d.refs.map Prod.fst) hcz.hro (by simpa using hlen)).frame hag2
  rw [hcrs] at hcfoot
  have hxcpn : xc ≠ pn := fun e => hxc (by simp [hown, e])
  have hxcr : xc ∉ d.refs.map Prod.fst := fun h => hxc (List.mem_append.mpr (.inr h))
  have hIp : Inv F ι σ2 (fnCtx (cloFn d xc τc .once)) (cP ++ ((cloFn d xc τc .once).refs.map Prod.fst).zip (cz.map Cap.loc))
      Eo Rc := by
    refine ⟨?_, hEo, ?_, ?_⟩
    · rw [hrefs', fnCtx_eq, hown', hrefs', ← henv]
      have := hfo.append hcfoot.foot
      rw [hsig] at this
      simpa [refCtx, capCtx] using this
    · intro l hl hl'
      rcases (hEom l).mp hl' with h | h
      · simp at h; exact hcL l hl (List.mem_cons_of_mem _ h)
      · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hwf l (hRca l hl)) (by
          have := h.1; simp [Store.set] at this ⊢; exact this))
    · rw [fnCtx_eq, hown', hrefs']
      have := hkeys0
      simp [ownCtx, refCtx, hown] at this ⊢
      exact ⟨⟨Ne.symm hxcpn, this.1⟩, fun m τ h => hxcr (List.mem_map.mpr ⟨_, h, rfl⟩), this.2⟩
  have hkeys : (((cloFn d xc τc .once).owns.map Prod.fst) ++ ((cloFn d xc τc .once).refs.map Prod.fst)).Nodup := by
    rw [hown', hrefs']
    have := hkeys0
    simp [hown] at this ⊢
    exact ⟨⟨Ne.symm hxcpn, this.1⟩, fun m τ h => hxcr (List.mem_map.mpr ⟨_, h, rfl⟩), this.2⟩
  have hKp := task_frames (r := .eff eS :: r) (e := e) (ls := cz.map Cap.loc) hkeys
    (fun o ho => by rw [hown'] at ho; simp at ho; rcases ho with rfl | rfl <;> simp [Ty.complete, hcτ])
    (by simpa [cloFn] using hbody) (fun l hl => by simpa using hS.hrT l (by simpa [cloFn, hrow] using hl))
    (by rw [hcells, hown']; rfl) hS.hop hS.hrefs hS.hret (by simpa [cloFn, hrow] using hS.heT) hIp
  rw [show (cloFn d xc τc .once).ret = .int by simp [cloFn, hret]] at hKp
  refine ⟨_, σ2, Eo, _, _, hmk, FramesOk.spawnRoot sp hKp, refCtx_ro fun x hx => ?_, ?_⟩
  · have : x.2 ∈ d.refs.map Prod.snd := List.mem_map.mpr ⟨x, by simpa [cloFn] using hx, rfl⟩
    rw [hrefs2] at this
    obtain ⟨c', -, hc'⟩ := List.mem_map.mp this
    rw [← hc']
  · -- The closure's cell freed, its parameters' cells allocated.
    have m1 : Moves σ (c :: Rw) (σ.set c none) Rw [] := Moves.free (E' := Rw) (D := [c]) hwf1 rfl
      (fun l hl => by
        rcases List.mem_cons.mp hl with rfl | hl
        · simp [hw]
        · exact hvw.alloc l hl)
      (fun l => by simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]; exact Or.comm)
      (fun l hl => by simp only [List.mem_singleton] at hl; subst hl; simp only [Store.set, ↓reduceIte])
      (fun l hl => hold1 l (by simpa using hl)) (fun l h1 h2 => by simp at h2; subst h2; exact hcRw h1)
    have m2 := Moves.grow (σ := σ.set c none) (σ' := σ2) (E := Rw) (E' := Eo) hwf1 hwf₂ hle hold
      (fun l h1 h2 => hnew l h1 h2) (fun l hl => by rw [hold1 l (fun e => hcRw (e ▸ hl))]; exact hvw.alloc l hl)
      (fun l => by rw [hEom]; simp) hrt
    exact m1.trans m2 disj_nil_left hwf

/-! ## Dropping what is left of a scope -/

/-- A scope that failed with `abort j k`, its activation `Eb` as it ended: the next of its waiting
tasks unwound to a new barrier, then the rest, by the dropping frame. -/
theorem drop_one [WorldOk F O ι.w] (hKk : EvalKOk F O m) (hRr : RetOk F O m) (hS : ScOk O e eS op opS rT R r τ)
    (hI : Inv F ι σ0 Γ env Eb S) (hT : TasksOk F O ι σf e eS r S (Kt :: Q') Xq Aq) (hagT : Agree σf σ0 (Xq ++ S))
    (hXa : ∀ l ∈ Xq, σf.mem l ≠ none) (hnd : Xq.Nodup) (hdE : Disj Eb Xq) (hdS : Disj S Xq)
    (haim : AimedIn j hs) (hA : ∀ a ∈ Aq, AimedIn a hs) (hR : Ready O hs r) (hwf : WF σ0) :
    Post F ι O σ0 (Eb ++ Xq) S Γ env τ r hs
      (ret F O m hs (.scE e eS hid τ .int (.abort j k) σ0.fresh.1 Q') (ret F O m (.abort .drop σ0.fresh.1 :: hs)
        (.scX e eS hid) (evalK F O m (.capture e hid :: .capture eS hid :: .abort .drop σ0.fresh.1 :: hs)
          σ0.fresh.2 Kt (.abort σ0.fresh.1 0)))) := by
  cases hT with
  | cons hK hro hagt hat hSt hdSt h1 h2 hdX hT' =>
  rename_i σt op0 Γt envt St X AK Xs As
  generalize hdd : σ0.fresh.1 = d
  have hwf1 : WF σ0.fresh.2 := hwf
  have hag01 : ∀ L, Agree σ0 σ0.fresh.2 L := fun _ => Agree.of' fun _ _ => rfl
  have hXa0 : ∀ l ∈ X ++ Xs, σ0.mem l ≠ none := fun l hl => by
    rw [hagT l (List.mem_append.mpr (.inl hl))]; exact hXa l hl
  have hR2 : Ready O (.abort .drop d :: hs) r := ⟨.abort (by intro e h; cases h) hR.1, fun l hl => covers_cons _ hR.2 l hl⟩
  have hR3 : Ready O (.capture e hid :: .capture eS hid :: .abort .drop d :: hs) (.eff e :: .eff eS :: r) :=
    sc_ready hS.hop hS.hopS hR2.1 hR2.2
  have hag1 : Agree σt σ0.fresh.2 (X ++ St) :=
    hagt.trans ((hagT.mono fun l hl => by
      rcases List.mem_append.mp hl with h | h
      · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inl h)))
      · exact List.mem_append.mpr (.inr (hSt l h))).trans (hag01 _))
  have hSta : ∀ l ∈ St, σ0.fresh.2.mem l ≠ none := fun l hl => by
    rw [hag1 l (List.mem_append.mpr (.inr hl))]; exact hat l (List.mem_append.mpr (.inr hl))
  have hk1 := hKk (.capture e hid :: .capture eS hid :: .abort .drop d :: hs) _ σt Kt ⟨Γt, envt, .int, St,
      .eff e :: .eff eS :: r⟩ X [] AK σ0.fresh.2 [] (.abort d 0) op0 [] hK hR3
    (fun a ha => (hA a (List.mem_append.mpr (.inl ha))).imp_right fun ⟨l, hl⟩ =>
      ⟨l, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hl))⟩) hwf1 hag1
    hat (nodup_append_disj.mp hnd).1 rfl (fun _ h => by simp at h) (by simp [mutCells])
    (by simp [mutCells, Disj]) (by simpa [mutCells] using hdSt)
    (.inr ⟨d, 0, rfl, .inr ⟨.drop, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩, rfl⟩)
  simp only [mutCells, List.flatMap_nil, List.append_nil] at hk1
  have hk2 := hRr (.abort .drop d :: hs) _ _ σ0.fresh.2 (.scX e eS hid) ⟨Γt, envt, .int, St, .eff e :: .eff eS :: r⟩
    ⟨Γt, envt, .int, St, r⟩ [] [] σ0.fresh.2 X _ (.scX hS.hop hS.howns hS.hrefs hS.hret hS.hopS hS.hSowns hS.hSrefs hS.hSret)
    hR2 (fun _ h => by simp at h) hwf1 Agree.self (fun _ h => by simp at h) List.nodup_nil disj_nil_left
    hSta (by simpa using hdSt) hk1
  simp only [List.nil_append] at hk2
  have hXs0 : ∀ l ∈ Xs, l ∈ X ++ Xs := fun l hl => List.mem_append.mpr (.inr hl)
  have hT0 := hT'.transfer (hagT.mono fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · exact List.mem_append.mpr (.inl (hXs0 l h))
    · exact List.mem_append.mpr (.inr h))
  have hdq := nodup_append_disj.mp hnd
  have hEba : ∀ l ∈ Eb, σ0.mem l ≠ none := fun l hl => hI.alloc l hl
  have hk3 := hRr hs _ _ σ0 (.scE e eS hid τ .int (.abort j k) d Q') ⟨Γt, envt, .int, St, r⟩ ⟨Γ, env, τ, S, r⟩ (Eb ++ Xs)
    (j :: As) σ0.fresh.2 X _ (.scEt hS hI hT0 (fun l h1 h2 => hdE l h1 (List.mem_append.mpr (.inr h2))) hSt hro) hR
    (fun a ha => by
      rcases List.mem_cons.mp ha with rfl | ha
      · exact haim
      · exact hA a (List.mem_append.mpr (.inr ha))) hwf1 (hag01 _)
    (fun l hl => by
      rcases List.mem_append.mp hl with h | h
      · exact hEba l h
      · exact hXa0 l (hXs0 l h))
    (nodup_append_disj.mpr ⟨hI.nodup, hdq.2.1, fun l h1 h2 => hdE l h1 (hXs0 l h2)⟩)
    (fun l h1 h2 => by
      rcases List.mem_append.mp h1 with h1 | h1
      · exact hdE l h1 (List.mem_append.mpr (.inl h2))
      · exact hdq.2.2 l h2 h1)
    (fun l hl => hI.allocS l hl)
    (fun l h1 h2 => by
      simp only [List.mem_append] at h2
      rcases h2 with (h2 | h2) | h2
      · exact hI.disj l h1 h2
      · exact hdS l h1 (hXs0 l h2)
      · exact hdS l h1 (List.mem_append.mpr (.inl h2))) hk2
  exact post_after ((Moves.freshen hwf fun l hl => by
      rcases List.mem_append.mp hl with h | h
      · exact hEba l h
      · exact hXa0 l h).relabel fun x => by
        simp only [List.mem_append, List.not_mem_nil, or_false, false_or, or_assoc, or_comm, or_left_comm]) hwf hk3

/-- A scope that failed, a task of it being dropped: once it is, the rest are, and the failure goes on
from the activation as it ended. -/
theorem ret_scEt [WorldOk F O ι.w] (hKo : ∀ m, n = m + 1 → EvalKOk F O m ∧ RetOk F O m) (hS : ScOk O e eS op opS rT R r τ)
    (hI : Inv F ι σf Γ env Eb S) (hT : TasksOk F O ι σf e eS r S Q Xq Aq) (hdT : Disj Eb Xq)
    (hR : Ready O hs r) (hA : ∀ a ∈ j :: Aq, AimedIn a hs) (hwf : WF σ0) (hag : Agree σf σ0 (Eb ++ Xq ++ S))
    (halloc : ∀ l ∈ Eb ++ Xq, σf.mem l ≠ none) (hnd : (Eb ++ Xq).Nodup) (hd : Disj (Eb ++ Xq) Ein)
    (hSa : ∀ l ∈ S, σ0.mem l ≠ none) (hSd : Disj S (Eb ++ Xq ++ Ein))
    (hSt : ∀ l ∈ St, l ∈ S) (hro : RoCtx Γt) (hp : Post F ι O σ0 Ein St Γt envt .int r (.abort .drop d :: hs) res) :
    Post F ι O σ0 (Eb ++ Xq ++ Ein) S Γ env τ r hs (ret F O n hs (.scE e eS hid τ .int (.abort j k) d Q) res) := by
  have hXa : ∀ l ∈ Eb ++ Xq, σ0.mem l ≠ none := fun l hl => by
    rw [hag l (List.mem_append.mpr (.inl hl))]; exact halloc l hl
  have hXSa : ∀ l ∈ Eb ++ Xq ++ S, σ0.mem l ≠ none := fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · exact hXa l h
    · exact hSa l h
  have hXSd : Disj (Eb ++ Xq ++ S) Ein := fun l hl h => by
    rcases List.mem_append.mp hl with hl | hl
    · exact hd l hl h
    · exact hSd l hl (List.mem_append.mpr (.inr h))
  have hnd2 := nodup_append_disj.mp hnd
  -- The task dropped: what is left goes on from the activation as it ended.
  have rest : ∀ {σ1 jj kk}, Moves σ0 Ein σ1 [] [] → AimedIn jj hs →
      Post F ι O σ0 (Eb ++ Xq ++ Ein) S Γ env τ r hs (match Q, n with
        | [], _ => (.abort jj kk, σ1)
        | _ :: _, 0 => (.timeout, σ1)
        | Kt :: Q', m + 1 => ret F O m hs (.scE e eS hid τ .int (.abort jj kk) σ1.fresh.1 Q') (ret F O m
            (.abort .drop σ1.fresh.1 :: hs) (.scX e eS hid) (evalK F O m (.capture e hid :: .capture eS hid ::
              .abort .drop σ1.fresh.1 :: hs) σ1.fresh.2 Kt (.abort σ1.fresh.1 0)))) := by
    intro σ1 jj kk hm haim
    have hag1 : Agree σf σ1 (Eb ++ Xq ++ S) := hag.trans (hm.keeps hwf hXSa hXSd)
    have hI1 : Inv F ι σ1 Γ env Eb S :=
      ⟨hI.foot.frame (hag1.mono fun l hl => by rcases List.mem_append.mp hl with h | h <;> simp [h]),
        hI.nodup, hI.disj, hI.keys⟩
    have hm' : Moves σ0 (Eb ++ Xq ++ Ein) σ1 (Eb ++ Xq) [] := (hm.widen hXa hd).relabel fun x => by simp
    cases Q with
    | nil =>
      cases hT
      exact ⟨haim, Eb, hI1, hm'.relabel fun x => by simp⟩
    | cons Kt Q' =>
      cases n with
      | zero => simp [Post]
      | succ m =>
      obtain ⟨hKk, hRr⟩ := hKo m rfl
      have hwf1 := hm.wf
      exact post_after hm' hwf (drop_one hKk hRr hS hI1 hT (hag1.mono fun l hl => by
          rcases List.mem_append.mp hl with h | h
          · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr h)))
          · exact List.mem_append.mpr (.inr h))
        (fun l hl => halloc l (by simp [hl])) hnd2.2.1 hdT (fun l h1 h2 => hSd l h1 (by simp [h2]))
        haim (fun a ha => hA a (List.mem_cons_of_mem _ ha)) hR hwf1)
  rcases res with ⟨res, σ1⟩
  cases res with
  | val v =>
    obtain ⟨E', L, hI', hv, -, -, hm⟩ := hp
    obtain rfl := foot_ro hI'.foot hro
    cases hv
    rw [ret.eq_def]
    simp only [bothPanic, Bool.false_eq_true, ↓reduceIte, drop, dropK, Option.map_some, konts_int]
    exact post_flushR_nil (rest (jj := j) (kk := k) hm (hA j (List.mem_cons_self ..)))
  | abort j' k' =>
    obtain ⟨haim, E', hI', hm⟩ := hp
    obtain rfl := foot_ro hI'.foot hro
    rw [ret.eq_def]
    -- A task dropped as a panic unwinds that panics in its own cleanup ends the program.
    by_cases h0 : j' = 0 ∧ j = 0
    · simp only [bothPanic, h0.1, h0.2, beq_self_eq_true, Bool.and_self, ↓reduceIte]; trivial
    simp only [bothPanic, Bool.and_eq_true, beq_iff_eq, h0, ↓reduceIte]
    by_cases hj : j' = d
    · simp only [hj, ↓reduceIte]
      exact post_flushR_nil (rest hm (hA j (List.mem_cons_self ..)))
    · simp only [hj, ↓reduceIte]
      exact post_flushR_nil (rest hm (aimed_pop haim hj))
  | susp j' ef vs ls K =>
    simp only [ret]
    exact post_susp_abort (.scEt hS hI hT hdT hSt hro) (fun _ => rfl) hR.2 hA (fun _ h => by cases h) hwf hag halloc hnd hd hSa hSd hp
  | stuck => simp [Post] at hp
  | timeout => simp [ret, Post]
  | ended => simp [ret, Post]

/-- A scope that failed with `abort jj kk`, its activation `Eb` as it ended: its waiting tasks are
dropped one by one, then the failure goes on. -/
theorem drop_rest [WorldOk F O ι.w] (hKo : ∀ m, n = m + 1 → EvalKOk F O m ∧ RetOk F O m) (hS : ScOk O e eS op opS rT R r τ)
    (hI : Inv F ι σ1 Γ env Eb S) (hT : TasksOk F O ι σf e eS r S Q Xq Aq) (hagT : Agree σf σ1 (Xq ++ S))
    (hXa : ∀ l ∈ Xq, σf.mem l ≠ none) (hnd : Xq.Nodup) (hdE : Disj Eb Xq) (hdS : Disj S Xq)
    (haim : AimedIn jj hs) (hA : ∀ a ∈ Aq, AimedIn a hs) (hR : Ready O hs r) (hwf1 : WF σ1) :
    Post F ι O σ1 (Eb ++ Xq) S Γ env τ r hs (match (generalizing := false) Q, n with
      | [], _ => (.abort jj kk, σ1)
      | _ :: _, 0 => (.timeout, σ1)
      | Kt :: Q', m + 1 => ret F O m hs (.scE e eS hid τ .int (.abort jj kk) σ1.fresh.1 Q') (ret F O m
          (.abort .drop σ1.fresh.1 :: hs) (.scX e eS hid) (evalK F O m (.capture e hid :: .capture eS hid ::
            .abort .drop σ1.fresh.1 :: hs) σ1.fresh.2 Kt (.abort σ1.fresh.1 0)))) := by
  cases Q with
  | nil =>
    cases hT
    exact ⟨haim, Eb, hI, by rw [List.append_nil]; exact Moves.refl hwf1 hI.alloc⟩
  | cons Kt Q' =>
    cases n with
    | zero => simp [Post]
    | succ m =>
    obtain ⟨hKk, hRr⟩ := hKo m rfl
    exact drop_one hKk hRr hS hI hT hagT hXa hnd hdE hdS haim hA hR hwf1

/-- A scope that failed, its body being dropped: once it is, its tasks are, and the failure goes on
from the activation the body left. -/
theorem ret_scEb [WorldOk F O ι.w] (hfl : FlushOk F ι (flushR F O n)) (hKo : ∀ m, n = m + 1 → EvalKOk F O m ∧ RetOk F O m) (hS : ScOk O e eS op opS rT R r τ)
    (hT : TasksOk F O ι σf e eS r S Q Xq Aq)
    (hR : Ready O hs r) (hA : ∀ a ∈ j :: Aq, AimedIn a hs) (hwf : WF σ0) (hag : Agree σf σ0 (Xq ++ S))
    (halloc : ∀ l ∈ Xq, σf.mem l ≠ none) (hnd : Xq.Nodup) (hd : Disj Xq Ein)
    (hSa : ∀ l ∈ S, σ0.mem l ≠ none) (hSd : Disj S (Xq ++ Ein))
    (hp : Post F ι O σ0 Ein S Γ env τ r (.abort .drop d :: hs) res) :
    Post F ι O σ0 (Xq ++ Ein) S Γ env τ r hs (ret F O n hs (.scE e eS hid τ τ (.abort j k) d Q) res) := by
  have hXa : ∀ l ∈ Xq, σ0.mem l ≠ none := fun l hl => by
    rw [hag l (List.mem_append.mpr (.inl hl))]; exact halloc l hl
  have hXSa : ∀ l ∈ Xq ++ S, σ0.mem l ≠ none := fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · exact hXa l h
    · exact hSa l h
  have hXSd : Disj (Xq ++ S) Ein := fun l hl h => by
    rcases List.mem_append.mp hl with hl | hl
    · exact hd l hl h
    · exact hSd l hl (List.mem_append.mpr (.inr h))
  have hSE : Disj S Ein := fun l hl h => hSd l hl (List.mem_append.mpr (.inr h))
  -- The body dropped, to activation `E'`: what is left goes on from it.
  have rest : ∀ {σ1 E' jj kk}, Inv F ι σ1 Γ env E' S → Moves σ0 Ein σ1 E' [] → AimedIn jj hs →
      Post F ι O σ0 (Xq ++ Ein) S Γ env τ r hs (match Q, n with
        | [], _ => (.abort jj kk, σ1)
        | _ :: _, 0 => (.timeout, σ1)
        | Kt :: Q', m + 1 => ret F O m hs (.scE e eS hid τ .int (.abort jj kk) σ1.fresh.1 Q') (ret F O m
            (.abort .drop σ1.fresh.1 :: hs) (.scX e eS hid) (evalK F O m (.capture e hid :: .capture eS hid ::
              .abort .drop σ1.fresh.1 :: hs) σ1.fresh.2 Kt (.abort σ1.fresh.1 0)))) := by
    intro σ1 E' jj kk hI1 hm haim
    have hag1 : Agree σf σ1 (Xq ++ S) := hag.trans (hm.keeps hwf hXSa hXSd)
    have hdX := (hm.apart hwf hXa hd).1
    exact post_after ((hm.widen hXa hd).relabel (E'' := E' ++ Xq) (L'' := []) fun x => by
        simp only [List.mem_append, List.not_mem_nil, or_false]; exact Or.comm) hwf
      (drop_rest hKo hS hI1 hT hag1 halloc hnd (fun l h1 h2 => hdX l h2 h1)
        (fun l h1 h2 => hSd l h1 (by simp [h2])) haim (fun a ha => hA a (List.mem_cons_of_mem _ ha)) hR hm.wf)
  rcases res with ⟨res, σ1⟩
  cases res with
  | val v =>
    obtain ⟨E', L, hI', hv, hdLE, hdLS, hm⟩ := hp
    have hwf1 := hm.wf
    obtain ⟨σ2', hdrop, hfg⟩ := dropF hfl hwf1 hv
    rw [ret.eq_def]
    simp only [bothPanic, Bool.false_eq_true, ↓reduceIte, hdrop, Option.map_some]
    refine hfg.post fun σ2 hd2 => ?_
    have hE'a : ∀ l ∈ E', σ1.mem l ≠ none := fun l hl => (hm.alloc l).mpr (.inr (.inl hl))
    have hI2 : Inv F ι σ2 Γ env E' S := hI'.dropped hd2 hwf1 hdLE hdLS
    have hm2 : Moves σ1 (E' ++ L) σ2 E' [] :=
      (hd2.widen (X := E') hE'a (fun l h1 h2 => hdLE l h2 h1)).relabel fun x => by simp
    have hm' : Moves σ0 Ein σ1 (E' ++ L) [] := hm.relabel fun x => by simp only [List.mem_append, List.not_mem_nil, or_false]
    exact rest hI2 (hm'.trans hm2 disj_nil_left hwf) (hA j (List.mem_cons_self ..))
  | abort j' k' =>
    obtain ⟨haim, E', hI', hm⟩ := hp
    rw [ret.eq_def]
    -- A task dropped as a panic unwinds that panics in its own cleanup ends the program.
    by_cases h0 : j' = 0 ∧ j = 0
    · simp only [bothPanic, h0.1, h0.2, beq_self_eq_true, Bool.and_self, ↓reduceIte]; trivial
    simp only [bothPanic, Bool.and_eq_true, beq_iff_eq, h0, ↓reduceIte]
    by_cases hj : j' = d
    · simp only [hj, ↓reduceIte]
      exact post_flushR_nil (rest hI' hm (hA j (List.mem_cons_self ..)))
    · simp only [hj, ↓reduceIte]
      exact post_flushR_nil (rest hI' hm (aimed_pop haim hj))
  | susp j' ef vs ls K =>
    simp only [ret]
    exact post_susp_abort (.scEb hS hT) (fun _ => rfl) hR.2 hA (fun _ h => by cases h) hwf hag halloc hnd hd hSa hSd hp
  | stuck => simp [Post] at hp
  | timeout => simp [ret, Post]
  | ended => simp [ret, Post]

/-! ## A scope's body running -/

/-- What gave way, resumed with `0`: what its continuation does. -/
theorem resume0 [WorldOk F O ι.w] (hKk : EvalKOk F O m) (hrefs : op.refs = []) (hret : op.ret = .int)
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

/-- A scope's body running: what it starts joins the tasks waiting; where it gives way, it goes on or
the first waiting task does; once it ends, the tasks run, its activation and value kept; if it fails,
the tasks are dropped. -/
theorem ret_scB [WorldOk F O ι.w] (hF : FnsOk F O) (hKo : ∀ m, n = m + 1 → EvalKOk F O m ∧ RetOk F O m)
    (hS : ScOk O e eS op opS rT R r τ) (hcz : ScCaps F ι σf cz R S Rc) (hT : TasksOk F O ι σf e eS r S Q Xq Aq)
    (hR : Ready O hs r) (hA : ∀ a ∈ Aq, AimedIn a hs) (hwf : WF σ0) (hag : Agree σf σ0 (Xq ++ S))
    (halloc : ∀ l ∈ Xq, σf.mem l ≠ none) (hnd : Xq.Nodup) (hd : Disj Xq Ein)
    (hSa : ∀ l ∈ S, σ0.mem l ≠ none) (hSd : Disj S (Xq ++ Ein))
    (hp : Post F ι O σ0 Ein S Γ env τ (.eff e :: .eff eS :: r) (.capture e hid :: .capture eS hid :: hs) res) :
    Post F ι O σ0 (Xq ++ Ein) S Γ env τ r hs (ret F O n hs (.scB e eS hid τ cz Q) res) := by
  have hXa : ∀ l ∈ Xq, σ0.mem l ≠ none := fun l hl => by
    rw [hag l (List.mem_append.mpr (.inl hl))]; exact halloc l hl
  have hXSa : ∀ l ∈ Xq ++ S, σ0.mem l ≠ none := fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · exact hXa l h
    · exact hSa l h
  have hXSd : Disj (Xq ++ S) Ein := fun l hl h => by
    rcases List.mem_append.mp hl with hl | hl
    · exact hd l hl h
    · exact hSd l hl (List.mem_append.mpr (.inr h))
  have hSE : Disj S Ein := fun l hl h => hSd l hl (List.mem_append.mpr (.inr h))
  have hRb : Ready O (.capture e hid :: .capture eS hid :: hs) (.eff e :: .eff eS :: r) := sc_ready hS.hop hS.hopS hR.1 hR.2
  have hdSX : Disj S Xq := fun l h1 h2 => hSd l h1 (List.mem_append.mpr (.inl h2))
  rcases res with ⟨res, σ1⟩
  cases res with
  | val v =>
    obtain ⟨E', L, hI', hv, hdLE, hdLS, hm⟩ := hp
    have hag1 : Agree σf σ1 (Xq ++ S) := hag.trans (hm.keeps hwf hXSa hXSd)
    obtain ⟨hdXE, hdXL⟩ := hm.apart hwf hXa hd
    cases Q with
    | nil =>
      cases hT
      rw [ret.eq_def]
      exact ⟨E', L, hI', hv, hdLE, hdLS, hm.relabel fun x => by simp⟩
    | cons Kt Q' =>
    cases n with
    | zero => rw [ret.eq_def]; simp [Post]
    | succ m =>
    obtain ⟨hKk, hRr⟩ := hKo m rfl
    have : ret F O (m + 1) hs (.scB e eS hid τ cz (Kt :: Q')) (.val v, σ1) =
        ret F O m hs (.scV e eS hid τ cz v Q') (evalK F O m (.capture e hid :: .capture eS hid :: hs) σ1 Kt (.val (.int 0))) := by
      rw [ret.eq_def]
    rw [this]
    cases hT with
    | cons hK hro hagt hat hSt hdSt h1 h2 hdX hT' =>
    rename_i σt op0 Γt envt St X AK Xs As
    have hwf1 := hm.wf
    have hagtX : Agree σt σ1 (X ++ St) := agree_task hagt hSt (fun l h => List.mem_append.mpr (.inl h)) hag1
    have hdq := nodup_append_disj.mp hnd
    have hres := resume0 (top := ⟨Γt, envt, .int, St, .eff e :: .eff eS :: r⟩) hKk h2 h1 hK hRb
      (fun a ha => (hA a (List.mem_append.mpr (.inl ha))).imp_right fun ⟨l, hl⟩ =>
        ⟨l, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hl)⟩) hwf1 hagtX hat hdq.1 hdSt
    have hT1 := hT'.transfer (hag1.mono fun l hl => by
      simp only [List.mem_append] at hl; rcases hl with h | h <;> simp [h])
    have hE'a : ∀ l ∈ E', σ1.mem l ≠ none := fun l hl => (hm.alloc l).mpr (.inr (.inl hl))
    have hXs1 : ∀ l ∈ Xs, σ1.mem l ≠ none := fun l hl => by
      rw [hag1 l (by simp [hl])]; exact halloc l (by simp [hl])
    have hS1 : ∀ l ∈ S, σ1.mem l ≠ none := fun l hl => by
      rw [hag1 l (by simp [hl]), ← hag l (by simp [hl])]; exact hSa l hl
    have h3 := hRr hs _ _ σ1 (.scV e eS hid τ cz v Q') ⟨Γt, envt, .int, St, .eff e :: .eff eS :: r⟩ ⟨Γ, env, τ, S, r⟩
      (E' ++ L ++ Xs) As σ1 X _
      (.scV hS (hcz.transfer (agree_S hag1)) hI' hv hdLE hdLS hT1 (fun l h1 h2 => by
        rcases List.mem_append.mp h1 with h1 | h1
        · exact hdXE l (by simp [h2]) h1
        · exact hdXL l (by simp [h2]) h1) hSt hro) hR (fun a ha => hA a (List.mem_append.mpr (.inr ha))) hwf1 Agree.self
      (fun l hl => by
        simp only [List.mem_append] at hl
        rcases hl with (h | h) | h
        · exact hE'a l h
        · exact hv.alloc l h
        · exact hXs1 l h)
      (nodup_append_disj.mpr ⟨nodup_append_disj.mpr ⟨hI'.nodup, hv.nodup, fun l h1 h2 => hdLE l h2 h1⟩,
        hdq.2.1, fun l h1 h2 => by
          rcases List.mem_append.mp h1 with h1 | h1
          · exact hdXE l (by simp [h2]) h1
          · exact hdXL l (by simp [h2]) h1⟩)
      (fun l h1 h2 => by
        simp only [List.mem_append] at h1
        rcases h1 with (h1 | h1) | h1
        · exact hdXE l (by simp [h2]) h1
        · exact hdXL l (by simp [h2]) h1
        · exact hdq.2.2 l h2 h1) hS1
      (fun l h1 h2 => by
        simp only [List.mem_append] at h2
        rcases h2 with ((h2 | h2) | h2) | h2
        · exact hI'.disj l h1 h2
        · exact hdLS l h2 h1
        · exact hdSX l h1 (by simp [h2])
        · exact hdSX l h1 (by simp [h2])) hres
    exact post_after ((hm.widen hXa hd).relabel (E'' := E' ++ L ++ Xs ++ X) (L'' := []) fun x => by
        simp only [List.mem_append, List.not_mem_nil, or_false]
        exact ⟨fun h => by rcases h with ((h | h) | h) | h <;> simp [h],
          fun h => by rcases h with ((h | h) | h) | h <;> simp [h]⟩)
      hwf (by simpa using h3)
  | abort j k =>
    obtain ⟨haim, E', hI', hm⟩ := hp
    have hag1 : Agree σf σ1 (Xq ++ S) := hag.trans (hm.keeps hwf hXSa hXSd)
    have hdXE := (hm.apart hwf hXa hd).1
    rw [ret.eq_def]
    exact post_after ((hm.widen hXa hd).relabel (E'' := E' ++ Xq) (L'' := []) fun x => by
        simp only [List.mem_append, List.not_mem_nil, or_false]; exact Or.comm) hwf
      (drop_rest hKo hS hI' hT hag1 halloc hnd (fun l h1 h2 => hdXE l h2 h1)
        hdSX (aimed_uncap2 haim) hA hR hm.wf)
  | susp j ef vs ls K =>
    by_cases hc : j ≠ hid ∨ (ef ≠ e ∧ ef ≠ eS)
    · have : ret F O n hs (.scB e eS hid τ cz Q) (.susp j ef vs ls K, σ1) =
          (.susp j ef vs ls (.scB e eS hid τ cz Q :: K), σ1) := by
        rw [ret.eq_def]; simp [hc]
      rw [this]
      exact post_susp (.scB hS hcz hT) hR.2 (fun _ h => aimed_uncap2 h) hA (fun h => by
        rcases h.of_cons_capture with ⟨rfl, rfl⟩ | h
        · simp at hc
        rcases h.of_cons_capture with ⟨rfl, rfl⟩ | h
        · simp at hc
        · exact h) hwf hag halloc hnd hd hSa hSd hp
    have hj : j = hid := by
      by_cases h : j = hid
      · exact h
      · exact absurd (.inl h) hc
    subst hj
    obtain ⟨op', X', hos, A', Lv, -, hop', -, haim, hK', hls, hvs, hLn, hdLX, hdLS, hm⟩ := hp
    have hop'r : op'.refs = [] := by
      by_cases hsp : ef = eS
      · subst hsp; rw [hS.hopS] at hop'; cases hop'; exact hS.hSrefs
      · have : ef = e := by
          by_cases h : ef = e
          · exact h
          · exact absurd (.inr ⟨h, hsp⟩) hc
        subst this; rw [hS.hop] at hop'; cases hop'; exact hS.hrefs
    obtain ⟨-, -, -, -, -, -, -, -, hts, -, -, hXn', -⟩ := hK'.base_of
    rw [hop'r] at hts
    obtain rfl : hos = [] := List.map_eq_nil_iff.mp hts
    simp only [olds, mutCells, List.map_nil, List.flatMap_nil, List.append_nil] at hm hdLX hdLS
    have hwf1 := hm.wf
    have hag1 : Agree σf σ1 (Xq ++ S) := hag.trans (hm.keeps hwf hXSa hXSd)
    have hdX' := (hm.apart hwf hXSa hXSd).1
    have hdXL' := (hm.apart hwf hXSa hXSd).2
    have hS1 : ∀ l ∈ S, σ1.mem l ≠ none := fun l hl => by
      rw [hag1 l (by simp [hl]), ← hag l (by simp [hl])]; exact hSa l hl
    have hXq1 : ∀ l ∈ Xq, σ1.mem l ≠ none := fun l hl => by
      rw [hag1 l (by simp [hl])]; exact halloc l hl
    have hX'a : ∀ l ∈ X', σ1.mem l ≠ none := fun l hl => (hm.alloc l).mpr (.inr (.inl hl))
    cases n with
    | zero =>
      rw [ret.eq_def]; simp only [ne_eq, not_true_eq_false, false_or]
      split <;> simp_all [Post]
    | succ m =>
    obtain ⟨hKk, hRr⟩ := hKo m rfl
    by_cases hsp : ef = eS
    · -- A task started: it joins the tasks waiting, and the body goes on.
      subst hsp
      obtain rfl : opS = op' := Option.some.inj (hS.hopS.symm.trans hop')
      rw [hS.hSowns] at hvs
      cases hvs with
      | cons hv hrest =>
      cases hrest
      rename_i w Lw
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hm hdLX hdLS hLn
      obtain ⟨Kt, σ2, Xt, Γk, envk, hmk, hKt, hroT, hmt⟩ := mkTask_ok ((O[ef]?.map Op.spawns).getD false) hF hS (hcz.transfer (agree_S hag1)) hv hwf1 hdLS
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hXtn, -⟩ := hKt.base_of
      have : ret F O (m + 1) hs (.scB e ef j τ cz Q) (.susp j ef [w] ls K, σ1) =
          ret F O m hs (.scB e ef j τ cz (Q ++ [Kt])) (evalK F O m (.capture e j :: .capture ef j :: hs) σ2 K (.val (.int 0))) := by
        rw [ret.eq_def]; simp [hmk]
      rw [this]
      have hwf2 := hmt.wf
      have hag12 : Agree σ1 σ2 (X' ++ Xq ++ S) := hmt.keeps hwf1 (fun l hl => by
          simp only [List.mem_append] at hl
          rcases hl with (h | h) | h
          · exact hX'a l h
          · exact hXq1 l h
          · exact hS1 l h)
        (fun l h1 h2 => by
          simp only [List.mem_append] at h1
          rcases h1 with (h1 | h1) | h1
          · exact hdLX l h2 h1
          · exact hdXL' l (by simp [h1]) (by simpa using h2)
          · exact hdLS l h2 h1)
      obtain ⟨hdLt, -⟩ := hmt.apart hwf1 (fun l hl => by
          simp only [List.mem_append] at hl
          rcases hl with (h | h) | h
          · exact hX'a l h
          · exact hXq1 l h
          · exact hS1 l h)
        (show Disj (X' ++ Xq ++ S) Lw from fun l h1 h2 => by
          simp only [List.mem_append] at h1
          rcases h1 with (h1 | h1) | h1
          · exact hdLX l h2 h1
          · exact hdXL' l (by simp [h1]) (by simpa using h2)
          · exact hdLS l h2 h1)
      have hXq2 : ∀ l ∈ Xq, σ2.mem l ≠ none := fun l hl => by rw [hag12 l (by simp [hl])]; exact hXq1 l hl
      have hres := resume0 (top := ⟨Γ, env, τ, S, .eff e :: .eff ef :: r⟩) hKk
        hS.hSrefs hS.hSret hK' hRb haim hwf2 (hag12.mono fun l hl => by
          rcases List.mem_append.mp hl with h | h <;> simp [h])
        (fun l hl => by
          rcases List.mem_append.mp hl with h | h
          · exact hX'a l h
          · exact hS1 l h) hXn' (fun l h1 h2 => hdX' l (by simp [h1]) h2)
      have hS2 : ∀ l ∈ S, σ2.mem l ≠ none := fun l hl => by rw [hag12 l (by simp [hl])]; exact hS1 l hl
      have hag2 : Agree σf σ2 (Xq ++ S) := hag1.trans (hag12.mono fun l hl => by
        simp only [List.mem_append] at hl ⊢; rcases hl with h | h <;> simp [h])
      have hT2 := (hT.transfer hag2).append hKt hroT Agree.self (fun l hl => by
          rcases List.mem_append.mp hl with h | h
          · exact (hmt.alloc l).mpr (.inr (.inl h))
          · exact hS2 l (hcz.hRc l h)) hcz.hRc (fun l h1 h2 => hdLt l (by simp [hcz.hRc l h1]) h2) hS.hret hS.hrefs
        (fun l h1 h2 => hdLt l (by simp [h1]) h2)
      have h3 := hRr hs _ _ σ2 (.scB e ef j τ cz (Q ++ [Kt])) ⟨Γ, env, τ, S, .eff e :: .eff ef :: r⟩ ⟨Γ, env, τ, S, r⟩
        (Xq ++ Xt) (Aq ++ []) σ2 X' _ (.scB hS (hcz.transfer (agree_S hag2)) hT2) hR (fun a ha => by simpa using hA a (by simpa using ha)) hwf2
        Agree.self
        (fun l hl => by
          rcases List.mem_append.mp hl with h | h
          · exact hXq2 l h
          · exact (hmt.alloc l).mpr (.inr (.inl h)))
        (nodup_append_disj.mpr ⟨hnd, hXtn, fun l h1 h2 => hdLt l (by simp [h1]) h2⟩)
        (fun l h1 h2 => by
          rcases List.mem_append.mp h1 with h1 | h1
          · exact hdX' l (by simp [h1]) h2
          · exact hdLt l (by simp [h2]) h1)
        hS2
        (fun l h1 h2 => by
          simp only [List.mem_append] at h2
          rcases h2 with (h2 | h2) | h2
          · exact hdSX l h1 h2
          · exact hdLt l (by simp [h1]) h2
          · exact hdX' l (by simp [h1]) h2) hres
      have m1 := (hm.widen hXa hd).relabel (E'' := X' ++ Xq ++ Lw) (L'' := []) fun x => by
        simp only [List.mem_append, List.not_mem_nil, or_false]
        exact ⟨fun h => by rcases h with (h | h) | h <;> simp [h], fun h => by rcases h with (h | h) | h <;> simp [h]⟩
      have m2 := hmt.widen (X := X' ++ Xq) (fun l hl => by
          rcases List.mem_append.mp hl with h | h
          · exact hX'a l h
          · exact hXq1 l h)
        (fun l h1 h2 => by
          rcases List.mem_append.mp h1 with h1 | h1
          · exact hdLX l h2 h1
          · exact hdXL' l (by simp [h1]) (by simpa using h2))
      exact post_after ((m1.trans m2 disj_nil_left hwf).relabel (E'' := Xq ++ Xt ++ X') (L'' := []) fun x => by
        simp only [List.mem_append, List.not_mem_nil, or_false, List.nil_append]
        exact ⟨fun h => by rcases h with (h | h) | h <;> simp [h], fun h => by rcases h with (h | h) | h <;> simp [h]⟩)
        hwf (by simpa using h3)
    · -- The body gave way: it goes on, or the first task waiting does, the body waiting where it gave way.
      have hef : ef = e := by
        by_cases h : ef = e
        · exact h
        · exact absurd (.inr ⟨h, hsp⟩) hc
      subst hef
      obtain rfl : op = op' := Option.some.inj (hS.hop.symm.trans hop')
      rw [hS.howns] at hvs
      cases hvs
      simp only [List.flatten_nil, List.append_nil] at hm
      have hwf2 : WF σ1.fresh.2 := hwf1
      have hag2 : Agree σf σ1.fresh.2 (Xq ++ S) := hag1.trans (Agree.of' fun _ _ => rfl)
      have hm2 : Moves σ0 (Xq ++ Ein) σ1.fresh.2 (Xq ++ X') [] :=
        ((hm.widen hXa hd).relabel (E'' := Xq ++ X') (L'' := []) fun x => by simp).trans
          (Moves.freshen hwf1 fun l hl => by
            rcases List.mem_append.mp hl with h | h
            · exact hXq1 l h
            · exact hX'a l h) disj_nil_left hwf |>.relabel fun x => by simp
      -- The body goes on.
      have bodyOn : Post F ι O σ0 (Xq ++ Ein) S Γ env τ r hs (ret F O m hs (.scB ef eS j τ cz Q)
          (evalK F O m (.capture ef j :: .capture eS j :: hs) σ1.fresh.2 K (.val (.int 0)))) := by
        have hres := resume0 (top := ⟨Γ, env, τ, S, .eff ef :: .eff eS :: r⟩) hKk hS.hrefs hS.hret hK' hRb haim
          hwf2 (Agree.of' fun _ _ => rfl) (fun l hl => by
            rcases List.mem_append.mp hl with h | h
            · exact hX'a l h
            · exact hS1 l h) hXn' (fun l h1 h2 => hdX' l (by simp [h1]) h2)
        have h3 := hRr hs _ _ σf (.scB ef eS j τ cz Q) ⟨Γ, env, τ, S, .eff ef :: .eff eS :: r⟩ ⟨Γ, env, τ, S, r⟩
          Xq Aq σ1.fresh.2 X' _ (.scB hS hcz hT) hR hA hwf2 hag2 halloc hnd (fun l h1 h2 => hdX' l (by simp [h1]) h2)
          hS1 (fun l h1 h2 => by
            rcases List.mem_append.mp h2 with h2 | h2
            · exact hdSX l h1 h2
            · exact hdX' l (by simp [h1]) h2) hres
        exact post_after hm2 hwf h3
      cases Q with
      | nil =>
        have : ret F O (m + 1) hs (.scB ef eS j τ cz []) (.susp j ef [] ls K, σ1) =
            ret F O m hs (.scB ef eS j τ cz []) (evalK F O m (.capture ef j :: .capture eS j :: hs) σ1.fresh.2 K
              (.val (.int 0))) := by
          rw [ret.eq_def]; simp [hsp]
        rw [this]; exact bodyOn
      | cons Kt Q' =>
      have : ret F O (m + 1) hs (.scB ef eS j τ cz (Kt :: Q')) (.susp j ef [] ls K, σ1) =
          if σ1.sched (σ1.ids + 1) = true then
            ret F O m hs (.scB ef eS j τ cz (Kt :: Q')) (evalK F O m (.capture ef j :: .capture eS j :: hs) σ1.fresh.2 K
              (.val (.int 0)))
          else
            ret F O m hs (.scW ef eS j τ cz K Q') (evalK F O m (.capture ef j :: .capture eS j :: hs) σ1.fresh.2 Kt
              (.val (.int 0))) := by
        rw [ret.eq_def]; simp [hsp]; rfl
      rw [this]
      split
      · exact bodyOn
      · -- The first task waiting goes on; the body waits where it gave way.
        cases hT with
        | cons hK hro hagt hat hSt hdSt h1 h2 hdX hT' =>
        rename_i σt op0 Γt envt St X AK Xs As
        have hdq := nodup_append_disj.mp hnd
        have hagt2 : Agree σt σ1.fresh.2 (X ++ St) := agree_task hagt hSt (fun l h => List.mem_append.mpr (.inl h)) hag2
        have hres := resume0 (top := ⟨Γt, envt, .int, St, .eff ef :: .eff eS :: r⟩) hKk h2 h1 hK hRb
          (fun a ha => (hA a (List.mem_append.mpr (.inl ha))).imp_right fun ⟨l, hl⟩ =>
            ⟨l, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hl)⟩) hwf2 hagt2 hat hdq.1 hdSt
        have hT1 := hT'.transfer (hag1.mono fun l hl => by
          simp only [List.mem_append] at hl; rcases hl with h | h <;> simp [h])
        have hXs1 : ∀ l ∈ Xs, σ1.mem l ≠ none := fun l hl => hXq1 l (by simp [hl])
        have h3 := hRr hs _ _ σ1 (.scW ef eS j τ cz K Q') ⟨Γt, envt, .int, St, .eff ef :: .eff eS :: r⟩
          ⟨Γ, env, τ, S, r⟩ (X' ++ Xs) (A' ++ As)
          σ1.fresh.2 X _ (.scW hS (hcz.transfer (agree_S hag1)) hS.hret hS.hrefs hK' Agree.self (fun l hl => by
              rcases List.mem_append.mp hl with h | h
              · exact hX'a l h
              · exact hS1 l h) hT1 (fun l h1 h2 => hdX' l (by simp [h2]) h1) hSt hro) hR
          (fun a ha => by
            rcases List.mem_append.mp ha with h | h
            · exact aimed_uncap2 (haim a h)
            · exact hA a (List.mem_append.mpr (.inr h))) hwf2 (Agree.of' fun _ _ => rfl)
          (fun l hl => by
            rcases List.mem_append.mp hl with h | h
            · exact hX'a l h
            · exact hXs1 l h)
          (nodup_append_disj.mpr ⟨hXn', hdq.2.1, fun l h1 h2 => hdX' l (by simp [h2]) h1⟩)
          (fun l h1 h2 => by
            rcases List.mem_append.mp h1 with h1 | h1
            · exact hdX' l (by simp [h2]) h1
            · exact hdq.2.2 l h2 h1) hS1
          (fun l h1 h2 => by
            simp only [List.mem_append] at h2
            rcases h2 with (h2 | h2) | h2
            · exact hdX' l (by simp [h1]) h2
            · exact hdSX l h1 (by simp [h2])
            · exact hdSX l h1 (by simp [h2])) hres
        exact post_after (hm2.relabel (E'' := X' ++ Xs ++ X) (L'' := []) fun x => by
          simp only [List.mem_append, List.not_mem_nil, or_false]
          exact ⟨fun h => by rcases h with (h | h) | h <;> simp [h], fun h => by rcases h with (h | h) | h <;> simp [h]⟩)
          hwf (by simpa using h3)
  | stuck => simp [Post] at hp
  | timeout => simp [ret, Post]
  | ended => simp [ret, Post]


/-! ## A scope's task running, its body waiting -/

/-- A scope's task running, its body waiting where it gave way: what the task starts joins the tasks
waiting; where it gives way, it goes on, or it waits last and the body goes on; once it ends, the
body goes on; if it fails, the body is dropped, then the other tasks. -/
theorem ret_scW [WorldOk F O ι.w] (hF : FnsOk F O) (hKo : ∀ m, n = m + 1 → EvalKOk F O m ∧ RetOk F O m)
    (hS : ScOk O e eS op opS rT R r τ) (hcz : ScCaps F ι σf cz R S Rc) (hbr : opb.ret = .int) (hbrefs : opb.refs = [])
    (hKb : FramesOk F O ι σb Kb opb ⟨Γ, env, τ, S, .eff e :: .eff eS :: r⟩ Xb [] Ab)
    (hagb : Agree σb σf (Xb ++ S)) (hab : ∀ l ∈ Xb ++ S, σb.mem l ≠ none)
    (hT : TasksOk F O ι σf e eS r S Q Xq Aq) (hdbq : Disj Xb Xq) (hSt : ∀ l ∈ St, l ∈ S) (hro : RoCtx Γt)
    (hR : Ready O hs r) (hA : ∀ a ∈ Ab ++ Aq, AimedIn a hs) (hwf : WF σ0) (hag : Agree σf σ0 (Xb ++ Xq ++ S))
    (halloc : ∀ l ∈ Xb ++ Xq, σf.mem l ≠ none) (hnd : (Xb ++ Xq).Nodup) (hd : Disj (Xb ++ Xq) Ein)
    (hSa : ∀ l ∈ S, σ0.mem l ≠ none) (hSd : Disj S (Xb ++ Xq ++ Ein))
    (hp : Post F ι O σ0 Ein St Γt envt .int (.eff e :: .eff eS :: r) (.capture e hid :: .capture eS hid :: hs) res) :
    Post F ι O σ0 (Xb ++ Xq ++ Ein) S Γ env τ r hs (ret F O n hs (.scW e eS hid τ cz Kb Q) res) := by
  have hXa : ∀ l ∈ Xb ++ Xq, σ0.mem l ≠ none := fun l hl => by
    rw [hag l (List.mem_append.mpr (.inl hl))]; exact halloc l hl
  have hXSa : ∀ l ∈ Xb ++ Xq ++ S, σ0.mem l ≠ none := fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · exact hXa l h
    · exact hSa l h
  have hXSd : Disj (Xb ++ Xq ++ S) Ein := fun l hl h => by
    rcases List.mem_append.mp hl with hl | hl
    · exact hd l hl h
    · exact hSd l hl (List.mem_append.mpr (.inr h))
  have hbq := nodup_append_disj.mp hnd
  have hRb : Ready O (.capture e hid :: .capture eS hid :: hs) (.eff e :: .eff eS :: r) := sc_ready hS.hop hS.hopS hR.1 hR.2
  have hdSb : Disj S Xb := fun l h1 h2 => hSd l h1 (by simp [h2])
  have hdSq : Disj S Xq := fun l h1 h2 => hSd l h1 (by simp [h2])
  have hfS : ∀ l ∈ S, σf.mem l ≠ none := fun l hl => by
    rw [← hag l (by simp [hl])]; exact hSa l hl
  -- The body, resumed where it gave way.
  have resumeB : ∀ {σr} m, EvalKOk F O m → WF σr → Agree σf σr (Xb ++ Xq ++ S) →
      Post F ι O σr Xb S Γ env τ (.eff e :: .eff eS :: r) (.capture e hid :: .capture eS hid :: hs)
        (evalK F O m (.capture e hid :: .capture eS hid :: hs) σr Kb (.val (.int 0))) := by
    intro σr m hKk hwfr hagr
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hXbn, -⟩ := hKb.base_of
    exact resume0 (top := ⟨Γ, env, τ, S, .eff e :: .eff eS :: r⟩) hKk hbrefs hbr hKb hRb
      (fun a ha => (hA a (List.mem_append.mpr (.inl ha))).imp_right fun ⟨l, hl⟩ =>
        ⟨l, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hl)⟩) hwfr
      (hagb.trans (hagr.mono fun l hl => by rcases List.mem_append.mp hl with h | h <;> simp [h])) hab hXbn
      (fun l h1 h2 => hdSb l h1 h2)
  rcases res with ⟨res, σ1⟩
  cases res with
  | val v =>
    obtain ⟨E', L, hI', hv, -, -, hm⟩ := hp
    obtain rfl := foot_ro hI'.foot hro
    obtain rfl : L = [] := by cases hv; rfl
    cases n with
    | zero => rw [ret.eq_def]; simp [Post]
    | succ m =>
    obtain ⟨hKk, hRr⟩ := hKo m rfl
    have : ret F O (m + 1) hs (.scW e eS hid τ cz Kb Q) (.val v, σ1) =
        ret F O m hs (.scB e eS hid τ cz Q) (evalK F O m (.capture e hid :: .capture eS hid :: hs) σ1 Kb (.val (.int 0))) := by
      rw [ret.eq_def]
    rw [this]
    have hwf1 := hm.wf
    have hag1 : Agree σf σ1 (Xb ++ Xq ++ S) := hag.trans (hm.keeps hwf hXSa hXSd)
    have hres := resumeB m hKk hwf1 hag1
    have hS1 : ∀ l ∈ S, σ1.mem l ≠ none := fun l hl => by rw [hag1 l (by simp [hl])]; exact hfS l hl
    have h3 := hRr hs _ _ σf (.scB e eS hid τ cz Q) ⟨Γ, env, τ, S, .eff e :: .eff eS :: r⟩ ⟨Γ, env, τ, S, r⟩ Xq Aq σ1 Xb _
      (.scB hS hcz hT) hR (fun a ha => hA a (List.mem_append.mpr (.inr ha))) hwf1
      (hag1.mono fun l hl => by rcases List.mem_append.mp hl with h | h <;> simp [h])
      (fun l hl => halloc l (by simp [hl])) hbq.2.1 (fun l h1 h2 => hdbq l h2 h1) hS1
      (fun l h1 h2 => by
        rcases List.mem_append.mp h2 with h2 | h2
        · exact hdSq l h1 h2
        · exact hdSb l h1 h2) hres
    exact post_after ((hm.widen hXa hd).relabel (E'' := Xq ++ Xb) (L'' := []) fun x => by
        simp only [List.mem_append, List.not_mem_nil, or_false, List.append_nil]
        exact ⟨fun h => by rcases h with h | h <;> simp [h], fun h => by rcases h with h | h <;> simp [h]⟩)
      hwf h3
  | abort j k =>
    obtain ⟨haim, E', hI', hm⟩ := hp
    obtain rfl := foot_ro hI'.foot hro
    cases n with
    | zero => rw [ret.eq_def]; simp [Post]
    | succ m =>
    obtain ⟨hKk, hRr⟩ := hKo m rfl
    have : ret F O (m + 1) hs (.scW e eS hid τ cz Kb Q) (.abort j k, σ1) =
        ret F O m hs (.scE e eS hid τ τ (.abort j k) σ1.fresh.1 Q) (ret F O m (.abort .drop σ1.fresh.1 :: hs)
          (.scX e eS hid) (evalK F O m (.capture e hid :: .capture eS hid :: .abort .drop σ1.fresh.1 :: hs)
            σ1.fresh.2 Kb (.abort σ1.fresh.1 0))) := by
      rw [ret.eq_def]
    rw [this]
    generalize hdd : σ1.fresh.1 = d
    have hwf1 := hm.wf
    have hwf2 : WF σ1.fresh.2 := hwf1
    have hag1 : Agree σf σ1 (Xb ++ Xq ++ S) := hag.trans (hm.keeps hwf hXSa hXSd)
    have hag2 : Agree σf σ1.fresh.2 (Xb ++ Xq ++ S) := hag1.trans (Agree.of' fun _ _ => rfl)
    have hR2 : Ready O (.abort .drop d :: hs) r := ⟨.abort (by intro e h; cases h) hR.1, fun l hl => covers_cons _ hR.2 l hl⟩
    have hR3 : Ready O (.capture e hid :: .capture eS hid :: .abort .drop d :: hs) (.eff e :: .eff eS :: r) :=
      sc_ready hS.hop hS.hopS hR2.1 hR2.2
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hXbn, -⟩ := hKb.base_of
    have hk1 := hKk (.capture e hid :: .capture eS hid :: .abort .drop d :: hs) _ σb Kb _ Xb [] Ab σ1.fresh.2 []
      (.abort d 0) opb [] hKb hR3
      (fun a ha => (hA a (List.mem_append.mpr (.inl ha))).imp_right fun ⟨l, hl⟩ =>
        ⟨l, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hl))⟩) hwf2
      (hagb.trans (hag2.mono fun l hl => by rcases List.mem_append.mp hl with h | h <;> simp [h])) hab hXbn rfl
      (fun _ h => by simp at h) (by simp [mutCells]) (by simp [mutCells, Disj])
      (by simpa [mutCells] using hdSb)
      (.inr ⟨d, 0, rfl, .inr ⟨.drop, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩, rfl⟩)
    simp only [mutCells, List.flatMap_nil, List.append_nil] at hk1
    have hS2 : ∀ l ∈ S, σ1.fresh.2.mem l ≠ none := fun l hl => by
      show σ1.mem l ≠ none
      rw [hag1 l (by simp [hl])]; exact hfS l hl
    have hk2 := hRr (.abort .drop d :: hs) _ _ σ1.fresh.2 (.scX e eS hid) ⟨Γ, env, τ, S, .eff e :: .eff eS :: r⟩
      ⟨Γ, env, τ, S, r⟩ [] [] σ1.fresh.2 Xb _ (.scX hS.hop hS.howns hS.hrefs hS.hret hS.hopS hS.hSowns hS.hSrefs hS.hSret)
      hR2 (fun _ h => by simp at h) hwf2 Agree.self (fun _ h => by simp at h) List.nodup_nil disj_nil_left hS2
      (by simpa using hdSb) hk1
    simp only [List.nil_append] at hk2
    have hk3 := hRr hs _ _ σf (.scE e eS hid τ τ (.abort j k) d Q) ⟨Γ, env, τ, S, r⟩ ⟨Γ, env, τ, S, r⟩ Xq (j :: Aq)
      σ1.fresh.2 Xb _ (.scEb hS hT) hR
      (fun a ha => by
        rcases List.mem_cons.mp ha with rfl | ha
        · exact aimed_uncap2 haim
        · exact hA a (List.mem_append.mpr (.inr ha))) hwf2
      (hag2.mono fun l hl => by rcases List.mem_append.mp hl with h | h <;> simp [h])
      (fun l hl => halloc l (by simp [hl])) hbq.2.1 (fun l h1 h2 => hdbq l h2 h1) hS2
      (fun l h1 h2 => by
        rcases List.mem_append.mp h2 with h2 | h2
        · exact hdSq l h1 h2
        · exact hdSb l h1 h2) hk2
    exact post_after (((hm.widen hXa hd).relabel (E'' := Xb ++ Xq) (L'' := []) fun x => by simp).trans
      (Moves.freshen hwf1 fun l hl => by rw [hag1 l (List.mem_append.mpr (.inl hl))]; exact halloc l hl)
        disj_nil_left hwf |>.relabel
      fun x => by
        simp only [List.mem_append, List.not_mem_nil, or_false, List.nil_append]
        exact ⟨fun h => by rcases h with h | h <;> simp [h], fun h => by rcases h with h | h <;> simp [h]⟩) hwf hk3
  | susp j ef vs ls K =>
    by_cases hc : j ≠ hid ∨ (ef ≠ e ∧ ef ≠ eS)
    · have : ret F O n hs (.scW e eS hid τ cz Kb Q) (.susp j ef vs ls K, σ1) =
          (.susp j ef vs ls (.scW e eS hid τ cz Kb Q :: K), σ1) := by
        rw [ret.eq_def]; simp [hc]
      rw [this]
      exact post_susp (.scW hS hcz hbr hbrefs hKb hagb hab hT hdbq hSt hro) hR.2 (fun _ h => aimed_uncap2 h) hA (fun h => by
        rcases h.of_cons_capture with ⟨rfl, rfl⟩ | h
        · simp at hc
        rcases h.of_cons_capture with ⟨rfl, rfl⟩ | h
        · simp at hc
        · exact h) hwf hag halloc hnd hd hSa hSd hp
    have hj : j = hid := by
      by_cases h : j = hid
      · exact h
      · exact absurd (.inl h) hc
    subst hj
    obtain ⟨op', X', hos, A', Lv, -, hop', -, haim, hK', hls, hvs, hLn, hdLX, hdLS, hm⟩ := hp
    have hop'r : op'.refs = [] := by
      by_cases hsp : ef = eS
      · subst hsp; rw [hS.hopS] at hop'; cases hop'; exact hS.hSrefs
      · have : ef = e := by
          by_cases h : ef = e
          · exact h
          · exact absurd (.inr ⟨h, hsp⟩) hc
        subst this; rw [hS.hop] at hop'; cases hop'; exact hS.hrefs
    obtain ⟨-, -, -, -, -, -, -, -, hts, -, -, hXn', -⟩ := hK'.base_of
    rw [hop'r] at hts
    obtain rfl : hos = [] := List.map_eq_nil_iff.mp hts
    simp only [olds, mutCells, List.map_nil, List.flatMap_nil, List.append_nil] at hm hdLX hdLS
    have hwf1 := hm.wf
    have hag1 : Agree σf σ1 (Xb ++ Xq ++ S) := hag.trans (hm.keeps hwf hXSa hXSd)
    have hdX' := (hm.apart hwf hXSa hXSd).1
    have hdXL' := (hm.apart hwf hXSa hXSd).2
    have hS1 : ∀ l ∈ S, σ1.mem l ≠ none := fun l hl => by rw [hag1 l (by simp [hl])]; exact hfS l hl
    have hXq1 : ∀ l ∈ Xb ++ Xq, σ1.mem l ≠ none := fun l hl => by
      rw [hag1 l (List.mem_append.mpr (.inl hl))]; exact halloc l hl
    have hX'a : ∀ l ∈ X', σ1.mem l ≠ none := fun l hl => (hm.alloc l).mpr (.inr (.inl hl))
    have hX'St : ∀ l ∈ X' ++ St, σ1.mem l ≠ none := fun l hl => by
      rcases List.mem_append.mp hl with h | h
      · exact hX'a l h
      · exact hS1 l (hSt l h)
    have hdStX' : Disj St X' := fun l h1 h2 => hdX' l (List.mem_append.mpr (.inr (hSt l h1))) h2
    cases n with
    | zero =>
      rw [ret.eq_def]; simp only [ne_eq, not_true_eq_false, false_or]
      split <;> simp_all [Post]
    | succ m =>
    obtain ⟨hKk, hRr⟩ := hKo m rfl
    by_cases hsp : ef = eS
    · -- The task started a task: it joins the tasks waiting, and the task goes on.
      subst hsp
      obtain rfl : opS = op' := Option.some.inj (hS.hopS.symm.trans hop')
      rw [hS.hSowns] at hvs
      cases hvs with
      | cons hv hrest =>
      cases hrest
      rename_i w Lw
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hm hdLX hdLS hLn hdXL'
      obtain ⟨Kt, σ2, Xt, Γk, envk, hmk, hKt, hroT, hmt⟩ :=
        mkTask_ok ((O[ef]?.map Op.spawns).getD false) hF hS (hcz.transfer (agree_S hag1)) hv hwf1 fun l h1 h2 => hdXL' l (by simp [h2]) h1
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hXtn, -⟩ := hKt.base_of
      have : ret F O (m + 1) hs (.scW e ef j τ cz Kb Q) (.susp j ef [w] ls K, σ1) =
          ret F O m hs (.scW e ef j τ cz Kb (Q ++ [Kt]))
            (evalK F O m (.capture e j :: .capture ef j :: hs) σ2 K (.val (.int 0))) := by
        rw [ret.eq_def]; simp [hmk]
      rw [this]
      have hwf2 := hmt.wf
      have hkeepA : ∀ l ∈ X' ++ (Xb ++ Xq) ++ S, σ1.mem l ≠ none := fun l hl => by
        simp only [List.mem_append] at hl
        rcases hl with (h | h | h) | h
        · exact hX'a l h
        · exact hXq1 l (by simp [h])
        · exact hXq1 l (by simp [h])
        · exact hS1 l h
      have hkeepD : Disj (X' ++ (Xb ++ Xq) ++ S) Lw := fun l h1 h2 => by
        simp only [List.mem_append] at h1
        rcases h1 with (h1 | h1 | h1) | h1
        · exact hdLX l h2 h1
        · exact hdXL' l (by simp [h1]) h2
        · exact hdXL' l (by simp [h1]) h2
        · exact hdXL' l (by simp [h1]) h2
      have hag12 : Agree σ1 σ2 (X' ++ (Xb ++ Xq) ++ S) := hmt.keeps hwf1 hkeepA hkeepD
      obtain ⟨hdLt, -⟩ := hmt.apart hwf1 hkeepA hkeepD
      have hag2 : Agree σf σ2 (Xb ++ Xq ++ S) := hag1.trans (hag12.mono fun l hl => by
        simp only [List.mem_append] at hl ⊢; grind)
      have hS2 : ∀ l ∈ S, σ2.mem l ≠ none := fun l hl => by rw [hag12 l (by simp [hl])]; exact hS1 l hl
      have hres := resume0 (top := ⟨Γt, envt, .int, St, .eff e :: .eff ef :: r⟩) hKk hS.hSrefs hS.hSret hK' hRb haim hwf2
        (hag12.mono fun l hl => by
          rcases List.mem_append.mp hl with h | h
          · simp [h]
          · simp [hSt l h])
        hX'St hXn' hdStX'
      have hT2 := (hT.transfer (hag2.mono fun l hl => by
          simp only [List.mem_append] at hl ⊢; rcases hl with h | h <;> simp [h])).append hKt hroT Agree.self
        (fun l hl => by
          rcases List.mem_append.mp hl with h | h
          · exact (hmt.alloc l).mpr (.inr (.inl h))
          · exact hS2 l (hcz.hRc l h)) hcz.hRc (fun l h1 h2 => hdLt l (by simp [hcz.hRc l h1]) h2) hS.hret hS.hrefs
        (fun l h1 h2 => hdLt l (by simp [h1]) h2)
      have h3 := hRr hs _ _ σ2 (.scW e ef j τ cz Kb (Q ++ [Kt])) ⟨Γt, envt, .int, St, .eff e :: .eff ef :: r⟩ ⟨Γ, env, τ, S, r⟩
        (Xb ++ (Xq ++ Xt)) (Ab ++ (Aq ++ [])) σ2 X' _
        (.scW hS (hcz.transfer (agree_S hag2)) hbr hbrefs hKb (hagb.trans (hag2.mono fun l hl => by
            rcases List.mem_append.mp hl with h | h <;> simp [h])) hab hT2
          (fun l h1 h2 => by
            rcases List.mem_append.mp h2 with h2 | h2
            · exact hdbq l h1 h2
            · exact hdLt l (by simp [h1]) h2) hSt hro) hR
        (fun a ha => hA a (by simpa using ha)) hwf2 Agree.self
        (fun l hl => by
          simp only [List.mem_append] at hl
          rcases hl with h | h | h
          · rw [hag12 l (by simp [h])]; exact hXq1 l (by simp [h])
          · rw [hag12 l (by simp [h])]; exact hXq1 l (by simp [h])
          · exact (hmt.alloc l).mpr (.inr (.inl h)))
        (by
          refine nodup_append_disj.mpr ⟨hbq.1, nodup_append_disj.mpr ⟨hbq.2.1, hXtn, fun l h1 h2 =>
            hdLt l (by simp [h1]) h2⟩, fun l h1 h2 => ?_⟩
          rcases List.mem_append.mp h2 with h2 | h2
          · exact hdbq l h1 h2
          · exact hdLt l (by simp [h1]) h2)
        (fun l h1 h2 => by
          simp only [List.mem_append] at h1
          rcases h1 with h1 | h1 | h1
          · exact hdX' l (by simp [h1]) h2
          · exact hdX' l (by simp [h1]) h2
          · exact hdLt l (by simp [h2]) h1)
        hS2
        (fun l h1 h2 => by
          simp only [List.mem_append] at h2
          rcases h2 with (h2 | h2 | h2) | h2
          · exact hdSb l h1 h2
          · exact hdSq l h1 h2
          · exact hdLt l (by simp [h1]) h2
          · exact hdX' l (by simp [h1]) h2) hres
      have m1 := (hm.widen hXa hd).relabel (E'' := X' ++ (Xb ++ Xq) ++ Lw) (L'' := []) fun x => by
        simp only [List.mem_append, List.not_mem_nil, or_false, false_or, or_assoc, or_comm, or_left_comm]
      have m2 := hmt.widen (X := X' ++ (Xb ++ Xq)) (fun l hl => hkeepA l (by simp only [List.mem_append] at hl ⊢; grind))
        (fun l h1 h2 => hkeepD l (by simp only [List.mem_append] at h1 ⊢; grind) h2)
      exact post_after ((m1.trans m2 disj_nil_left hwf).relabel (E'' := Xb ++ (Xq ++ Xt) ++ X') (L'' := []) fun x => by
        simp only [List.mem_append, List.not_mem_nil, or_false, List.nil_append, false_or, or_assoc, or_comm, or_left_comm])
        hwf (by simpa using h3)
    · -- The task gave way: it goes on, or it waits last and the body goes on.
      have hef : ef = e := by
        by_cases h : ef = e
        · exact h
        · exact absurd (.inr ⟨h, hsp⟩) hc
      subst hef
      obtain rfl : op = op' := Option.some.inj (hS.hop.symm.trans hop')
      rw [hS.howns] at hvs
      cases hvs
      simp only [List.flatten_nil] at hm
      have hwf2 : WF σ1.fresh.2 := hwf1
      have hag2 : Agree σf σ1.fresh.2 (Xb ++ Xq ++ S) := hag1.trans (Agree.of' fun _ _ => rfl)
      have hm2 : Moves σ0 (Xb ++ Xq ++ Ein) σ1.fresh.2 (Xb ++ Xq ++ X') [] :=
        ((hm.widen hXa hd).relabel (E'' := Xb ++ Xq ++ X') (L'' := []) fun x => by simp).trans
          (Moves.freshen hwf1 fun l hl => by
            rcases List.mem_append.mp hl with h | h
            · exact hXq1 l h
            · exact hX'a l h) disj_nil_left hwf |>.relabel fun x => by simp
      have : ret F O (m + 1) hs (.scW ef eS j τ cz Kb Q) (.susp j ef [] ls K, σ1) =
          if σ1.sched (σ1.ids + 1) = true then
            ret F O m hs (.scW ef eS j τ cz Kb Q) (evalK F O m (.capture ef j :: .capture eS j :: hs) σ1.fresh.2 K
              (.val (.int 0)))
          else
            ret F O m hs (.scB ef eS j τ cz (Q ++ [K])) (evalK F O m (.capture ef j :: .capture eS j :: hs) σ1.fresh.2 Kb
              (.val (.int 0))) := by
        rw [ret.eq_def]; simp [hsp]; rfl
      rw [this]
      split
      · -- The task goes on.
        have hres := resume0 (top := ⟨Γt, envt, .int, St, .eff ef :: .eff eS :: r⟩) hKk hS.hrefs hS.hret hK' hRb haim hwf2
          (Agree.of' fun _ _ => rfl) hX'St hXn' hdStX'
        have h3 := hRr hs _ _ σf (.scW ef eS j τ cz Kb Q) ⟨Γt, envt, .int, St, .eff ef :: .eff eS :: r⟩ ⟨Γ, env, τ, S, r⟩
          (Xb ++ Xq) (Ab ++ Aq)
          σ1.fresh.2 X' _ (.scW hS hcz hbr hbrefs hKb hagb hab hT hdbq hSt hro) hR hA hwf2 hag2 halloc hnd
          (fun l h1 h2 => hdX' l (by simp only [List.mem_append] at h1 ⊢; grind) h2)
          (fun l hl => by show σ1.mem l ≠ none; exact hS1 l hl)
          (fun l h1 h2 => by
            simp only [List.mem_append] at h2
            rcases h2 with (h2 | h2) | h2
            · exact hdSb l h1 h2
            · exact hdSq l h1 h2
            · exact hdX' l (by simp [h1]) h2) (by simpa [Kont.push] using hres)
        exact post_after hm2 hwf h3
      · -- The task waits last; the body goes on.
        have hres := resumeB m hKk hwf2 hag2
        have hT2 := (hT.transfer (hag1.mono fun l hl => by
            simp only [List.mem_append] at hl ⊢; rcases hl with h | h <;> simp [h])).append hK' hro Agree.self
          hX'St hSt hdStX' hS.hret hS.hrefs (fun l h1 h2 => hdX' l (by simp [h1]) h2)
        have h3 := hRr hs _ _ σ1 (.scB ef eS j τ cz (Q ++ [K])) ⟨Γ, env, τ, S, .eff ef :: .eff eS :: r⟩ ⟨Γ, env, τ, S, r⟩
          (Xq ++ X') (Aq ++ A') σ1.fresh.2 Xb _ (.scB hS (hcz.transfer (agree_S hag1)) hT2) hR
          (fun a ha => by
            rcases List.mem_append.mp ha with h | h
            · exact hA a (List.mem_append.mpr (.inr h))
            · exact aimed_uncap2 (haim a h)) hwf2 (Agree.of' fun _ _ => rfl)
          (fun l hl => by
            rcases List.mem_append.mp hl with h | h
            · exact hXq1 l (by simp [h])
            · exact hX'a l h)
          (nodup_append_disj.mpr ⟨hbq.2.1, hXn', fun l h1 h2 => hdX' l (by simp [h1]) h2⟩)
          (fun l h1 h2 => by
            rcases List.mem_append.mp h1 with h1 | h1
            · exact hdbq l h2 h1
            · exact hdX' l (by simp [h2]) h1)
          (fun l hl => by show σ1.mem l ≠ none; exact hS1 l hl)
          (fun l h1 h2 => by
            simp only [List.mem_append] at h2
            rcases h2 with (h2 | h2) | h2
            · exact hdSq l h1 h2
            · exact hdX' l (by simp [h1]) h2
            · exact hdSb l h1 h2) hres
        exact post_after (hm2.relabel (E'' := Xq ++ X' ++ Xb) (L'' := []) fun x => by
          simp only [List.mem_append, List.not_mem_nil, or_false]
          exact ⟨fun h => by rcases h with (h | h) | h <;> simp [h], fun h => by rcases h with (h | h) | h <;> simp [h]⟩)
          hwf h3
  | stuck => simp [Post] at hp
  | timeout => simp [ret, Post]
  | ended => simp [ret, Post]


/-! ## A scope's task running, its body done -/

/-- A scope's task running, its body done with `v`, its activation `Eb` as it ended: once every task
has ended, the scope gives `v`; if a task fails, `v` is dropped, then the other tasks. -/
theorem ret_scV [WorldOk F O ι.w] (hfl : FlushOk F ι (flushR F O n)) (hF : FnsOk F O) (hKo : ∀ m, n = m + 1 → EvalKOk F O m ∧ RetOk F O m)
    (hS : ScOk O e eS op opS rT R r τ) (hcz : ScCaps F ι σf cz R S Rc) (hIb : Inv F ι σf Γ env Eb S) (hv : VT F ι σf τ v Lv)
    (hdLE : Disj Lv Eb) (hdLS : Disj Lv S) (hT : TasksOk F O ι σf e eS r S Q Xq Aq) (hdq : Disj (Eb ++ Lv) Xq)
    (hSt : ∀ l ∈ St, l ∈ S) (hro : RoCtx Γt) (hR : Ready O hs r) (hA : ∀ a ∈ Aq, AimedIn a hs) (hwf : WF σ0) (hag : Agree σf σ0 (Eb ++ Lv ++ Xq ++ S))
    (halloc : ∀ l ∈ Eb ++ Lv ++ Xq, σf.mem l ≠ none) (hnd : (Eb ++ Lv ++ Xq).Nodup) (hd : Disj (Eb ++ Lv ++ Xq) Ein)
    (hSa : ∀ l ∈ S, σ0.mem l ≠ none) (hSd : Disj S (Eb ++ Lv ++ Xq ++ Ein))
    (hp : Post F ι O σ0 Ein St Γt envt .int (.eff e :: .eff eS :: r) (.capture e hid :: .capture eS hid :: hs) res) :
    Post F ι O σ0 (Eb ++ Lv ++ Xq ++ Ein) S Γ env τ r hs (ret F O n hs (.scV e eS hid τ cz v Q) res) := by
  have hdSb : Disj S Eb := fun l h1 h2 => hIb.disj l h1 h2
  have hXa : ∀ l ∈ Eb ++ Lv ++ Xq, σ0.mem l ≠ none := fun l hl => by
    rw [hag l (List.mem_append.mpr (.inl hl))]; exact halloc l hl
  have hXSa : ∀ l ∈ Eb ++ Lv ++ Xq ++ S, σ0.mem l ≠ none := fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · exact hXa l h
    · exact hSa l h
  have hXSd : Disj (Eb ++ Lv ++ Xq ++ S) Ein := fun l hl h => by
    rcases List.mem_append.mp hl with hl | hl
    · exact hd l hl h
    · exact hSd l hl (List.mem_append.mpr (.inr h))
  have hn3 := nodup_append_disj.mp hnd
  have hn2 := nodup_append_disj.mp hn3.1
  have hRb : Ready O (.capture e hid :: .capture eS hid :: hs) (.eff e :: .eff eS :: r) := sc_ready hS.hop hS.hopS hR.1 hR.2
  have hdSq : Disj S Xq := fun l h1 h2 => hSd l h1 (by simp [h2])
  have hfS : ∀ l ∈ S, σf.mem l ≠ none := fun l hl => by
    rw [← hag l (by simp [hl])]; exact hSa l hl
  -- What the frame keeps, in a store agreeing with it.
  have kept : ∀ {σ1}, Agree σf σ1 (Eb ++ Lv ++ Xq ++ S) →
      Inv F ι σ1 Γ env Eb S ∧ VT F ι σ1 τ v Lv ∧ TasksOk F O ι σ1 e eS r S Q Xq Aq := fun hag1 =>
    ⟨⟨hIb.foot.frame (hag1.mono fun l hl => by rcases List.mem_append.mp hl with h | h <;> simp [h]),
      hIb.nodup, hIb.disj, hIb.keys⟩, hv.frame (hag1.mono fun l hl => by simp [hl]),
      hT.transfer (hag1.mono fun l hl => by
        simp only [List.mem_append] at hl ⊢; rcases hl with h | h <;> simp [h])⟩
  rcases res with ⟨res, σ1⟩
  cases res with
  | val w =>
    obtain ⟨E', L, hI', hw, -, -, hm⟩ := hp
    obtain rfl := foot_ro hI'.foot hro
    obtain rfl : L = [] := by cases hw; rfl
    have hag1 : Agree σf σ1 (Eb ++ Lv ++ Xq ++ S) := hag.trans (hm.keeps hwf hXSa hXSd)
    obtain ⟨hI1, hv1, hT1⟩ := kept hag1
    have hm' : Moves σ0 (Eb ++ Lv ++ Xq ++ Ein) σ1 (Eb ++ Lv ++ Xq) [] :=
      (hm.widen hXa hd).relabel fun x => by simp
    cases Q with
    | nil =>
      cases hT
      rw [ret.eq_def]
      exact ⟨Eb, Lv, hI1, hv1, hdLE, hdLS, hm'.relabel fun x => by simp⟩
    | cons Kt Q' =>
    cases n with
    | zero => rw [ret.eq_def]; simp [Post]
    | succ m =>
    obtain ⟨hKk, hRr⟩ := hKo m rfl
    have : ret F O (m + 1) hs (.scV e eS hid τ cz v (Kt :: Q')) (.val w, σ1) =
        ret F O m hs (.scV e eS hid τ cz v Q') (evalK F O m (.capture e hid :: .capture eS hid :: hs) σ1 Kt (.val (.int 0))) := by
      rw [ret.eq_def]
    rw [this]
    cases hT with
    | cons hK hro0 hagt hat hSt0 hdSt0 h1 h2 hdX hT' =>
    rename_i σt op0 Γt0 envt0 St0 X AK Xs As
    have hwf1 := hm.wf
    have hXn := (nodup_append_disj.mp hn3.2.1).1
    have hres := resume0 (top := ⟨Γt0, envt0, .int, St0, .eff e :: .eff eS :: r⟩) hKk h2 h1 hK hRb
      (fun a ha => (hA a (List.mem_append.mpr (.inl ha))).imp_right fun ⟨l, hl⟩ =>
        ⟨l, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hl)⟩) hwf1
      (agree_task hagt hSt0 (fun l h => by simp [h]) hag1) hat hXn hdSt0
    have h3 := hRr hs _ _ σf (.scV e eS hid τ cz v Q') ⟨Γt0, envt0, .int, St0, .eff e :: .eff eS :: r⟩ ⟨Γ, env, τ, S, r⟩
      (Eb ++ Lv ++ Xs) As σ1 X _
      (.scV hS hcz hIb hv hdLE hdLS hT' (fun l h1 h2 => hdq l h1 (by simp [h2])) hSt0 hro0) hR
      (fun a ha => hA a (List.mem_append.mpr (.inr ha))) hwf1
      (hag1.mono fun l hl => by simp only [List.mem_append] at hl ⊢; grind)
      (fun l hl => halloc l (by simp only [List.mem_append] at hl ⊢; grind))
      (nodup_append_disj.mpr ⟨hn3.1, (nodup_append_disj.mp hn3.2.1).2.1, fun l h1 h2 => hn3.2.2 l h1 (by simp [h2])⟩)
      (fun l h1 h2 => by
        rcases List.mem_append.mp h1 with h1 | h1
        · exact hn3.2.2 l h1 (by simp [h2])
        · exact (nodup_append_disj.mp hn3.2.1).2.2 l h2 h1)
      (fun l hl => by rw [hag1 l (by simp [hl])]; exact hfS l hl)
      (fun l h1 h2 => by
        simp only [List.mem_append] at h2
        rcases h2 with ((h2 | h2) | h2) | h2
        · exact hIb.disj l h1 h2
        · exact hdLS l h2 h1
        · exact hdSq l h1 (by simp [h2])
        · exact hdSq l h1 (by simp [h2])) hres
    exact post_after (hm'.relabel fun x => by
        simp only [List.mem_append, List.not_mem_nil, or_false, false_or, or_assoc, or_comm, or_left_comm]) hwf h3
  | abort j k =>
    obtain ⟨haim, E', hI', hm⟩ := hp
    obtain rfl := foot_ro hI'.foot hro
    have hwf1 := hm.wf
    have hag1 : Agree σf σ1 (Eb ++ Lv ++ Xq ++ S) := hag.trans (hm.keeps hwf hXSa hXSd)
    obtain ⟨hI1, hv1, hT1⟩ := kept hag1
    obtain ⟨σ2', hdrop, hfg⟩ := dropF hfl hwf1 hv1
    rw [ret.eq_def]
    simp only [hdrop]
    refine hfg.post fun σ2 hd2 => ?_
    have hwf2 : WF σ2 := hd2.wf
    have hag12 : Agree σ1 σ2 (Eb ++ Xq ++ S) := hd2.keeps hwf1 (fun l hl => by
        rw [hag1 l (by simp only [List.mem_append] at hl ⊢; rcases hl with (h | h) | h <;> simp [h])]
        exact (by
          simp only [List.mem_append] at hl
          rcases hl with (h | h) | h
          · exact halloc l (by simp [h])
          · exact halloc l (by simp [h])
          · rw [← hag l (by simp [h])]; exact hSa l h)) fun l hl h => by
      simp only [List.mem_append] at hl
      rcases hl with (hl | hl) | hl
      · exact hdLE l h hl
      · exact hdq l (by simp [h]) hl
      · exact hdLS l h hl
    have hI2 : Inv F ι σ2 Γ env Eb S := ⟨hI1.foot.frame (hag12.mono fun l hl => by
        rcases List.mem_append.mp hl with h | h <;> simp [h]), hI1.nodup, hI1.disj, hI1.keys⟩
    have hm2 : Moves σ1 (Eb ++ Lv ++ Xq) σ2 (Eb ++ Xq) [] :=
      ((hd2.widen (X := Eb ++ Xq) (fun l hl => by
        rw [hag1 l (by simp only [List.mem_append] at hl ⊢; rcases hl with h | h <;> simp [h])]
        exact halloc l (by simp only [List.mem_append] at hl ⊢; rcases hl with h | h <;> simp [h]))
      (fun l h1 h2 => by
        rcases List.mem_append.mp h1 with h1 | h1
        · exact hdLE l h2 h1
        · exact hdq l (by simp [h2]) h1)).congr_left fun x => by
          simp only [List.mem_append]; exact ⟨fun h => by rcases h with (h | h) | h <;> simp [h],
            fun h => by rcases h with (h | h) | h <;> simp [h]⟩).relabel fun x => by simp
    have hm' : Moves σ0 (Eb ++ Lv ++ Xq ++ Ein) σ1 (Eb ++ Lv ++ Xq) [] := (hm.widen hXa hd).relabel fun x => by simp
    exact post_after (hm'.trans hm2 disj_nil_left hwf) hwf
      (drop_rest hKo hS hI2 hT1 (hag12.mono fun l hl => by
          simp only [List.mem_append] at hl ⊢; rcases hl with h | h <;> simp [h])
        (fun l hl => by rw [hag1 l (by simp [hl])]; exact halloc l (by simp [hl])) hn3.2.1
        (fun l h1 h2 => hdq l (by simp [h1]) h2) hdSq (aimed_uncap2 haim) hA hR hwf2)
  | susp j ef vs ls K =>
    by_cases hc : j ≠ hid ∨ (ef ≠ e ∧ ef ≠ eS)
    · have : ret F O n hs (.scV e eS hid τ cz v Q) (.susp j ef vs ls K, σ1) =
          (.susp j ef vs ls (.scV e eS hid τ cz v Q :: K), σ1) := by
        rw [ret.eq_def]; simp [hc]
      rw [this]
      exact post_susp (.scV hS hcz hIb hv hdLE hdLS hT hdq hSt hro) hR.2 (fun _ h => aimed_uncap2 h) hA (fun h => by
        rcases h.of_cons_capture with ⟨rfl, rfl⟩ | h
        · simp at hc
        rcases h.of_cons_capture with ⟨rfl, rfl⟩ | h
        · simp at hc
        · exact h) hwf hag halloc hnd hd hSa hSd hp
    have hj : j = hid := by
      by_cases h : j = hid
      · exact h
      · exact absurd (.inl h) hc
    subst hj
    obtain ⟨op', X', hos, A', Lw0, -, hop', -, haim, hK', hls, hvs, hLn, hdLX, hdLS', hm⟩ := hp
    have hop'r : op'.refs = [] := by
      by_cases hsp : ef = eS
      · subst hsp; rw [hS.hopS] at hop'; cases hop'; exact hS.hSrefs
      · have : ef = e := by
          by_cases h : ef = e
          · exact h
          · exact absurd (.inr ⟨h, hsp⟩) hc
        subst this; rw [hS.hop] at hop'; cases hop'; exact hS.hrefs
    obtain ⟨-, -, -, -, -, -, -, -, hts, -, -, hXn', -⟩ := hK'.base_of
    rw [hop'r] at hts
    obtain rfl : hos = [] := List.map_eq_nil_iff.mp hts
    simp only [olds, mutCells, List.map_nil, List.flatMap_nil, List.append_nil] at hm hdLX hdLS'
    have hwf1 := hm.wf
    have hag1 : Agree σf σ1 (Eb ++ Lv ++ Xq ++ S) := hag.trans (hm.keeps hwf hXSa hXSd)
    have hdX' := (hm.apart hwf hXSa hXSd).1
    have hdXL' := (hm.apart hwf hXSa hXSd).2
    have hS1 : ∀ l ∈ S, σ1.mem l ≠ none := fun l hl => by rw [hag1 l (by simp [hl])]; exact hfS l hl
    have hK1 : ∀ l ∈ Eb ++ Lv ++ Xq, σ1.mem l ≠ none := fun l hl => by
      rw [hag1 l (List.mem_append.mpr (.inl hl))]; exact halloc l hl
    have hX'a : ∀ l ∈ X', σ1.mem l ≠ none := fun l hl => (hm.alloc l).mpr (.inr (.inl hl))
    have hX'St : ∀ l ∈ X' ++ St, σ1.mem l ≠ none := fun l hl => by
      rcases List.mem_append.mp hl with h | h
      · exact hX'a l h
      · exact hS1 l (hSt l h)
    have hdStX' : Disj St X' := fun l h1 h2 => hdX' l (List.mem_append.mpr (.inr (hSt l h1))) h2
    cases n with
    | zero =>
      rw [ret.eq_def]; simp only [ne_eq, not_true_eq_false, false_or]
      split <;> simp_all [Post]
    | succ m =>
    obtain ⟨hKk, hRr⟩ := hKo m rfl
    by_cases hsp : ef = eS
    · -- The task started a task: it joins the tasks waiting, and the task goes on.
      subst hsp
      obtain rfl : opS = op' := Option.some.inj (hS.hopS.symm.trans hop')
      rw [hS.hSowns] at hvs
      cases hvs with
      | cons hw hrest =>
      cases hrest
      rename_i w Lw
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hm hdLX hdLS' hLn hdXL'
      obtain ⟨Kt, σ2, Xt, Γk, envk, hmk, hKt, hroT, hmt⟩ :=
        mkTask_ok ((O[ef]?.map Op.spawns).getD false) hF hS (hcz.transfer (agree_S hag1)) hw hwf1 fun l h1 h2 => hdXL' l (by simp [h2]) h1
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hXtn, -⟩ := hKt.base_of
      have : ret F O (m + 1) hs (.scV e ef j τ cz v Q) (.susp j ef [w] ls K, σ1) =
          ret F O m hs (.scV e ef j τ cz v (Q ++ [Kt]))
            (evalK F O m (.capture e j :: .capture ef j :: hs) σ2 K (.val (.int 0))) := by
        rw [ret.eq_def]; simp [hmk]
      rw [this]
      have hwf2 := hmt.wf
      have hkeepA : ∀ l ∈ X' ++ (Eb ++ Lv ++ Xq) ++ S, σ1.mem l ≠ none := fun l hl => by
        simp only [List.mem_append] at hl
        rcases hl with (h | h) | h
        · exact hX'a l h
        · exact hK1 l (by simp only [List.mem_append]; exact h)
        · exact hS1 l h
      have hkeepD : Disj (X' ++ (Eb ++ Lv ++ Xq) ++ S) Lw := fun l h1 h2 => by
        simp only [List.mem_append] at h1
        rcases h1 with (h1 | h1) | h1
        · exact hdLX l h2 h1
        · exact hdXL' l (by simp only [List.mem_append]; exact .inl h1) h2
        · exact hdXL' l (by simp [h1]) h2
      have hag12 : Agree σ1 σ2 (X' ++ (Eb ++ Lv ++ Xq) ++ S) := hmt.keeps hwf1 hkeepA hkeepD
      obtain ⟨hdLt, -⟩ := hmt.apart hwf1 hkeepA hkeepD
      have hag2 : Agree σf σ2 (Eb ++ Lv ++ Xq ++ S) := hag1.trans (hag12.mono fun l hl => by
        simp only [List.mem_append] at hl ⊢; grind)
      obtain ⟨hI2, hv2, hT2'⟩ := kept hag2
      have hS2 : ∀ l ∈ S, σ2.mem l ≠ none := fun l hl => by rw [hag12 l (by simp [hl])]; exact hS1 l hl
      have hres := resume0 (top := ⟨Γt, envt, .int, St, .eff e :: .eff ef :: r⟩) hKk hS.hSrefs hS.hSret hK' hRb haim hwf2
        (hag12.mono fun l hl => by
          rcases List.mem_append.mp hl with h | h
          · simp [h]
          · simp [hSt l h])
        hX'St hXn' hdStX'
      have hT2 := hT2'.append hKt hroT Agree.self (fun l hl => by
          rcases List.mem_append.mp hl with h | h
          · exact (hmt.alloc l).mpr (.inr (.inl h))
          · exact hS2 l (hcz.hRc l h)) hcz.hRc (fun l h1 h2 => hdLt l (by simp [hcz.hRc l h1]) h2) hS.hret hS.hrefs
        (fun l h1 h2 => hdLt l (by simp [h1]) h2)
      have hK2 : ∀ l ∈ Eb ++ Lv ++ Xq, σ2.mem l ≠ none := fun l hl => by
        rw [hag12 l (by simp only [List.mem_append] at hl ⊢; grind)]; exact hK1 l hl
      have h3 := hRr hs _ _ σ2 (.scV e ef j τ cz v (Q ++ [Kt])) ⟨Γt, envt, .int, St, .eff e :: .eff ef :: r⟩ ⟨Γ, env, τ, S, r⟩
        (Eb ++ Lv ++ (Xq ++ Xt)) (Aq ++ []) σ2 X' _
        (.scV hS (hcz.transfer (agree_S hag2)) hI2 hv2 hdLE hdLS hT2 (fun l h1 h2 => by
            rcases List.mem_append.mp h2 with h2 | h2
            · exact hdq l h1 h2
            · exact hdLt l (by simp only [List.mem_append] at h1 ⊢; grind) h2) hSt hro) hR
        (fun a ha => hA a (by simpa using ha)) hwf2 Agree.self
        (fun l hl => by
          simp only [List.mem_append] at hl
          rcases hl with (h | h) | h | h
          · exact hK2 l (by simp [h])
          · exact hK2 l (by simp [h])
          · exact hK2 l (by simp [h])
          · exact (hmt.alloc l).mpr (.inr (.inl h)))
        (by
          refine nodup_append_disj.mpr ⟨hn3.1, nodup_append_disj.mpr ⟨hn3.2.1, hXtn, fun l h1 h2 =>
            hdLt l (by simp [h1]) h2⟩, fun l h1 h2 => ?_⟩
          rcases List.mem_append.mp h2 with h2 | h2
          · exact hn3.2.2 l h1 h2
          · exact hdLt l (by simp only [List.mem_append] at h1 ⊢; grind) h2)
        (fun l h1 h2 => by
          simp only [List.mem_append] at h1
          rcases h1 with (h1 | h1) | h1 | h1
          · exact hdX' l (by simp [h1]) h2
          · exact hdX' l (by simp [h1]) h2
          · exact hdX' l (by simp [h1]) h2
          · exact hdLt l (by simp [h2]) h1)
        hS2
        (fun l h1 h2 => by
          simp only [List.mem_append] at h2
          rcases h2 with ((h2 | h2) | h2 | h2) | h2
          · exact hdSb l h1 h2
          · exact hdLS l h2 h1
          · exact hdSq l h1 h2
          · exact hdLt l (by simp [h1]) h2
          · exact hdX' l (by simp [h1]) h2) hres
      have m1 := (hm.widen hXa hd).relabel (E'' := X' ++ (Eb ++ Lv ++ Xq) ++ Lw) (L'' := []) fun x => by
        simp only [List.mem_append, List.not_mem_nil, or_false, false_or, or_assoc, or_comm, or_left_comm]
      have m2 := hmt.widen (X := X' ++ (Eb ++ Lv ++ Xq)) (fun l hl => hkeepA l (by simp only [List.mem_append] at hl ⊢; grind))
        (fun l h1 h2 => hkeepD l (by simp only [List.mem_append] at h1 ⊢; grind) h2)
      exact post_after ((m1.trans m2 disj_nil_left hwf).relabel (E'' := Eb ++ Lv ++ (Xq ++ Xt) ++ X') (L'' := []) fun x => by
        simp only [List.mem_append, List.not_mem_nil, or_false, List.nil_append, false_or, or_assoc, or_comm, or_left_comm])
        hwf (by simpa using h3)
    · -- The task gave way: it goes on, or it waits last and the first task waiting goes on.
      have hef : ef = e := by
        by_cases h : ef = e
        · exact h
        · exact absurd (.inr ⟨h, hsp⟩) hc
      subst hef
      obtain rfl : op = op' := Option.some.inj (hS.hop.symm.trans hop')
      rw [hS.howns] at hvs
      cases hvs
      simp only [List.flatten_nil] at hm
      have hwf2 : WF σ1.fresh.2 := hwf1
      have hag2 : Agree σf σ1.fresh.2 (Eb ++ Lv ++ Xq ++ S) := hag1.trans (Agree.of' fun _ _ => rfl)
      have hm2 : Moves σ0 (Eb ++ Lv ++ Xq ++ Ein) σ1.fresh.2 (Eb ++ Lv ++ Xq ++ X') [] :=
        ((hm.widen hXa hd).relabel (E'' := Eb ++ Lv ++ Xq ++ X') (L'' := []) fun x => by simp).trans
          (Moves.freshen hwf1 fun l hl => by
            rcases List.mem_append.mp hl with h | h
            · exact hK1 l h
            · exact hX'a l h) disj_nil_left hwf |>.relabel fun x => by simp
      -- The same task goes on.
      have taskOn : Post F ι O σ0 (Eb ++ Lv ++ Xq ++ Ein) S Γ env τ r hs (ret F O m hs (.scV ef eS j τ cz v Q)
          (evalK F O m (.capture ef j :: .capture eS j :: hs) σ1.fresh.2 K (.val (.int 0)))) := by
        have hres := resume0 (top := ⟨Γt, envt, .int, St, .eff ef :: .eff eS :: r⟩) hKk hS.hrefs hS.hret hK' hRb haim hwf2
          (Agree.of' fun _ _ => rfl) hX'St hXn' hdStX'
        have h3 := hRr hs _ _ σf (.scV ef eS j τ cz v Q) ⟨Γt, envt, .int, St, .eff ef :: .eff eS :: r⟩ ⟨Γ, env, τ, S, r⟩
          (Eb ++ Lv ++ Xq) Aq
          σ1.fresh.2 X' _ (.scV hS hcz hIb hv hdLE hdLS hT hdq hSt hro) hR hA hwf2 hag2 halloc hnd
          (fun l h1 h2 => hdX' l (by simp only [List.mem_append] at h1 ⊢; grind) h2)
          (fun l hl => by show σ1.mem l ≠ none; exact hS1 l hl)
          (fun l h1 h2 => by
            simp only [List.mem_append] at h2
            rcases h2 with ((h2 | h2) | h2) | h2
            · exact hdSb l h1 h2
            · exact hdLS l h2 h1
            · exact hdSq l h1 h2
            · exact hdX' l (by simp [h1]) h2) (by simpa [Kont.push] using hres)
        exact post_after hm2 hwf h3
      cases Q with
      | nil =>
        have : ret F O (m + 1) hs (.scV ef eS j τ cz v []) (.susp j ef [] ls K, σ1) =
            ret F O m hs (.scV ef eS j τ cz v []) (evalK F O m (.capture ef j :: .capture eS j :: hs) σ1.fresh.2 K
              (.val (.int 0))) := by
          rw [ret.eq_def]; simp [hsp]
        rw [this]; exact taskOn
      | cons Kt Q' =>
      have : ret F O (m + 1) hs (.scV ef eS j τ cz v (Kt :: Q')) (.susp j ef [] ls K, σ1) =
          if σ1.sched (σ1.ids + 1) = true then
            ret F O m hs (.scV ef eS j τ cz v (Kt :: Q')) (evalK F O m (.capture ef j :: .capture eS j :: hs) σ1.fresh.2 K
              (.val (.int 0)))
          else
            ret F O m hs (.scV ef eS j τ cz v (Q' ++ [K])) (evalK F O m (.capture ef j :: .capture eS j :: hs) σ1.fresh.2 Kt
              (.val (.int 0))) := by
        rw [ret.eq_def]; simp [hsp]; rfl
      rw [this]
      split
      · exact taskOn
      · -- This task waits last; the first one waiting goes on.
        obtain ⟨hI1, hv1, hT1⟩ := kept hag1
        cases hT1 with
        | cons hK hro0 hagt hat hSt0 hdSt0 h1 h2 hdX hT' =>
        rename_i σt op0 Γt0 envt0 St0 X AK Xs As
        have hXn := (nodup_append_disj.mp hn3.2.1).1
        have hres := resume0 (top := ⟨Γt0, envt0, .int, St0, .eff ef :: .eff eS :: r⟩) hKk h2 h1 hK hRb
          (fun a ha => (hA a (List.mem_append.mpr (.inl ha))).imp_right fun ⟨l, hl⟩ =>
            ⟨l, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hl)⟩) hwf2
          (hagt.trans (Agree.of' (σ := σ1) (σ' := σ1.fresh.2) (L := X ++ St0) fun _ _ => rfl))
          hat hXn hdSt0
        have hT2 := hT'.append hK' hro Agree.self hX'St hSt hdStX' hS.hret hS.hrefs
          (fun l h1 h2 => hdX' l (by simp [h1]) h2)
        have h3 := hRr hs _ _ σ1 (.scV ef eS j τ cz v (Q' ++ [K])) ⟨Γt0, envt0, .int, St0, .eff ef :: .eff eS :: r⟩
          ⟨Γ, env, τ, S, r⟩ (Eb ++ Lv ++ (Xs ++ X')) (As ++ A') σ1.fresh.2 X _
          (.scV hS (hcz.transfer (agree_S hag1)) hI1 hv1 hdLE hdLS hT2 (fun l h1 h2 => by
            rcases List.mem_append.mp h2 with h2 | h2
            · exact hdq l h1 (by simp [h2])
            · exact hdX' l (by simp only [List.mem_append] at h1 ⊢; grind) h2) hSt0 hro0) hR
          (fun a ha => by
            rcases List.mem_append.mp ha with h | h
            · exact hA a (List.mem_append.mpr (.inr h))
            · exact aimed_uncap2 (haim a h)) hwf2 (Agree.of' fun _ _ => rfl)
          (fun l hl => by
            simp only [List.mem_append] at hl
            rcases hl with (h | h) | h | h
            · exact hK1 l (by simp [h])
            · exact hK1 l (by simp [h])
            · exact hK1 l (by simp [h])
            · exact hX'a l h)
          (by
            have hXs := (nodup_append_disj.mp hn3.2.1)
            refine nodup_append_disj.mpr ⟨hn3.1, nodup_append_disj.mpr ⟨hXs.2.1, hXn', fun l h1 h2 =>
              hdX' l (by simp [h1]) h2⟩, fun l h1 h2 => ?_⟩
            rcases List.mem_append.mp h2 with h2 | h2
            · exact hn3.2.2 l h1 (by simp [h2])
            · exact hdX' l (by simp only [List.mem_append] at h1 ⊢; grind) h2)
          (fun l h1 h2 => by
            simp only [List.mem_append] at h1
            rcases h1 with (h1 | h1) | h1 | h1
            · exact hn3.2.2 l (by simp [h1]) (by simp [h2])
            · exact hn3.2.2 l (by simp [h1]) (by simp [h2])
            · exact (nodup_append_disj.mp hn3.2.1).2.2 l h2 h1
            · exact hdX' l (by simp [h2]) h1)
          (fun l hl => by show σ1.mem l ≠ none; exact hS1 l hl)
          (fun l h1 h2 => by
            simp only [List.mem_append] at h2
            rcases h2 with ((h2 | h2) | h2 | h2) | h2
            · exact hdSb l h1 h2
            · exact hdLS l h2 h1
            · exact hdSq l h1 (by simp [h2])
            · exact hdX' l (by simp [h1]) h2
            · exact hdSq l h1 (by simp [h2])) hres
        exact post_after (hm2.relabel (E'' := Eb ++ Lv ++ (Xs ++ X') ++ X) (L'' := []) fun x => by
          simp only [List.mem_append, List.not_mem_nil, or_false, false_or, or_assoc, or_comm, or_left_comm])
          hwf (by simpa using h3)
  | stuck => simp [Post] at hp
  | timeout => simp [ret, Post]
  | ended => simp [ret, Post]


/-! ## A scope started -/

/-- The places a scope lends its tasks, each a variable only read: where they are, and their trees,
among what the code around only reads. -/
theorem scope_caps (hf : Foot F ι σ Γ env E S) : ∀ {caps : List (Cap Place)},
    (∀ c ∈ caps, c.mode = .ro ∧ ∃ y, c.loc = .var y ∧ lookup y Γ = some (.ref .ro c.ty)) →
    ∃ ls Rc, caps.mapM (fun c => resolve σ env c.loc) = some ls ∧
      CapsOk F ι σ (List.zipWith Cap.at caps ls) Rc [] ∧ (∀ l ∈ Rc, l ∈ S) ∧
      (List.zipWith Cap.at caps ls).map Cap.ty = caps.map Cap.ty ∧ ∀ c ∈ List.zipWith Cap.at caps ls, c.mode = .ro
  | [], _ => ⟨[], [], rfl, .nil, by simp, rfl, by simp⟩
  | ⟨x, m, τ, p⟩ :: caps, h => by
    obtain ⟨hm, y, hy, hl⟩ := h _ (List.mem_cons_self ..)
    simp only at hm hy hl
    subst hm hy
    obtain ⟨ls, Rc, hmap, hc, hRc, hty, hro⟩ := scope_caps hf fun c hc => h c (List.mem_cons_of_mem _ hc)
    obtain ⟨a, L, ha, hs, -, hsh⟩ := foot_lookup hf hl
    refine ⟨a :: ls, L ++ Rc, by simp [List.mapM_cons, resolve, ha, hmap], .ro hs hc, ?_, by simp [Cap.at, hty], ?_⟩
    · intro l hl'
      rcases List.mem_append.mp hl' with h | h
      · exact hsh l (by simpa [sharedPart, Slot.excl] using h)
      · exact hRc l h
    · intro c hc
      simp only [List.zipWith_cons_cons, List.mem_cons] at hc
      rcases hc with rfl | hc
      · rfl
      · exact hro c hc

/-- `scope`: its body runs, giving way and starting tasks through the scope's frame, no task yet
waiting, each task it starts lent the places it names. -/
theorem scope_ok [WorldOk F O ι.w] (hE : EvalOk F O n) (hR : RetOk F O n) (hS : ScOk O e eS op opS rT R r τ)
    (hRt : R.toList = caps.map Cap.ty)
    (hcaps : ∀ c ∈ caps, c.mode = .ro ∧ ∃ y, c.loc = .var y ∧ lookup y Γ = some (.ref .ro c.ty))
    (hb : Typed F O Γ body τ Γb (.eff e :: .eff eS :: r)) (hI : Inv F ι σ Γ env E S) (hwf : WF σ)
    (hRdy : Ready O hs r) :
    Post F ι O σ E S Γb env τ r hs (evalS F O n hs σ env (.scope e eS caps τ body)) := by
  obtain ⟨ls, Rc, hmap, hc, hRc, hty, hro⟩ := scope_caps hI.foot hcaps
  simp only [evalS, hmap]
  have hI1 : Inv F ι σ.fresh.2 Γ env E S := ⟨hI.foot.frame (Agree.of' fun _ _ => rfl), hI.nodup, hI.disj, hI.keys⟩
  have hwf1 : WF σ.fresh.2 := hwf
  have hcz : ScCaps F ι σ.fresh.2 (List.zipWith Cap.at caps ls) R S Rc :=
    ⟨hc.frame (Agree.of' fun _ _ => rfl), hRc, by rw [hRt, hty], hro⟩
  have hp := hE (.capture e (σ.ids + 1) :: .capture eS (σ.ids + 1) :: hs) σ.fresh.2 ι Γ env E S body τ Γb _ hb hI1 hwf1
    (sc_ready hS.hop hS.hopS hRdy.1 hRdy.2)
  have h2 := hR hs ι ι σ.fresh.2 (.scB e eS (σ.ids + 1) τ (List.zipWith Cap.at caps ls) []) ⟨Γb, env, τ, S, .eff e :: .eff eS :: r⟩
    ⟨Γb, env, τ, S, r⟩ [] [] σ.fresh.2 E _ (.scB hS hcz .nil) hRdy (fun _ h => by simp at h) hwf1 Agree.self
    (fun _ h => by simp at h) List.nodup_nil disj_nil_left (fun l hl => hI.allocS l hl)
    (fun l h1 h2 => hI.disj l h1 (by simpa using h2)) hp
  exact post_after (Moves.freshen hwf hI.alloc) hwf (by simpa [Store.fresh] using h2)

end FlyCore.Ownership
