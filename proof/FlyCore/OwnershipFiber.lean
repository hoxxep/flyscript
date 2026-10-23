import FlyCore.OwnershipScope

/-!
# Ownership: a `handle` whose arm keeps its continuation

The `handle`'s body runs on a fiber of its own, under no handler but its own: it performs only its
operation. Each time it does, the fiber's frames become a continuation value, owning what the fiber
allocated since it was last entered and still holds, and what it owned then, but for what the
operation passes out; the arm, a function, is called with what the operation passes and the
continuation, in the code around. Resuming the continuation enters the fiber again.
-/

namespace FlyCore.Ownership

variable {F : List Fn} {O : List Op}

theorem Vals.append : Vals F ι σ τs vs Ls → Vals F ι σ τs' vs' Ls' → Vals F ι σ (τs ++ τs') (vs ++ vs') (Ls ++ Ls')
  | .nil, h => h
  | .cons hv hr, h => .cons hv (hr.append h)

/-- What a fiber owns where it gives way, as `kfoot` computes it: the cells it owned when it was
entered and those it allocated since, still there, but for what it passes out — which is what its
frames own. -/
theorem kfoot_perm (hwf0 : WF σ0) (hwf' : WF σ') (hm : Moves σ0 Ein σ' X Lv) (hB : ∀ l ∈ B, l < s)
    (hBn : B.Nodup) (hBE : ∀ l ∈ B, l ∈ Ein) (hEB : ∀ l ∈ Ein, l ∈ B ∨ (s ≤ l ∧ l < σ0.next))
    (hsn : s ≤ σ0.next) (hnew : ∀ l, s ≤ l → l < σ0.next → σ0.mem l ≠ none → l ∈ Ein) (hXn : X.Nodup)
    (hdX : Disj Lv X) (hfoot : vs.flatMap Val.foot = Lv) :
    (kfoot σ' B s vs).Perm X ∧ (kfoot σ' B s vs).Nodup ∧ ∀ l ∈ kfoot σ' B s vs, σ'.mem l ≠ none := by
  have hmem : ∀ l, l ∈ kfoot σ' B s vs ↔ (l ∈ B ∨ (s ≤ l ∧ l < σ'.next)) ∧ σ'.mem l ≠ none ∧ l ∉ Lv := by
    intro l
    simp only [kfoot, List.mem_filter, List.mem_append, List.mem_range'_1, Bool.and_eq_true,
      Option.isSome_iff_ne_none, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not, hfoot]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1.imp_right fun h => ⟨h.1, by omega⟩, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1.imp_right fun h => ⟨h.1, by omega⟩, h2, h3⟩
  have hXlive : ∀ l ∈ X, σ'.mem l ≠ none := fun l hl => (hm.alloc l).mpr (.inr (.inl hl))
  have hiff : ∀ l, l ∈ kfoot σ' B s vs ↔ l ∈ X := by
    intro l
    rw [hmem]
    constructor
    · rintro ⟨hin, hlive, hLv⟩
      rcases (hm.alloc l).mp hlive with ⟨h0, hE⟩ | h | h
      · exfalso
        rcases hin with hb | ⟨h1, h2⟩
        · exact hE (hBE l hb)
        · by_cases hlt : l < σ0.next
          · exact hE (hnew l h1 hlt h0)
          · exact hlt (hwf0 l h0)
      · exact h
      · exact absurd h hLv
    · intro hl
      refine ⟨?_, hXlive l hl, fun h => hdX l h hl⟩
      rcases hm.within l (.inr hl) with h | h
      · rcases hEB l h with h | h
        · exact .inl h
        · exact .inr ⟨h.1, Nat.lt_of_lt_of_le h.2 hm.next⟩
      · exact .inr ⟨Nat.le_trans hsn h, hwf' l (hXlive l hl)⟩
  have hnd : (kfoot σ' B s vs).Nodup := by
    refine List.Nodup.sublist List.filter_sublist (nodup_append_disj.mpr ⟨hBn, List.nodup_range' .., fun l h1 h2 => ?_⟩)
    have := hB l h1
    simp only [List.mem_range'_1] at h2
    omega
  exact ⟨(List.perm_ext_iff_of_nodup hnd hXn).mpr hiff, hnd, fun l hl => ((hmem l).mp hl).2.1⟩

theorem Ty.cross_rfree {τ : Ty} (h : τ.cross = true) : τ.rfree = true := by
  cases τ <;> simp_all [Ty.cross, Ty.rfree]

/-- The fiber of a `handle` whose arm keeps its continuation, as what runs on it ends: with a value,
which passes out; never unwinding, its own operation the only one in force; or giving way by its
operation, which calls the arm with what the operation passes and the continuation, which owns the
fiber's cells. -/
theorem ret_capV_ok [WorldOk F O ι.w] (hF : FnsOk F O)
    (hKo : ∀ m, n = m + 1 → EvalOk F O m ∧ FlushOk F ι (flushR F O m))
    (hc : CapVOk F O e fa op τ ra) (hra : ∀ l ∈ ra, l ∈ r) (hR : Ready O hs r) (hwf : WF σ0)
    (hI : Inv F ι σ0 Γ₁ env E₁ S) (hd : Disj E₁ Ein) (hdS : Disj S Ein)
    (hB : ∀ l ∈ B, l < s) (hBn : B.Nodup) (hBE : ∀ l ∈ B, l ∈ Ein)
    (hEB : ∀ l ∈ Ein, l ∈ B ∨ (s ≤ l ∧ l < σ0.next)) (hsn : s ≤ σ0.next)
    (hnew : ∀ l, s ≤ l → l < σ0.next → σ0.mem l ≠ none → l ∈ Ein)
    (hp : Post F ⟨[], ι.w⟩ O σ0 Ein [] [] [] τ [.eff e] [.capture e g] res) :
    Post F ι O σ0 (E₁ ++ Ein) S Γ₁ env τ r hs (ret F O n hs (.capV τ e g fa B s) res) := by
  have hE1a : ∀ l ∈ E₁ ++ S, σ0.mem l ≠ none := fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · exact hI.alloc l h
    · exact hI.allocS l h
  have hE1d : Disj (E₁ ++ S) Ein := fun l hl h => by
    rcases List.mem_append.mp hl with h' | h'
    · exact hd l h' h
    · exact hdS l h' h
  -- What the fiber leaves, the code around stands.
  have around : ∀ {σ' E' L}, Moves σ0 Ein σ' E' L →
      Inv F ι σ' Γ₁ env E₁ S ∧ Disj (E₁ ++ S) E' ∧ Disj (E₁ ++ S) L := fun hm =>
    ⟨⟨hI.foot.frame (hm.keeps hwf hE1a hE1d), hI.nodup, hI.disj, hI.keys⟩, (hm.apart hwf hE1a hE1d).1,
      (hm.apart hwf hE1a hE1d).2⟩
  have hτr : τ.rfree = true := Ty.cross_rfree hc.hτ
  rcases res with ⟨res, σ'⟩
  cases res with
  | val v =>
    obtain ⟨E', L, hI', hv, -, -, hm⟩ := hp
    obtain ⟨rfl, -⟩ := hI'.nil_E
    have hret : ret F O n hs (.capV τ e g fa B s) (.val v, σ') = (.val v, σ') := by rw [ret.eq_def]
    rw [hret]
    obtain ⟨hI1, -, hdL⟩ := around hm
    refine ⟨E₁, L, hI1, hv.rfree_iota hτr, fun l h1 h2 => hdL l (List.mem_append.mpr (.inl h2)) h1,
      fun l h1 h2 => hdL l (List.mem_append.mpr (.inr h2)) h1, ?_⟩
    exact (hm.widen (X := E₁) (fun l hl => hI.alloc l hl) hd).relabel fun x => by simp
  | abort j k =>
    obtain ⟨⟨l, hl⟩, -⟩ := hp
    simp at hl
  | stuck => simp [Post] at hp
  | timeout => rw [ret.eq_def]; simp [Post]
  | panic => rw [ret.eq_def]; simp [Post]
  | susp j ef vs ls K =>
    obtain ⟨op', X, hos, A, Lv, hcap, hop', -, haim, hK, hls, hvs, hLn, hdX, -, hm⟩ := hp
    simp only [List.mem_singleton, Frame.capture.injEq] at hcap
    obtain ⟨hj, hef⟩ := hcap
    subst j ef
    obtain rfl : op = op' := Option.some.inj (hc.hop.symm.trans hop')
    obtain ⟨-, -, -, -, -, -, -, -, hts, -, -, hXn, -, -⟩ := hK.base_of
    rw [hc.hrefs] at hts
    obtain rfl : hos = [] := List.map_eq_nil_iff.mp hts
    obtain rfl : A = [] := List.eq_nil_iff_forall_not_mem.mpr fun a ha => by
      obtain ⟨l, hl⟩ := haim a ha
      simp at hl
    simp only [List.map_nil] at hls
    subst hls
    simp only [olds, mutCells, List.map_nil, List.flatMap_nil, List.append_nil] at hm hdX
    cases n with
    | zero => rw [ret.eq_def]; simp [Post]
    | succ m =>
    obtain ⟨hEm, hflm⟩ := hKo m rfl
    obtain ⟨da, hfa, hdowns, hdrefs, hdret, hdrow, hdretp, hdcap⟩ := hc.harm
    obtain ⟨hko, hfoot⟩ := hvs.konts hc.howns hLn
    obtain ⟨hperm, hXn'', hXa''⟩ := kfoot_perm hwf hm.wf hm hB hBn hBE hEB hsn hnew hXn
      (fun l h1 h2 => hdX l h1 h2) hfoot
    -- The continuation: a value of the world's, owning the fiber's cells.
    have hkv : VT F ι σ' (.cont .int τ ra) (.kont (.capV τ e g fa B s :: K) (kfoot σ' B s vs))
        (kfoot σ' B s vs) :=
      .kont hXn'' hXa'' ⟨σ', ((WorldOk.ok (F := F) (O := O) (W := ι.w)) σ' _ _ _).mpr
        ⟨τ, e, g, fa, B, s, K, op, ra, X, rfl, rfl, hc, hK, hperm⟩, Agree.self⟩
    have hvs' : Vals F ι σ' (da.owns.map Prod.snd) (vs ++ [.kont (.capV τ e g fa B s :: K) (kfoot σ' B s vs)])
        (Lv ++ [kfoot σ' B s vs]) := by
      rw [hdowns]
      exact (hvs.rfree_iota (fun τ' h => Ty.cross_rfree (hc.howns τ' h))).append (.cons hkv .nil)
    obtain ⟨hk, hb⟩ := hF da (List.mem_of_getElem? hfa)
    rw [hdcap, hdretp] at hb
    obtain ⟨Γ'', hb⟩ := hb
    obtain ⟨hI1, hdE, hdL⟩ := around hm
    have hLall : ∀ l, l ∈ (Lv ++ [kfoot σ' B s vs]).flatten ↔ l ∈ Lv.flatten ∨ l ∈ X := fun l => by
      simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_append]
      rw [hperm.mem_iff]
    have hm1 : Moves σ0 (E₁ ++ Ein) σ' E₁ (Lv ++ [kfoot σ' B s vs]).flatten :=
      (hm.widen (X := E₁) (fun l hl => hI.alloc l hl) hd).relabel fun x => by
        rw [hLall]; simp only [List.mem_append, List.append_nil]
        constructor
        · rintro (h | h | h)
          · exact .inl (.inl h)
          · exact .inr h
          · exact .inl (.inr h)
        · rintro ((h | h) | h)
          · exact .inl h
          · exact .inr (.inr h)
          · exact .inr (.inl h)
    have hcore := call_core0 (n := m) (d := da) (hos := []) (Γ'' := Γ'') hflm hEm hk hb
      (fun l hl => hra l (hdrow ▸ hl)) hI1 hwf hm1 hvs'
      (by
        simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
        exact nodup_append_disj.mpr ⟨hLn, hXn'', fun l h1 h2 => hdX l h1 (hperm.mem_iff.mp h2)⟩)
      (fun l hl h => by
        rcases (hLall l).mp hl with h' | h'
        · exact hdL l (List.mem_append.mpr (.inl h)) h'
        · exact hdE l (List.mem_append.mpr (.inl h)) h')
      (fun l hl h => by
        rcases (hLall l).mp hl with h' | h'
        · exact hdL l (List.mem_append.mpr (.inr h)) h'
        · exact hdE l (List.mem_append.mpr (.inr h)) h')
      (fun _ h => by simp at h) List.Pairwise.nil (by simp [hdrefs]) hR
    rw [hdret] at hcore
    have hlen : (vs ++ [Val.kont (.capV τ e g fa B s :: K) (kfoot σ' B s vs)]).length = da.owns.length := by
      rw [hvs'.length, List.length_map]
    rw [ret.eq_def]
    simpa [hfa, hlen, hdrefs] using hcore

/-- The fiber of a kept continuation, entered again: it runs on its own barrier, owning what it did
when it gave way. -/
theorem fiber_ready (hop : O[e]? = some op) : Ready O [.capture e g] [.eff e] :=
  ⟨.capture ⟨op, hop⟩ .nil, fun l hl => by
    simp only [List.mem_singleton] at hl
    subst hl
    exact ⟨.capture e g, by simp [find, Frame.handles]⟩⟩

/-- `k(a)`: the continuation moved out of its variable, its fiber entered again with `a` as what its
operation gave. -/
theorem resumeV_ok [WorldOk F O ι.w] (hF : FnsOk F O) (hKk : EvalKOk F O n)
    (hKo : ∀ m, n = m + 1 → EvalOk F O m ∧ FlushOk F ι (flushR F O m))
    (hx : lookup x Γ = some (.own (.cont .int τ ra) true)) (hra : ∀ l ∈ ra, l ∈ r)
    (ha : AtomTy (setSlot Γ x (.own (.cont .int τ ra) false)) a .int Γ₁)
    (hI : Inv F ι σ Γ env E S) (hwf : WF σ) (hRdy : Ready O hs r) :
    Post F ι O σ E S Γ₁ env τ r hs (evalS F O n hs σ env (.resume x a)) := by
  obtain ⟨v, σ1, E₁, X, hev, hI₁, hv, hdL, hdLS, hm₁⟩ := atom_ok (.move hx (by simp [Ty.complete])) hI hwf
  have hwf₁ := hm₁.wf
  obtain ⟨w, σ2, E₂, L₂, hev2, hI₂, hw, -, -, hm₂⟩ := atom_ok ha hI₁ hwf₁
  cases hw with
  | @int k =>
  cases hv with
  | @kont _ K _ _ _ hXn hXa hks =>
  obtain ⟨σs, hkok, hagS⟩ := hks
  obtain ⟨τh, e, g, fa, B, s, K', op, ra', X', rfl, hτ, hcv, hK', hperm⟩ :=
    ((WorldOk.ok (F := F) (O := O) (W := ι.w)) σs _ _ X).mp hkok
  injection hτ with _ h1 h2
  subst h1 h2
  -- The continuation, where it was.
  have hσ : ∃ c, lookup x env = some c ∧ σ.mem c = some (.kont (.capV τ e g fa B s :: K') X) ∧
      σ.set c (some .moved) = σ1 := by
    cases hc : lookup x env with
    | none => simp [evalAtom, hc] at hev
    | some c =>
      cases hm : σ.mem c with
      | none => simp [evalAtom, hc, hm] at hev
      | some w =>
        cases w <;> simp [evalAtom, hc, hm] at hev
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hev
        exact ⟨c, rfl, hm, rfl⟩
  obtain ⟨c, hc, hmc, hσ1⟩ := hσ
  simp only [evalS, hc, hmc, hσ1, hev2, Val.foot, List.append_nil]
  have hwf₂ := hm₂.wf
  have hX'X : ∀ l, l ∈ X' ↔ l ∈ X := fun l => hperm.mem_iff.symm
  have hXlt : ∀ l ∈ X, l < σ1.next := fun l hl => hwf₁ l (hXa l hl)
  have hag12 : Agree σ1 σ2 X := hm₂.keeps hwf₁ hXa hdL
  have hXa2 : ∀ l ∈ X, σ2.mem l ≠ none := fun l hl => by rw [hag12 l hl]; exact hXa l hl
  -- The fiber's frames, as the world says, entered again.
  have hres := yield_resume (ι := ⟨[], ι.w⟩) (k := k) (top := ⟨[], [], τ, [], [.eff e]⟩) (hs := [.capture e g]) hKk
    hcv.hop hcv.hrefs hcv.hret hK' (fiber_ready hcv.hop) (fun _ h => by simp at h) hwf₂
    ((hagS.trans hag12).mono fun l hl => (hX'X l).mp (by simpa using hl))
    (fun l hl => by
      have hl' := (hX'X l).mp (by simpa using hl)
      rw [← hagS l hl']; exact hXa l hl')
    (hperm.nodup_iff.mp hXn) disj_nil_left
  have hd2 : Disj E₂ X' := fun l h1 h2 => by
    have h2' := (hX'X l).mp h2
    rcases hm₂.within l (.inr h1) with h | h
    · exact hdL l h2' h
    · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hXlt l h2') h)
  have hcap := ret_capV_ok (n := n) (B := X) (s := σ2.next) (Ein := X') hF hKo hcv hra hRdy hwf₂ hI₂ hd2
    (fun l h1 h2 => hdLS l ((hX'X l).mp h2) h1)
    (fun l hl => hwf₂ l (hXa2 l hl)) hXn (fun l hl => (hX'X l).mpr hl) (fun l hl => .inl ((hX'X l).mp hl))
    (Nat.le_refl _) (fun l h1 h2 => absurd h2 (Nat.not_lt.mpr h1)) (by simpa using hres)
  have m1 : Moves σ E σ1 (E₁ ++ X) [] := hm₁.relabel fun x => by simp [or_comm]
  have m2 : Moves σ1 (E₁ ++ X) σ2 (E₂ ++ X') [] :=
    ((hm₂.widen (X := X) hXa hdL).congr_left fun x => by simp [or_comm]).relabel fun x => by
      simp only [List.mem_append, List.not_mem_nil, or_false, hX'X]; exact or_comm
  exact post_after (m1.trans m2 disj_nil_left hwf) hwf hcap

/-- `handle { f(owned) } with E { op(x…) resumes k => fa(x…, k) }`: the arguments taken and the
parameters allocated on a fiber of the `handle`'s own, which runs under its barrier alone. -/
theorem handleV_ok [WorldOk F O ι.w] (hF : FnsOk F O) (hKk : EvalKOk F O n)
    (hKo : ∀ m, n = m + 1 → EvalOk F O m ∧ FlushOk F ι (flushR F O m))
    (hop : O[e]? = some op) (htask : op.task = false) (hrefs : op.refs = []) (hret : op.ret = .int)
    (howns : ∀ τ' ∈ op.owns, τ'.cross = true) (hτ : τ.cross = true)
    (hfa : F[fa]? = some da) (hdowns : da.owns.map Prod.snd = op.owns ++ [.cont .int τ ra]) (hdrefs : da.refs = [])
    (hdret : da.ret = τ) (hdrow : da.row = ra) (hdretp : da.retp = none) (hdcap : da.cap = none)
    (hra : ∀ l ∈ ra, l ∈ r) (hf : F[f]? = some d) (hrefsd : d.refs = []) (hretd : d.ret = τ)
    (hretpd : d.retp = none) (hcapd : d.cap = none) (he : Label.eff e ∈ d.row) (hrow : ∀ l ∈ d.row, l = .eff e)
    (hcross : ∀ τ' ∈ d.owns.map Prod.snd, τ'.cross = true) (hargs : AtomsTy Γ owned (d.owns.map Prod.snd) Γ₁)
    (hI : Inv F ι σ Γ env E S) (hwf : WF σ) (hRdy : Ready O hs r) :
    Post F ι O σ E S Γ₁ env τ r hs (evalS F O n hs σ env (.handleV τ e f owned fa)) := by
  have hc : CapVOk F O e fa op τ ra :=
    ⟨hop, htask, hrefs, hret, howns, hτ, ⟨da, hfa, hdowns, hdrefs, hdret, hdrow, hdretp, hdcap⟩⟩
  obtain ⟨vs, σ1, E₁, Ls, hevs, hI₁, hvs, hLn, hdL, hdLS, hm₁⟩ := atoms_ok hargs hI hwf
  have hwf₁ := hm₁.wf
  obtain ⟨hk, hb⟩ := hF d (List.mem_of_getElem? hf)
  rw [hcapd, hretpd] at hb
  obtain ⟨Γd, hb⟩ := hb
  have hlen : vs.length = d.owns.length := by rw [hvs.length]; simp
  obtain ⟨-, hfoot⟩ := hvs.konts hcross hLn
  simp only [evalS, hf, hevs]
  rw [if_pos ⟨hlen, hrefsd⟩, hfoot]
  -- The parameters, on the fiber.
  have hvs2 : Vals F ⟨[], ι.w⟩ σ1.fresh.2 (d.owns.map Prod.snd) vs Ls :=
    (hvs.rfree_iota (fun τ' h => Ty.cross_rfree (hcross τ' h))).frame (Agree.of (fun _ _ => rfl) Store.fresh_rt)
  have hwf2 : WF σ1.fresh.2 := hwf₁
  obtain ⟨Eo, hfo, hEo, hEom, hle, hwf4, hold, hnew, -⟩ :=
    allocAll_ok (names := d.owns.map Prod.fst) hvs2 (by simp) hwf2 hLn
  rw [zip_fst_snd] at hfo
  have hcells : (allocAll σ1.fresh.2 ((d.owns.map Prod.fst).zip vs)).1.map Prod.fst = d.owns.map Prod.fst := by
    rw [allocAll_fst]; exact List.map_fst_zip (by rw [hlen]; simp)
  have hrt := allocAll_rt σ1.fresh.2 ((d.owns.map Prod.fst).zip vs)
  generalize allocAll σ1.fresh.2 ((d.owns.map Prod.fst).zip vs) = al at hfo hEom hle hwf4 hold hnew hcells hrt ⊢
  obtain ⟨cells, σ4⟩ := al
  dsimp only at hfo hEom hle hwf4 hold hnew hcells hrt ⊢
  have hEoin : ∀ l ∈ Eo, l ∈ Ls.flatten ∨ σ1.next ≤ l := fun l hl => by
    rcases (hEom l).mp hl with h | h
    · exact .inl h
    · exact .inr h.1
  have hId := callee_inv (k := 0) (d := d) (hs := []) (ι := ⟨[], ι.w⟩) hI₁ (fun _ h => by simp at h)
    List.Pairwise.nil (by simp [hrefsd]) hk hfo hEo hEoin hdL hdLS hwf₁ hold hrt (fun _ h => by simp at h)
  have hId' : Inv F ⟨[], ι.w⟩ σ4 (fnCtx d) (cells ++ (d.refs.map Prod.fst).zip []) Eo [] := by
    simpa [olds, mutCells, roCells] using hId
  have hKd := task_frames (r := []) (ls := []) hk hvs2.owns_complete hb
    (fun l hl => by rw [hrow l hl]; exact List.mem_singleton_self _) hcells hop hrefs hret he hId'
  simp only [hrefsd, hretd, List.map_nil, List.zip_nil_left, List.append_nil, refCtx] at hKd
  have hres := yield_resume (ι := ⟨[], ι.w⟩) (top := ⟨[], [], τ, [], [.eff e]⟩) (hs := [.capture e σ1.fresh.1])
    hKk hop hrefs hret hKd (fiber_ready hop) (fun _ h => by simp at h) hwf4 Agree.self
    (fun l hl => hId'.foot.alloc l (List.mem_append.mp hl)) hEo disj_nil_left
  -- The code around, as the fiber starts.
  have hE1a : ∀ l ∈ E₁ ++ S, σ1.mem l ≠ none := fun l hl => hI₁.foot.alloc l (List.mem_append.mp hl)
  have hI4 : Inv F ι σ4 Γ₁ env E₁ S :=
    ⟨hI₁.foot.frame (Agree.of (fun l hl => hold l (hwf₁ l (hE1a l hl))) hrt), hI₁.nodup, hI₁.disj, hI₁.keys⟩
  have hLa : ∀ l ∈ Ls.flatten, σ1.mem l ≠ none := hvs.alloc
  have apart : ∀ {X}, (∀ l ∈ X, σ1.mem l ≠ none) → Disj Ls.flatten X → Disj X Eo := fun hX hdX l h1 h2 => by
    rcases hEoin l h2 with h | h
    · exact hdX l h h1
    · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hwf₁ l (hX l h1)) h)
  have hcap := ret_capV_ok (n := n) (B := Ls.flatten) (s := σ1.fresh.2.next) (Ein := Eo) hF hKo hc hra hRdy hwf4 hI4
    (apart hI₁.alloc hdL) (apart hI₁.allocS hdLS) (fun l hl => hwf₁ l (hLa l hl)) hLn
    (fun l hl => (hEom l).mpr (.inl hl)) (fun l hl => (hEom l).mp hl) hle
    (fun l h1 h2 _ => (hEom l).mpr (.inr ⟨h1, h2⟩)) hres
  have m1 : Moves σ E σ1 (E₁ ++ Ls.flatten) [] := hm₁.relabel fun x => by simp
  have hEL : ∀ l ∈ E₁ ++ Ls.flatten, σ1.mem l ≠ none := fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · exact hI₁.alloc l h
    · exact hLa l h
  have m2 := Moves.freshen (E := E₁ ++ Ls.flatten) hwf₁ hEL
  have m3 := Moves.grow (σ := σ1.fresh.2) (σ' := σ4) (E := E₁ ++ Ls.flatten) (E' := E₁ ++ Eo) hwf2 hwf4 hle hold hnew
    hEL (fun l => by simp only [List.mem_append, hEom]; exact or_assoc.symm) hrt
  exact post_after (((m1.trans m2 disj_nil_left hwf).trans m3 disj_nil_left hwf).relabel fun x => by simp) hwf hcap

end FlyCore.Ownership
