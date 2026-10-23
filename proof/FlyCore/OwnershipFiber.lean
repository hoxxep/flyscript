import FlyCore.OwnershipScope

/-!
# Ownership: a `handle` whose arm keeps its continuation

The `handle`'s body runs on a fiber of its own, under the handlers of the code around but for its
own operation and failures, which its own handler takes. Each time it performs its operation, the
fiber's frames become a continuation value, owning what the fiber allocated since it was last entered
and still holds, and what it owned then, but for what the operation passes out; the arm, a function,
is called with what the operation passes and the continuation, in the code around. An operation the
code around takes, it takes with the fiber as one frame, which enters the fiber again once answered.
Resuming the continuation enters the fiber again.
-/

namespace FlyCore.Ownership

variable {F : List Fn} {O : List Op}

theorem Vals.append : Vals F ι σ τs vs Ls → Vals F ι σ τs' vs' Ls' → Vals F ι σ (τs ++ τs') (vs ++ vs') (Ls ++ Ls')
  | .nil, h => h
  | .cons hv hr, h => .cons hv (hr.append h)

/-- What a fiber owns where it gives way, as `kfoot` computes it: the cells it owned when it was
entered and those it allocated since, still there, but for what it passes out — which is what its
frames own. -/
theorem kfoot_perm (hwf0 : WF σ0) (hwf' : WF σ') (hm : Moves σ0 Ein σ' X Lv)
    (hBE : ∀ l ∈ B, l ∈ Ein) (hEB : ∀ l ∈ Ein, l ∈ B ∨ (s ≤ l ∧ l < σ0.next))
    (hsn : s ≤ σ0.next) (hnew : ∀ l, s ≤ l → l < σ0.next → σ0.mem l ≠ none → l ∈ Ein) (hXn : X.Nodup)
    (hdX : Disj Lv X) (hfoot : vs.flatMap (Val.tree σ') = Lv) :
    (kfoot σ' B s vs).Perm X ∧ (kfoot σ' B s vs).Nodup ∧ ∀ l ∈ kfoot σ' B s vs, σ'.mem l ≠ none := by
  have hmem : ∀ l, l ∈ kfoot σ' B s vs ↔ (l ∈ B ∨ (s ≤ l ∧ l < σ'.next)) ∧ σ'.mem l ≠ none ∧ l ∉ Lv := by
    intro l
    simp only [kfoot, List.mem_filter, mem_dedupL, List.mem_append, List.mem_range'_1, Bool.and_eq_true,
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
  have hnd : (kfoot σ' B s vs).Nodup := (nodup_dedupL _).sublist List.filter_sublist
  exact ⟨(List.perm_ext_iff_of_nodup hnd hXn).mpr hiff, hnd, fun l hl => ((hmem l).mp hl).2.1⟩

theorem Ty.cross_rfree {τ : Ty} (h : τ.cross = true) : τ.rfree = true := by
  simp only [Ty.cross, Bool.and_eq_true] at h; exact h.1

theorem Ty.cross_complete' {τ : Ty} (h : τ.cross = true) : τ.complete = true := by
  simp only [Ty.cross, Bool.and_eq_true] at h; exact h.2

/-! ## The handlers in force on a fiber -/

theorem hsConv_ok (h : HSOk O hs) : HSOk O (hsConv hs) := by
  induction h with
  | nil => exact .nil
  | @abort l hid rest hl _ ih =>
    cases l with
    | eff e =>
      obtain ⟨op, hop, -⟩ := hl e rfl
      exact .capture ⟨op, hop⟩ ih
    | fail => simpa [hsConv] using ih
    | drop => simpa [hsConv] using ih
  | capture ho _ ih => exact .capture ho ih
  | cancel _ ih => exact .cancel ih

theorem mem_hsConv : ∀ {hs : HS} {x : Frame}, x ∈ hsConv hs →
    (∃ e j, x = .capture e j ∧ Takes hs j e) ∨ (∃ j, x = .cancel j ∧ Frame.cancel j ∈ hs)
  | [], _, h => by simp [hsConv] at h
  | f :: hs, x, h => by
    cases f with
    | abort l c =>
      cases l with
      | eff e =>
        simp only [hsConv, List.mem_cons] at h
        rcases h with rfl | h
        · exact .inl ⟨e, c, rfl, .inr (.inr (List.mem_cons_self ..))⟩
        · rcases mem_hsConv h with ⟨e', j, rfl, ht⟩ | ⟨j, rfl, hj⟩
          · exact .inl ⟨e', j, rfl, ht.cons⟩
          · exact .inr ⟨j, rfl, List.mem_cons_of_mem _ hj⟩
      | fail =>
        simp only [hsConv] at h
        rcases mem_hsConv h with ⟨e', j, rfl, ht⟩ | ⟨j, rfl, hj⟩
        · exact .inl ⟨e', j, rfl, ht.cons⟩
        · exact .inr ⟨j, rfl, List.mem_cons_of_mem _ hj⟩
      | drop =>
        simp only [hsConv] at h
        rcases mem_hsConv h with ⟨e', j, rfl, ht⟩ | ⟨j, rfl, hj⟩
        · exact .inl ⟨e', j, rfl, ht.cons⟩
        · exact .inr ⟨j, rfl, List.mem_cons_of_mem _ hj⟩
    | capture e c =>
      simp only [hsConv, List.mem_cons] at h
      rcases h with rfl | h
      · exact .inl ⟨e, c, rfl, .inl (List.mem_cons_self ..)⟩
      · rcases mem_hsConv h with ⟨e', j, rfl, ht⟩ | ⟨j, rfl, hj⟩
        · exact .inl ⟨e', j, rfl, ht.cons⟩
        · exact .inr ⟨j, rfl, List.mem_cons_of_mem _ hj⟩
    | cancel c =>
      simp only [hsConv, List.mem_cons] at h
      rcases h with rfl | h
      · exact .inr ⟨c, rfl, List.mem_cons_self ..⟩
      · rcases mem_hsConv h with ⟨e', j, rfl, ht⟩ | ⟨j, rfl, hj⟩
        · exact .inl ⟨e', j, rfl, ht.cons⟩
        · exact .inr ⟨j, rfl, List.mem_cons_of_mem _ hj⟩

theorem takes_hsConv (h : Takes (hsConv hs) j e) : Takes hs j e := by
  rcases h with h | h | h
  · rcases mem_hsConv h with ⟨e', j', h1, ht⟩ | ⟨j', h1, -⟩
    · simp only [Frame.capture.injEq] at h1; obtain ⟨rfl, rfl⟩ := h1; exact ht
    · cases h1
  · rcases mem_hsConv h with ⟨e', j', h1, -⟩ | ⟨j', h1, hj⟩
    · cases h1
    · simp only [Frame.cancel.injEq] at h1; subst h1; exact .inr (.inl hj)
  · rcases mem_hsConv h with ⟨e', j', h1, -⟩ | ⟨j', h1, -⟩ <;> cases h1

theorem not_aimed_hsConv (h : AimedIn a (hsConv hs)) : False := by
  obtain ⟨l, h⟩ := h
  rcases mem_hsConv h with ⟨e', j', h1, -⟩ | ⟨j', h1, -⟩ <;> cases h1

theorem find_hsConv : ∀ {hs : HS} {e : Nat} {f : Frame}, find (.eff e) hs = some f →
    ∃ f', find (.eff e) (hsConv hs) = some f'
  | [], _, _, h => by simp [find] at h
  | x :: hs, e, f, h => by
    cases x with
    | abort l c =>
      cases l with
      | eff e' =>
        by_cases he : e' = e
        · subst he; exact ⟨.capture e' c, by simp [hsConv, find, Frame.handles]⟩
        · simp only [find, Frame.handles, beq_iff_eq, Label.eff.injEq, he, ↓reduceIte] at h
          obtain ⟨f', hf'⟩ := find_hsConv h
          exact ⟨f', by simp [hsConv, find, Frame.handles, he, hf']⟩
      | fail =>
        simp only [find, Frame.handles, beq_iff_eq, reduceCtorEq, ↓reduceIte] at h
        simpa [hsConv] using find_hsConv h
      | drop =>
        simp only [find, Frame.handles, beq_iff_eq, reduceCtorEq, ↓reduceIte] at h
        simpa [hsConv] using find_hsConv h
    | capture e' c =>
      by_cases he : e' = e
      · subst he; exact ⟨.capture e' c, by simp [hsConv, find, Frame.handles]⟩
      · simp only [find, Frame.handles, beq_iff_eq, he, ↓reduceIte] at h
        obtain ⟨f', hf'⟩ := find_hsConv h
        exact ⟨f', by simp [hsConv, find, Frame.handles, he, hf']⟩
    | cancel c => exact ⟨.cancel c, by simp [hsConv, find, Frame.handles]⟩

/-- What the code on a fiber may perform has a handler: its own operation and failures the fiber's,
the rest those of the code around. -/
theorem fiber_ready (hop : O[e]? = some op) (hR : Ready O hs r) (hrow : FiberRow e ff ra rf)
    (hra : ∀ l ∈ ra, l ∈ r) : Ready O (fiberHS e g ff hs) rf := by
  refine ⟨.capture ⟨op, hop⟩ ?_, fun l hl => ?_⟩
  · cases ff
    · simpa using hsConv_ok hR.1
    · exact .abort (fun _ h => by cases h) (hsConv_ok hR.1)
  rcases hrow.1 l hl with rfl | ⟨hla, hne⟩
  · exact ⟨.capture e g, by simp [fiberHS, find, Frame.handles]⟩
  cases l with
  | drop => exact absurd rfl hne
  | fail =>
    have hff := hrow.2.2 hl
    subst hff
    exact ⟨.abort .fail g, by simp [fiberHS, find, Frame.handles]⟩
  | eff e' =>
    obtain ⟨f, hf⟩ := hR.2 _ (hra _ hla)
    obtain ⟨f', hf'⟩ := find_hsConv hf
    refine covers_cons _ (fun l hl => ?_) (.eff e') (List.mem_singleton_self _)
    simp only [List.mem_singleton] at hl
    subst hl
    cases ff
    · exact ⟨f', by simpa using hf'⟩
    · exact covers_cons _ (fun l hl => by simp only [List.mem_singleton] at hl; subst hl; exact ⟨f', hf'⟩)
        (.eff e') (List.mem_singleton_self _)

theorem fiber_aimed (h : AimedIn a (fiberHS e g ff hs)) : a = g ∧ ff = true := by
  obtain ⟨l, h⟩ := h
  simp only [fiberHS, List.mem_cons, reduceCtorEq, false_or, List.mem_append] at h
  rcases h with h | h
  · cases ff <;> simp at h
    exact ⟨h.2, rfl⟩
  · exact (not_aimed_hsConv ⟨l, h⟩).elim

theorem fiber_takes (h : Takes (fiberHS e g ff hs) j ef) : (j = g ∧ ef = e) ∨ Takes hs j ef := by
  simp only [fiberHS] at h
  rcases h.of_cons_capture with h | h
  · exact .inl h
  · cases ff
    · exact .inr (takes_hsConv (by simpa using h))
    · exact .inr (takes_hsConv h.of_cons_fail)

theorem find_fail (h : find .fail hs = some f) : ∃ j, f = .abort .fail j ∧ AimedIn j hs := by
  induction hs with
  | nil => simp [find] at h
  | cons x hs ih =>
    simp only [find] at h
    split at h
    · rename_i hx
      simp only [Option.some.injEq] at h
      subst h
      cases x with
      | abort l c =>
        simp only [Frame.handles, beq_iff_eq] at hx
        subst hx
        exact ⟨c, rfl, ⟨.fail, List.mem_cons_self ..⟩⟩
      | capture => simp [Frame.handles] at hx
      | cancel => simp [Frame.handles] at hx
    · obtain ⟨j, rfl, l, hl⟩ := ih h
      exact ⟨j, rfl, l, List.mem_cons_of_mem _ hl⟩

theorem Ty.whole_rfree {τ : Ty} (h : τ.whole = true) (hr : τ.rfree = true) : τ.complete = true := by
  cases τ <;> simp_all [Ty.whole, Ty.rfree]

/-- What a place lent by an operation holds is what its tree is, read off the store. -/
theorem hole_tree (hok : HoleOk F ι σ Γ env h) (hr : h.ty.rfree = true) (hwf : WF σ) :
    cellTree σ h.loc = h.old := by
  have hlt := hok.old_lt
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hw, _⟩ := hok
  exact hlt.cell_tree (Ty.whole_rfree hw hr) hwf

/-! ## Where the fiber gives way, or ends -/

/-- The fiber of a `handle` whose arm keeps its continuation, as what runs on it ends: with a value,
which passes out; unwinding by a failure, which goes on to the handler of the code around; giving way
by its operation, which calls the arm with what the operation passes and the continuation, which owns
the fiber's cells; or by an operation of the code around, which takes the fiber as one frame. -/
theorem ret_capV_ok [WorldOk F O ι.w] (hF : FnsOk F O)
    (hKo : ∀ m, n = m + 1 → EvalOk F O m ∧ FlushOk F ι (flushR F O m))
    (hc : CapVOk F O e fa op τ ra) (hrow : FiberRow e ff ra rf) (hra : ∀ l ∈ ra, l ∈ r) (hR : Ready O hs r)
    (hwf : WF σ0) (hI : Inv F ι σ0 Γ₁ env E₁ S) (hd : Disj E₁ Ein) (hdS : Disj S Ein)
    (hBE : ∀ l ∈ B, l ∈ Ein) (hEB : ∀ l ∈ Ein, l ∈ B ∨ (s ≤ l ∧ l < σ0.next)) (hsn : s ≤ σ0.next)
    (hnew : ∀ l, s ≤ l → l < σ0.next → σ0.mem l ≠ none → l ∈ Ein)
    (hp : Post F ⟨[], ι.w⟩ O σ0 Ein [] [] [] τ rf (fiberHS e g ff hs) res) :
    Post F ι O σ0 (E₁ ++ Ein) S Γ₁ env τ r hs (ret F O n hs (.capV τ e g fa ff B s) res) := by
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
    have hret : ret F O n hs (.capV τ e g fa ff B s) (.val v, σ') = (.val v, σ') := by rw [ret.eq_def]
    rw [hret]
    obtain ⟨hI1, -, hdL⟩ := around hm
    refine ⟨E₁, L, hI1, hv.rfree_iota hτr, fun l h1 h2 => hdL l (List.mem_append.mpr (.inl h2)) h1,
      fun l h1 h2 => hdL l (List.mem_append.mpr (.inr h2)) h1, ?_⟩
    exact (hm.widen (X := E₁) (fun l hl => hI.alloc l hl) hd).relabel fun x => by simp
  | abort j k =>
    obtain ⟨haim, E', hI', hm⟩ := hp
    obtain ⟨rfl, -⟩ := hI'.nil_E
    obtain ⟨rfl, rfl⟩ := fiber_aimed haim
    -- A failure of the body: rethrown to the handler of the code around.
    obtain ⟨f, hf⟩ := hR.2 .fail (hra _ (hrow.2.1 rfl))
    obtain ⟨j', rfl, hj'⟩ := find_fail hf
    have hret : ret F O n hs (.capV τ e j fa true B s) (.abort j k, σ') = (.abort j' k, σ') := by
      rw [ret.eq_def]; simp [hf]
    rw [hret]
    obtain ⟨hI1, -, -⟩ := around hm
    exact ⟨hj', E₁, hI1, (hm.widen (X := E₁) (fun l hl => hI.alloc l hl) hd).relabel fun x => by simp⟩
  | stuck => simp [Post] at hp
  | timeout => rw [ret.eq_def]; simp [Post]
  | panic => rw [ret.eq_def]; simp [Post]
  | susp j ef vs ls K =>
    obtain ⟨op', X, hos, A, Lv, hcap, hop', -, haim, hK, hls, hvs, hLn, hdX, -, hm⟩ := hp
    obtain ⟨ι₁, Γf, envf, Ef, Sf, hIf, hholes, hpw, hts, -, -, hXn, hXM, hw₁⟩ := hK.base_of
    have hA : ∀ a ∈ A, a = g ∧ ff = true := fun a ha => fiber_aimed (haim a ha)
    have hfoot := hvs.trees hm.wf
    have hXMn : (X ++ mutCells (olds hos)).Nodup := nodup_append_disj.mpr ⟨hXn, olds_nodup hIf hholes hpw, hXM⟩
    obtain ⟨hperm, hXn'', hXa''⟩ := kfoot_perm hwf hm.wf hm hBE hEB hsn hnew hXMn (fun l h1 h2 => hdX l h1 h2) hfoot
    obtain ⟨hI1, hdE, hdL⟩ := around hm
    by_cases hown : j = g ∧ ef = e
    · obtain ⟨hj, he⟩ := hown
      subst j; subst ef
      obtain rfl : op = op' := Option.some.inj (hc.hop.symm.trans hop')
      rw [hc.hrefs] at hts
      obtain rfl : hos = [] := List.map_eq_nil_iff.mp hts
      simp only [List.map_nil] at hls
      subst hls
      simp only [olds, mutCells, List.map_nil, List.flatMap_nil, List.append_nil] at hm hdX hperm hXMn hdE
      cases n with
      | zero => rw [ret.eq_def]; simp [Post]
      | succ m =>
      obtain ⟨hEm, hflm⟩ := hKo m rfl
      obtain ⟨da, hfa, hdowns, hdrefs, hdret, hdrow, hdretp, hdcap⟩ := hc.harm
      -- The continuation: a value of the world's, owning the fiber's cells.
      have hkv : VT F ι σ' (.cont op.ret τ ra) (.kont (.capV τ e g fa ff B s :: K) (kfoot σ' B s vs))
          (kfoot σ' B s vs) :=
        .kont hXn'' hXa'' ⟨σ', ((WorldOk.ok (F := F) (O := O) (W := ι.w)) σ' _ _ _).mpr
          ⟨τ, e, g, fa, ff, B, s, K, op, ra, rf, A, X, rfl, rfl, hc, hrow, hA, hK, hperm⟩, Agree.self⟩
      have hvs' : Vals F ι σ' (da.owns.map Prod.snd) (vs ++ [.kont (.capV τ e g fa ff B s :: K) (kfoot σ' B s vs)])
          (Lv ++ [kfoot σ' B s vs]) := by
        rw [hdowns]
        exact (hvs.rfree_iota (fun τ' h => Ty.cross_rfree (hc.howns τ' h))).append (.cons hkv .nil)
      obtain ⟨hk, hb⟩ := hF da (List.mem_of_getElem? hfa)
      rw [hdcap, hdretp] at hb
      obtain ⟨Γ'', hb⟩ := hb
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
      have hlen : (vs ++ [Val.kont (.capV τ e g fa ff B s :: K) (kfoot σ' B s vs)]).length = da.owns.length := by
        rw [hvs'.length, List.length_map]
      rw [ret.eq_def]
      simpa [hfa, hlen, hdrefs] using hcore
    · -- An operation of the code around: it takes the fiber as one frame.
      have hret : ret F O n hs (.capV τ e g fa ff B s) (.susp j ef vs ls K, σ') =
          (.susp j ef vs ls [.enterK τ e g fa ff K
            ((kfoot σ' B s vs).filter fun l => !(ls.flatMap (cellTree σ')).contains l) ls], σ') := by
        rw [ret.eq_def]; simp [hown]
      rw [hret]
      have htrees : ∀ l, l ∈ ls.flatMap (cellTree σ') ↔ l ∈ hos.flatMap Hole.old := fun l => by
        subst hls
        simp only [List.flatMap_map, List.mem_flatMap]
        constructor
        · rintro ⟨h, hh, hl⟩
          have hr : h.ty.rfree = true := by
            have : (h.mode, h.ty) ∈ op'.refs := hts ▸ List.mem_map_of_mem hh
            exact Op.refs_rfree op' _ this
          exact ⟨h, hh, by rw [← hole_tree (hholes h hh) hr hm.wf]; exact hl⟩
        · rintro ⟨h, hh, hl⟩
          have hr : h.ty.rfree = true := by
            have : (h.mode, h.ty) ∈ op'.refs := hts ▸ List.mem_map_of_mem hh
            exact Op.refs_rfree op' _ this
          exact ⟨h, hh, by rw [hole_tree (hholes h hh) hr hm.wf]; exact hl⟩
      have hXrmem : ∀ l, l ∈ (kfoot σ' B s vs).filter (fun l => !(ls.flatMap (cellTree σ')).contains l) ↔
          (l ∈ X ∨ l ∈ mutCells (olds hos)) ∧ l ∉ hos.flatMap Hole.old := fun l => by
        simp only [List.mem_filter, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not, htrees,
          hperm.mem_iff, List.mem_append]
      have hnest := FramesOk.nest (Γ' := Γ₁) hc hrow hra hA hK hI1 (Weaker.refl _)
        (fun l h1 h2 => hdE l (List.mem_append.mpr (.inl h1)) h2)
        (fun l h1 h2 => hdE l (List.mem_append.mpr (.inr h1)) h2) (hXn''.filter _) hXrmem hls
      refine ⟨op', E₁ ++ X, hos, [], Lv, ?_, hop', hR.2, fun _ h => by simp at h, hnest, hls,
        hvs.rfree_iota (Op.owns_rfree op'), hLn, ?_, fun l h1 h2 => hdL l (List.mem_append.mpr (.inr h2)) h1, ?_⟩
      · rcases fiber_takes hcap with h | h
        · exact absurd h hown
        · exact h
      · intro l h1 h2
        simp only [List.mem_append] at h2
        rcases h2 with (h2 | h2) | h2
        · exact hdL l (List.mem_append.mpr (.inl h2)) h1
        · exact hdX l h1 (List.mem_append.mpr (.inl h2))
        · exact hdX l h1 (List.mem_append.mpr (.inr h2))
      · exact (hm.widen (X := E₁) (fun l hl => hI.alloc l hl) hd).relabel fun x => by simp [or_assoc]

/-! ## Entering a fiber again -/

theorem exclPart_mut {h : Hole} (hm : h.mode = .mut) (L : List Nat) :
    exclPart h.slot L = if h.ty.shell then L.tail else L := by
  simp [exclPart, Hole.slot, Slot.excl, Slot.shell, hm]

theorem exclPart_ro {h : Hole} (hm : h.mode = .ro) (L : List Nat) : exclPart h.slot L = [] := by
  simp [exclPart, Hole.slot, Slot.excl, hm]

/-- In a tree lent `mut` with its first cell, a cell is that first cell or one the borrow may change. -/
theorem mem_cons_excl {h : Hole} (hm : h.mode = .mut) (hl : l ∈ h.loc :: R) :
    l = h.loc ∨ l ∈ exclPart h.slot (h.loc :: R) := by
  rw [exclPart_mut hm]
  rcases List.mem_cons.mp hl with rfl | hl
  · exact .inl rfl
  · split <;> simp [hl]

/-- What the fiber owns as it is entered again, as the semantics computes it: what it owned where it
gave way, but for the trees of the places it lent; those trees as they are now; and the answer's
cells. That is what its frames own, what the places it lent `mut` now hold, and the answer's. -/
theorem reenter_cells {hos : List Hole} {ps : List (Hole × List Nat)}
    (hXrmem : ∀ l, l ∈ Xr ↔ (l ∈ Xi ∨ l ∈ mutCells (olds hos)) ∧ l ∉ hos.flatMap Hole.old)
    (hi : ∀ h ∈ hos, ∀ l ∈ h.old, l ∈ Xi ∨ l ∈ mutCells (olds hos))
    (hiii : ∀ h ∈ hos, ∀ l ∈ h.old, l ∈ mutCells (olds hos) → l ∈ exclPart h.slot h.old)
    (hXM : Disj Xi (mutCells (olds hos)))
    (hro : ∀ h ∈ hos, h.mode = .ro → cellTree σ h.loc = h.old)
    (hmut : ∀ p ∈ ps, p.1.mode = .mut → cellTree σ p.1.loc = p.2)
    (hps : ps.map Prod.fst = hos) (hold : ∀ h ∈ hos, ∃ R, h.old = h.loc :: R)
    (hnd : ∀ h ∈ hos, h.old.Nodup) (hnewh : ∀ p ∈ ps, p.1.mode = .mut → ∃ R, p.2 = p.1.loc :: R) :
    ∀ l, l ∈ Xr ++ (hos.map Hole.loc).flatMap (cellTree σ) ++ Lv ↔ l ∈ Xi ++ mutCells ps ++ Lv := by
  have hmutOld : ∀ l ∈ mutCells (olds hos), l ∈ hos.flatMap Hole.old := fun l hl => by
    obtain ⟨h, hh, hl⟩ := mem_olds_mut.mp hl
    exact List.mem_flatMap.mpr ⟨h, hh, exclPart_sub hl⟩
  have hhos : ∀ h ∈ hos, ∃ p ∈ ps, p.1 = h := fun h hh => by
    rw [← hps] at hh
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hh
    exact ⟨p, hp, rfl⟩
  have hpsh : ∀ p ∈ ps, p.1 ∈ hos := fun p hp => hps ▸ List.mem_map_of_mem hp
  -- A cell of a tree lent `mut` that is the frames' own is the place's first cell.
  have hhead : ∀ h ∈ hos, h.mode = .mut → ∀ l ∈ h.old, l ∈ Xi → l = h.loc := fun h hh hm l hl hX => by
    obtain ⟨R, hR⟩ := hold h hh
    rw [hR] at hl
    rcases mem_cons_excl hm hl with h1 | h1
    · exact h1
    · rw [← hR] at h1
      exact absurd (mem_olds_mut.mpr ⟨h, hh, h1⟩) (hXM l hX)
  -- The first cell of a place lent `mut` whose borrow may not change it is the frames' own.
  have hlocX : ∀ h ∈ hos, h.mode = .mut → h.ty.shell = true → h.loc ∈ Xi := fun h hh hm hsh => by
    obtain ⟨R, hR⟩ := hold h hh
    have hlo : h.loc ∈ h.old := by rw [hR]; exact List.mem_cons_self ..
    rcases hi h hh _ hlo with h2 | h2
    · exact h2
    · have h3 := hiii h hh _ hlo h2
      rw [exclPart_mut hm, hR] at h3
      simp only [hsh, ↓reduceIte, List.tail_cons] at h3
      have := hnd h hh
      rw [hR] at this
      exact absurd h3 (List.nodup_cons.mp this).1
  intro l
  simp only [List.mem_append, List.flatMap_map, hXrmem]
  constructor
  · rintro ((⟨h1, h2⟩ | hl) | hl)
    · rcases h1 with h1 | h1
      · exact .inl (.inl h1)
      · exact absurd (hmutOld l h1) h2
    · obtain ⟨h, hh, hl⟩ := List.mem_flatMap.mp hl
      cases hm : h.mode with
      | ro =>
        rw [hro h hh hm] at hl
        rcases hi h hh l hl with h1 | h1
        · exact .inl (.inl h1)
        · have := hiii h hh l hl h1
          rw [exclPart_ro hm] at this; simp at this
      | «mut» =>
        obtain ⟨p, hp, rfl⟩ := hhos h hh
        rw [hmut p hp hm] at hl
        by_cases hsh : p.1.ty.shell = true
        · obtain ⟨R', hR'⟩ := hnewh p hp hm
          rw [hR'] at hl
          rcases List.mem_cons.mp hl with rfl | h1
          · exact .inl (.inl (hlocX p.1 hh hm hsh))
          · refine .inl (.inr (mem_mutCells.mpr ⟨p, hp, ?_⟩))
            rw [exclPart_mut hm, hR']; simp [hsh, h1]
        · exact .inl (.inr (mem_mutCells.mpr ⟨p, hp, by rw [exclPart_mut hm]; simp [hsh, hl]⟩))
    · exact .inr hl
  · rintro ((h1 | h1) | h1)
    · by_cases ho : l ∈ hos.flatMap Hole.old
      · obtain ⟨h, hh, hl⟩ := List.mem_flatMap.mp ho
        refine .inl (.inr (List.mem_flatMap.mpr ⟨h, hh, ?_⟩))
        cases hm : h.mode with
        | ro => rw [hro h hh hm]; exact hl
        | «mut» =>
          obtain rfl := hhead h hh hm l hl h1
          obtain ⟨p, hp, rfl⟩ := hhos h hh
          rw [hmut p hp hm]
          obtain ⟨R', hR'⟩ := hnewh p hp hm
          rw [hR']; exact List.mem_cons_self ..
      · exact .inl (.inl ⟨.inl h1, ho⟩)
    · obtain ⟨p, hp, hl⟩ := mem_mutCells.mp h1
      have hm := (Hole.excl_mut hl).1
      exact .inl (.inr (List.mem_flatMap.mpr ⟨p.1, hpsh p hp, by rw [hmut p hp hm]; exact exclPart_sub hl⟩))
    · exact .inr h1

/-- The trees of the places the fiber's frames lent are among their cells and those the places lent
`mut` may change; and a cell of one tree the borrows may change is one its own borrow may. -/
theorem holes_base {hos : List Hole} {Xi Ef Sf : List Nat} (hIf : Inv F ι₁ σ Γf envf Ef Sf)
    (hholes : ∀ h ∈ hos, HoleOk F ι₁ σ Γf envf h) (hpw : hos.Pairwise Apart)
    (hEf : ∀ l ∈ Ef, l ∉ mutCells (olds hos) → l ∈ Xi) (hSf : ∀ l ∈ Sf, l ∈ Xi ∨ l ∈ ([] : List Nat)) :
    (∀ h ∈ hos, ∀ l ∈ h.old, l ∈ Xi ∨ l ∈ mutCells (olds hos)) ∧
    (∀ h ∈ hos, ∀ l ∈ h.old, l ∈ mutCells (olds hos) → l ∈ exclPart h.slot h.old) := by
  refine ⟨fun h hh l hl => ?_, fun h hh l hl hM => ?_⟩
  · rcases (hole_in hIf (hholes h hh)).1 l (List.mem_append.mpr (.inr hl)) with h1 | h1
    · by_cases hM : l ∈ mutCells (olds hos)
      · exact .inr hM
      · exact .inl (hEf l h1 hM)
    · rcases hSf l h1 with h2 | h2
      · exact .inl h2
      · simp at h2
  · obtain ⟨h', hh', hl'⟩ := mem_olds_mut.mp hM
    by_cases he : h' = h
    · subst he; exact hl'
    · have hm' := (Hole.excl_mut hl').1
      rcases hole_sep hpw hh' hh hm' he with hr | hd
      · exact absurd (List.mem_append.mpr (.inr hl)) (hole_apart hIf (hholes h' hh') (hholes h hh) hr hm' l hl')
      · exact absurd hl (hd l (exclPart_sub hl'))

/-- A fiber taken through an operation of the code around, answered or dropped: answered, it is
entered again with the answer, owning what its frames do, what the places it lent `mut` now hold, and
the answer; dropped, it unwinds, every operation its cleanup performs cancelled. -/
theorem nest_core [WorldOk F O ι.w] (hF : FnsOk F O)
    (hKs : ∀ m, m < n → EvalOk F O m ∧ EvalKOk F O m ∧ RetOk F O m)
    (hc : CapVOk F O e fa op τ ra) (hrow : FiberRow e ff ra rf) (hra : ∀ l ∈ ra, l ∈ r)
    (hAi : ∀ a ∈ Ai, a = g ∧ ff = true)
    (hKi : FramesOk F O ⟨[], ι.w⟩ σs K op0 ⟨[], [], τ, [], rf⟩ Xi hos Ai)
    (hI : Inv F ι σs Γ₁ env E₁ S) (w : Weaker Γ' Γ₁) (hdE : Disj E₁ (Xi ++ mutCells (olds hos)))
    (hdS' : Disj S (Xi ++ mutCells (olds hos))) (hXrn : Xr.Nodup)
    (hXrmem : ∀ l, l ∈ Xr ↔ (l ∈ Xi ∨ l ∈ mutCells (olds hos)) ∧ l ∉ hos.flatMap Hole.old)
    (hls : ls = hos.map Hole.loc) (hR : Ready O hs r) (hwf : WF σr)
    (hag : Agree σs σr ((E₁ ++ Xi) ++ S)) (halloc : ∀ l ∈ (E₁ ++ Xi) ++ S, σs.mem l ≠ none)
    (hnd : (E₁ ++ Xi).Nodup) (hps : ps.map Prod.fst = hos)
    (hnew : ∀ p ∈ ps, p.1.mode = .mut → LT F ι σr p.1.loc p.1.ty p.2) (hMn : (mutCells ps).Nodup)
    (hX : Disj (E₁ ++ Xi) (mutCells ps)) (hdS : Disj S ((E₁ ++ Xi) ++ mutCells ps ++ Lv))
    (hin : (∃ v, r0 = .val v ∧ VT F ι σr op0.ret v Lv ∧ Disj Lv ((E₁ ++ Xi) ++ mutCells ps)) ∨
      (∃ a k, r0 = .abort a k ∧ AimedIn a hs ∧ Lv = [])) :
    Post F ι O σr ((E₁ ++ Xi) ++ mutCells ps ++ Lv) S Γ' env τ r hs
      (evalK F O n hs σr [.enterK τ e g fa ff K Xr ls] r0) := by
  simp only [evalK, Kont.push]
  cases n with
  | zero => rcases hin with ⟨v, rfl, -⟩ | ⟨a, k, rfl, -⟩ <;> simp [ret, Post]
  | succ m =>
  obtain ⟨hEm, hKm, hRm⟩ := hKs m (by omega)
  have hKo' : ∀ m', m = m' + 1 → EvalOk F O m' ∧ FlushOk F ι (flushR F O m') :=
    fun m' h => ⟨(hKs m' (by omega)).1, flushR_ok fun k hk => (hKs k (by omega)).2.1⟩
  obtain ⟨ι₁, Γf, envf, Ef, Sf, hIf, hholes, hpw, hts, hEf, hSf, hXin, hXM, hw₁⟩ := hKi.base_of
  have hrf : ∀ p ∈ ps, p.1.ty.rfree = true := fun p hp => by
    have : (p.1.mode, p.1.ty) ∈ op0.refs := by
      rw [← hts, ← hps]; exact List.mem_map_of_mem (List.mem_map_of_mem hp)
    exact op0.refs_rfree _ this
  have hEn := (List.nodup_append.mp hnd)
  have hXia : ∀ l ∈ Xi, σs.mem l ≠ none := fun l hl => halloc l (by simp [hl])
  have hE1S : ∀ l ∈ E₁ ++ S, σs.mem l ≠ none := fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · exact halloc l (by simp [h])
    · exact halloc l (by simp [h])
  have hagE : Agree σs σr (E₁ ++ S) := hag.mono fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · simp [h]
    · simp [h]
  have hagX : Agree σs σr (Xi ++ []) := hag.mono fun l hl => by simp at hl; simp [hl]
  have hIr : Inv F ι σr Γ₁ env E₁ S := ⟨hI.foot.frame hagE, hI.nodup, hI.disj, hI.keys⟩
  have hpsι : ∀ p ∈ ps, p.1.mode = .mut → LT F ⟨[], ι.w⟩ σr p.1.loc p.1.ty p.2 :=
    fun p hp hm => (hnew p hp hm).rfree_iota (hrf p hp)
  have hdXi : Disj Xi (mutCells ps) := fun l h1 h2 => hX l (by simp [h1]) h2
  rcases hin with ⟨v, rfl, hv, hdv⟩ | ⟨a, k, rfl, ha, rfl⟩
  · -- Answered: the fiber entered again.
    have hret : ret F O (m + 1) hs (.enterK τ e g fa ff K Xr ls) (.val v, σr) =
        ret F O m hs (.capV τ e g fa ff (Xr ++ ls.flatMap (cellTree σr) ++ v.tree σr) σr.next)
          (evalK F O m (fiberHS e g ff hs) σr K (.val v)) := by rw [ret.eq_def]
    rw [hret]
    have hinner := hKm (fiberHS e g ff hs) ⟨[], ι.w⟩ σs K ⟨[], [], τ, [], rf⟩ Xi hos Ai σr ps (.val v) op0 Lv hKi
      (fiber_ready hc.hop hR hrow hra)
      (fun a ha => by
        obtain ⟨rfl, rfl⟩ := hAi a ha
        exact ⟨.fail, by simp [fiberHS]⟩) hwf hagX (fun l hl => hXia l (by simpa using hl)) hEn.2.1 hps hpsι hMn
      hdXi (fun _ h => by simp at h)
      (.inl ⟨v, rfl, hv.rfree_iota op0.ret_rfree, fun l h1 h2 => hdv l h1 (by
        rcases List.mem_append.mp h2 with h | h
        · simp [h]
        · simp [h])⟩)
    have hbase := holes_base hIf hholes hpw hEf hSf
    have hrh : ∀ h ∈ hos, h.ty.rfree = true := fun h hh => by
      have : (h.mode, h.ty) ∈ op0.refs := hts ▸ List.mem_map_of_mem hh
      exact op0.refs_rfree _ this
    have hpsh : ∀ p ∈ ps, p.1 ∈ hos := fun p hp => hps ▸ List.mem_map_of_mem hp
    have hcells := reenter_cells (σ := σr) (Lv := Lv) (ps := ps) hXrmem hbase.1 hbase.2 hXM
      (fun h hh hm => by
        have hold : ∀ l ∈ h.old, l ∈ Xi := fun l hl => by
          rcases hbase.1 h hh l hl with h1 | h1
          · exact h1
          · have := hbase.2 h hh l hl h1
            rw [exclPart_ro hm] at this; simp at this
        have hlt := (hholes h hh).old_lt.frame (hagX.mono fun l hl => by simpa using hold l hl)
        exact hlt.cell_tree (Ty.whole_rfree (hholes h hh).whole (hrh h hh)) hwf)
      (fun p hp hm => (hnew p hp hm).cell_tree
        (Ty.whole_rfree (hholes p.1 (hpsh p hp)).whole (hrh p.1 (hpsh p hp))) hwf)
      hps (fun h hh => (hholes h hh).old_head) (fun h hh => (hholes h hh).old_nodup)
      (fun p hp hm => (hnew p hp hm).cons (Ty.whole_not_hole (hholes p.1 (hpsh p hp)).whole))
    rw [← hls] at hcells
    have hd : Disj E₁ (Xi ++ mutCells ps ++ Lv) := fun l h1 h2 => by
      rcases List.mem_append.mp h2 with h2 | h2
      · rcases List.mem_append.mp h2 with h2 | h2
        · exact hEn.2.2 l h1 l h2 rfl
        · exact hX l (by simp [h1]) h2
      · exact hdv l h2 (by simp [h1])
    have hcap := ret_capV_ok (n := m) (B := Xr ++ ls.flatMap (cellTree σr) ++ v.tree σr) (s := σr.next)
      (Ein := Xi ++ mutCells ps ++ Lv) hF hKo' hc hrow hra hR hwf hIr hd
      (fun l h1 h2 => hdS l h1 (by
        simp only [List.mem_append] at h2 ⊢
        rcases h2 with (h2 | h2) | h2
        · exact .inl (.inl (.inr h2))
        · exact .inl (.inr h2)
        · exact .inr h2))
      (fun l hl => by rw [hv.tree_eq hwf] at hl; exact (hcells l).mp hl)
      (fun l hl => .inl (by rw [hv.tree_eq hwf]; exact (hcells l).mpr hl))
      (Nat.le_refl _) (fun l h1 h2 => absurd h2 (Nat.not_lt.mpr h1)) hinner
    exact post_weaken (by simpa [List.append_assoc] using hcap) w
  · -- Dropped: the fiber unwinds, its operations cancelled.
    have hfr : FrameOk F O ⟨[], ι.w⟩ ⟨[], ι.w⟩ σs (.capD τ e g σr.fresh.1) ⟨[], [], τ, [], rf⟩
        ⟨[], [], .int, [], [.fail]⟩ [] [σr.fresh.1] :=
      .capD hc.hop hc.hrefs (Ty.cross_complete hc.hτ) fun l hl => by
        rcases hrow.1 l hl with rfl | ⟨-, hne⟩
        · exact .inl ⟨e, rfl⟩
        · cases l with
          | fail => exact .inr (List.mem_singleton_self _)
          | eff e' => exact .inl ⟨e', rfl⟩
          | drop => exact absurd rfl hne
    have hFr := FramesOk.cons (A := σr.fresh.1 :: Ai) hfr (Weaker.refl _) Agree.self (fun _ h => by simp at h)
      List.nodup_nil disj_nil_left hKi (fun a h => by simp at h; simp [h])
      (fun a ha => .inl (List.mem_cons_of_mem _ ha))
    simp only [List.nil_append] at hFr
    have hwf1 : WF σr.fresh.2 := hwf
    have hag1 : Agree σr σr.fresh.2 (E₁ ++ Xi ++ mutCells ps ++ S) := Agree.of (fun _ _ => rfl) Store.fresh_rt
    have hpost := hKm (hsDie g σr.fresh.1) ⟨[], ι.w⟩ σs (.capD τ e g σr.fresh.1 :: K) ⟨[], [], .int, [], [.fail]⟩
      Xi hos (σr.fresh.1 :: Ai) σr.fresh.2 ps (.abort σr.fresh.1 0) op0 [] hFr
      ⟨.abort (by intro e h; cases h) (.abort (by intro e h; cases h) (.abort (by intro e h; cases h) .nil)),
        fun l hl => by simp at hl; subst hl; exact ⟨_, by simp [hsDie, find, Frame.handles]; rfl⟩⟩
      (fun a h => by
        rcases List.mem_cons.mp h with rfl | h
        · exact ⟨.drop, by simp [hsDie]⟩
        · obtain ⟨rfl, -⟩ := hAi a h; exact ⟨.drop, by simp [hsDie]⟩) hwf1
      (hagX.trans (Agree.of (fun _ _ => rfl) Store.fresh_rt)) (fun l hl => hXia l (by simpa using hl)) hEn.2.1 hps
      (fun p hp hm => (hpsι p hp hm).frame (Agree.of (fun _ _ => rfl) Store.fresh_rt)) hMn hdXi
      (fun _ h => by simp at h) (.inr ⟨σr.fresh.1, 0, rfl, ⟨.drop, by simp [hsDie]⟩, rfl⟩)
    simp only [List.append_nil] at hpost
    have hE1a : ∀ l ∈ E₁ ++ S, σr.fresh.2.mem l ≠ none := fun l hl => by
      show σr.mem l ≠ none
      rw [hagE l hl]; exact hE1S l hl
    have hE1d : Disj (E₁ ++ S) (Xi ++ mutCells ps) := fun l h1 h2 => by
      rcases List.mem_append.mp h1 with h1 | h1 <;> rcases List.mem_append.mp h2 with h2 | h2
      · exact hEn.2.2 l h1 l h2 rfl
      · exact hX l (by simp [h1]) h2
      · exact hdS l h1 (by simp [h2])
      · exact hdS l h1 (by simp [h2])
    have hEa : ∀ l ∈ E₁ ++ Xi ++ mutCells ps, σr.mem l ≠ none := fun l hl => by
      simp only [List.mem_append] at hl
      rcases hl with (h | h) | h
      · rw [hagE l (by simp [h])]; exact hE1S l (by simp [h])
      · rw [hagX l (by simp [h])]; exact hXia l h
      · obtain ⟨p, hp, hlp⟩ := mem_mutCells.mp h
        exact (hnew p hp (Hole.excl_mut hlp).1).alloc l (exclPart_sub hlp)
    -- The fiber unwound: what it owned freed, the code around as it was.
    have hdone : ∀ σ2, Moves σr.fresh.2 (Xi ++ mutCells ps) σ2 [] [] →
        Post F ι O σr (E₁ ++ Xi ++ mutCells ps ++ []) S Γ' env τ r hs (.abort a k, σ2) := fun σ2 hm => by
      have hkeep := hm.keeps hwf1 hE1a hE1d
      have hI2 : Inv F ι σ2 Γ₁ env E₁ S :=
        ⟨hIr.foot.frame ((Agree.of (σ := σr) (σ' := σr.fresh.2) (fun _ _ => rfl) Store.fresh_rt).trans hkeep), hIr.nodup, hIr.disj, hIr.keys⟩
      have m1 : Moves σr (E₁ ++ Xi ++ mutCells ps) σr.fresh.2 (E₁ ++ Xi ++ mutCells ps) [] := Moves.freshen hwf hEa
      have m2 : Moves σr.fresh.2 (E₁ ++ Xi ++ mutCells ps) σ2 E₁ [] :=
        ((hm.widen (X := E₁) (fun l hl => hE1a l (by simp [hl])) (fun l h1 h2 => hE1d l (by simp [h1]) h2)).congr_left
          fun x => by simp [or_assoc]).relabel fun x => by simp
      exact ⟨ha, E₁, hI2.weaken w, by simpa using (m1.trans m2 disj_nil_left hwf)⟩
    rw [ret.eq_def]
    simp only [Store.fresh] at hpost hdone ⊢
    generalize evalK F O m (hsDie g σr.ids) { σr with ids := σr.ids + 1 } (.capD τ e g σr.ids :: K)
      (.abort σr.ids 0) = res at hpost ⊢
    rcases res with ⟨res, σ2⟩
    cases res with
    | val w' =>
      obtain ⟨E', L, hI', hw', -, -, hm⟩ := hpost
      obtain ⟨rfl, -⟩ := hI'.nil_E
      cases hw'
      exact hdone σ2 (by simpa using hm)
    | abort j k' =>
      obtain ⟨-, E', hI', hm⟩ := hpost
      obtain ⟨rfl, -⟩ := hI'.nil_E
      exact hdone σ2 hm
    | susp j ef ws ls' K2 =>
      obtain ⟨-, -, -, -, -, hc', -⟩ := hpost
      rcases hc' with hc' | hc' <;> simp [hsDie] at hc'
    | stuck => simp [Post] at hpost
    | timeout => simp [Post]
    | panic => simp [Post]

/-- A fiber taken through an operation of the code around, answered or dropped: answered, it is
entered again with the answer, owning what its frames do, what the places it lent `mut` now hold, and
the answer; dropped, it unwinds, every operation its cleanup performs cancelled. -/
theorem nest_ok (hF : FnsOk F O) (hKs : ∀ m, m < n → EvalOk F O m ∧ EvalKOk F O m ∧ RetOk F O m) :
    NestOk F O n := by
  intro hs ι σs _ _ _ _ _ _ _ _ top X hos A σr ps r0 op0 Lv _ hK hR haim hwf hag halloc hnd hps hnew hMn
    hX hdS hin
  cases hK with
  | cons hf => cases hf
  | nest h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 =>
    exact nest_core hF hKs h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 hR hwf hag halloc hnd hps hnew hMn hX hdS hin

/-- `k(a)`: the continuation moved out of its variable, its fiber entered again with `a` as what its
operation gave. -/
theorem resumeV_ok [WorldOk F O ι.w] (hF : FnsOk F O) (hKk : EvalKOk F O n)
    (hKo : ∀ m, n = m + 1 → EvalOk F O m ∧ FlushOk F ι (flushR F O m))
    (hx : lookup x Γ = some (.own (.cont A τ ra) true)) (hra : ∀ l ∈ ra, l ∈ r)
    (ha : AtomTy (setSlot Γ x (.own (.cont A τ ra) false)) a A Γ₁)
    (hI : Inv F ι σ Γ env E S) (hwf : WF σ) (hRdy : Ready O hs r) :
    Post F ι O σ E S Γ₁ env τ r hs (evalS F O n hs σ env (.resume x a)) := by
  obtain ⟨v, σ1, E₁, X, hev, hI₁, hv, hdL, hdLS, hm₁⟩ := atom_ok (.move hx (by simp [Ty.complete])) hI hwf
  have hwf₁ := hm₁.wf
  obtain ⟨w, σ2, E₂, Lw, hev2, hI₂, hw, hdw, hdwS, hm₂⟩ := atom_ok ha hI₁ hwf₁
  have hwf₂ := hm₂.wf
  cases hv with
  | @kont _ K _ _ _ hXn hXa hks =>
  obtain ⟨σs, hkok, hagS⟩ := hks
  obtain ⟨τh, e, g, fa, ff, B, s, K', op, ra', rf, A', X', rfl, hτ, hcv, hrow, hA, hK', hperm⟩ :=
    ((WorldOk.ok (F := F) (O := O) (W := ι.w)) σs _ _ X).mp hkok
  injection hτ with h0 h1 h2
  subst h0 h1 h2
  -- The continuation, where it was.
  have hσ : ∃ c, lookup x env = some c ∧ σ.mem c = some (.kont (.capV τ e g fa ff B s :: K') X) ∧
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
  simp only [evalS, hc, hmc, hσ1, hev2, hw.tree_eq hwf₂]
  have hX'X : ∀ l, l ∈ X' ↔ l ∈ X := fun l => hperm.mem_iff.symm
  have hXlt : ∀ l ∈ X, l < σ1.next := fun l hl => hwf₁ l (hXa l hl)
  have hag12 : Agree σ1 σ2 X := hm₂.keeps hwf₁ hXa hdL
  have hXa2 : ∀ l ∈ X, σ2.mem l ≠ none := fun l hl => by rw [hag12 l hl]; exact hXa l hl
  -- What `a` owns is new to the fiber, apart from what it owned.
  have hdXw : Disj X Lw := fun l h1 h2 => by
    rcases hm₂.within l (.inl h2) with h | h
    · exact hdL l h1 h
    · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hXlt l h1) h)
  have hcr := hcv.hret
  simp only [Ty.cross, Bool.and_eq_true] at hcr
  -- The fiber's frames, as the world says, entered again with `a`.
  have hres := hKk (fiberHS e g ff hs) ⟨[], ι.w⟩ σs K' ⟨[], [], τ, [], rf⟩ X' [] A' σ2 [] (.val w) op Lw hK'
    (fiber_ready hcv.hop hRdy hrow hra)
    (fun a ha => by obtain ⟨rfl, rfl⟩ := hA a ha; exact ⟨.fail, by simp [fiberHS]⟩) hwf₂
    ((hagS.trans hag12).mono fun l hl => (hX'X l).mp (by simpa using hl))
    (fun l hl => by
      have hl' := (hX'X l).mp (by simpa using hl)
      rw [← hagS l hl']; exact hXa l hl')
    (hperm.nodup_iff.mp hXn) rfl (fun _ h => by simp at h) (by simp [mutCells]) (by simp [mutCells, Disj])
    (fun _ h => by simp at h)
    (.inl ⟨w, rfl, hw.rfree_iota hcr.1, by
      simp only [mutCells, List.flatMap_nil, List.append_nil]
      exact fun l h1 h2 => hdXw l ((hX'X l).mp h2) h1⟩)
  simp only [mutCells, List.flatMap_nil, List.append_nil] at hres
  have hd2 : Disj E₂ (X' ++ Lw) := fun l h1 h2 => by
    rcases List.mem_append.mp h2 with h2 | h2
    · have h2' := (hX'X l).mp h2
      rcases hm₂.within l (.inr h1) with h | h
      · exact hdL l h2' h
      · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hXlt l h2') h)
    · exact hdw l h2 h1
  have hcap := ret_capV_ok (n := n) (B := X ++ Lw) (s := σ2.next) (Ein := X' ++ Lw) hF hKo hcv hrow hra hRdy hwf₂ hI₂
    hd2
    (fun l h1 h2 => by
      rcases List.mem_append.mp h2 with h2 | h2
      · exact hdLS l ((hX'X l).mp h2) h1
      · exact hdwS l h2 h1)
    (fun l hl => by
      rcases List.mem_append.mp hl with h | h
      · exact List.mem_append.mpr (.inl ((hX'X l).mpr h))
      · exact List.mem_append.mpr (.inr h))
    (fun l hl => by
      rcases List.mem_append.mp hl with h | h
      · exact .inl (List.mem_append.mpr (.inl ((hX'X l).mp h)))
      · exact .inl (List.mem_append.mpr (.inr h)))
    (Nat.le_refl _) (fun l h1 h2 => absurd h2 (Nat.not_lt.mpr h1)) hres
  have m1 : Moves σ E σ1 (E₁ ++ X) [] := hm₁.relabel fun x => by simp [or_comm]
  have m2 : Moves σ1 (E₁ ++ X) σ2 (E₂ ++ (X' ++ Lw)) [] :=
    ((hm₂.widen (X := X) hXa hdL).congr_left fun x => by simp [or_comm]).relabel fun x => by
      simp only [List.mem_append, List.not_mem_nil, or_false, hX'X]
      constructor
      · rintro (h | h | h)
        · exact .inl (.inr h)
        · exact .inl (.inl h)
        · exact .inr h
      · rintro ((h | h) | h)
        · exact .inr (.inl h)
        · exact .inl h
        · exact .inr (.inr h)
  exact post_after (m1.trans m2 disj_nil_left hwf) hwf hcap

/-- `handle { f(owned) } with E { op(x…) resumes k => fa(x…, k) }`: the arguments moved to a fiber of
the `handle`'s own, which calls `f` under its barrier alone. -/
theorem handleV_ok [WorldOk F O ι.w] (hF : FnsOk F O) (hE : EvalOk F O n)
    (hfln : ∀ ι', [WorldOk F O ι'.w] → FlushOk F ι' (flushR F O n))
    (hKo : ∀ m, n = m + 1 → EvalOk F O m ∧ FlushOk F ι (flushR F O m))
    (hop : O[e]? = some op) (htask : op.task = false) (hrefs : op.refs = []) (hret : op.ret.cross = true)
    (howns : ∀ τ' ∈ op.owns, τ'.cross = true) (hτ : τ.cross = true)
    (hfa : F[fa]? = some da) (hdowns : da.owns.map Prod.snd = op.owns ++ [.cont op.ret τ ra]) (hdrefs : da.refs = [])
    (hdret : da.ret = τ) (hdrow : da.row = ra) (hdretp : da.retp = none) (hdcap : da.cap = none)
    (hra : ∀ l ∈ ra, l ∈ r) (hf : F[f]? = some d) (hrefsd : d.refs = []) (hretd : d.ret = τ)
    (hretpd : d.retp = none) (hcapd : d.cap = none) (he : Label.eff e ∈ d.row)
    (hrow : ∀ l ∈ d.row, l = .eff e ∨ (l ∈ ra ∧ l ≠ .drop))
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
  simp only [evalS, hf, hevs]
  rw [if_pos ⟨hlen, hrefsd⟩, hvs.trees hwf₁]
  -- The arguments, moved to the fiber.
  have hvs2 : Vals F ⟨[], ι.w⟩ σ1.fresh.2 (d.owns.map Prod.snd) vs Ls :=
    (hvs.rfree_iota (fun τ' h => by
      have := hcross τ' h; simp only [Ty.cross, Bool.and_eq_true] at this; exact this.1)).frame
      (Agree.of (fun _ _ => rfl) Store.fresh_rt)
  have hwf2 : WF σ1.fresh.2 := hwf₁
  have hLa : ∀ l ∈ Ls.flatten, σ1.mem l ≠ none := hvs.alloc
  have hfr : FiberRow e (decide (Label.fail ∈ d.row)) ra d.row :=
    ⟨hrow, fun h => by
      have := of_decide_eq_true h
      rcases hrow _ this with h' | h'
      · cases h'
      · exact h'.1, fun h => decide_eq_true h⟩
  have hc0 := call_core0 (ι := ⟨[], ι.w⟩) (hs := fiberHS e σ1.fresh.1 (decide (Label.fail ∈ d.row)) hs) (d := d)
    (hos := []) (Γ₁ := []) (env := []) (E₁ := []) (S := []) (σ := σ1.fresh.2) (E := Ls.flatten) (σ1 := σ1.fresh.2)
    (hfln _) hE hk hb (fun _ h => h)
    ⟨.nil, List.nodup_nil, fun _ h => by simp at h, List.nodup_nil⟩ hwf2
    ((Moves.refl hwf2 hLa).relabel fun x => by simp [or_comm]) hvs2 hLn (fun _ _ h => by simp at h)
    (fun _ _ h => by simp at h) (fun _ h => by simp at h) List.Pairwise.nil (by simp [hrefsd])
    (fiber_ready hop hRdy hfr hra)
  simp only [hrefsd, hretd, List.map_nil, List.zip_nil_left, List.append_nil] at hc0
  -- The code around, as the fiber starts.
  have hI2 : Inv F ι σ1.fresh.2 Γ₁ env E₁ S :=
    ⟨hI₁.foot.frame (Agree.of (fun _ _ => rfl) Store.fresh_rt), hI₁.nodup, hI₁.disj, hI₁.keys⟩
  have hcap := ret_capV_ok (n := n) (B := Ls.flatten) (s := σ1.fresh.2.next) (Ein := Ls.flatten) hF hKo hc hfr hra
    hRdy hwf2 hI2 (fun l h1 h2 => hdL l h2 h1) (fun l h1 h2 => hdLS l h2 h1) (fun _ h => h) (fun _ h => .inl h) (Nat.le_refl _) (fun l h1 h2 => absurd h2 (Nat.not_lt.mpr h1)) hc0
  have m1 : Moves σ E σ1 (E₁ ++ Ls.flatten) [] := hm₁.relabel fun x => by simp
  have m2 := Moves.freshen (E := E₁ ++ Ls.flatten) hwf₁ fun l hl => by
    rcases List.mem_append.mp hl with h | h
    · exact hI₁.alloc l h
    · exact hLa l h
  exact post_after (m1.trans m2 disj_nil_left hwf) hwf hcap

end FlyCore.Ownership
