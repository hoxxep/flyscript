import FlyCore.OwnershipFrames

/-!
# Ownership: what a call does

A call evaluates its owned arguments, binds them in fresh cells, lends its places — each a hole in
the tree of the variable it is rooted at — runs the body, and drops the parameters it owns. The
lemmas here follow those steps; `eval_ok` puts them together.
-/

namespace FlyCore.Ownership

/-! ## What a `handle` lends its arm -/

/-- The places a `handle` lent its arm, each holding a value of its type: `R` the cells of those
lent `readonly`, `H` of those lent `mut`. -/
inductive CapsOk (F : List Fn) (ι : Iota) (σ : Store) : List (Cap Nat) → List Nat → List Nat → Prop
  | nil : CapsOk F ι σ [] [] []
  | ro : LT F ι σ a τ L → CapsOk F ι σ rest R H → CapsOk F ι σ (⟨x, .ro, τ, a⟩ :: rest) (L ++ R) H
  | mut : LT F ι σ a τ L → τ.shell = false → CapsOk F ι σ rest R H → CapsOk F ι σ (⟨x, .mut, τ, a⟩ :: rest) R (L ++ H)

/-! ## Variables perhaps moved -/

theorem Slot.Le.excl : Slot.Le s' s → s'.excl = s.excl
  | .refl => rfl
  | .forget _ => rfl

theorem Slot.Le.shell : Slot.Le s' s → s'.shell = s.shell
  | .refl => rfl
  | .forget _ => rfl

theorem SlotOk.weaken : Slot.Le s' s → SlotOk F ι σ s a L → SlotOk F ι σ s' a L
  | .refl, h => h
  | .forget hτ, h => .inr ⟨h, hτ⟩

/-- What an atom gives has no place lent out of it. -/
theorem AtomTy.complete : AtomTy Γ a τ Γ' → τ.complete = true
  | .lit => rfl
  | .read _ => rfl
  | .readRef _ => rfl
  | .move _ hc => hc

theorem Weaker.refl : ∀ Γ : Ctx, Weaker Γ Γ
  | [] => .nil
  | (_, _) :: Γ => .cons .refl (Weaker.refl Γ)

theorem Slot.Le.trans : Slot.Le s₁ s₂ → Slot.Le s₂ s₃ → Slot.Le s₁ s₃
  | .refl, h => h
  | h, .refl => h

theorem Weaker.trans : Weaker Γ₁ Γ₂ → Weaker Γ₂ Γ₃ → Weaker Γ₁ Γ₃
  | .nil, .nil => .nil
  | .cons h₁ w₁, .cons h₂ w₂ => .cons (h₁.trans h₂) (w₁.trans w₂)

theorem Foot.weaken : Foot F ι σ Γ env E S → Weaker Γ' Γ → Foot F ι σ Γ' env E S := by
  intro h
  induction h generalizing Γ' with
  | nil => intro w; cases w; exact .nil
  | @cons s a L Γ env E S x hs _ ih =>
    intro w
    cases w with
    | cons hle w =>
      have := Foot.cons (x := x) (hs.weaken hle) (ih w)
      simp only [addE, addS, exclPart, sharedPart, hle.excl, hle.shell] at this ⊢
      exact this

theorem Inv.weaken (h : Inv F ι σ Γ env E S) (w : Weaker Γ' Γ) : Inv F ι σ Γ' env E S :=
  ⟨h.foot.weaken w, h.nodup, h.disj, w.keys ▸ h.keys⟩

theorem setSlot_weaker : ∀ {Γ : Ctx}, (Γ.map Prod.fst).Nodup → lookup x Γ = some s → Slot.Le s' s →
    Weaker (setSlot Γ x s') Γ
  | [], _, h, _ => by simp [lookup] at h
  | (y, t) :: Γ, hk, hx, hle => by
    simp only [List.map_cons] at hk
    obtain ⟨hy, hk⟩ := List.nodup_cons.mp hk
    by_cases hxy : x = y
    · subst hxy
      simp only [lookup, ↓reduceIte, Option.some.injEq] at hx
      subst hx
      rw [setSlot_head Γ hy]
      exact .cons hle (Weaker.refl Γ)
    · rw [setSlot_tail Γ (Ne.symm hxy)]
      simp only [lookup, hxy, ↓reduceIte] at hx
      exact .cons .refl (setSlot_weaker hk hx hle)

theorem Weaker.cons_inv : Weaker Γb (p :: Γ) → ∃ s' Γb', Γb = (p.1, s') :: Γb' ∧ Slot.Le s' p.2 ∧ Weaker Γb' Γ := by
  intro h
  cases h with
  | cons hle w => exact ⟨_, _, rfl, hle, w⟩

theorem Weaker.nil_inv : Weaker Γb [] → Γb = [] := by
  intro h
  cases h
  rfl

/-- What a `handle`'s body leaves of a context it only read in part, given back: weaker than the
context it started from. -/
theorem thaw_weaker {ys : List Var} : ∀ {Γ Γb : Ctx}, Weaker Γb (freeze Γ ys) → Weaker (thaw Γ ys Γb) Γ := by
  intro Γ
  induction Γ with
  | nil => intro Γb h; rw [Weaker.nil_inv h]; exact .nil
  | cons p Γ ih =>
    intro Γb h
    obtain ⟨y, s⟩ := p
    obtain ⟨s', Γb', rfl, hle, w⟩ := Weaker.cons_inv h
    simp only [thaw, List.zipWith_cons_cons]
    by_cases hy : y ∈ ys
    · simp only [hy, ↓reduceIte]
      exact .cons .refl (ih w)
    · simp only [hy, ↓reduceIte] at hle ⊢
      exact .cons hle (ih w)

/-- What the code a `mut` borrow was in scope for leaves, the borrowed variable given back. -/
theorem thaw_weaker_hide : ∀ {Γ Γb : Ctx}, Weaker Γb (hide Γ y) → Weaker (thaw Γ [y] Γb) Γ := by
  intro Γ
  induction Γ with
  | nil => intro Γb h; rw [Weaker.nil_inv h]; exact .nil
  | cons p Γ ih =>
    intro Γb h
    obtain ⟨z, s⟩ := p
    simp only [hide, List.map_cons] at h
    by_cases hzy : z = y
    · simp only [hzy, ↓reduceIte] at h
      obtain ⟨s', Γb', rfl, hle, w⟩ := Weaker.cons_inv h
      rw [thaw_cons]; simp only [List.mem_singleton, hzy, ↓reduceIte]
      exact .cons .refl (ih w)
    · simp only [hzy, ↓reduceIte] at h
      obtain ⟨s', Γb', rfl, hle, w⟩ := Weaker.cons_inv h
      rw [thaw_cons]; simp only [List.mem_singleton, hzy, ↓reduceIte]
      exact .cons hle (ih w)

theorem thaw_weaker_set : ∀ {Γ Γb : Ctx}, Weaker Γb (setSlot Γ y s0) → Weaker (thaw Γ [y] Γb) Γ := by
  intro Γ
  induction Γ with
  | nil => intro Γb h; rw [Weaker.nil_inv h]; exact .nil
  | cons p Γ ih =>
    intro Γb h
    obtain ⟨z, s⟩ := p
    simp only [setSlot, List.map_cons] at h
    by_cases hzy : z = y
    · simp only [hzy, ↓reduceIte] at h
      obtain ⟨s', Γb', rfl, hle, w⟩ := Weaker.cons_inv h
      rw [thaw_cons]; simp only [List.mem_singleton, hzy, ↓reduceIte]
      exact .cons .refl (ih w)
    · simp only [hzy, ↓reduceIte] at h
      obtain ⟨s', Γb', rfl, hle, w⟩ := Weaker.cons_inv h
      rw [thaw_cons]; simp only [List.mem_singleton, hzy, ↓reduceIte]
      exact .cons hle (ih w)

/-- Giving back what was lent keeps what is weaker weaker. -/
theorem thaw_mono {ys : List Var} : ∀ {Γ Γb Γb' : Ctx}, Weaker Γb' Γb → Weaker (thaw Γ ys Γb') (thaw Γ ys Γb)
  | [], _, _, _ => by simp [thaw]; exact .nil
  | _ :: _, [], _, w => by rw [Weaker.nil_inv w]; simp [thaw]; exact .nil
  | (z, s) :: Γ, q :: Γb, _, w => by
    obtain ⟨s', Γb'', rfl, hle, w'⟩ := Weaker.cons_inv w
    rw [thaw_cons, thaw_cons]
    by_cases hz : z ∈ ys
    · simp only [hz, ↓reduceIte]; exact .cons .refl (thaw_mono w')
    · simp only [hz, ↓reduceIte]; exact .cons hle (thaw_mono w')

theorem thaw_weaker_lend : Weaker Γb (lendCtx m Γ y) → Weaker (thaw Γ [y] Γb) Γ := by
  cases m
  · exact thaw_weaker
  · exact thaw_weaker_hide

/-- What the code the variables `ys` were hidden from leaves, them given back. -/
theorem unhideAll_weaker : ∀ {Γ Γb : Ctx} {ys : List Var}, Weaker Γb (hideAll Γ ys) → Weaker (unhideAll Γ ys Γb) Γ
  | _, _, [], h => h
  | Γ, _, y :: ys, h => thaw_weaker_hide (unhideAll_weaker (Γ := hide Γ y) (ys := ys) h)

theorem Ty.shiftBy_inj : ∀ {A B : Ty}, A.shiftBy n = B.shiftBy n → A = B
  | .int, B, h => by cases B <;> simp_all [Ty.shiftBy]
  | .box A, B, h => by cases B <;> simp_all [Ty.shiftBy]; exact Ty.shiftBy_inj h
  | .fn _ _ _ _ _, B, h => by cases B <;> simp_all [Ty.shiftBy]
  | .pair A₁ A₂, B, h => by
    cases B <;> simp_all [Ty.shiftBy]; exact ⟨Ty.shiftBy_inj h.1, Ty.shiftBy_inj h.2⟩
  | .sum A₁ A₂, B, h => by
    cases B <;> simp_all [Ty.shiftBy]; exact ⟨Ty.shiftBy_inj h.1, Ty.shiftBy_inj h.2⟩
  | .hole A, B, h => by cases B <;> simp_all [Ty.shiftBy]; exact Ty.shiftBy_inj h
  | .rref c k A, B, h => by cases B <;> simp_all [Ty.shiftBy]
  | .arena k, B, h => by cases B <;> simp_all [Ty.shiftBy]
  | .vec _ A, B, h => by cases B <;> simp_all [Ty.shiftBy]; exact Ty.shiftBy_inj h.2
  | .cont _ _ _, B, h => by cases B <;> simp_all [Ty.shiftBy]

theorem Slot.shiftBy_inj {s s' : Slot} (h : s.shiftBy n = s'.shiftBy n) : s = s' := by
  cases s <;> cases s' <;> simp only [Slot.shiftBy, Slot.own.injEq, Slot.ref.injEq, Slot.lent.injEq,
    Slot.half.injEq, reduceCtorEq] at h ⊢
  all_goals first
    | exact ⟨Ty.shiftBy_inj h.1, h.2⟩
    | exact ⟨h.1, Ty.shiftBy_inj h.2⟩
    | exact Ty.shiftBy_inj h
    | exact ⟨h.1, Ty.shiftBy_inj h.2.1, Ty.shiftBy_inj h.2.2⟩

theorem Slot.Le.unshift : Slot.Le (s'.shiftBy n) (s.shiftBy n) → Slot.Le s' s := by
  intro h
  generalize hs' : s'.shiftBy n = t' at h
  generalize hs : s.shiftBy n = t at h
  cases h with
  | refl => subst hs'; exact (Slot.shiftBy_inj hs).symm ▸ .refl
  | forget hτ =>
    cases s' <;> cases s <;> simp_all [Slot.shiftBy]
    obtain ⟨rfl, -⟩ := hs'
    obtain ⟨h1, -⟩ := hs
    obtain rfl := Ty.shiftBy_inj h1
    exact .forget (by cases ‹Ty› <;> simp_all [Ty.isHole, Ty.shiftBy])

theorem Weaker.unshift : ∀ {Γ' Γ : Ctx}, Weaker (Ctx.shift Γ') (Ctx.shift Γ) → Weaker Γ' Γ
  | [], [], _ => .nil
  | (x, s') :: Γ', (y, s) :: Γ, h => by
    cases h with
    | cons hs w => exact .cons (Slot.Le.unshift hs) (Weaker.unshift w)
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h

theorem atom_weaker : AtomTy Γ a τ Γ' → (Γ.map Prod.fst).Nodup → Weaker Γ' Γ
  | .lit, _ => Weaker.refl _
  | .read _, _ => Weaker.refl _
  | .readRef _, _ => Weaker.refl _
  | .move hx hc, hk => setSlot_weaker hk hx (.forget (Ty.complete_not_hole hc))

theorem atoms_weaker : AtomsTy Γ as τs Γ' → (Γ.map Prod.fst).Nodup → Weaker Γ' Γ
  | .nil, _ => Weaker.refl _
  | .cons ha hrest, hk => (atoms_weaker hrest (by rw [atom_keys ha]; exact hk)).trans (atom_weaker ha hk)

/-- Typing only ever moves: what an expression leaves is what it found, some owned variables perhaps
moved. -/
theorem typed_weaker : Typed F O Γ e τ Γ' r → (Γ.map Prod.fst).Nodup → Weaker Γ' Γ
  | .atom ha, hk => atom_weaker ha hk
  | .scope _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb, hk => typed_weaker hb hk
  | .add ha hb, hk => (atom_weaker hb (by rw [atom_keys ha]; exact hk)).trans (atom_weaker ha hk)
  | .new ha, hk => atom_weaker ha hk
  | .pair ha hb, hk => (atom_weaker hb (by rw [atom_keys ha]; exact hk)).trans (atom_weaker ha hk)
  | .inj ha _, hk => atom_weaker ha hk
  | .case hx _ hy h₁ _ w₁ _, hk => by
    have := typed_weaker h₁ (List.nodup_cons.mpr ⟨by rw [setSlot_keys]; exact lookup_none_keys hy,
      by rw [setSlot_keys]; exact hk⟩)
    cases this with
    | cons _ w => exact w₁.trans (w.trans (setSlot_weaker hk hx (.forget rfl)))
  | .caseRef hx _ _ _ _ h₁ _ w₁ _, hk => by
    have := typed_weaker h₁ (List.nodup_cons.mpr ⟨by rw [lendCtx_keys]; exact lookup_none_keys hx,
      by rw [lendCtx_keys]; exact hk⟩)
    cases this with
    | cons _ w => exact thaw_weaker_lend (w₁.trans w)
  | .let_ hx ha hb, hk => by
    have := typed_weaker hb (List.nodup_cons.mpr ⟨by rw [typed_keys ha]; exact lookup_none_keys hx,
      by rw [typed_keys ha]; exact hk⟩)
    cases this with
    | cons _ w => exact w.trans (typed_weaker ha hk)
  | .write ha _, hk => atom_weaker ha hk
  | .assign ha _ _, hk => atom_weaker ha hk
  | .rlnew _ _ _, _ => Weaker.refl _
  | .rpush _ _ _ _ _, _ => Weaker.refl _
  | .rnth _ _ _ _ _, _ => Weaker.refl _
  | .rlen _ _ _, _ => Weaker.refl _
  | .vnew _, _ => Weaker.refl _
  | .vlen _, _ => Weaker.refl _
  | .vpush ha _, hk => atom_weaker ha hk
  | .vpop _ _, _ => Weaker.refl _
  | .lendSlice hx _ _ _ _ hb, hk => by
    have := typed_weaker hb (List.nodup_cons.mpr ⟨by rw [lendCtx_keys]; exact lookup_none_keys hx,
      by rw [lendCtx_keys]; exact hk⟩)
    cases this with
    | cons _ w => exact thaw_weaker_lend w
  | .call _ _ _ _ hargs _ _, hk => atoms_weaker hargs hk
  | .lam _ _ _ _ _ ha _, hk => atom_weaker ha hk
  | .lendClo _ _ _ _ _ _ _ hx hb, hk => by
    have := typed_weaker hb (List.nodup_cons.mpr ⟨by rw [freeze_keys]; exact lookup_none_keys hx,
      by rw [freeze_keys]; exact hk⟩)
    cases this with
    | cons _ w => exact thaw_weaker w
  | .lendField hx _ _ _ _ _ hb, hk => by
    have := typed_weaker hb (List.nodup_cons.mpr ⟨by rw [setSlot_keys]; exact lookup_none_keys hx,
      by rw [setSlot_keys]; exact hk⟩)
    cases this with
    | cons _ w => exact thaw_weaker_set w
  | .gen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hargs _ _ hb _, hk => by
    have hk₁ := (atoms_keys hargs).symm ▸ hk
    exact (unhideAll_weaker (thaw_weaker (typed_weaker hb (by rw [freeze_keys, hideAll_keys]; exact hk₁)))).trans
      (atoms_weaker hargs hk)
  | .lendCloMut _ _ _ _ _ _ _ _ hx hb, hk => by
    have := typed_weaker hb (List.nodup_cons.mpr ⟨by rw [hide_keys]; exact lookup_none_keys hx,
      by rw [hide_keys]; exact hk⟩)
    cases this with
    | cons _ w => exact thaw_weaker_hide w
  | .applyOnce hx _ ha, hk =>
    (atom_weaker ha (by rw [setSlot_keys]; exact hk)).trans (setSlot_weaker hk hx (.forget rfl))
  | .applyBorrow _ ha _ _ _, hk => atom_weaker ha hk
  | .lendCall (m := m) _ _ _ _ hargs _ _ _ _ hx hb, hk => by
    have hk₁ := hk
    rw [← atoms_keys hargs] at hk₁
    have := typed_weaker hb (List.nodup_cons.mpr ⟨by rw [lendCtxs_keys]; exact lookup_none_keys hx,
      by rw [lendCtxs_keys]; exact hk₁⟩)
    cases this with
    | cons _ w =>
      refine Weaker.trans ?_ (atoms_weaker hargs hk)
      cases m
      · exact thaw_weaker w
      · exact unhideAll_weaker w
  | .ite hc ha _ wa _, hk =>
    wa.trans ((typed_weaker ha (by rw [atom_keys hc]; exact hk)).trans (atom_weaker hc hk))
  | .throw_ ha _, hk => atom_weaker ha hk
  | .try_ hx hb hh, hk => by
    have := typed_weaker hh (List.nodup_cons.mpr ⟨by exact lookup_none_keys hx,
      by rw [typed_keys hb]; exact hk⟩)
    cases this with
    | cons _ w => exact w.trans (typed_weaker hb hk)
  | .while_ _ _, _ => Weaker.refl _
  | .defer hb _, hk => typed_weaker hb hk
  | .lend hx _ _ _ _ hb, hk => by
    have := typed_weaker hb (List.nodup_cons.mpr ⟨by rw [lendCtx_keys]; exact lookup_none_keys hx,
      by rw [lendCtx_keys]; exact hk⟩)
    cases this with
    | cons _ w => exact thaw_weaker_lend w
  | .lendIdx hx _ _ _ _ _ hb, hk => by
    have := typed_weaker hb (List.nodup_cons.mpr ⟨by rw [lendCtx_keys]; exact lookup_none_keys hx,
      by rw [lendCtx_keys]; exact hk⟩)
    cases this with
    | cons _ w => exact thaw_weaker_lend w
  | .perform _ _ hargs _ _, hk => atoms_weaker hargs hk
  | .handle _ _ _ _ _ _ _ _ _ hb, hk =>
    unhideAll_weaker (thaw_weaker (typed_weaker hb (by rw [freeze_keys, hideAll_keys]; exact hk)))
  | .handleR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb, hk =>
    unhideAll_weaker (thaw_weaker (typed_weaker hb (by rw [freeze_keys, hideAll_keys]; exact hk)))
  | .handleAbort _ _ _ hx hb hh, hk => by
    have := typed_weaker hh (List.nodup_cons.mpr ⟨by exact lookup_none_keys hx,
      by rw [typed_keys hb]; exact hk⟩)
    cases this with
    | cons _ w => exact w.trans (typed_weaker hb hk)
  | .par _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hargs _, hk => atoms_weaker hargs hk
  | .handleV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hargs, hk => atoms_weaker hargs hk
  | .resume hx _ ha, hk => (atom_weaker ha (by rw [setSlot_keys]; exact hk)).trans
      (setSlot_weaker hk hx (.forget rfl))
  | .region hR _ hb, hk => by
    have w := typed_weaker hb (List.nodup_cons.mpr ⟨by
      simpa [Ctx.shift, Function.comp_def] using lookup_none_keys hR, by simpa [Ctx.shift, Function.comp_def] using hk⟩)
    cases w with
    | cons _ w => exact Weaker.unshift w
  | .ralloc _ _ _ _, _ => Weaker.refl _
  | .rget _ _ _ _, _ => Weaker.refl _
  | .rset _ _ _ _ _, _ => Weaker.refl _

/-- A function's context: its owned parameters, live, then its borrowed ones. -/
def fnCtx (d : Fn) : Ctx :=
  d.owns.map (fun p => (p.1, Slot.own p.2 true)) ++ d.refs.map (fun p => (p.1, Slot.ref p.2.1 p.2.2))

/-- A function whose parameters are named apart and whose body has its result type, performing
only what its row names; or, for one that returns a borrow, whose body ends where the place it
returns is one of its result type, rooted at the borrowed parameter it says, and changeable if the
borrow is `mut`. -/
def FnOk (F : List Fn) (O : List Op) (d : Fn) : Prop :=
  ((d.owns.map Prod.fst) ++ (d.refs.map Prod.fst)).Nodup ∧
  match d.cap, d.retp with
  | none, none => ∃ Γ', Typed F O (fnCtx d) d.body d.ret Γ' d.row
  | none, some (m, cs) => cs ≠ [] ∧ ∃ Γ', Typed F O (fnCtx d) d.body .int Γ' d.row ∧
      ∀ c ∈ cs, ∃ x mi τi w, d.refs[c.1]? = some (x, mi, τi) ∧ PlaceTy Γ' c.2 d.ret w x ∧ (m = .mut → w = true)
  | some (xc, τc, k), none => xc ∉ d.owns.map Prod.fst ++ d.refs.map Prod.fst ∧
      ∃ Γ', Typed F O (fnCtx (cloFn d xc τc k)) d.body d.ret Γ' d.row
  | some _, some _ => False

def FnsOk (F : List Fn) (O : List Op) : Prop := ∀ d ∈ F, FnOk F O d

/-! ## Steps that keep what they do not own -/

/-- Cells that were allocated and outside the footprint are as they were. -/
theorem Moves.keeps (h : Moves σ E σ' E' L) (hwf : WF σ) (hX : ∀ l ∈ X, σ.mem l ≠ none)
    (hd : Disj X E) : Agree σ σ' X :=
  ⟨fun l hl => h.frame l (hwf l (hX l hl)) (hd l hl), h.rt, fun a ha l x hx => by
    cases h0 : σ.rt l with
    | none =>
      rcases h.fresh l a x hx h0 with h' | h'
      · exact absurd h' (hd a ha)
      · exact absurd (Nat.lt_of_lt_of_le (hwf a (hX a ha)) h') (Nat.lt_irrefl _)
    | some y =>
      have := h.rt l y h0
      rw [hx] at this
      cases this
      rfl⟩

/-- What a step gives or leaves in its footprint is apart from cells it could not reach. -/
theorem Moves.apart (h : Moves σ E σ' E' L) (hwf : WF σ) (hX : ∀ l ∈ X, σ.mem l ≠ none)
    (hd : Disj X E) : Disj X E' ∧ Disj X L := by
  refine ⟨fun l hl hl' => ?_, fun l hl hl' => ?_⟩ <;>
  · rcases h.within l (by first | exact .inr hl' | exact .inl hl') with h' | h'
    · exact hd l hl h'
    · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hwf l (hX l hl)) h')

/-- A step widened by cells it leaves alone. -/
theorem Moves.widen (h : Moves σ E σ' E' L) (hX : ∀ l ∈ X, σ.mem l ≠ none) (hd : Disj X E) :
    Moves σ (X ++ E) σ' (X ++ E') L where
  rt := h.rt
  fresh := fun l a x h1 h2 => (h.fresh l a x h1 h2).imp_left fun h => List.mem_append.mpr (.inr h)
  within := by
    intro l hl
    rcases hl with hl | hl
    · rcases h.within l (.inl hl) with h' | h'
      · exact .inl (List.mem_append.mpr (.inr h'))
      · exact .inr h'
    · rcases List.mem_append.mp hl with hl | hl
      · exact .inl (List.mem_append.mpr (.inl hl))
      · rcases h.within l (.inr hl) with h' | h'
        · exact .inl (List.mem_append.mpr (.inr h'))
        · exact .inr h'
  next := h.next
  wf := h.wf
  frame := fun l hl hn => h.frame l hl (fun h' => hn (List.mem_append.mpr (.inr h')))
  alloc := by
    intro l
    rw [h.alloc]
    simp only [List.mem_append, not_or]
    constructor
    · rintro (⟨ha, hE⟩ | h' | h')
      · by_cases hlX : l ∈ X
        · exact .inr (.inl (.inl hlX))
        · exact .inl ⟨ha, hlX, hE⟩
      · exact .inr (.inl (.inr h'))
      · exact .inr (.inr h')
    · rintro (⟨ha, -, hE⟩ | (h' | h') | h')
      · exact .inl ⟨ha, hE⟩
      · exact .inl ⟨hX l h', hd l h'⟩
      · exact .inr (.inl h')
      · exact .inr (.inr h')

/-- A step that only allocates: everything below `σ.next` is as it was, and the new cells join the
footprint. -/
theorem Moves.grow (hwf : WF σ) (hwf' : WF σ') (hn : σ.next ≤ σ'.next)
    (hold : ∀ l, l < σ.next → σ'.mem l = σ.mem l) (hnew : ∀ l, σ.next ≤ l → l < σ'.next → σ'.mem l ≠ none)
    (hE : ∀ l ∈ E, σ.mem l ≠ none) (hE' : ∀ l, l ∈ E' ↔ l ∈ E ∨ (σ.next ≤ l ∧ l < σ'.next))
    (hrt : σ'.rt = σ.rt := by rt_tac) :
    Moves σ E σ' E' [] where
  rt := fun l x h => by rw [hrt]; exact h
  fresh := fun _ _ _ h h0 => by rw [hrt, h0] at h; cases h
  within := by
    intro l hl
    rcases hl with hl | hl
    · simp at hl
    · rcases (hE' l).mp hl with h | h
      · exact .inl h
      · exact .inr h.1
  next := hn
  wf := hwf'
  frame := fun l hl _ => hold l hl
  alloc := by
    intro l
    rw [hE']
    simp only [List.not_mem_nil, or_false]
    by_cases hl : l < σ.next
    · rw [hold l hl]
      constructor
      · intro ha
        by_cases hlE : l ∈ E
        · exact .inr (.inl hlE)
        · exact .inl ⟨ha, hlE⟩
      · rintro (⟨ha, -⟩ | hlE | ⟨h, -⟩)
        · exact ha
        · exact hE l hlE
        · exact absurd hl (Nat.not_lt.mpr h)
    · have hnone : σ.mem l = none := by
        by_cases h : σ.mem l = none
        · exact h
        · exact absurd (hwf l h) hl
      have hnE : l ∉ E := fun h => hE l h hnone
      constructor
      · intro ha
        exact .inr (.inr ⟨Nat.not_lt.mp hl, hwf' l ha⟩)
      · rintro (⟨ha, -⟩ | hlE | ⟨h1, h2⟩)
        · exact absurd hnone ha
        · exact absurd hlE hnE
        · exact hnew l h1 h2

/-- What a step accounts for depends on the cells it may change, not on their order. -/
theorem Moves.congr_left (h : Moves σ E σ' E' L) (hE : ∀ x, x ∈ E ↔ x ∈ E₀) : Moves σ E₀ σ' E' L where
  rt := h.rt
  fresh := fun l a x h1 h2 => (h.fresh l a x h1 h2).imp_left (hE a).mp
  within := fun l hl => (h.within l hl).imp_left (hE l).mp
  next := h.next
  wf := h.wf
  frame := fun l hl hn => h.frame l hl fun h' => hn ((hE l).mp h')
  alloc := fun l => by rw [h.alloc l, hE l]

theorem CapsOk.frame : CapsOk F ι σ caps R H → Agree σ σ' (R ++ H) → CapsOk F ι σ' caps R H
  | .nil, _ => .nil
  | .ro hL hr, hag => .ro (hL.frame (hag.mono fun l hl => by simp [hl]))
      (hr.frame (hag.mono fun l hl => by rcases List.mem_append.mp hl with h | h <;> simp [h]))
  | .mut hL hfn hr, hag => .mut (hL.frame (hag.mono fun l hl => by simp [hl])) hfn
      (hr.frame (hag.mono fun l hl => by rcases List.mem_append.mp hl with h | h <;> simp [h]))

theorem CapsOk.alloc : CapsOk F ι σ caps R H → ∀ l ∈ R ++ H, σ.mem l ≠ none
  | .nil, _, h => by simp at h
  | .ro hL hr, l, h => by
    simp only [List.mem_append, or_assoc] at h
    rcases h with h | h
    · exact hL.alloc l h
    · exact hr.alloc l (List.mem_append.mpr h)
  | .mut hL _ hr, l, h => by
    simp only [List.mem_append] at h
    rcases h with h | h | h
    · exact hr.alloc l (List.mem_append.mpr (.inl h))
    · exact hL.alloc l h
    · exact hr.alloc l (List.mem_append.mpr (.inr h))

/-- What a frame's arm only reads is as it was, wherever the store agrees on it. -/
theorem CapsOk.mono : CapsOk F ι σ caps R H → ι.w.le W → CapsOk F (ι.inW W) σ caps R H
  | .nil, _ => .nil
  | .ro hL hr, hW => .ro (hL.mono hW) (hr.mono hW)
  | .mut hL hsh hr, hW => .mut (hL.mono hW) hsh (hr.mono hW)

theorem CapsOk.det_ro : CapsOk F ι σ caps R H → CapsOk F ι σ' caps R' H' → Agree σ σ' R → R' = R
  | .nil, .nil, _ => rfl
  | .ro hL hr, .ro hL' hr', hag => by
    obtain rfl := (hL.frame (hag.mono fun l hl => by simp [hl])).det hL'
    rw [hr.det_ro hr' (hag.mono fun l hl => by simp [hl])]
  | .mut _ _ hr, .mut _ _ hr', hag => hr.det_ro hr' hag

/-! ## Owned arguments -/

/-- Values of the given types, each owning its cells. -/
inductive Vals (F : List Fn) (ι : Iota) (σ : Store) : List Ty → List Val → List (List Nat) → Prop
  | nil : Vals F ι σ [] [] []
  | cons : VT F ι σ τ v L → Vals F ι σ τs vs Ls → Vals F ι σ (τ :: τs) (v :: vs) (L :: Ls)

theorem Vals.frame : Vals F ι σ τs vs Ls → Agree σ σ' Ls.flatten → Vals F ι σ' τs vs Ls := by
  intro h hag
  induction h with
  | nil => exact .nil
  | cons hv _ ih =>
    simp only [List.flatten_cons] at hag
    exact .cons (hv.frame (hag.mono fun l hl => List.mem_append.mpr (.inl hl)))
      (ih (hag.mono fun l hl => List.mem_append.mpr (.inr hl)))

theorem Vals.alloc : Vals F ι σ τs vs Ls → ∀ l ∈ Ls.flatten, σ.mem l ≠ none := by
  intro h
  induction h with
  | nil => simp
  | cons hv _ ih =>
    intro l hl
    rcases List.mem_append.mp (List.flatten_cons ▸ hl) with hl | hl
    · exact hv.alloc l hl
    · exact ih l hl

theorem Vals.complete : Vals F ι σ τs vs Ls → ∀ τ ∈ τs, τ.complete = true := by
  intro h
  induction h with
  | nil => simp
  | cons hv _ ih =>
    intro τ hτ
    rcases List.mem_cons.mp hτ with rfl | hτ
    · exact hv.complete
    · exact ih τ hτ

theorem Vals.owns_complete {owns : List (Var × Ty)} (h : Vals F ι σ (owns.map Prod.snd) vs Ls) :
    ∀ o ∈ owns, o.2.complete = true :=
  fun o ho => h.complete o.2 (List.mem_map_of_mem ho)

theorem Vals.length : Vals F ι σ τs vs Ls → vs.length = τs.length := by
  intro h
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-! ## Binding the owned parameters -/

def ownCtx (ps : List (Var × Ty)) : Ctx := ps.map fun p => (p.1, Slot.own p.2 true)

/-- Each owned argument in a fresh cell: the cells, and what the values owned, are the footprint of
the callee's owned parameters. -/
theorem allocAll_ok : ∀ {σ : Store} {names : List Var} {τs vs Ls}, Vals F ι σ τs vs Ls →
    names.length = τs.length → WF σ → Ls.flatten.Nodup →
    ∃ Eo, Foot F ι (allocAll σ (names.zip vs)).2 (ownCtx (names.zip τs)) (allocAll σ (names.zip vs)).1 Eo [] ∧
      Eo.Nodup ∧ (∀ l, l ∈ Eo ↔ l ∈ Ls.flatten ∨ (σ.next ≤ l ∧ l < (allocAll σ (names.zip vs)).2.next)) ∧
      σ.next ≤ (allocAll σ (names.zip vs)).2.next ∧ WF (allocAll σ (names.zip vs)).2 ∧
      (∀ l, l < σ.next → (allocAll σ (names.zip vs)).2.mem l = σ.mem l) ∧
      (∀ l, σ.next ≤ l → l < (allocAll σ (names.zip vs)).2.next → (allocAll σ (names.zip vs)).2.mem l ≠ none) ∧
      (allocAll σ (names.zip vs)).1.length = names.length
  | σ, [], _, _, _, h, hl, hwf, _ => by
    cases h with
    | nil =>
      refine ⟨[], .nil, List.nodup_nil, ?_, Nat.le_refl _, hwf, fun _ _ => rfl, ?_, rfl⟩
      · intro l; simp only [List.zip_nil_left, allocAll, List.flatten_nil, List.not_mem_nil, false_or, false_iff]; omega
      · intro l h1 h2; simp only [List.zip_nil_left, allocAll] at h2; omega
    | cons => simp at hl
  | σ, x :: names, _, _, _, h, hl, hwf, hn => by
    cases h with
    | nil => simp at hl
    | @cons τ v L τs vs Ls hv hvs =>
      simp only [List.flatten_cons] at hn
      obtain ⟨hnL, hnLs, hdL⟩ := nodup_append_disj.mp hn
      have hag : Agree σ (σ.alloc v).2 (L ++ Ls.flatten) := agree_alloc hwf (by
        intro l hl
        rcases List.mem_append.mp hl with hl | hl
        · exact hv.alloc l hl
        · exact hvs.alloc l hl)
      have hlow : ∀ l ∈ L ++ Ls.flatten, l < σ.next := by
        intro l hl
        rcases List.mem_append.mp hl with hl | hl
        · exact hwf l (hv.alloc l hl)
        · exact hwf l (hvs.alloc l hl)
      obtain ⟨Eo, hf, hnd, hmem, hle, hwf2, hold, hnew, hlen⟩ :=
        allocAll_ok (σ := (σ.alloc v).2) (names := names)
          (hvs.frame (hag.mono fun l hl => List.mem_append.mpr (.inr hl))) (by simpa using hl) hwf.alloc hnLs
      simp only [List.zip_cons_cons, allocAll]
      have hn1 : (σ.alloc v).2.next = σ.next + 1 := rfl
      have hc : (σ.alloc v).1 = σ.next := rfl
      rw [hc]
      have hrt := allocAll_rt (σ.alloc v).2 (names.zip vs)
      generalize hr : allocAll (σ.alloc v).2 (names.zip vs) = r at hf hmem hle hwf2 hold hnew hlen hrt
      obtain ⟨cells, σ2⟩ := r
      dsimp only at hf hmem hle hwf2 hold hnew hlen hrt ⊢
      have hcL : σ.next ∉ L := fun h => Nat.lt_irrefl _ (hlow _ (List.mem_append.mpr (.inl h)))
      have hLt : LT F ι σ2 σ.next τ (σ.next :: L) := by
        refine (LT.of_contents (by simp [Store.alloc]) (hv.frame (hag.mono fun l hl => List.mem_append.mpr (.inl hl))) hcL).frame (Agree.of (fun l hl => hold l ?_) hrt)
        rcases List.mem_cons.mp hl with rfl | hl
        · rw [hn1]; omega
        · have := hlow l (List.mem_append.mpr (.inl hl)); rw [hn1]; omega
      have hlowE : ∀ l ∈ Eo, l ≠ σ.next ∧ l ∉ L := by
        intro l hl
        rcases (hmem l).mp hl with h | ⟨h, -⟩
        · have := hlow l (List.mem_append.mpr (.inr h))
          exact ⟨by omega, fun h' => hdL l h' h⟩
        · rw [hn1] at h
          exact ⟨by omega, fun h' => by have := hlow l (List.mem_append.mpr (.inl h')); omega⟩
      refine ⟨(σ.next :: L) ++ Eo, ?_, ?_, ?_, by rw [hn1] at hle; omega, hwf2, ?_, ?_, by simp [hlen]⟩
      · have := Foot.cons (x := x) (s := .own τ true) hLt hf
        simpa [ownCtx, addE, addS, Slot.excl, exclPart, sharedPart, Slot.shell, Ty.shell, Bool.false_eq_true] using this
      · refine nodup_append_disj.mpr ⟨List.nodup_cons.mpr ⟨hcL, hnL⟩, hnd, ?_⟩
        intro l hl hl'
        rcases List.mem_cons.mp hl with rfl | hl
        · exact (hlowE _ hl').1 rfl
        · exact (hlowE _ hl').2 hl
      · intro l
        simp only [List.mem_append, List.mem_cons, hmem, List.flatten_cons]
        rw [hn1]
        constructor
        · rintro ((rfl | h) | h | ⟨h1, h2⟩)
          · exact .inr ⟨Nat.le_refl _, by omega⟩
          · exact .inl (.inl h)
          · exact .inl (.inr h)
          · exact .inr ⟨by omega, h2⟩
        · rintro ((h | h) | ⟨h1, h2⟩)
          · exact .inl (.inr h)
          · exact .inr (.inl h)
          · by_cases he : l = σ.next
            · exact .inl (.inl he)
            · exact .inr (.inr ⟨by omega, h2⟩)
      · intro l hl
        rw [hold l (by rw [hn1]; omega)]
        simp [Store.alloc, Nat.ne_of_lt hl]
      · intro l h1 h2
        by_cases he : l = σ.next
        · subst he; rw [hold _ (by rw [hn1]; omega)]; simp [Store.alloc]
        · exact hnew l (by rw [hn1]; omega) h2

/-! ## The callee's variables when it ends -/

/-- A slot with its liveness forgotten: what typing a body cannot change. -/
def Slot.shape : Slot → Slot
  | .own τ _ => .own τ true
  | .ref m τ => .ref m τ
  | .lent τ h => .lent τ h
  | .half t A B => .half t A B

def shape (Γ : Ctx) : Ctx := Γ.map fun p => (p.1, p.2.shape)

theorem Slot.Le.shape : Slot.Le s' s → s'.shape = s.shape
  | .refl => rfl
  | .forget _ => rfl

theorem Weaker.shape : Weaker Γ' Γ → shape Γ' = shape Γ
  | .nil => rfl
  | .cons hle w => by
    show (_, _) :: FlyCore.Ownership.shape _ = (_, _) :: FlyCore.Ownership.shape _
    rw [hle.shape, w.shape]

theorem typed_shape (h : Typed F O Γ e τ Γ' r) (hk : (Γ.map Prod.fst).Nodup) : shape Γ' = shape Γ :=
  (typed_weaker h hk).shape

/-- Where the shape ends in borrows, so does the context: borrows are their own shape. -/
theorem shape_split : ∀ (A : Ctx) {Γ : Ctx}, shape Γ = A ++ B → (∀ p ∈ B, ∃ m τ, p.2 = .ref m τ) →
    ∃ Γa, Γ = Γa ++ B ∧ shape Γa = A
  | [], Γ, h, hB => by
    refine ⟨[], ?_, rfl⟩
    simp only [List.nil_append] at h ⊢
    subst h
    induction Γ with
    | nil => rfl
    | cons p Γ ih =>
      obtain ⟨x, s⟩ := p
      simp only [shape, List.map_cons, List.mem_cons, forall_eq_or_imp] at hB ih ⊢
      obtain ⟨⟨m, τ, hs⟩, hB⟩ := hB
      cases s with
      | own => simp [Slot.shape] at hs
      | ref => simp only [Slot.shape]; exact congrArg _ (ih hB)
      | lent => simp [Slot.shape] at hs
      | half => simp [Slot.shape] at hs
  | a :: A, [], h, _ => by simp [shape] at h
  | a :: A, g :: Γ, h, hB => by
    simp only [shape, List.map_cons, List.cons_append, List.cons.injEq] at h
    obtain ⟨Γa, rfl, hΓa⟩ := shape_split A h.2 hB
    exact ⟨g :: Γa, rfl, by simp only [shape, List.map_cons] at hΓa ⊢; rw [hΓa, h.1]⟩

/-! ## Dropping the owned parameters -/

theorem cellKonts_ok (hτ : τ.complete = true) (h : SlotOk F ι σ (.own τ live) c L) :
    KontsOk F ι σ (cellKonts σ τ c) ∧ ∀ l ∈ (cellKonts σ τ c).flatMap Val.foot, l ∈ L := by
  have live_case : ∀ {L}, LT F ι σ c τ L →
      KontsOk F ι σ (cellKonts σ τ c) ∧ ∀ l ∈ (cellKonts σ τ c).flatMap Val.foot, l ∈ L := fun h => by
    obtain ⟨w, R', hw, hv, rfl, -⟩ := h.contents hτ
    rw [cellKonts_live hw hv]
    obtain ⟨h1, h2⟩ := konts_ok hv
    exact ⟨h1, fun l hl => List.mem_cons_of_mem _ (h2 l hl)⟩
  cases live with
  | true => exact live_case h
  | false =>
    rcases h with ⟨hc, -⟩ | ⟨h, -⟩
    · simp [cellKonts, hc, KontsOk.nil]
    · exact live_case h

theorem cellKonts_frame (hτ : τ.complete = true) (h : SlotOk F ι σ (.own τ live) c L)
    (hag : ∀ l ∈ L, σ'.mem l = σ.mem l) (hn : σ'.next = σ.next) : cellKonts σ' τ c = cellKonts σ τ c := by
  have live_case : ∀ {L}, LT F ι σ c τ L → (∀ l ∈ L, σ'.mem l = σ.mem l) → cellKonts σ' τ c = cellKonts σ τ c :=
    fun h hag => by
      obtain ⟨w, R', hw, hv, rfl, -⟩ := h.contents hτ
      have hw' := (hag c (List.mem_cons_self ..)).trans hw
      rw [cellKonts_live hw hv, cellKonts_of hw' hv.not_moved]
      simp only [konts, hn]
      exact kontsK_frame _ _ _ _ _ hv _ fun l hl => hag l (List.mem_cons_of_mem _ hl)
  cases live with
  | true => exact live_case h hag
  | false =>
    rcases h with ⟨hc, rfl⟩ | ⟨h, -⟩
    · have hc' := (hag c (List.mem_singleton_self _)).trans hc
      simp [cellKonts, hc, hc']
    · exact live_case h hag

theorem cellsKonts_frame : ∀ {Γo : Ctx} {σ : Store} {eo : Env} {Eo So} {owns : List (Var × Ty)},
    Foot F ι σ Γo eo Eo So → shape Γo = ownCtx owns → (∀ o ∈ owns, o.2.complete = true) →
    (∀ l ∈ Eo, σ'.mem l = σ.mem l) → σ'.next = σ.next →
    cellsKonts σ' ((owns.map Prod.snd).zip (eo.map Prod.snd)) = cellsKonts σ ((owns.map Prod.snd).zip (eo.map Prod.snd))
  | [], σ, _, _, _, owns, h, hs, _, _, _ => by
    cases h
    cases owns with
    | nil => rfl
    | cons => simp [shape, ownCtx] at hs
  | (z, r) :: Γo, σ, _, _, _, owns, h, hs, hc, hag, hn => by
    cases h with
    | @cons _ c M _ eo E S _ hr hrest =>
    cases owns with
    | nil => simp [shape, ownCtx] at hs
    | cons o owns =>
    simp only [shape, ownCtx, List.map_cons, List.cons.injEq, Prod.mk.injEq] at hs
    obtain ⟨⟨-, hrs⟩, hs⟩ := hs
    cases r with
    | ref => simp [Slot.shape] at hrs
    | lent => simp [Slot.shape] at hrs
    | half => simp [Slot.shape] at hrs
    | own τ live =>
    simp only [Slot.shape, Slot.own.injEq] at hrs
    obtain ⟨rfl, -⟩ := hrs
    simp only [addE, Slot.excl, ↓reduceIte, exclPart, Slot.shell, Ty.shell, Bool.false_eq_true] at hag
    simp only [List.map_cons, List.zip_cons_cons, cellsKonts]
    rw [cellKonts_frame (hc _ (List.mem_cons_self ..)) hr (fun l hl => hag l (List.mem_append.mpr (.inl hl))) hn,
      cellsKonts_frame hrest hs (fun o ho => hc o (List.mem_cons_of_mem _ ho))
        (fun l hl => hag l (List.mem_append.mpr (.inr hl))) hn]

/-- Dropping the callee's owned parameters, live or moved, frees their footprints but what the
continuations they hold own. -/
theorem dropCells_ok : ∀ {Γo : Ctx} {σ : Store} {eo : Env} {Eo So} {owns : List (Var × Ty)},
    Foot F ι σ Γo eo Eo So → shape Γo = ownCtx owns → Eo.Nodup → WF σ → (∀ o ∈ owns, o.2.complete = true) →
    So = [] ∧ ∃ σ', dropCells σ ((owns.map Prod.snd).zip (eo.map Prod.snd)) = some σ' ∧
      σ'.next = σ.next ∧
      (∀ l ∈ Eo, l ∉ (cellsKonts σ ((owns.map Prod.snd).zip (eo.map Prod.snd))).flatMap Val.foot → σ'.mem l = none) ∧
      (∀ l, l ∉ Eo ∨ l ∈ (cellsKonts σ ((owns.map Prod.snd).zip (eo.map Prod.snd))).flatMap Val.foot →
        σ'.mem l = σ.mem l) ∧ σ'.rt = σ.rt ∧
      KontsOk F ι σ (cellsKonts σ ((owns.map Prod.snd).zip (eo.map Prod.snd))) ∧
      ∀ l ∈ (cellsKonts σ ((owns.map Prod.snd).zip (eo.map Prod.snd))).flatMap Val.foot, l ∈ Eo
  | [], σ, _, _, _, owns, h, hs, _, _, _ => by
    cases h
    cases owns with
    | nil => exact ⟨rfl, σ, by simp [dropCells], rfl, by simp, fun _ _ => rfl, rfl, by simp [cellsKonts, KontsOk.nil],
        by simp [cellsKonts]⟩
    | cons => simp [shape, ownCtx] at hs
  | (z, r) :: Γo, σ, _, _, _, owns, h, hs, hn, hwf, hc => by
    cases h with
    | @cons _ c M _ eo E S _ hr hrest =>
    cases owns with
    | nil => simp [shape, ownCtx] at hs
    | cons o owns =>
    simp only [shape, ownCtx, List.map_cons, List.cons.injEq, Prod.mk.injEq] at hs
    obtain ⟨⟨-, hrs⟩, hs⟩ := hs
    cases r with
    | ref => simp [Slot.shape] at hrs
    | lent => simp [Slot.shape] at hrs
    | half => simp [Slot.shape] at hrs
    | own τ live =>
    simp only [Slot.shape, Slot.own.injEq] at hrs
    obtain ⟨rfl, -⟩ := hrs
    simp only [addE, addS, Slot.excl, ↓reduceIte, exclPart, sharedPart, Slot.shell, Ty.shell, Bool.false_eq_true] at hn ⊢
    obtain ⟨hnM, hnE, hdME⟩ := nodup_append_disj.mp hn
    have hc' : ∀ o ∈ owns, o.2.complete = true := fun o ho => hc o (List.mem_cons_of_mem _ ho)
    have hco := hc _ (List.mem_cons_self ..)
    obtain ⟨σ1, hd1, hn1, hfree1, hkeep1, hrt1⟩ := dropCell_own hwf hco hr
    obtain ⟨hk1, hs1⟩ := cellKonts_ok hco hr
    obtain ⟨rfl, -, -, -, -, -, -, hkr, hsr⟩ := dropCells_ok hrest hs hnE hwf hc'
    have hagE : ∀ l ∈ E, σ1.mem l = σ.mem l := fun l hl => hkeep1 l (.inl fun h => hdME l h hl)
    have hrest1 := hrest.frame (σ' := σ1) (Agree.of (fun l hl => hagE l (by simpa using hl)) hrt1)
    obtain ⟨-, σ', hd', hn', hfree', hkeep', hrt', -, -⟩ :=
      dropCells_ok hrest1 hs hnE (WF.of_drop hwf hn1 hfree1 hkeep1) hc'
    rw [cellsKonts_frame hrest hs hc' (fun l hl => hagE l hl) hn1] at hfree' hkeep'
    simp only [List.map_cons, List.zip_cons_cons, cellsKonts, List.flatMap_append, dropCells, hd1, hd']
    refine ⟨rfl, σ', rfl, by rw [hn', hn1], ?_, ?_, by rw [hrt', hrt1], ?_, ?_⟩
    · intro l hl hlY
      simp only [List.mem_append, not_or] at hlY
      rcases List.mem_append.mp hl with hl | hl
      · rw [hkeep' l (.inl fun h => hdME l hl h)]; exact hfree1 l hl hlY.1
      · exact hfree' l hl hlY.2
    · intro l hl
      simp only [List.mem_append, not_or] at hl
      rcases hl with ⟨hl1, hl2⟩ | hl | hl
      · rw [hkeep' l (.inl hl2), hkeep1 l (.inl hl1)]
      · have hM := hs1 l hl
        rw [hkeep' l (.inl fun h => hdME l hM h), hkeep1 l (.inr hl)]
      · have hE := hsr l hl
        rw [hkeep' l (.inr hl), hkeep1 l (.inl fun h => hdME l h hE)]
    · exact hk1.append hkr fun l h1 h2 => hdME l (hs1 l h1) (hsr l h2)
    · intro l hl
      rcases List.mem_append.mp hl with hl | hl
      · exact List.mem_append.mpr (.inl (hs1 l hl))
      · exact List.mem_append.mpr (.inr (hsr l hl))

/-! ## Lending: holes in the caller's trees -/

/-- A place lent: its mode and type, the variable it is rooted at, the location, the cells on the
path to it, and the tree there. -/
structure Hole where
  mode : Mode
  ty : Ty
  root : Var
  loc : Nat
  path : List Nat
  old : List Nat
  /-- The root's tree: the path, the fields it passes by, and the tree at the hole. -/
  tree : List Nat

/-- What the borrow of a hole is to the callee. -/
def Hole.slot (h : Hole) : Slot := .ref h.mode h.ty

def HoleOk (F : List Fn) (ι : Iota) (σ : Store) (Γ : Ctx) (env : Env) (h : Hole) : Prop :=
  ∃ s a τr, lookup h.root Γ = some s ∧ lookup h.root env = some a ∧ (h.mode = .mut → s.excl = true) ∧
    Path F ι σ a τr h.path h.loc h.ty ∧ LT F ι σ a τr h.tree ∧ h.tree.Perm (h.path ++ h.old) ∧
    SlotOk F ι σ s a h.tree ∧ LT F ι σ h.loc h.ty h.old ∧ (∀ ι' σ' L', LT F ι' σ' a τr L' → SlotOk F ι' σ' s a L') ∧
    (s.shell = true → (h.path = [] ∧ h.ty = τr) ∨ ∃ P, h.path = a :: P) ∧ h.ty.whole = true ∧ τr = s.ty

theorem HoleOk.mono (h : HoleOk F ι σ Γ env hl) (hW : ι.w.le W) : HoleOk F (ι.inW W) σ Γ env hl := by
  obtain ⟨s, a, τr, h1, h2, h3, hp, hL, hperm, hso, hold, huniv, h4, h5, h6⟩ := h
  exact ⟨s, a, τr, h1, h2, h3, hp.mono hW, hL.mono hW, hperm, hso.mono hW, hold.mono hW, huniv, h4, h5, h6⟩

theorem HoleOk.entry (h : HoleOk F ι σ Γ env hl) :
    ∃ s a, Entry F ι σ Γ env hl.root s a hl.tree ∧ (hl.mode = .mut → s.excl = true) :=
  let ⟨s, a, _, hs, ha, hm, _, _, _, hso, _⟩ := h
  ⟨s, a, ⟨hs, ha, hso⟩, hm⟩

theorem HoleOk.perm (h : HoleOk F ι σ Γ env hl) : hl.tree.Perm (hl.path ++ hl.old) :=
  let ⟨_, _, _, _, _, _, _, _, hp, _⟩ := h
  hp

theorem HoleOk.mem_tree (h : HoleOk F ι σ Γ env hl) : l ∈ hl.tree ↔ l ∈ hl.path ∨ l ∈ hl.old := by
  rw [h.perm.mem_iff, List.mem_append]

/-- A closure borrowed `mut` holds the closure's cell first. -/
theorem SlotOk.cons_of_shell (h : SlotOk F ι σ s a L) (hs : s.shell = true) : ∃ R, L = a :: R :=
  h.head_of_shell hs

/-- A `mut` borrow's slot is a ref slot of the type its footprint says. -/
theorem SlotOk.ref_ty (h : SlotOk F ι σ (.ref m (.fn k A B r Rf)) a L) (hL : LT F ι σ a τ L) : .fn k A B r Rf = τ :=
  (LT.det_fn h hL (hL.nonhole_of h rfl)).1.symm

/-- What a `mut` hole lets the callee change lies in what its root may change. -/
theorem HoleOk.excl_sub (hok : HoleOk F ι σ Γ env h) (hm : h.mode = .mut) :
    ∃ s a, Entry F ι σ Γ env h.root s a h.tree ∧
      ∀ l ∈ exclPart h.slot h.old, l ∈ exclPart s h.tree := by
  obtain ⟨s, a, τr, hs, ha, hex, hpath, hLT, hperm, hso, hold, -, hsh, hcomp, hty'⟩ := hok
  refine ⟨s, a, ⟨hs, ha, hso⟩, fun l hl => ?_⟩
  cases hss : s.shell
  · rw [exclPart_plain hss, if_pos (hex hm)]
    exact hperm.mem_iff.mpr (List.mem_append.mpr (.inr (exclPart_sub hl)))
  · have hnh : τr.isHole = false := by
      rw [hty']
      match s, hss with
      | .ref .mut _, h => exact Ty.shell_nonhole h
      | .half _ _ _, _ => exact Ty.lent1_isHole
    obtain ⟨R0, hR0⟩ := hLT.cons hnh
    rcases hsh hss with ⟨hp, hty⟩ | ⟨P, hp⟩
    · -- The hole is the root itself, a closure: the same tree, the same slot.
      rw [hp, List.nil_append] at hperm
      match s, hss, hso with
      | .half _ _ _, _, _ =>
        rw [hty, hty'] at hcomp; simp [Slot.ty, Ty.lent1_whole] at hcomp
      | .ref .mut τ', hsh, hso =>
        have hsh' : τ'.shell = true := hsh
        have : τ' = τr := hty'.symm
        simp only [Hole.slot, hm, hty, ← this] at hl
        obtain ⟨R1, hR1⟩ := hold.cons (by rw [hty, ← this]; exact Ty.shell_nonhole hsh')
        rw [hR0] at hperm ⊢
        rw [hR1] at hperm hl
        have hla : h.loc = a := by rw [hp] at hpath; cases hpath; rfl
        subst hla
        have := (List.Perm.cons_inv hperm)
        simp only [exclPart, Slot.excl, Slot.shell, hsh', ↓reduceIte, List.tail_cons] at hl ⊢
        exact this.mem_iff.mpr hl
    · -- Past the root's first cell, which is only read.
      rw [hp] at hperm
      rw [hR0] at hperm ⊢
      have : R0.Perm (P ++ h.old) := by simpa using hperm
      simp only [exclPart, Slot.shell_excl hss, hss, ↓reduceIte, List.tail_cons]
      exact this.mem_iff.mpr (List.mem_append.mpr (.inr (exclPart_sub hl)))

theorem Hole.excl_mut {h : Hole} (hl : l ∈ exclPart h.slot L) : h.mode = .mut ∧ l ∈ L := by
  refine ⟨?_, exclPart_sub hl⟩
  cases hm : h.mode
  · simp [Hole.slot, hm, exclPart, Slot.excl] at hl
  · rfl

theorem Hole.shared_ro {h : Hole} (hm : h.mode = .ro) : sharedPart h.slot L = L := by
  simp [Hole.slot, hm, sharedPart, Slot.excl]

theorem Hole.excl_ro {h : Hole} (hm : h.mode = .ro) : exclPart h.slot L = [] := by
  simp [Hole.slot, hm, exclPart, Slot.excl]

def refCtx (refs : List (Var × Mode × Ty)) : Ctx := refs.map fun p => (p.1, Slot.ref p.2.1 p.2.2)

/-- The cells of the trees lent that the callee may change, and of those it only reads. -/
def mutCells (ps : List (Hole × List Nat)) : List Nat :=
  ps.flatMap fun p => exclPart p.1.slot p.2

def roCells (ps : List (Hole × List Nat)) : List Nat :=
  ps.flatMap fun p => sharedPart p.1.slot p.2

theorem mem_mutCells : l ∈ mutCells ps ↔ ∃ p ∈ ps, l ∈ exclPart p.1.slot p.2 := by
  simp [mutCells, List.mem_flatMap]

theorem mem_roCells : l ∈ roCells ps ↔ ∃ p ∈ ps, l ∈ sharedPart p.1.slot p.2 := by
  simp [roCells, List.mem_flatMap]

/-- A cell of a tree lent is one the callee may change or one it only reads. -/
theorem mem_cells_of (hp : p ∈ ps) (hl : l ∈ p.2) : l ∈ mutCells ps ∨ l ∈ roCells ps :=
  (mem_parts (s := p.1.slot) hl).imp (fun h => mem_mutCells.mpr ⟨p, hp, h⟩) (fun h => mem_roCells.mpr ⟨p, hp, h⟩)

/-- The callee's borrowed parameters, bound to the holes: each holds the tree at its hole. -/
theorem foot_refs : ∀ {refs : List (Var × Mode × Ty)} {hs : List Hole} {E S : List Nat},
    refs.map Prod.snd = hs.map (fun h => (h.mode, h.ty)) →
    (Foot F ι σ (refCtx refs) ((refs.map Prod.fst).zip (hs.map Hole.loc)) E S ↔
      ∃ ps : List (Hole × List Nat), ps.map Prod.fst = hs ∧ (∀ p ∈ ps, LT F ι σ p.1.loc p.1.ty p.2) ∧
        E = mutCells ps ∧ S = roCells ps)
  | [], [], E, S, _ => by
    constructor
    · intro h; cases h; exact ⟨[], rfl, by simp, rfl, rfl⟩
    · rintro ⟨ps, hps, -, rfl, rfl⟩
      cases ps with
      | nil => exact .nil
      | cons => simp at hps
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | (x, m, τ) :: refs, h :: hs, E, S, heq => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at heq
    obtain ⟨⟨rfl, rfl⟩, heq⟩ := heq
    simp only [refCtx, List.map_cons, List.zip_cons_cons]
    constructor
    · intro hf
      cases hf with
      | @cons _ _ L _ _ _ _ _ hs' hrest =>
        obtain ⟨ps, h1, h2, rfl, rfl⟩ := (foot_refs heq).mp hrest
        refine ⟨(h, L) :: ps, by simp [h1], ?_, by simp [addE, mutCells, Hole.slot], by simp [addS, roCells, Hole.slot]⟩
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hs'
        · exact h2 p hp
    · rintro ⟨ps, hps, hlt, rfl, rfl⟩
      cases ps with
      | nil => simp at hps
      | cons p ps =>
        obtain ⟨hh, R⟩ := p
        simp only [List.map_cons, List.cons.injEq] at hps
        obtain ⟨hhe, hps⟩ := hps
        subst hhe
        have hrest := (foot_refs heq).mpr ⟨ps, hps, fun p hp => hlt p (List.mem_cons_of_mem _ hp), rfl, rfl⟩
        have := Foot.cons (x := x) (s := .ref hh.mode hh.ty) (hlt _ (List.mem_cons_self ..)) hrest
        simpa [refCtx, addE, addS, mutCells, roCells, Hole.slot] using this

/-- Of two different elements of a list related pairwise by a symmetric relation, the relation
holds. -/
theorem pairwise_of_mem {R : α → α → Prop} (hR : ∀ a b, R a b → R b a) :
    ∀ {l : List α}, l.Pairwise R → a ∈ l → b ∈ l → a ≠ b → R a b
  | [], _, ha, _, _ => by simp at ha
  | c :: l, h, ha, hb, hne => by
    obtain ⟨hc, hl⟩ := List.pairwise_cons.mp h
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd rfl hne
      · exact hc b hb'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact hR _ _ (hc a ha')
      · exact pairwise_of_mem hR hl ha' hb' hne

/-- In a list whose concatenation has no duplicates, two different elements' lists are apart. -/
theorem flatMap_apart {f : α → List Nat} :
    ∀ {l : List α}, (l.flatMap f).Nodup → a ∈ l → b ∈ l → a ≠ b → Disj (f a) (f b)
  | [], _, ha, _, _ => by simp at ha
  | c :: l, h, ha, hb, hne => by
    simp only [List.flatMap_cons] at h
    obtain ⟨-, hl, hd⟩ := nodup_append_disj.mp h
    have hin : ∀ {d}, d ∈ l → ∀ x ∈ f d, x ∈ l.flatMap f := fun hd x hx => List.mem_flatMap.mpr ⟨_, hd, hx⟩
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd rfl hne
      · exact fun x hx hx' => hd x hx (hin hb' x hx')
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact fun x hx hx' => hd x hx' (hin ha' x hx)
      · exact flatMap_apart hl ha' hb' hne

/-- Two holes rooted at one variable are both `readonly`, or hold trees apart. -/
def Apart (h h' : Hole) : Prop := h.root = h'.root → (h.mode = .ro ∧ h'.mode = .ro) ∨ Disj h.old h'.old

theorem Apart.symm : Apart h h' → Apart h' h := fun h e => (h e.symm).imp (fun ⟨a, b⟩ => ⟨b, a⟩) Disj.symm

/-- The places a call lends denote locations, each a hole in its root's tree, from a place lent. -/
theorem lends_holes : Lends Γ lent ts ys → Foot F ι σ Γ env E S → LentApart lent →
    ∃ hs : List Hole, hs.map (fun h => (h.mode, h.ty)) = ts ∧ hs.map (fun h => (h.mode, h.root)) = ys ∧
      lent.mapM (fun x => resolve σ env x.2) = some (hs.map Hole.loc) ∧ (∀ h ∈ hs, HoleOk F ι σ Γ env h) ∧
      (∀ h ∈ hs, ∀ s, lookup h.root Γ = some s → s.shell = true → s.ty.shell = true → h.path = []) ∧
      hs.Pairwise Apart ∧ ∀ h ∈ hs, ∃ p w, (h.mode, p) ∈ lent ∧ PlaceTy Γ p h.ty w h.root ∧ resolve σ env p = some h.loc := by
  intro hl hf
  induction hl with
  | nil => intro _; exact ⟨[], rfl, rfl, rfl, by simp, by simp, .nil, by simp⟩
  | @cons p τ w y m rest ts ys hp hw hτc _ ih =>
    intro hap
    obtain ⟨hc, hap'⟩ := List.pairwise_cons.mp hap
    obtain ⟨hs, h1, h2, h3, h4, h5, h6, h7⟩ := ih hap'
    obtain ⟨a, τr, Lr, P, l, s, ha, hLr, hpath, hres, -, -, hs', hso, hex, hlt, hsh, hty⟩ := place_ok hp hf
    obtain ⟨R, hR, hLrp⟩ := path_split hpath hLr
    refine ⟨⟨m, τ, y, l, P, R, Lr⟩ :: hs, by simp [h1], by simp [h2], ?_, ?_, ?_, ?_, ?_⟩
    · simp [List.mapM_cons, hres, h3]
    · intro h hh
      rcases List.mem_cons.mp hh with rfl | hh
      · exact ⟨s, a, τr, hs', ha, fun hm => hex (hw hm), hpath, hLr, hLrp, hso, hR, hlt,
          fun h => (hsh h).imp id (fun ⟨_, P', hP⟩ => ⟨P', hP⟩), hτc, hty⟩
      · exact h4 h hh
    · intro h hh s0 hs0 hsh0 hfn0
      rcases List.mem_cons.mp hh with rfl | hh
      · obtain rfl := lookup_det hs' hs0
        rcases hsh hsh0 with ⟨h1, -⟩ | ⟨hfn, -⟩
        · exact h1
        · rw [hty] at hfn; rw [hfn] at hfn0; cases hfn0
      · exact h5 h hh s0 hs0 hsh0 hfn0
    · refine List.pairwise_cons.mpr ⟨fun h' hh' => ?_, h6⟩
      intro e
      -- Lent with another place rooted at the same variable: both `readonly`, or apart.
      obtain ⟨p', w', hmem, hp', hres'⟩ := h7 h' hh'
      have hr : p.root = p'.root := by rw [← hp.root_eq, ← hp'.root_eq]; exact e
      rcases hc _ hmem hr with hro | hA
      · exact .inl hro
      · obtain ⟨l', R', hres'', hR'⟩ := place_lt hp' hf
        rw [hres'] at hres''; cases hres''
        obtain ⟨_, _, _, _, _, _, _, _, _, _, hold', _⟩ := h4 h' hh'
        obtain rfl := hold'.det hR'
        exact .inr (place_apart hA hp hp' hf hres hres' hR hR')
    · intro h hh
      rcases List.mem_cons.mp hh with rfl | hh
      · exact ⟨p, w, List.mem_cons_self .., hp, hres⟩
      · obtain ⟨p', w', hmem, hp', hres'⟩ := h7 h hh
        exact ⟨p', w', List.mem_cons_of_mem _ hmem, hp', hres'⟩

theorem lends_ok (hl : Lends Γ lent ts ys) (hf : Foot F ι σ Γ env E S) (hap : LentApart lent) :
    ∃ hs : List Hole, hs.map (fun h => (h.mode, h.ty)) = ts ∧ hs.map (fun h => (h.mode, h.root)) = ys ∧
      lent.mapM (fun x => resolve σ env x.2) = some (hs.map Hole.loc) ∧ (∀ h ∈ hs, HoleOk F ι σ Γ env h) ∧
      (∀ h ∈ hs, ∀ s, lookup h.root Γ = some s → s.shell = true → s.ty.shell = true → h.path = []) ∧
      hs.Pairwise Apart :=
  let ⟨hs, h1, h2, h3, h4, h5, h6, _⟩ := lends_holes hl hf hap
  ⟨hs, h1, h2, h3, h4, h5, h6⟩

/-- The trees as they were at the holes. -/
def olds (hs : List Hole) : List (Hole × List Nat) := hs.map fun h => (h, h.old)

theorem mem_olds_mut : l ∈ mutCells (olds hs) ↔ ∃ h ∈ hs, l ∈ exclPart h.slot h.old := by
  rw [mem_mutCells]
  simp only [olds, List.mem_map]
  constructor
  · rintro ⟨_, ⟨h, hh, rfl⟩, hl⟩; exact ⟨h, hh, hl⟩
  · rintro ⟨h, hh, hl⟩; exact ⟨_, ⟨h, hh, rfl⟩, hl⟩

theorem mem_olds_ro : l ∈ roCells (olds hs) ↔ ∃ h ∈ hs, l ∈ sharedPart h.slot h.old := by
  rw [mem_roCells]
  simp only [olds, List.mem_map]
  constructor
  · rintro ⟨_, ⟨h, hh, rfl⟩, hl⟩; exact ⟨h, hh, hl⟩
  · rintro ⟨h, hh, hl⟩; exact ⟨_, ⟨h, hh, rfl⟩, hl⟩

/-- A hole's tree is in the caller's footprints; what a `mut` hole lets the callee change, in the
exclusive ones. -/
theorem hole_in (hI : Inv F ι σ Γ env E S) (hok : HoleOk F ι σ Γ env h) :
    (∀ l ∈ h.path ++ h.old, l ∈ E ∨ l ∈ S) ∧ (h.mode = .mut → ∀ l ∈ exclPart h.slot h.old, l ∈ E) := by
  refine ⟨fun l hl => ?_, fun hm l hl => ?_⟩
  · obtain ⟨s, a, he, -⟩ := hok.entry
    rcases hI.entry_sub he l (hok.mem_tree.mpr (List.mem_append.mp hl)) with ⟨-, h1⟩ | ⟨-, h1⟩
    · exact .inl h1
    · exact .inr h1
  · obtain ⟨s, a, he, hsub⟩ := hok.excl_sub hm
    exact (hI.foot.memE hI.keys l).mpr ⟨_, s, a, _, he, hsub l hl⟩

/-- Holes rooted at different variables, one of them lent `mut`: what it lets the callee change is
apart from the other's tree. -/
theorem hole_apart (hI : Inv F ι σ Γ env E S) (hok : HoleOk F ι σ Γ env h) (hok' : HoleOk F ι σ Γ env h')
    (hr : h.root ≠ h'.root) (hm : h.mode = .mut) : Disj (exclPart h.slot h.old) (h'.path ++ h'.old) := by
  obtain ⟨s, a, he, hsub⟩ := hok.excl_sub hm
  obtain ⟨s', a', he', -⟩ := hok'.entry
  exact fun l hl hl' => hI.apart he he' hr l (hsub l hl) (hok'.mem_tree.mpr (List.mem_append.mp hl'))

/-- Two holes, one lent `mut`, are rooted at different variables or hold trees apart. -/
theorem hole_sep {hs : List Hole} (hpw : hs.Pairwise Apart) (hh : h ∈ hs) (hh' : h' ∈ hs)
    (hm : h.mode = .mut) (hne : h ≠ h') : h.root ≠ h'.root ∨ Disj h.old h'.old := by
  by_cases e : h.root = h'.root
  · rcases (pairwise_of_mem (fun _ _ => Apart.symm) hpw hh hh' hne) e with ⟨h1, -⟩ | hd
    · rw [hm] at h1; cases h1
    · exact .inr hd
  · exact .inl e

theorem HoleOk.old_lt (hok : HoleOk F ι σ Γ env h) : LT F ι σ h.loc h.ty h.old := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hlt, _⟩ := hok
  exact hlt

theorem HoleOk.old_nodup (hok : HoleOk F ι σ Γ env h) : h.old.Nodup := hok.old_lt.nodup

theorem HoleOk.tree_nodup (hok : HoleOk F ι σ Γ env h) : (h.path ++ h.old).Nodup := by
  obtain ⟨_, _, _, _, _, _, _, hLT, hp, _⟩ := hok
  exact hp.nodup_iff.mp (LT.nodup hLT)

theorem HoleOk.path_old (hok : HoleOk F ι σ Γ env h) : Disj h.path h.old :=
  (nodup_append_disj.mp hok.tree_nodup).2.2

/-- A hole's tree starts at its location. -/
theorem HoleOk.whole (hok : HoleOk F ι σ Γ env h) : h.ty.whole = true := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h, _⟩ := hok
  exact h

theorem HoleOk.old_head (hok : HoleOk F ι σ Γ env h) : ∃ R, h.old = h.loc :: R :=
  hok.old_lt.cons (Ty.whole_not_hole hok.whole)

/-- A root that may change all but its first cell, lent `mut`: the hole is the root itself, a
closure as the callee borrows it, or a place past that cell. -/
theorem HoleOk.shell_root (hok : HoleOk F ι σ Γ env h) (he : Entry F ι σ Γ env h.root s a L)
    (hs : s.shell = true) (hm : h.mode = .mut) :
    (h.path = [] ∧ s = h.slot) ∨ ∃ P, h.path = a :: P := by
  obtain ⟨s', a', τr, hs', ha', -, -, hLT, -, hso, -, -, hsh, hcomp, hty'⟩ := hok
  rw [lookup_det hs' he.1] at hso hsh hty'
  rw [lookup_det ha' he.2.1] at hso hsh hLT
  rcases hsh hs with ⟨hp, hty⟩ | hp
  · refine .inl ⟨hp, ?_⟩
    match s, hs, hso with
    | .half _ _ _, _, _ =>
      rw [hty, hty'] at hcomp; simp [Slot.ty, Ty.lent1_whole] at hcomp
    | .ref .mut τ', _, hso =>
      have : τ' = τr := hty'.symm
      simp only [Hole.slot, hm, hty, ← this]
  · exact .inr hp

/-- What a `mut` hole only lets the callee read is the head of the tree there. -/
theorem Hole.shared_mut_head {h : Hole} (hm : h.mode = .mut) (hl : l ∈ sharedPart h.slot (c :: R)) : l = c := by
  unfold sharedPart at hl
  simp only [Hole.slot, hm, Slot.excl, ↓reduceIte] at hl
  split at hl
  · simpa using hl
  · simp at hl

theorem Hole.shared_mut_swap {h : Hole} (hm : h.mode = .mut) (hl : l ∈ sharedPart h.slot (c :: R)) :
    l ∈ sharedPart h.slot (c :: R') := by
  obtain rfl := Hole.shared_mut_head hm hl
  unfold sharedPart at hl ⊢
  simp only [Hole.slot, hm, Slot.excl, ↓reduceIte] at hl ⊢
  split at hl <;> simp_all

theorem olds_nodup (hI : Inv F ι σ Γ env E S) : ∀ {hs : List Hole}, (∀ h ∈ hs, HoleOk F ι σ Γ env h) →
    hs.Pairwise Apart → (mutCells (olds hs)).Nodup
  | [], _, _ => by simp [mutCells, olds]
  | h :: hs, hholes, hpw => by
    obtain ⟨hc, hl⟩ := List.pairwise_cons.mp hpw
    have ih := olds_nodup hI (fun h' hh => hholes h' (List.mem_cons_of_mem _ hh)) hl
    have hsplit : mutCells (olds (h :: hs)) = exclPart h.slot h.old ++ mutCells (olds hs) := by
      simp [mutCells, olds]
    rw [hsplit]
    refine nodup_append_disj.mpr ⟨(parts_nodup (hholes h (List.mem_cons_self ..)).old_nodup).1, ih, ?_⟩
    intro l hl hl'
    have hm := (Hole.excl_mut hl).1
    obtain ⟨h', hh', hl'⟩ := mem_olds_mut.mp hl'
    by_cases hr : h.root = h'.root
    · rcases hc h' hh' hr with ⟨h1, -⟩ | hd
      · rw [hm] at h1; cases h1
      · exact hd l (exclPart_sub hl) (exclPart_sub hl')
    · exact hole_apart hI (hholes h (List.mem_cons_self ..)) (hholes h' (List.mem_cons_of_mem _ hh')) hr hm l
        hl (List.mem_append.mpr (.inr (exclPart_sub hl')))

/-- What a hole lets the callee only read, no hole lets it change. -/
theorem shared_not_mut (hI : Inv F ι σ Γ env E S) {hs : List Hole} (hholes : ∀ h ∈ hs, HoleOk F ι σ Γ env h)
    (hpw : hs.Pairwise Apart) (hh : h ∈ hs) (hl : l ∈ sharedPart h.slot h.old) : l ∉ mutCells (olds hs) := by
  intro hM
  obtain ⟨h', hh', hl'⟩ := mem_olds_mut.mp hM
  have hm' := (Hole.excl_mut hl').1
  by_cases hne : h' = h
  · subst hne
    exact parts_disj (hholes h' hh).old_nodup l hl' hl
  · rcases hole_sep hpw hh' hh hm' hne with hr | hd
    · exact hole_apart hI (hholes h' hh') (hholes h hh) hr hm' l
        hl' (List.mem_append.mpr (.inr (sharedPart_sub hl)))
    · exact hd l (exclPart_sub hl') (sharedPart_sub hl)

/-! ## The callee's activation -/

/-- Each hole's cells were allocated before the call and are no argument's: not in the footprint of
the callee's owned parameters. -/
theorem hole_out {Eo Lall : List Nat} (hI : Inv F ι σ Γ env E S) (hok : HoleOk F ι σ Γ env h) (hwf : WF σ)
    (hEo_in : ∀ l ∈ Eo, l ∈ Lall ∨ σ.next ≤ l) (hdL : Disj Lall E) (hdLS : Disj Lall S) :
    ∀ l ∈ h.path ++ h.old, σ.mem l ≠ none ∧ l ∉ Eo := by
  intro l hl
  have hin := (hole_in hI hok).1 l hl
  have ha : σ.mem l ≠ none := by
    rcases hin with h | h
    · exact hI.alloc l h
    · exact hI.allocS l h
  refine ⟨ha, fun he => ?_⟩
  rcases hEo_in l he with h | h
  · rcases hin with h' | h'
    · exact hdL l h h'
    · exact hdLS l h h'
  · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hwf l ha) h)

theorem fnCtx_eq (d : Fn) : fnCtx d = ownCtx d.owns ++ refCtx d.refs := rfl

/-- A hole as a callee whose innermost region is the caller's `k`th sees it. -/
def Hole.lower (k : Nat) (h : Hole) : Hole := { h with ty := h.ty.lowerBy k }

theorem Hole.lower_parts (h : Hole) :
    exclPart (h.lower k).slot L = exclPart h.slot L ∧ sharedPart (h.lower k).slot L = sharedPart h.slot L := by
  obtain ⟨m, τ, _, _, _, _, _⟩ := h
  simp only [Hole.lower, Hole.slot, exclPart, sharedPart]
  cases m <;> cases τ <;> first | exact ⟨rfl, rfl⟩ | (rename_i g _; cases g <;> exact ⟨rfl, rfl⟩)

theorem olds_lower : mutCells (olds (hs.map (Hole.lower k))) = mutCells (olds hs) ∧
    roCells (olds (hs.map (Hole.lower k))) = roCells (olds hs) := by
  induction hs with
  | nil => exact ⟨rfl, rfl⟩
  | cons h hs ih =>
    simp only [olds, List.map_map, List.map_cons, mutCells, roCells, List.flatMap_cons] at ih ⊢
    exact ⟨by rw [ih.1, (h.lower_parts).1]; rfl, by rw [ih.2, (h.lower_parts).2]; rfl⟩

/-- What a callee whose innermost region is the caller's `k`th leaves at the places it was lent. -/
theorem foot_refs_lower : ∀ {refs : List (Var × Mode × Ty)} {hs : List Hole} {E S : List Nat},
    refs.map Prod.snd = hs.map (fun h => (h.mode, h.ty.lowerBy k)) →
    Foot F ι σ (refCtx refs) ((refs.map Prod.fst).zip (hs.map Hole.loc)) E S →
    ∃ ps : List (Hole × List Nat), ps.map Prod.fst = hs ∧ (∀ p ∈ ps, LT F ι σ p.1.loc (p.1.ty.lowerBy k) p.2) ∧
      E = mutCells ps ∧ S = roCells ps
  | [], [], E, S, _, hf => by cases hf; exact ⟨[], rfl, by simp, rfl, rfl⟩
  | [], _ :: _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _ => by simp at h
  | (x, m, τ) :: refs, h :: hs, E, S, heq, hf => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at heq
    obtain ⟨⟨rfl, rfl⟩, heq⟩ := heq
    simp only [refCtx, List.map_cons, List.zip_cons_cons] at hf
    cases hf with
    | @cons _ _ L _ _ _ _ _ hs' hrest =>
      obtain ⟨ps, h1, h2, rfl, rfl⟩ := foot_refs_lower heq hrest
      refine ⟨(h, L) :: ps, by simp [h1], ?_, ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hs'
        · exact h2 p hp
      · simp only [addE, mutCells, List.flatMap_cons]
        rw [← (h.lower_parts (k := k) (L := L)).1]; rfl
      · simp only [addS, roCells, List.flatMap_cons]
        rw [← (h.lower_parts (k := k) (L := L)).2]; rfl

/-- The callee starts with its owned parameters' footprints, the trees lent `mut` exclusive and those
lent `readonly` shared. -/
theorem callee_inv {Eo Lall : List Nat} {hs : List Hole} (hI : Inv F ι₁ σ1 Γ₁ env E₁ S) (hholes : ∀ h ∈ hs, HoleOk F ι₁ σ1 Γ₁ env h)
    (hpw : hs.Pairwise Apart) (hrefs : d.refs.map Prod.snd = hs.map fun h => (h.mode, h.ty.lowerBy k))
    (hkeys : ((d.owns.map Prod.fst) ++ (d.refs.map Prod.fst)).Nodup)
    (hfo : Foot F ι σ2 (ownCtx d.owns) cells Eo []) (hEo : Eo.Nodup)
    (hEo_in : ∀ l ∈ Eo, l ∈ Lall ∨ σ1.next ≤ l) (hdL : Disj Lall E₁) (hdLS : Disj Lall S) (hwf : WF σ1)
    (hold : ∀ l, l < σ1.next → σ2.mem l = σ1.mem l) (hrt : σ2.rt = σ1.rt)
    (hconv : ∀ h ∈ hs, ∀ L, LT F ι₁ σ2 h.loc h.ty L → LT F ι σ2 h.loc (h.ty.lowerBy k) L) :
    Inv F ι σ2 (fnCtx d) (cells ++ (d.refs.map Prod.fst).zip (hs.map Hole.loc))
      (Eo ++ mutCells (olds hs)) (roCells (olds hs)) := by
  have hout := fun h hh => hole_out hI (hholes h hh) hwf hEo_in hdL hdLS
  have hfr := (foot_refs (F := F) (ι := ι) (σ := σ2) (hs := hs.map (Hole.lower k))
    (by rw [hrefs]; simp [Hole.lower, Function.comp_def])).mpr
    ⟨olds (hs.map (Hole.lower k)), by simp [olds, Function.comp_def], ?_, rfl, rfl⟩
  · rw [olds_lower.1, olds_lower.2, List.map_map, show Hole.loc ∘ Hole.lower k = Hole.loc from rfl] at hfr
    rw [fnCtx_eq]
    refine ⟨by simpa using hfo.append hfr, ?_, ?_, ?_⟩
    · refine nodup_append_disj.mpr ⟨hEo, olds_nodup hI hholes hpw, fun l hl hl' => ?_⟩
      obtain ⟨h, hh, hl'⟩ := mem_olds_mut.mp hl'
      exact (hout h hh l (List.mem_append.mpr (.inr (exclPart_sub hl')))).2 hl
    · intro l hl hl'
      obtain ⟨h, hh, hl⟩ := mem_olds_ro.mp hl
      rcases List.mem_append.mp hl' with hl' | hl'
      · exact (hout h hh l (List.mem_append.mpr (.inr (sharedPart_sub hl)))).2 hl'
      · exact shared_not_mut hI hholes hpw hh hl hl'
    · simpa [ownCtx, refCtx, List.map_map, Function.comp_def] using hkeys
  · intro p hp
    simp only [olds, List.mem_map] at hp
    obtain ⟨_, ⟨h, hh, rfl⟩, rfl⟩ := hp
    exact hconv h hh _ ((hholes h hh).old_lt.frame
      (Agree.of (fun l hl => hold l (hwf l (hout h hh l (List.mem_append.mpr (.inr hl))).1)) hrt))

/-! ## The caller after the call -/

section rebuild
variable {σ σ' : Store} {Γ : Ctx} {env : Env} {E S : List Nat} {hs : List Hole}
  {ps : List (Hole × List Nat)}

theorem ps_pairwise (hpw : hs.Pairwise Apart) (hps : ps.map Prod.fst = hs) :
    ps.Pairwise fun p q => Apart p.1 q.1 := by
  rw [← hps] at hpw; exact List.pairwise_map.mp hpw

theorem mem_keep {M : List Nat} : l ∈ E.filter (fun l => l ∉ M) ↔ l ∈ E ∧ l ∉ M := by
  simp [List.mem_filter]

/-- The places rooted at `x` lent `mut`, each with the tree it had and the tree the callee left. -/
def cutsOf (ps : List (Hole × List Nat)) (x : Var) : List Cut :=
  (ps.filter fun p => p.1.root == x && p.1.mode == .mut).map fun p => ⟨p.1.loc, p.1.ty, p.1.old, p.2⟩

theorem mem_cutsOf {c : Cut} : c ∈ cutsOf ps x ↔
    ∃ p ∈ ps, p.1.root = x ∧ p.1.mode = .mut ∧ c = ⟨p.1.loc, p.1.ty, p.1.old, p.2⟩ := by
  simp only [cutsOf, List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨p, ⟨hp, hr, hm⟩, rfl⟩; exact ⟨p, hp, hr, hm, rfl⟩
  · rintro ⟨p, hp, hr, hm, rfl⟩; exact ⟨p, ⟨hp, hr, hm⟩, rfl⟩

/-- What a slot may change of its footprint: all of it, if it may change any, but a closure's cell
borrowed `mut`. -/
theorem mem_exclPart_iff (h : SlotOk F ι σ s a L) :
    z ∈ exclPart s L ↔ s.excl = true ∧ z ∈ L ∧ (s.shell = true → z ≠ a) := by
  cases hsh : s.shell
  · rw [exclPart_plain hsh]
    by_cases hx : s.excl = true <;> simp [hx]
  · have hex := Slot.shell_excl hsh
    obtain ⟨R, rfl⟩ := h.cons_of_shell hsh
    have ha := (List.nodup_cons.mp h.nodup).1
    simp only [exclPart, hex, hsh, ↓reduceIte, List.tail_cons, List.mem_cons, true_and, forall_const]
    constructor
    · intro hz; exact ⟨.inr hz, fun e => ha (e ▸ hz)⟩
    · rintro ⟨hz | hz, hne⟩
      · exact absurd hz hne
      · exact hz

/-- A hole's root holds the hole's tree, and the path to it. -/
theorem HoleOk.at (hok : HoleOk F ι σ Γ env h) (he : Entry F ι σ Γ env h.root s a L) (hτ : τr = s.ty) :
    h.tree = L ∧ Path F ι σ a τr h.path h.loc h.ty := by
  obtain ⟨s', a', τr', hs', ha', -, hpath, -, -, hso, -, -, -, -, hty⟩ := hok
  obtain ⟨rfl, rfl, rfl⟩ := he.det ⟨hs', ha', hso⟩
  subst hτ hty
  exact ⟨rfl, hpath⟩

/-- A cell of a variable's tree in no place of it lent `mut` is in no tree the callee could change. -/
theorem kept_in (hI : Inv F ι σ Γ env E S) (hholes : ∀ h ∈ hs, HoleOk F ι σ Γ env h) (hps : ps.map Prod.fst = hs)
    (he : Entry F ι σ Γ env x s a L) (hz : z ∈ L) (hk : ∀ c ∈ cutsOf ps x, z ∉ c.old) :
    (z ∈ exclPart s L ∧ z ∈ E.filter (fun l => l ∉ mutCells (olds hs))) ∨ (z ∈ sharedPart s L ∧ z ∈ S) := by
  rcases hI.entry_sub he z hz with ⟨h1, hE⟩ | h2
  · refine .inl ⟨h1, mem_keep.mpr ⟨hE, fun hM => ?_⟩⟩
    obtain ⟨h', hh', hl'⟩ := mem_olds_mut.mp hM
    have hm' := (Hole.excl_mut hl').1
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (hps ▸ hh' : h' ∈ ps.map Prod.fst)
    by_cases hr : p.1.root = x
    · exact hk _ (mem_cutsOf.mpr ⟨p, hp, hr, hm', rfl⟩) (exclPart_sub hl')
    · obtain ⟨s', a', he', hsub⟩ := (hholes p.1 hh').excl_sub hm'
      exact hI.apart he' he hr z (hsub z hl') hz
  · exact .inr h2

/-- What a hole lets the callee only read was kept. -/
theorem shared_kept (hI : Inv F ι σ Γ env E S) (hholes : ∀ h ∈ hs, HoleOk F ι σ Γ env h)
    (hpw : hs.Pairwise Apart) (hh : h ∈ hs) (hl : l ∈ sharedPart h.slot h.old) :
    l ∈ E.filter (fun l => l ∉ mutCells (olds hs)) ∨ l ∈ S := by
  rcases (hole_in hI (hholes h hh)).1 l (List.mem_append.mpr (.inr (sharedPart_sub hl))) with hE | hS
  · exact .inl (mem_keep.mpr ⟨hE, shared_not_mut hI hholes hpw hh hl⟩)
  · exact .inr hS

/-- What the callee left at a `mut` hole: what it could change, or the hole's location, which it
only read. -/
theorem new_cases {p : Hole × List Nat} (hok : HoleOk F ι σ Γ env p.1) (hnew : LT F ι σ' p.1.loc p.1.ty p.2) (hm : p.1.mode = .mut)
    (hz : z ∈ p.2) : z ∈ exclPart p.1.slot p.2 ∨ (z = p.1.loc ∧ z ∈ p.1.old ∧ z ∈ sharedPart p.1.slot p.1.old) := by
  rcases mem_parts (s := p.1.slot) hz with h1 | h1
  · exact .inl h1
  · obtain ⟨R, hR⟩ := hnew.cons (Ty.whole_not_hole hok.whole)
    obtain ⟨R0, hR0⟩ := hok.old_head
    rw [hR] at h1
    have he := Hole.shared_mut_head hm h1
    subst he
    exact .inr ⟨rfl, by rw [hR0]; exact List.mem_cons_self .., by rw [hR0]; exact Hole.shared_mut_swap hm h1⟩

/-- After the call, a variable's tree is what it kept and what the callee left at the places of it
lent `mut`; it reaches each of those places, and any other place `extra` names, apart from them and
kept. -/
theorem root_join (hI : Inv F ι σ Γ env E S) (hholes : ∀ h ∈ hs, HoleOk F ι σ Γ env h)
    (hpw : hs.Pairwise Apart) (hps : ps.map Prod.fst = hs)
    (hnew : ∀ p ∈ ps, p.1.mode = .mut → LT F ι σ' p.1.loc p.1.ty p.2) (hMn : (mutCells ps).Nodup)
    (hag : Agree σ σ' (E.filter (fun l => l ∉ mutCells (olds hs)) ++ S))
    (hX : Disj (E.filter (fun l => l ∉ mutCells (olds hs))) (mutCells ps)) (hSX : Disj S (mutCells ps))
    (he : Entry F ι σ Γ env x s a L) (hLT : LT F ι σ a τr L) (hτ : τr = s.ty) (extra : List Cut)
    (hepath : ∀ e ∈ extra, (∃ P, Path F ι σ a τr P e.loc e.ty) ∧ LT F ι σ e.loc e.ty e.old ∧ e.new = e.old ∧
      e.ty.whole = true)
    (heXS : ∀ e ∈ extra, ∀ z ∈ e.old, z ∈ E.filter (fun l => l ∉ mutCells (olds hs)) ∨ z ∈ S)
    (hed : ∀ e ∈ extra, ∀ c ∈ cutsOf ps x, Disj e.old c.old)
    (hee : ∀ e ∈ extra, ∀ e' ∈ extra, e ≠ e' → Disj e.old e'.old) :
    ∃ L', LT F ι σ' a τr L' ∧
      (∀ z, z ∈ L' ↔ Kept L (cutsOf ps x ++ extra) z ∨ ∃ c ∈ cutsOf ps x ++ extra, z ∈ c.new) ∧
      ∀ c ∈ cutsOf ps x ++ extra, ∃ P, Path F ι σ' a τr P c.loc c.ty := by
  have hpsok : ∀ p ∈ ps, HoleOk F ι σ Γ env p.1 := fun p hp => hholes p.1 (hps ▸ List.mem_map_of_mem hp)
  have hpsin : ∀ p ∈ ps, p.1 ∈ hs := fun p hp => hps ▸ List.mem_map_of_mem hp
  have hMX : ∀ z, z ∈ mutCells ps → (z ∈ E.filter (fun l => l ∉ mutCells (olds hs)) ∨ z ∈ S) → False :=
    fun z hM h => h.elim (fun h => hX z h hM) (fun h => hSX z h hM)
  -- A place of `x` lent `mut`: on a path into its tree.
  have hroot : ∀ p ∈ ps, p.1.root = x → p.1.tree = L ∧ Path F ι σ a τr p.1.path p.1.loc p.1.ty :=
    fun p hp hr => (hpsok p hp).at (hr ▸ he) hτ
  -- Two places of `x` lent `mut` hold trees apart.
  have hdd : ∀ p ∈ ps, ∀ q ∈ ps, p ≠ q → p.1.root = x → q.1.root = x → p.1.mode = .mut →
      Disj p.1.old q.1.old := by
    intro p hp q hq hne hr hr' hm
    rcases pairwise_of_mem (fun _ _ => Apart.symm) (ps_pairwise hpw hps) hp hq hne (hr.trans hr'.symm) with
      ⟨h1, -⟩ | hd
    · rw [hm] at h1; cases h1
    · exact hd
  -- A cell of `x`'s tree in none of the places lent: kept.
  have hkept : ∀ z, Kept L (cutsOf ps x ++ extra) z →
      z ∈ E.filter (fun l => l ∉ mutCells (olds hs)) ∨ z ∈ S := by
    intro z hk
    rcases kept_in hI hholes hps he hk.1 (fun c hc => hk.2 c (List.mem_append.mpr (.inl hc))) with h | h
    · exact .inl h.2
    · exact .inr h.2
  -- What the callee left at a place lent `mut`.
  have hnc : ∀ p ∈ ps, p.1.mode = .mut → ∀ z ∈ p.2, z ∈ exclPart p.1.slot p.2 ∨
      (z ∈ p.1.old ∧ (z ∈ E.filter (fun l => l ∉ mutCells (olds hs)) ∨ z ∈ S)) := by
    intro p hp hm z hz
    rcases new_cases (hpsok p hp) (hnew p hp hm) hm hz with h | ⟨-, h1, h2⟩
    · exact .inl h
    · exact .inr ⟨h1, shared_kept hI hholes hpw (hpsin p hp) h2⟩
  have hcut := fun {c} (h : c ∈ cutsOf ps x) => mem_cutsOf.mp h
  refine multi_join hLT hag.rt (cutsOf ps x ++ extra) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨p, hp, hr, hm, rfl⟩ := hcut hc
      exact ⟨⟨_, (hroot p hp hr).2⟩, (hpsok p hp).old_lt, hnew p hp hm⟩
    · obtain ⟨hpth, hold, hn, -⟩ := hepath c hc
      refine ⟨hpth, hold, ?_⟩
      rw [hn]
      refine hold.frame (hag.mono fun z hz => ?_)
      rcases heXS c hc z hz with h1 | h1
      · exact List.mem_append.mpr (.inl h1)
      · exact List.mem_append.mpr (.inr h1)
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨p, hp, -, -, rfl⟩ := hcut hc
      exact (hpsok p hp).whole
    · exact (hepath c hc).2.2.2
  · intro c hc d hd hne
    rcases List.mem_append.mp hc with hc | hc <;> rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨p, hp, hr, hm, rfl⟩ := hcut hc
      obtain ⟨q, hq, hr', -, rfl⟩ := hcut hd
      exact hdd p hp q hq (fun e => hne (by rw [e])) hr hr' hm
    · exact (hed d hd c hc).symm
    · exact hed c hc d hd
    · exact hee c hc d hd hne
  · intro z hk
    rcases hkept z hk with h | h
    · exact hag z (List.mem_append.mpr (.inl h))
    · exact hag z (List.mem_append.mpr (.inr h))
  · intro z hk
    rcases hkept z hk with h | h
    · exact hag.fresh z (List.mem_append.mpr (.inl h))
    · exact hag.fresh z (List.mem_append.mpr (.inr h))
  · intro c hc z hz hk
    rcases List.mem_append.mp hc with hc' | hc'
    · obtain ⟨p, hp, -, hm, rfl⟩ := hcut hc'
      rcases hnc p hp hm z hz with h | ⟨h, -⟩
      · exact hMX z (mem_mutCells.mpr ⟨p, hp, h⟩) (hkept z hk)
      · exact hk.2 _ hc h
    · rw [(hepath c hc').2.2.1] at hz
      exact hk.2 c hc hz
  · intro c hc d hd hne z hz hz'
    rcases List.mem_append.mp hc with hc | hc <;> rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨p, hp, hr, hm, rfl⟩ := hcut hc
      obtain ⟨q, hq, hr', hm', rfl⟩ := hcut hd
      have hpq : p ≠ q := fun e => hne (by rw [e])
      rcases hnc p hp hm z hz with h1 | ⟨h1, k1⟩ <;> rcases hnc q hq hm' z hz' with h2 | ⟨h2, k2⟩
      · exact flatMap_apart (f := fun p : Hole × List Nat => exclPart p.1.slot p.2) hMn hp hq hpq z h1 h2
      · exact hMX z (mem_mutCells.mpr ⟨p, hp, h1⟩) k2
      · exact hMX z (mem_mutCells.mpr ⟨q, hq, h2⟩) k1
      · exact hdd p hp q hq hpq hr hr' hm z h1 h2
    · obtain ⟨p, hp, -, hm, rfl⟩ := hcut hc
      rw [(hepath d hd).2.2.1] at hz'
      rcases hnc p hp hm z hz with h1 | ⟨h1, -⟩
      · exact hMX z (mem_mutCells.mpr ⟨p, hp, h1⟩) (heXS d hd z hz')
      · exact hed d hd _ hc z hz' h1
    · obtain ⟨q, hq, -, hm, rfl⟩ := hcut hd
      rw [(hepath c hc).2.2.1] at hz
      rcases hnc q hq hm z hz' with h1 | ⟨h1, -⟩
      · exact hMX z (mem_mutCells.mpr ⟨q, hq, h1⟩) (heXS c hc z hz)
      · exact hed c hc _ hd z hz h1
    · rw [(hepath c hc).2.2.1] at hz
      rw [(hepath d hd).2.2.1] at hz'
      exact hee c hc d hd hne z hz hz'

/-- After the call, what a place lent is rooted at reaches it, and holds a tree its slot accepts;
a place lent `readonly` holds what it held. -/
theorem hole_after (hI : Inv F ι σ Γ env E S) (hholes : ∀ h ∈ hs, HoleOk F ι σ Γ env h)
    (hpw : hs.Pairwise Apart) (hps : ps.map Prod.fst = hs)
    (hnew : ∀ p ∈ ps, p.1.mode = .mut → LT F ι σ' p.1.loc p.1.ty p.2) (hMn : (mutCells ps).Nodup)
    (hag : Agree σ σ' (E.filter (fun l => l ∉ mutCells (olds hs)) ++ S))
    (hX : Disj (E.filter (fun l => l ∉ mutCells (olds hs))) (mutCells ps)) (hSX : Disj S (mutCells ps))
    (hh : h ∈ hs) :
    ∃ s a τr P L', lookup h.root Γ = some s ∧ lookup h.root env = some a ∧ (h.mode = .mut → s.excl = true) ∧
      Path F ι σ' a τr P h.loc h.ty ∧ LT F ι σ' a τr L' ∧ SlotOk F ι σ' s a L' ∧
      (∀ ι'' σ'' L', LT F ι'' σ'' a τr L' → SlotOk F ι'' σ'' s a L') ∧ (h.mode = .ro → LT F ι σ' h.loc h.ty h.old) := by
  obtain ⟨s, a, τr, hs', ha', hex, hpath, hLT, -, hso, hold, huniv, -, hcomp, hty⟩ := hholes h hh
  have he : Entry F ι σ Γ env h.root s a h.tree := ⟨hs', ha', hso⟩
  cases hm : h.mode
  · -- The place is reached as other places lent `readonly` are: as one more, kept, place.
    have hXS : ∀ z ∈ h.old, z ∈ E.filter (fun l => l ∉ mutCells (olds hs)) ∨ z ∈ S := by
      intro z hz
      rcases (hole_in hI (hholes h hh)).1 z (List.mem_append.mpr (.inr hz)) with hE | hS
      · refine .inl (mem_keep.mpr ⟨hE, fun hM => ?_⟩)
        obtain ⟨h', hh', hl'⟩ := mem_olds_mut.mp hM
        have hm' := (Hole.excl_mut hl').1
        have hne : h' ≠ h := fun e => by rw [e, hm] at hm'; cases hm'
        rcases hole_sep hpw hh' hh hm' hne with hr | hd
        · exact hole_apart hI (hholes h' hh') (hholes h hh) hr hm' z hl' (List.mem_append.mpr (.inr hz))
        · exact hd z (exclPart_sub hl') hz
      · exact .inr hS
    have hold' : LT F ι σ' h.loc h.ty h.old := hold.frame <| hag.mono fun z hz => by
      rcases hXS z hz with h1 | h1
      · exact List.mem_append.mpr (.inl h1)
      · exact List.mem_append.mpr (.inr h1)
    obtain ⟨L', hL', -, hpaths⟩ := root_join hI hholes hpw hps hnew hMn hag hX hSX he hLT hty
      [⟨h.loc, h.ty, h.old, h.old⟩]
      (by intro e he; simp only [List.mem_singleton] at he; subst he; exact ⟨⟨_, hpath⟩, hold, rfl, hcomp⟩)
      (by intro e he; simp only [List.mem_singleton] at he; subst he; exact hXS)
      (by
        intro e he c hc
        simp only [List.mem_singleton] at he; subst he
        obtain ⟨p, hp, hr, hm', rfl⟩ := mem_cutsOf.mp hc
        have hph : p.1 ∈ hs := hps ▸ List.mem_map_of_mem hp
        have hne : p.1 ≠ h := fun e => by rw [e, hm] at hm'; cases hm'
        rcases hole_sep hpw hph hh hm' hne with hr' | hd
        · exact absurd hr hr'
        · exact hd.symm)
      (by intro e he e' he' hne; simp only [List.mem_singleton] at he he'; exact absurd (he.trans he'.symm) hne)
    obtain ⟨P, hP⟩ := hpaths _ (List.mem_append.mpr (.inr (List.mem_singleton_self _)))
    exact ⟨s, a, τr, P, L', hs', ha', (fun h => by cases h), hP, hL', huniv _ σ' L' hL', huniv, fun _ => hold'⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (hps ▸ hh : h ∈ ps.map Prod.fst)
    obtain ⟨L', hL', -, hpaths⟩ := root_join hI hholes hpw hps hnew hMn hag hX hSX he hLT hty []
      (by simp) (by simp) (by simp) (by simp)
    obtain ⟨P, hP⟩ := hpaths ⟨p.1.loc, p.1.ty, p.1.old, p.2⟩
      (List.mem_append.mpr (.inl (mem_cutsOf.mpr ⟨p, hp, rfl, hm, rfl⟩)))
    exact ⟨s, a, τr, P, L', hs', ha', (fun _ => hex hm), hP, hL', huniv _ σ' L' hL', huniv, (fun h => by cases h)⟩

/-- After the call, the caller's variables hold what they held but at the places lent `mut`, which
hold what the callee left there. -/
theorem caller_rebuild (hI : Inv F ι σ Γ env E S) (hholes : ∀ h ∈ hs, HoleOk F ι σ Γ env h)
    (hpw : hs.Pairwise Apart) (hps : ps.map Prod.fst = hs)
    (hnew : ∀ p ∈ ps, p.1.mode = .mut → LT F ι σ' p.1.loc p.1.ty p.2) (hMn : (mutCells ps).Nodup)
    (hag : Agree σ σ' (E.filter (fun l => l ∉ mutCells (olds hs)) ++ S))
    (hX : Disj (E.filter (fun l => l ∉ mutCells (olds hs))) (mutCells ps))
    (hSX : Disj S (mutCells ps)) :
    ∃ E', Inv F ι σ' Γ env E' S ∧
      ∀ l, l ∈ E' ↔ l ∈ E.filter (fun l => l ∉ mutCells (olds hs)) ∨ l ∈ mutCells ps := by
  have hpsok : ∀ p ∈ ps, HoleOk F ι σ Γ env p.1 := fun p hp => hholes p.1 (hps ▸ List.mem_map_of_mem hp)
  have hpsin : ∀ p ∈ ps, p.1 ∈ hs := fun p hp => hps ▸ List.mem_map_of_mem hp
  -- A variable's tree after the call: what it kept and what the callee left at its places.
  let nf : Var → Nat → Prop := fun x z => ∃ s a L, Entry F ι σ Γ env x s a L ∧ s.excl = true ∧
    (s.shell = true → z ≠ a) ∧ (Kept L (cutsOf ps x) z ∨ ∃ c ∈ cutsOf ps x, z ∈ c.new)
  have hnf : ∀ {x s a L z}, Entry F ι σ Γ env x s a L → (nf x z ↔ s.excl = true ∧
      (s.shell = true → z ≠ a) ∧ (Kept L (cutsOf ps x) z ∨ ∃ c ∈ cutsOf ps x, z ∈ c.new)) := by
    intro x s a L z he
    constructor
    · rintro ⟨s', a', L', he', h⟩
      obtain ⟨rfl, rfl, rfl⟩ := he.det he'
      exact h
    · intro h; exact ⟨s, a, L, he, h⟩
  -- What a variable may change after the call: kept, or what the callee left at a place of it.
  have hsub : ∀ {x s a L z}, Entry F ι σ Γ env x s a L → nf x z →
      (z ∈ exclPart s L ∧ z ∈ E.filter (fun l => l ∉ mutCells (olds hs))) ∨
      ∃ p ∈ ps, p.1.root = x ∧ p.1.mode = .mut ∧ z ∈ exclPart p.1.slot p.2 := by
    intro x s a L z he h
    obtain ⟨hex, hsh, hk | ⟨c, hc, hz⟩⟩ := (hnf he).mp h
    · have hzx : z ∈ exclPart s L := (mem_exclPart_iff he.2.2).mpr ⟨hex, hk.1, hsh⟩
      rcases kept_in hI hholes hps he hk.1 hk.2 with h1 | ⟨h1, -⟩
      · exact .inl h1
      · exact absurd h1 (parts_disj he.2.2.nodup z hzx)
    · obtain ⟨p, hp, hr, hm, rfl⟩ := mem_cutsOf.mp hc
      rcases new_cases (hpsok p hp) (hnew p hp hm) hm hz with h1 | ⟨-, h1, h2⟩
      · exact .inr ⟨p, hp, hr, hm, h1⟩
      · obtain ⟨s', a', he', -⟩ := (hpsok p hp).entry
        rw [hr] at he'
        obtain ⟨rfl, rfl, hL⟩ := he.det he'
        have hzL : z ∈ L := hL ▸ (hpsok p hp).mem_tree.mpr (.inr h1)
        have hzx : z ∈ exclPart s L := (mem_exclPart_iff he.2.2).mpr ⟨hex, hzL, hsh⟩
        rcases shared_kept hI hholes hpw (hpsin p hp) h2 with h3 | h3
        · exact .inl ⟨hzx, h3⟩
        · exact absurd ((hI.foot.memE hI.keys z).mpr ⟨x, s, a, L, he, hzx⟩) (hI.disj z h3)
  obtain ⟨E', hf', hn', hmem'⟩ := hI.foot.rebuild (σ' := σ') nf hI.keys
    (by
      intro x s a L he
      by_cases hcx : cutsOf ps x = []
      · -- Nothing of it lent `mut`: kept as it was.
        refine ⟨L, he.2.2.frame (hag.mono fun l hl => ?_), rfl, fun z => ?_⟩
        · rcases kept_in hI hholes hps he hl (by simp [hcx]) with ⟨-, h⟩ | ⟨-, h⟩
          · exact List.mem_append.mpr (.inl h)
          · exact List.mem_append.mpr (.inr h)
        · rw [mem_exclPart_iff he.2.2, hnf he]
          constructor
          · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3, .inl ⟨h2, by simp [hcx]⟩⟩
          · rintro ⟨h1, h3, ⟨h2, -⟩ | ⟨c, hc, -⟩⟩
            · exact ⟨h1, h2, h3⟩
            · rw [hcx] at hc; simp at hc
      · obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hcx
        obtain ⟨p, hp, hr, hm, -⟩ := mem_cutsOf.mp hc
        obtain ⟨s', a', τr, hs', ha', hex, -, hLT, -, hso, -, huniv, -, -, hty⟩ := hpsok p hp
        rw [hr] at hs' ha'
        obtain ⟨rfl, rfl, hL⟩ := he.det ⟨hs', ha', hso⟩
        rw [← hL] at hLT
        obtain ⟨L', hL', hmem, -⟩ := root_join hI hholes hpw hps hnew hMn hag hX hSX he hLT hty []
          (by simp) (by simp) (by simp) (by simp)
        simp only [List.append_nil] at hmem
        have hso' := huniv _ σ' L' hL'
        refine ⟨L', hso', ?_, fun z => ?_⟩
        · cases hsh : s.shell
          · simp [sharedPart_plain hsh, hex hm]
          · have hnh : τr.isHole = false := match s, hsh, he.2.2 with
              | .ref .mut _, h, hso => hLT.nonhole_of hso (Ty.shell_nonhole h)
              | .half _ _ _, _, hso => hLT.nonhole_of hso Ty.lent1_isHole
            obtain ⟨R1, hR1⟩ := hL'.cons hnh
            obtain ⟨R0, hR0⟩ := hLT.cons hnh
            rw [hR1, hR0]
            simp [sharedPart, hex hm, hsh]
        · rw [mem_exclPart_iff hso', hnf he, hmem]
          constructor
          · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3, h2⟩
          · rintro ⟨h1, h3, h2⟩; exact ⟨h1, h2, h3⟩)
    (by
      intro x s a L y t b L' z hx hy hne h h'
      rcases hsub hx h with ⟨hlL, hlX⟩ | ⟨p, hp, hpr, hpm, hlp⟩ <;>
        rcases hsub hy h' with ⟨hlL', hlX'⟩ | ⟨q, hq, hqr, hqm, hlq⟩
      · exact hI.apart hx hy hne z hlL (exclPart_sub hlL')
      · exact hX z hlX (mem_mutCells.mpr ⟨q, hq, hlq⟩)
      · exact hX z hlX' (mem_mutCells.mpr ⟨p, hp, hlp⟩)
      · have hpq : p ≠ q := fun e => hne (hpr ▸ hqr ▸ e ▸ rfl)
        exact flatMap_apart (f := fun p : Hole × List Nat => exclPart p.1.slot p.2) hMn hp hq hpq z hlp hlq)
  have hto : ∀ l, l ∈ E' → l ∈ E.filter (fun l => l ∉ mutCells (olds hs)) ∨ l ∈ mutCells ps := by
    intro l hl
    obtain ⟨x, s, a, L, he, h⟩ := (hmem' l).mp hl
    rcases hsub he h with ⟨-, h1⟩ | ⟨p, hp, -, -, h1⟩
    · exact .inl h1
    · exact .inr (mem_mutCells.mpr ⟨p, hp, h1⟩)
  refine ⟨E', ⟨hf', hn', fun l hS hl => ?_, hI.keys⟩, fun l => ⟨hto l, ?_⟩⟩
  · rcases hto l hl with h | h
    · exact hI.disj l hS (mem_keep.mp h).1
    · exact hSX l hS h
  · rw [hmem']
    rintro (hlX | hlM)
    · obtain ⟨hE, hnM⟩ := mem_keep.mp hlX
      obtain ⟨x, s, a, L, he, hl⟩ := (hI.foot.memE hI.keys l).mp hE
      obtain ⟨hex, hlL, hsh⟩ := (mem_exclPart_iff he.2.2).mp hl
      refine ⟨x, s, a, L, he, (hnf he).mpr ⟨hex, hsh, ?_⟩⟩
      by_cases hk : ∃ c ∈ cutsOf ps x, l ∈ c.old
      · -- In a place lent `mut`, but not what the callee could change: the place's location.
        obtain ⟨c, hc, hlc⟩ := hk
        obtain ⟨p, hp, -, hm, rfl⟩ := mem_cutsOf.mp hc
        refine .inr ⟨_, hc, ?_⟩
        rcases mem_parts (s := p.1.slot) hlc with h1 | h1
        · exact absurd (mem_olds_mut.mpr ⟨p.1, hpsin p hp, h1⟩) hnM
        · obtain ⟨R0, hR0⟩ := (hpsok p hp).old_head
          obtain ⟨R, hR⟩ := (hnew p hp hm).cons (Ty.whole_not_hole (hpsok p hp).whole)
          rw [hR0] at h1
          have := Hole.shared_mut_head hm h1
          subst this
          show p.1.loc ∈ p.2
          rw [hR]; exact List.mem_cons_self ..
      · exact .inl ⟨hlL, fun c hc h => hk ⟨c, hc, h⟩⟩
    · obtain ⟨p, hp, hlp⟩ := mem_mutCells.mp hlM
      have hpm := (Hole.excl_mut hlp).1
      obtain ⟨s, a, he, hex⟩ := (hpsok p hp).entry
      refine ⟨p.1.root, s, a, _, he, (hnf he).mpr ⟨hex hpm, fun hsh e => ?_,
        .inr ⟨_, mem_cutsOf.mpr ⟨p, hp, rfl, hpm, rfl⟩, exclPart_sub hlp⟩⟩⟩
      -- A closure's cell borrowed `mut` is only read.
      obtain ⟨R, hR⟩ := he.2.2.cons_of_shell hsh
      have haS : a ∈ S := (hI.foot.memS hI.keys a).mpr ⟨_, s, a, _, he, by
        rw [hR]; simp [sharedPart, Slot.shell_excl hsh, hsh]⟩
      exact hSX a haS (e ▸ hlM)

end rebuild

theorem zip_fst_snd : ∀ (l : List (α × β)), (l.map Prod.fst).zip (l.map Prod.snd) = l
  | [] => rfl
  | p :: l => by simp [zip_fst_snd l]

theorem shape_fnCtx (d : Fn) : shape (fnCtx d) = ownCtx d.owns ++ refCtx d.refs := by
  simp [shape, fnCtx, ownCtx, refCtx, Slot.shape, Function.comp_def]

theorem refCtx_refs (refs : List (Var × Mode × Ty)) : ∀ p ∈ refCtx refs, ∃ m τ, p.2 = .ref m τ := by
  intro p hp
  simp only [refCtx, List.mem_map] at hp
  obtain ⟨q, -, rfl⟩ := hp
  exact ⟨_, _, rfl⟩

/-! ## A `handle`'s body: what its arm was lent, only read -/

theorem perm_front {A B L : List Nat} : (L ++ (A ++ B)).Perm (A ++ (L ++ B)) := by
  rw [← List.append_assoc, ← List.append_assoc]; exact List.perm_append_comm.append_right B

theorem perm_assoc {A B L : List Nat} : (L ++ (A ++ B)).Perm (L ++ A ++ B) :=
  List.Perm.of_eq (List.append_assoc _ _ _).symm

theorem SlotOk.ro {s : Slot} (h : SlotOk F ι σ s a L) (hs : ∀ τ, s ≠ .own τ false) : SlotOk F ι σ s.ro a L := by
  rcases s with ⟨τ, live⟩ | ⟨m, τ⟩ | ⟨τ, hd⟩ | ⟨t, A, B⟩
  · cases live
    · exact absurd rfl (hs τ)
    · exact h
  · exact h
  · exact h
  · exact h

theorem SlotOk.unro {s : Slot} (h : SlotOk F ι σ s.ro a L) (hs : ∀ τ, s ≠ .own τ false) : SlotOk F ι σ s a L := by
  rcases s with ⟨τ, live⟩ | ⟨m, τ⟩ | ⟨τ, hd⟩ | ⟨t, A, B⟩
  · cases live
    · exact absurd rfl (hs τ)
    · exact h
  · exact h
  · exact h
  · exact h

theorem Slot.ro_excl {s : Slot} : s.ro.excl = false := by
  rcases s with ⟨τ, live⟩ | ⟨m, τ⟩ | ⟨τ, hd⟩ | ⟨t, A, B⟩ <;> rfl

/-- A slot not changeable is its own `ro`. -/
theorem Slot.ro_of_excl {s : Slot} (h : s.excl = false) : s.ro = s := by
  rcases s with ⟨τ, live⟩ | ⟨m, τ⟩ | ⟨τ, hd⟩ | ⟨t, A, B⟩
  · simp [Slot.excl] at h
  · cases m
    · rfl
    · simp [Slot.excl] at h
  · rfl
  · simp [Slot.excl] at h

/-- Only read, a slot is weakened by nothing. -/
theorem Slot.Le.of_ro {s s' : Slot} (h : Slot.Le s' s.ro) : s' = s.ro := by
  rcases s with ⟨τ, live⟩ | ⟨m, τ⟩ | ⟨τ, hd⟩ | ⟨t, A, B⟩ <;> (simp only [Slot.ro] at h ⊢; cases h; rfl)

/-- The variables `ys` only read, as a `handle`'s body has them: what they owned, `Fz`, is shared
while the body runs, and given back once it ends, as it was, if nothing changed it or what the
activation only reads. -/
theorem perm_mid {A B C D : List Nat} : (A ++ B ++ (C ++ D)).Perm (A ++ C ++ (B ++ D)) := by
  simp only [List.append_assoc]
  refine List.Perm.append_left A ?_
  rw [← List.append_assoc, ← List.append_assoc]
  exact List.perm_append_comm.append_right D

/-- Two footprints of slots alike at one location: their shared parts are the same, if what they
may change is. -/
theorem SlotOk.shared_eq (h : SlotOk F ι σ s a L) (h' : SlotOk F ι σ' s' a L') (hsh : s'.shell = s.shell)
    (hex : s.excl = true) (hex' : s'.excl = true) : sharedPart s' L' = sharedPart s L := by
  cases hs : s.shell
  · rw [sharedPart_plain hs, sharedPart_plain (hsh.trans hs), if_pos hex, if_pos hex']
  · obtain ⟨R, rfl⟩ := h.head_of_shell hs
    obtain ⟨R', rfl⟩ := h'.head_of_shell (hsh.trans hs)
    simp [sharedPart, hex, hex', hs, hsh.trans hs]

/-- The variables `ys` only read, as a `handle`'s body has them: what they could change, `Fz`, is
shared while the body runs, and given back once it ends, as it was, if nothing changed it or what
the activation only reads. -/
theorem Foot.handle (h : Foot F ι σ Γ env E S) (hk : (Γ.map Prod.fst).Nodup)
    (hok : ∀ y ∈ ys, ∀ τ, lookup y Γ ≠ some (.own τ false)) :
    ∃ Eb Sb Fz, Foot F ι σ (freeze Γ ys) env Eb Sb ∧ E.Perm (Eb ++ Fz) ∧ Sb.Perm (Fz ++ S) ∧
      (∀ y s a L, Entry F ι σ Γ env y s a L → y ∈ ys → ∀ l ∈ L, l ∈ Fz ∨ l ∈ S) ∧
      ∀ W, ι.w.le W → ∀ σ' Γb Eb', Foot F (ι.inW W) σ' Γb env Eb' Sb → Weaker Γb (freeze Γ ys) →
        Agree σ σ' (Fz ++ S) → ∃ E', Foot F (ι.inW W) σ' (thaw Γ ys Γb) env E' S ∧ E'.Perm (Eb' ++ Fz) := by
  induction h with
  | nil =>
    refine ⟨[], [], [], .nil, .refl _, .refl _, fun y s a L he => absurd he.1 (by simp [lookup]), ?_⟩
    intro W hW σ' Γb Eb' hb hw _
    rw [Weaker.nil_inv hw] at hb
    cases hb
    exact ⟨[], .nil, .refl _⟩
  | @cons s a L Γ env E S x hs hrest ih =>
    simp only [List.map_cons, List.nodup_cons] at hk
    obtain ⟨hx, hk⟩ := hk
    have hok' : ∀ y ∈ ys, ∀ τ, lookup y Γ ≠ some (.own τ false) := by
      intro y hy τ h
      by_cases hyx : y = x
      · subst hyx; exact hx (lookup_some_keys h)
      · exact hok y hy τ (by simp [lookup, hyx, h])
    obtain ⟨Eb, Sb, Fz, hfb, hE, hS, hent, hthaw⟩ := ih hk hok'
    have hfr : freeze ((x, s) :: Γ) ys = (x, if x ∈ ys then s.ro else s) :: freeze Γ ys := by
      by_cases h : x ∈ ys <;> simp [freeze, h]
    have hkeys' : x ∉ (freeze Γ ys).map Prod.fst := by rw [freeze_keys]; exact hx
    -- Entries of the head and of the rest.
    have hentry : ∀ y t b L', Entry F ι σ ((x, s) :: Γ) ((x, a) :: env) y t b L' →
        (y = x ∧ t = s ∧ L' = L) ∨ (y ≠ x ∧ Entry F ι σ Γ env y t b L') := by
      intro y t b L' he
      rcases (entry_cons hx).mp he with ⟨rfl, rfl, rfl, hL⟩ | ⟨hne, he⟩
      · exact .inl ⟨rfl, rfl, hL.det hs⟩
      · exact .inr ⟨hne, he⟩
    have hroE : ∀ {L E}, addE s.ro L E = E := by simp [addE, exclPart, Slot.ro_excl]
    have hroS : ∀ {L S}, addS s.ro L S = L ++ S := by simp [addS, sharedPart, Slot.ro_excl]
    by_cases hxy : x ∈ ys
    · have hsno : ∀ τ, s ≠ .own τ false := fun τ h => hok x hxy τ (by simp [lookup, h])
      have hsro := hs.ro hsno
      -- Shared while the body runs: what it could change frozen, and owned again after.
      refine ⟨Eb, L ++ Sb, exclPart s L ++ Fz, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hfr]; simp only [hxy, ↓reduceIte]
        have := Foot.cons (x := x) hsro hfb
        rwa [hroE, hroS] at this
      · simp only [addE]
        exact (hE.append_left _).trans perm_front
      · simp only [addS]
        refine (hS.append_left L).trans ?_
        exact ((parts_perm (s := s)).append_right _).trans perm_mid
      · intro y t b L' he hy l hl
        rcases hentry y t b L' he with ⟨rfl, rfl, rfl⟩ | ⟨-, he⟩
        · rcases mem_parts (s := t) hl with h1 | h1
          · exact .inl (List.mem_append.mpr (.inl h1))
          · exact .inr (mem_addS.mpr (.inl h1))
        · rcases hent y t b L' he hy l hl with h | h
          · exact .inl (List.mem_append.mpr (.inr h))
          · exact .inr (mem_addS.mpr (.inr h))
      · intro W hW σ' Γb Eb' hb hw hag
        rw [hfr] at hw
        obtain ⟨s', Γb', rfl, hle, hw'⟩ := Weaker.cons_inv hw
        simp only [hxy, ↓reduceIte] at hle
        obtain rfl := hle.of_ro
        obtain ⟨L', Et, St, hs', hft, rfl, hSt⟩ := hb.uncons
        simp only [addS, sharedPart, Slot.ro_excl, Bool.false_eq_true, ↓reduceIte] at hSt
        have hLs : SlotOk F (ι.inW W) σ' s.ro a L := (hsro.frame (hag.mono fun l hl => by
          rcases mem_parts (s := s) hl with h1 | h1
          · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inl h1)))
          · exact List.mem_append.mpr (.inr (mem_addS.mpr (.inl h1))))).mono hW
        obtain rfl := hLs.det hs'
        obtain rfl := List.append_cancel_left hSt
        obtain ⟨E', hf', hp⟩ := hthaw W hW σ' Γb' Et hft hw' ((hag.mono fun l hl => by
          rcases List.mem_append.mp hl with h | h
          · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr h)))
          · exact List.mem_append.mpr (.inr (mem_addS.mpr (.inr h)))))
        rw [hroE]
        refine ⟨addE s L E', ?_, ?_⟩
        · rw [thaw_cons]; simp only [hxy, ↓reduceIte]
          exact Foot.cons (x := x) (hLs.unro hsno) hf'
        · simp only [addE]
          exact (hp.append_left _).trans perm_front
    · -- Not lent to the arm: as it is.
      refine ⟨addE s L Eb, addS s L Sb, Fz, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hfr]; simp only [hxy, ↓reduceIte]; exact .cons hs hfb
      · simp only [addE]; exact (hE.append_left _).trans perm_assoc
      · simp only [addS]; exact (hS.append_left _).trans perm_front
      · intro y t b L' he hy l hl
        rcases hentry y t b L' he with ⟨rfl, -, -⟩ | ⟨-, he⟩
        · exact absurd hy hxy
        · rcases hent y t b L' he hy l hl with h | h
          · exact .inl h
          · exact .inr (mem_addS.mpr (.inr h))
      · intro W hW σ' Γb Eb' hb hw hag
        rw [hfr] at hw
        obtain ⟨s', Γb', rfl, hle, hw'⟩ := Weaker.cons_inv hw
        simp only [hxy, ↓reduceIte] at hle
        obtain ⟨L', Et, St, hs', hft, rfl, hSt⟩ := hb.uncons
        have hex' : s'.excl = s.excl := hle.excl
        cases hex : s.excl
        · -- Only read: the same tree as before.
          have hle' : s = s' := by
            cases hle with
            | refl => rfl
            | forget => simp [Slot.excl] at hex
          subst hle'
          have hsh : s.shell = false := by
            cases h : s.shell
            · rfl
            · rw [Slot.shell_excl h] at hex; cases hex
          have hLs : SlotOk F (ι.inW W) σ' s a L := (hs.frame (hag.mono fun l hl => List.mem_append.mpr
            (.inr (mem_addS.mpr (.inl (by rw [sharedPart_plain hsh, if_neg (by simp [hex])]; exact hl)))))).mono hW
          obtain rfl := hLs.det hs'
          obtain rfl := List.append_cancel_left hSt
          obtain ⟨E', hf', hp⟩ := hthaw W hW σ' Γb' Et hft hw' ((hag.mono fun l hl => by
            rcases List.mem_append.mp hl with h | h
            · exact List.mem_append.mpr (.inl h)
            · exact List.mem_append.mpr (.inr (mem_addS.mpr (.inr h)))))
          refine ⟨addE s L E', ?_, ?_⟩
          · rw [thaw_cons]; simp only [hxy, ↓reduceIte]
            exact Foot.cons (x := x) hLs hf'
          · simp only [addE, exclPart, hex, Bool.false_eq_true, ↓reduceIte, List.nil_append]
            exact hp
        · have hsheq := SlotOk.shared_eq (hs.mono hW) hs' hle.shell hex (hex'.trans hex)
          simp only [addS, hsheq] at hSt
          obtain rfl := List.append_cancel_left hSt
          obtain ⟨E', hf', hp⟩ := hthaw W hW σ' Γb' Et hft hw' ((hag.mono fun l hl => by
            rcases List.mem_append.mp hl with h | h
            · exact List.mem_append.mpr (.inl h)
            · exact List.mem_append.mpr (.inr (mem_addS.mpr (.inr h)))))
          refine ⟨addE s' L' E', ?_, ?_⟩
          · rw [thaw_cons]; simp only [hxy, ↓reduceIte]
            have := Foot.cons (x := x) hs' hf'
            rwa [show ∀ X, addS s' L' X = addS s L X from fun X => by simp [addS, hsheq]] at this
          · simp only [addE]
            exact (hp.append_left _).trans perm_assoc

/-- The root of a place the code may reach has its value: it was not moved. -/
theorem PlaceTy.root_live : PlaceTy Γ p τ w y → ∀ τ', lookup y Γ ≠ some (.own τ' false)
  | .own h, τ', h' => by rw [h] at h'; cases h'
  | .ref h, τ', h' => by rw [h] at h'; cases h'
  | .half h _, τ', h' => by rw [h] at h'; cases h'
  | .deref hp, τ', h' => hp.root_live τ' h'
  | .fst hp, τ', h' => hp.root_live τ' h'
  | .snd hp, τ', h' => hp.root_live τ' h'

theorem Caps.roots_live : Caps Γ caps ys → ∀ p ∈ ys, ∀ τ, lookup p.2 Γ ≠ some (.own τ false)
  | .nil, _, h, _ => by simp at h
  | .ro hp _ hr, p, h, τ => by
    rcases List.mem_cons.mp h with rfl | h
    · exact hp.root_live τ
    · exact hr.roots_live p h τ
  | .mut hp _ _ hr, p, h, τ => by
    rcases List.mem_cons.mp h with rfl | h
    · exact hp.root_live τ
    · exact hr.roots_live p h τ

/-- The variables `ys`, in order, each changeable, with the trees they own in turn: `H`. -/
inductive Trees (F : List Fn) (ι : Iota) (σ : Store) (Γ : Ctx) (env : Env) : List Var → List Nat → Prop
  | nil : Trees F ι σ Γ env [] []
  | cons : Entry F ι σ Γ env y s a L → s.excl = true → s.shell = false → Trees F ι σ Γ env ys H →
      Trees F ι σ Γ env (y :: ys) (L ++ H)

theorem Trees.frame : Trees F ι σ Γ env ys H → Agree σ σ' H → Trees F ι σ' Γ env ys H
  | .nil, _ => .nil
  | .cons ⟨hl, ha, hs⟩ hex hsh hr, hag =>
    .cons ⟨hl, ha, hs.frame (hag.mono fun l hl => List.mem_append.mpr (.inl hl))⟩ hex hsh
      (hr.frame (hag.mono fun l hl => List.mem_append.mpr (.inr hl)))

theorem Trees.mono : Trees F ι σ Γ env ys H → ι.w.le W → Trees F (ι.inW W) σ Γ env ys H
  | .nil, _ => .nil
  | .cons ⟨hl, ha, hs⟩ hex hsh hr, hW => .cons ⟨hl, ha, hs.mono hW⟩ hex hsh (hr.mono hW)

theorem Trees.nodup_keys : Trees F ι σ Γ env ys H → ∀ y ∈ ys, ∃ s a L, Entry F ι σ Γ env y s a L
  | .nil, _, h => by simp at h
  | .cons he _ _ hr, y, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, _, _, he⟩
    · exact hr.nodup_keys y h

/-- One of the variables `ys`, its tree taken out of theirs: the rest, `Hr`, and once it holds
another tree, in a store that kept the rest, the trees of `ys` again. -/
theorem Trees.split : Trees F ι σ Γ env ys H → y ∈ ys → ys.Nodup → Entry F ι σ Γ env y s a L →
    ∃ Hr, H.Perm (L ++ Hr) ∧ ∀ W, ι.w.le W → ∀ σ' L', Agree σ σ' Hr → SlotOk F (ι.inW W) σ' s a L' →
      ∃ H', Trees F (ι.inW W) σ' Γ env ys H' ∧ H'.Perm (L' ++ Hr)
  | .nil, h, _, _ => by simp at h
  | @Trees.cons _ _ _ _ _ z s0 a0 L0 zs Hz he0 hex0 hsh0 hr, h, hn, he => by
    obtain ⟨hz, hn'⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp h with rfl | h
    · obtain ⟨rfl, rfl, rfl⟩ := he.det he0
      refine ⟨Hz, .refl _, fun W hW σ' L' hag hs' =>
        ⟨L' ++ Hz, .cons ⟨he0.1, he0.2.1, hs'⟩ hex0 hsh0 ((hr.frame hag).mono hW), .refl _⟩⟩
    · obtain ⟨Hr, hp, hre⟩ := hr.split h hn' he
      refine ⟨L0 ++ Hr, ?_, fun W hW σ' L' hag hs' => ?_⟩
      · exact (hp.append_left L0).trans perm_front
      · obtain ⟨H', ht', hp'⟩ := hre W hW σ' L' ((hag.mono fun l hl => List.mem_append.mpr (.inr hl))) hs'
        refine ⟨L0 ++ H', .cons ⟨he0.1, he0.2.1,
          (he0.2.2.frame (hag.mono fun l hl => List.mem_append.mpr (.inl hl))).mono hW⟩
          hex0 hsh0 ht', (hp'.append_left L0).trans perm_front⟩

theorem pick_mem {α : Type} {ps : List α} (k : Int) (h : ps ≠ []) : ∃ p, pick ps k = some p ∧ p ∈ ps := by
  have hlt : min k.toNat (ps.length - 1) < ps.length := by
    have : ps.length ≠ 0 := by simpa using h
    omega
  exact ⟨_, List.getElem?_eq_getElem hlt, List.getElem_mem hlt⟩

theorem Pairs.mem_left {α β : Type} {R : α → β → Prop} {as : List α} {bs : List β} {a : α} :
    Pairs R as bs → a ∈ as → ∃ b ∈ bs, R a b
  | .nil, h => by simp at h
  | .cons hr hrest, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, List.mem_cons_self .., hr⟩
    · obtain ⟨b, hb, hab⟩ := hrest.mem_left h
      exact ⟨b, List.mem_cons_of_mem _ hb, hab⟩

theorem Pairs.mem_right {α β : Type} {R : α → β → Prop} {as : List α} {bs : List β} {b : β} :
    Pairs R as bs → b ∈ bs → ∃ a ∈ as, R a b
  | .nil, h => by simp at h
  | .cons hr hrest, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨_, List.mem_cons_self .., hr⟩
    · obtain ⟨a, ha, hab⟩ := hrest.mem_right h
      exact ⟨a, List.mem_cons_of_mem _ ha, hab⟩

theorem Pairs.imp {α β : Type} {R R' : α → β → Prop} {as : List α} {bs : List β} :
    Pairs R as bs → (∀ a ∈ as, ∀ b, R a b → R' a b) → Pairs R' as bs
  | .nil, _ => .nil
  | .cons hr hrest, h => .cons (h _ (List.mem_cons_self ..) _ hr)
      (hrest.imp fun a ha => h a (List.mem_cons_of_mem _ ha))

/-- Variables, each paired with something that makes it changeable, have trees. -/
theorem Trees.of_pairs {α : Type} {R : α → Var → Prop} {as : List α} {zs : List Var} :
    Pairs R as zs → (∀ a ∈ as, ∀ z, R a z → ∃ s b L, Entry F ι σ Γ env z s b L ∧ s.excl = true ∧ s.shell = false) →
    ∃ H, Trees F ι σ Γ env zs H
  | .nil, _ => ⟨[], .nil⟩
  | .cons hr hrest, h => by
    obtain ⟨s, b, L, he, hex, hsh⟩ := h _ (List.mem_cons_self ..) _ hr
    obtain ⟨H, ht⟩ := Trees.of_pairs hrest fun a ha => h a (List.mem_cons_of_mem _ ha)
    exact ⟨L ++ H, .cons he hex hsh ht⟩

theorem roots_cons_ro : roots .mut ((.ro, y) :: ys) = roots .mut ys := by simp [roots]
theorem roots_cons_mut : roots .mut ((.mut, y) :: ys) = y :: roots .mut ys := by simp [roots]
theorem roots_cons_ro' : roots .ro ((.ro, y) :: ys) = y :: roots .ro ys := by simp [roots]
theorem roots_cons_mut' : roots .ro ((.mut, y) :: ys) = roots .ro ys := by simp [roots]

/-- The places a `handle` lends its arm, in the activation it is in: each holds a value of its
type; those lent `readonly` among the footprints of the variables they are rooted at, those lent
`mut` the trees of their variables, as they are now and as they will be. -/
theorem caps_ok (hc : Caps Γ caps ys) (hf : Foot F ι σ Γ env E S) :
    ∃ ls Rc Hc, caps.mapM (fun c => resolve σ env c.loc) = some ls ∧ ls.length = caps.length ∧
      CapsOk F ι σ (List.zipWith Cap.at caps ls) Rc Hc ∧
      (∀ l ∈ Rc, ∃ y, (.ro, y) ∈ ys ∧ ∃ s a L, Entry F ι σ Γ env y s a L ∧ l ∈ L) ∧
      Trees F ι σ Γ env (roots .mut ys) Hc ∧
      ∀ ι' σ' Rc' Hc', CapsOk F ι' σ' (List.zipWith Cap.at caps ls) Rc' Hc' → Trees F ι' σ' Γ env (roots .mut ys) Hc' := by
  induction hc with
  | nil => exact ⟨[], [], [], rfl, rfl, .nil, by simp, .nil, fun _ _ _ _ h => by cases h; exact .nil⟩
  | @ro p τ w y rest ys' x hp _ _ ih =>
    obtain ⟨ls, Rc, Hc, hmap, hlen, hcok, hin, htr, hnew⟩ := ih
    obtain ⟨a, τr, Lr, P, l, s, ha, hLr, hpath, hres, -, -, hs, hso, -, -⟩ := place_ok hp hf
    obtain ⟨R, hR, hLrp⟩ := path_split hpath hLr
    refine ⟨l :: ls, R ++ Rc, Hc, by simp [List.mapM_cons, hres, hmap], by simp [hlen], .ro hR hcok, ?_,
      by rw [roots_cons_ro]; exact htr, ?_⟩
    · intro l' hl'
      rcases List.mem_append.mp hl' with h | h
      · exact ⟨y, List.mem_cons_self .., s, a, Lr, ⟨hs, ha, hso⟩, hLrp.mem_iff.mpr (List.mem_append.mpr (.inr h))⟩
      · obtain ⟨y', hy', s', a', L', he, hl⟩ := hin l' h
        exact ⟨y', List.mem_cons_of_mem _ hy', s', a', L', he, hl⟩
    · intro ι' σ' Rc' Hc' h
      rw [roots_cons_ro]
      cases h with
      | ro _ hr => exact hnew ι' σ' _ _ hr
  | @«mut» y τ rest ys' x hp hfn hτc _ ih =>
    obtain ⟨ls, Rc, Hc, hmap, hlen, hcok, hin, htr, hnew⟩ := ih
    obtain ⟨a, τr, Lr, P, l, s, ha, hLr, hpath, hres, -, -, hs, hso, hexw, hslot, -, hty⟩ := place_ok hp hf
    obtain ⟨R, hR, -⟩ := path_split hpath hLr
    simp only [resolve] at hres
    rw [ha] at hres
    cases hres
    obtain ⟨-, rfl⟩ := hpath.self hLr (Ty.complete_not_hole hτc)
    obtain rfl := hLr.det hR
    -- A variable lent `mut` to an arm is no closure, and so no closure borrowed `mut`, and has no field
    -- lent.
    have hsh : s.shell = false := by
      cases h : s.shell
      · rfl
      · match s, h, hso with
        | .ref .mut τ', h, hso => rw [hty] at hfn; simp only [Slot.ty] at hfn; simp [Slot.shell, hfn] at h
        | .half _ _ _, _, _ => simp [hty, Slot.ty, Ty.lent1_complete] at hτc
    refine ⟨a :: ls, Rc, _ ++ Hc, by simp [List.mapM_cons, resolve, ha, hmap], by simp [hlen], .mut hR hfn hcok, ?_,
      by rw [roots_cons_mut]; exact .cons ⟨hs, ha, hso⟩ (hexw rfl) hsh htr, ?_⟩
    · intro l' hl'
      obtain ⟨y', hy', s', a', L', he, hl⟩ := hin l' hl'
      exact ⟨y', List.mem_cons_of_mem _ hy', s', a', L', he, hl⟩
    · intro ι' σ' Rc' Hc' h
      rw [roots_cons_mut]
      cases h with
      | «mut» hL _ hr => exact .cons ⟨hs, ha, hslot _ σ' _ hL⟩ (hexw rfl) hsh (hnew ι' σ' _ _ hr)

theorem lookup_freeze : lookup y (freeze Γ ys) = (lookup y Γ).map (fun s => if y ∈ ys then s.ro else s) := by
  induction Γ with
  | nil => rfl
  | cons p Γ ih =>
    obtain ⟨x, s⟩ := p
    by_cases hyx : y = x
    · subst hyx; by_cases hy : y ∈ ys <;> simp [freeze, lookup, hy]
    · by_cases hx : x ∈ ys <;> simp_all [freeze, lookup]

/-- A variable a `handle` lent its arm cannot be changed through in its body. -/
theorem PlaceTy.frozen (h : PlaceTy (freeze Γ ys) p τ w y) (hy : y ∈ ys) : w = false := by
  induction h with
  | own hx =>
    rw [lookup_freeze] at hx
    simp only [Option.map_eq_some_iff, hy, ↓reduceIte] at hx
    obtain ⟨s, -, hs⟩ := hx
    rcases s <;> simp [Slot.ro] at hs
  | ref hx =>
    rw [lookup_freeze] at hx
    simp only [Option.map_eq_some_iff, hy, ↓reduceIte] at hx
    obtain ⟨s, -, hs⟩ := hx
    rcases s with ⟨_, _⟩ | ⟨_, _⟩ | _ | ⟨_, _, _⟩
    · simp only [Slot.ro, Slot.ref.injEq] at hs; obtain ⟨rfl, -⟩ := hs; rfl
    · simp only [Slot.ro, Slot.ref.injEq] at hs; obtain ⟨rfl, -⟩ := hs; rfl
    · simp [Slot.ro] at hs
    · simp only [Slot.ro, Slot.ref.injEq] at hs; obtain ⟨rfl, -⟩ := hs; rfl
  | half hx _ =>
    rw [lookup_freeze] at hx
    simp only [Option.map_eq_some_iff, hy, ↓reduceIte] at hx
    obtain ⟨s, -, hs⟩ := hx
    rcases s <;> simp [Slot.ro] at hs
  | deref _ ih => exact ih hy
  | fst _ ih => exact ih hy
  | snd _ ih => exact ih hy

theorem hide_absent : y ∉ Γ.map Prod.fst → hide Γ y = Γ := by
  induction Γ with
  | nil => intro; rfl
  | cons p Γ ih =>
    obtain ⟨z, s⟩ := p
    intro h
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [hide, List.map_cons, List.cons.injEq]
    refine ⟨by simp [Ne.symm h.1], ih h.2⟩

theorem thaw_absent : ∀ {Γ Γb : Ctx}, y ∉ Γ.map Prod.fst → Γb.map Prod.fst = Γ.map Prod.fst →
    thaw Γ [y] Γb = Γb
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | (z, s) :: Γ, (z', s') :: Γb, hy, hk => by
    simp only [List.map_cons, List.mem_cons, not_or, List.cons.injEq] at hy hk
    rw [thaw_cons]
    simp only [List.mem_singleton, Ne.symm hy.1, ↓reduceIte, List.cons.injEq, true_and]
    exact thaw_absent hy.2 hk.2

/-- A variable lent `mut` to a borrow: what it owned, `Ly`, is the borrow's while the borrow lives,
and the variable owns again, once the borrow ends, what the borrow left there, the rest of the
activation as it was. -/
theorem Foot.hidden (h : Foot F ι σ Γ env E S) (hk : (Γ.map Prod.fst).Nodup) (he : Entry F ι σ Γ env y s a Ly)
    (hex : s.excl = true) (hsh : s.shell = false) :
    ∃ Eh, Foot F ι σ (hide Γ y) env Eh S ∧ E.Perm (Ly ++ Eh) ∧
      ∀ W, ι.w.le W → ∀ σ' Γb Eb' Ly', Foot F (ι.inW W) σ' Γb env Eb' S → Weaker Γb (hide Γ y) → Agree σ σ' S →
        SlotOk F (ι.inW W) σ' s a Ly' → ∃ E', Foot F (ι.inW W) σ' (thaw Γ [y] Γb) env E' S ∧ E'.Perm (Ly' ++ Eb') := by
  induction h with
  | nil => exact absurd he.1 (by simp [lookup])
  | @cons s0 a0 L0 Γ env E S x hs hrest ih =>
    simp only [List.map_cons, List.nodup_cons] at hk
    obtain ⟨hx, hk⟩ := hk
    rcases (entry_cons hx).mp he with ⟨rfl, rfl, rfl, hL⟩ | ⟨hne, he'⟩
    · -- The variable lent is this one.
      obtain rfl := hL.det hs
      have hhide : hide ((y, s) :: Γ) y = (y, .lent s.ty s.shell) :: Γ := by
        simp only [hide, List.map_cons, ↓reduceIte, List.cons.injEq, true_and]
        exact hide_absent hx
      have hS : ∀ {L S}, addS s L S = S := by simp [addS, sharedPart_plain hsh, hex]
      have hE : ∀ {L E}, addE s L E = L ++ E := by simp [addE, exclPart_plain hsh, hex]
      rw [hS, hE]
      refine ⟨E, ?_, .refl _, ?_⟩
      · rw [hhide]
        simpa [addE, addS, Slot.excl, exclPart, sharedPart, Slot.shell, Ty.shell, Bool.false_eq_true] using Foot.cons (s := .lent s.ty s.shell) (x := y) (L := []) (a := a) (by simp [SlotOk, hsh]) hrest
      · intro W hW σ' Γb Eb' Ly' hb hw hag hs'
        rw [hhide] at hw
        obtain ⟨s', Γb', rfl, hle, hw'⟩ := Weaker.cons_inv hw
        cases hle
        obtain ⟨L', Et, St, hL', hft, rfl, hSt⟩ := hb.uncons
        simp only [SlotOk, hsh] at hL'
        subst hL'
        simp only [addS, Slot.excl, Bool.false_eq_true, ↓reduceIte, List.nil_append, sharedPart] at hSt
        subst hSt
        refine ⟨Ly' ++ Eb', ?_, .refl _⟩
        rw [thaw_cons]
        simp only [List.mem_singleton, ↓reduceIte]
        rw [thaw_absent hx (by rw [hw'.keys])]
        have := Foot.cons (x := y) hs' hft
        rwa [hS, hE] at this
    · -- Another: as it was.
      obtain ⟨Eh, hfh, hp, hthaw⟩ := ih hk he'
      have hhide : hide ((x, s0) :: Γ) y = (x, s0) :: hide Γ y := by
        simp only [hide, List.map_cons, List.cons.injEq]
        simp [Ne.symm hne]
      refine ⟨addE s0 L0 Eh, by rw [hhide]; exact .cons hs hfh, ?_, ?_⟩
      · simp only [addE]; exact (hp.append_left _).trans perm_front
      · intro W hW σ' Γb Eb' Ly' hb hw hag hs'
        rw [hhide] at hw
        obtain ⟨s', Γb', rfl, hle, hw'⟩ := Weaker.cons_inv hw
        obtain ⟨L', Et, St, hL', hft, rfl, hSt⟩ := hb.uncons
        have hex' : s'.excl = s0.excl := hle.excl
        cases hx0 : s0.excl
        · -- Only read: the same slot, with the same tree.
          have hsame : s' = s0 := by
            cases hle with
            | refl => rfl
            | forget => simp [Slot.excl] at hx0
          subst hsame
          have hsh0 : s'.shell = false := by
            cases h : s'.shell
            · rfl
            · rw [Slot.shell_excl h] at hx0; cases hx0
          have hro : ∀ {L}, sharedPart s' L = L := by simp [sharedPart_plain hsh0, hx0]
          have hLL := ((hs.frame (hag.mono fun l hl => mem_addS.mpr (.inl (by rw [hro]; exact hl)))).mono hW).det hL'
          subst hLL
          simp only [addS, hro] at hSt
          have hSS := List.append_cancel_left hSt
          subst hSS
          obtain ⟨E', hf', hp'⟩ := hthaw W hW σ' Γb' Et Ly' hft hw' ((hag.mono fun l hl => mem_addS.mpr (.inr hl))) hs'
          refine ⟨E', ?_, by simpa [addE, exclPart, hx0] using hp'⟩
          rw [thaw_cons]
          simp only [List.mem_singleton, Ne.symm hne, ↓reduceIte]
          simpa [addE, exclPart, hx0] using Foot.cons (x := x) hL' hf'
        · have hsheq := SlotOk.shared_eq (hs.mono hW) hL' hle.shell hx0 (hex'.trans hx0)
          simp only [addS, hsheq] at hSt
          obtain rfl := List.append_cancel_left hSt
          obtain ⟨E', hf', hp'⟩ := hthaw W hW σ' Γb' Et Ly' hft hw' ((hag.mono fun l hl => mem_addS.mpr (.inr hl))) hs'
          refine ⟨addE s' L' E', ?_, ?_⟩
          · rw [thaw_cons]
            simp only [List.mem_singleton, Ne.symm hne, ↓reduceIte]
            have := Foot.cons (x := x) hL' hf'
            rwa [show ∀ X, addS s' L' X = addS s0 L0 X from fun X => by simp [addS, hsheq]] at this
          · simp only [addE]
            exact (hp'.append_left _).trans perm_front

/-- A variable's slot swapped for another of the same cell that may be changed: the rest of the
activation stands; and once the code that holds it ends, the variable may take its own slot back,
with a new footprint, the rest as that code left it. -/
theorem Foot.swap (h : Foot F ι σ Γ env E S) (hk : (Γ.map Prod.fst).Nodup) (he : Entry F ι σ Γ env y s a Ly)
    (hs' : SlotOk F ι σ s' a Ly') (hex' : s'.excl = true) (hnown : ∀ τ l, s' ≠ .own τ l)
    (hhead : ∃ R, Ly' = a :: R) :
    ∃ Er Sr E' S', Foot F ι σ (setSlot Γ y s') env E' S' ∧
      E.Perm (exclPart s Ly ++ Er) ∧ S.Perm (sharedPart s Ly ++ Sr) ∧
      E'.Perm (exclPart s' Ly' ++ Er) ∧ S'.Perm (sharedPart s' Ly' ++ Sr) ∧
      ∀ W, ι.w.le W → ∀ σ1 Γb Eb, Foot F (ι.inW W) σ1 Γb env Eb S' → Weaker Γb (setSlot Γ y s') → Agree σ σ1 Sr →
        ∃ Lb Ebr, SlotOk F (ι.inW W) σ1 s' a Lb ∧ Eb.Perm (exclPart s' Lb ++ Ebr) ∧
          ∀ Lnew, SlotOk F (ι.inW W) σ1 s a Lnew → sharedPart s Lnew = sharedPart s Ly →
            ∃ E2, Foot F (ι.inW W) σ1 (thaw Γ [y] Γb) env E2 S ∧ E2.Perm (exclPart s Lnew ++ Ebr) := by
  induction h with
  | nil => exact absurd he.1 (by simp [lookup])
  | @cons s0 a0 L0 Γ env E S x hs hrest ih =>
    simp only [List.map_cons, List.nodup_cons] at hk
    obtain ⟨hx, hk⟩ := hk
    rcases (entry_cons hx).mp he with ⟨rfl, rfl, rfl, hL⟩ | ⟨hne, he'⟩
    · -- The variable swapped is this one.
      obtain rfl := hL.det hs
      have hset : setSlot ((y, s) :: Γ) y s' = (y, s') :: Γ := setSlot_head Γ hx
      refine ⟨E, S, _, _, by rw [hset]; exact Foot.cons hs' hrest, .refl _, .refl _, .refl _, .refl _, ?_⟩
      intro W hW σ1 Γb Eb hb hw _
      rw [hset] at hw
      obtain ⟨sb, Γb', rfl, hle, hw'⟩ := Weaker.cons_inv hw
      have hsb : sb = s' := by
        cases hle with
        | refl => rfl
        | forget => exact absurd rfl (hnown _ true)
      subst hsb
      obtain ⟨Lb, Et, St, hLb, hft, rfl, hSt⟩ := hb.uncons
      have hsheq : sharedPart sb Lb = sharedPart sb Ly' := by
        cases hshb : sb.shell
        · simp [sharedPart, hex', hshb]
        · obtain ⟨R, rfl⟩ := hLb.head_of_shell hshb
          obtain ⟨R', rfl⟩ := hhead
          simp [sharedPart, hex', hshb]
      simp only [addS, hsheq] at hSt
      obtain rfl := List.append_cancel_left hSt
      refine ⟨Lb, Et, hLb, by simp [addE], fun Lnew hnew hsn => ⟨addE s Lnew Et, ?_, by simp [addE]⟩⟩
      rw [thaw_cons]
      simp only [List.mem_singleton, ↓reduceIte]
      rw [thaw_absent hx (by rw [hw'.keys])]
      have := Foot.cons (x := y) hnew hft
      rwa [show ∀ X, addS s Lnew X = addS s Ly X from fun X => by simp [addS, hsn]] at this
    · -- Another: as it was.
      obtain ⟨Er, Sr, E', S', hf', hE, hS, hE', hS', hreb⟩ := ih hk he'
      have hset : setSlot ((x, s0) :: Γ) y s' = (x, s0) :: setSlot Γ y s' := setSlot_tail Γ (Ne.symm hne)
      refine ⟨exclPart s0 L0 ++ Er, sharedPart s0 L0 ++ Sr, addE s0 L0 E', addS s0 L0 S',
        by rw [hset]; exact Foot.cons hs hf', ?_, ?_, ?_, ?_, ?_⟩
      · simp only [addE]; exact (hE.append_left _).trans perm_front
      · simp only [addS]; exact (hS.append_left _).trans perm_front
      · simp only [addE]; exact (hE'.append_left _).trans perm_front
      · simp only [addS]; exact (hS'.append_left _).trans perm_front
      · intro W hW σ1 Γb Eb hb hw hag
        rw [hset] at hw
        obtain ⟨s1, Γb', rfl, hle, hw'⟩ := Weaker.cons_inv hw
        obtain ⟨L1, Et, St, hL1, hft, rfl, hSt⟩ := hb.uncons
        -- This variable's part only read is as it was.
        have hex1 : s1.excl = s0.excl := hle.excl
        have hsheq : sharedPart s1 L1 = sharedPart s0 L0 := by
          cases hx0 : s0.excl
          · have hsame : s1 = s0 := by
              cases hle with
              | refl => rfl
              | forget => simp [Slot.excl] at hx0
            subst hsame
            have hsh0 : s1.shell = false := by
              cases h : s1.shell
              · rfl
              · rw [Slot.shell_excl h] at hx0; cases hx0
            have hro : ∀ {L}, sharedPart s1 L = L := by simp [sharedPart_plain hsh0, hx0]
            have hLL := ((hs.frame (hag.mono fun l hl => List.mem_append.mpr (.inl (by rw [hro]; exact hl)))).mono hW).det hL1
            rw [hro, hro, hLL]
          · exact SlotOk.shared_eq (hs.mono hW) hL1 hle.shell hx0 (hex1.trans hx0)
        simp only [addS, hsheq] at hSt
        obtain rfl := List.append_cancel_left hSt
        obtain ⟨Lb, Ebr, hLb, hEb, hk2⟩ := hreb W hW σ1 Γb' Et hft hw' ((hag.mono fun l hl => List.mem_append.mpr (.inr hl)))
        refine ⟨Lb, exclPart s1 L1 ++ Ebr, hLb, ?_, fun Lnew hnew hsn => ?_⟩
        · simp only [addE]; exact (hEb.append_left _).trans perm_front
        · obtain ⟨E2, hf2, hp2⟩ := hk2 Lnew hnew hsn
          refine ⟨addE s1 L1 E2, ?_, ?_⟩
          · rw [thaw_cons]
            simp only [List.mem_singleton, Ne.symm hne, ↓reduceIte]
            have := Foot.cons (x := x) hL1 hf2
            rwa [show ∀ X, addS s1 L1 X = addS s0 L0 X from fun X => by simp [addS, hsheq]] at this
          · simp only [addE]; exact (hp2.append_left _).trans perm_front

theorem lookup_hide_ne (h : z ≠ y) : lookup z (hide Γ y) = lookup z Γ := by
  induction Γ with
  | nil => rfl
  | cons p Γ ih =>
    obtain ⟨x, s⟩ := p
    by_cases hxy : x = y
    · subst hxy
      have hzx : z ≠ x := h
      simp [hide, lookup, hzx] at ih ⊢
      exact ih
    · by_cases hzx : z = x
      · subst hzx; simp [hide, lookup, hxy]
      · simp [hide, lookup, hxy, hzx] at ih ⊢; exact ih

theorem lookup_hideAll : ∀ {ys : List Var} {Γ : Ctx}, z ∉ ys → lookup z (hideAll Γ ys) = lookup z Γ
  | [], _, _ => rfl
  | y :: ys, Γ, h => by
    simp only [List.mem_cons, not_or] at h
    rw [hideAll, lookup_hideAll h.2, lookup_hide_ne h.1]

theorem Trees.hide : Trees F ι σ Γ env ys H → y ∉ ys → Trees F ι σ (hide Γ y) env ys H
  | .nil, _ => .nil
  | .cons ⟨hl, ha, hs⟩ hex hsh hr, h => by
    simp only [List.mem_cons, not_or] at h
    exact .cons ⟨by rw [lookup_hide_ne (Ne.symm h.1)]; exact hl, ha, hs⟩ hex hsh (hr.hide h.2)

/-- The variables `ys`, each changeable, hidden from the code in turn: what the code may change is
the rest; once it ends, they are given back, each with the tree it has then. -/
theorem Foot.hiddenAll : ∀ {ys : List Var} {Γ : Ctx} {E H : List Nat}, Foot F ι σ Γ env E S → (Γ.map Prod.fst).Nodup →
    Trees F ι σ Γ env ys H → ys.Nodup →
    ∃ Eh, Foot F ι σ (hideAll Γ ys) env Eh S ∧ E.Perm (H ++ Eh) ∧
      ∀ W, ι.w.le W → ∀ σ' Γb Eb' H', Foot F (ι.inW W) σ' Γb env Eb' S → Weaker Γb (hideAll Γ ys) → Agree σ σ' S →
        Trees F (ι.inW W) σ' Γ env ys H' → ∃ E', Foot F (ι.inW W) σ' (unhideAll Γ ys Γb) env E' S ∧ E'.Perm (H' ++ Eb')
  | [], Γ, E, H, h, _, ht, _ => by
    cases ht
    refine ⟨E, h, .refl _, fun W hW σ' Γb Eb' H' hb _ _ ht' => ?_⟩
    cases ht'
    exact ⟨Eb', hb, .refl _⟩
  | y :: ys, Γ, E, H, h, hk, ht, hn => by
    obtain ⟨hy, hn⟩ := List.nodup_cons.mp hn
    cases ht with
    | @cons _ s a L _ Hr he hex hsh hr =>
    obtain ⟨Eh1, hf1, hp1, hre1⟩ := h.hidden hk he hex hsh
    obtain ⟨Eh, hf, hp, hre⟩ := Foot.hiddenAll hf1 (by rw [hide_keys]; exact hk) (hr.hide hy) hn
    refine ⟨Eh, hf, hp1.trans ((hp.append_left L).trans (by simp)), ?_⟩
    intro W hW σ' Γb Eb' H' hb hw hag ht'
    cases ht' with
    | @cons _ s' a' L' _ Hr' he' _ _ hr' =>
    obtain ⟨rfl, rfl⟩ : s' = s ∧ a' = a := by
      obtain ⟨h1, h2, -⟩ := he
      obtain ⟨h1', h2', -⟩ := he'
      rw [h1] at h1'; rw [h2] at h2'
      exact ⟨(Option.some.inj h1').symm, (Option.some.inj h2').symm⟩
    obtain ⟨E1', hf1', hp1'⟩ := hre W hW σ' Γb Eb' Hr' hb hw hag (hr'.hide hy)
    obtain ⟨E', hf', hp'⟩ := hre1 W hW σ' _ E1' L' hf1' (unhideAll_weaker hw) hag he'.2.2
    exact ⟨E', hf', hp'.trans ((hp1'.append_left L').trans (by simp))⟩

theorem shape_length (Γ : Ctx) : (shape Γ).length = Γ.length := by simp [shape]

theorem shape_append (A B : Ctx) : shape (A ++ B) = shape A ++ shape B := by simp [shape]

/-- Variables only read: what an arm's `handle` lent it. -/
theorem zipWith_at_name : ∀ {caps : List (Cap Place)} {ls : List Nat}, ls.length = caps.length →
    (List.zipWith Cap.at caps ls).map Cap.name = caps.map Cap.name
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [List.zipWith_cons_cons, Cap.at, zipWith_at_name h]

theorem zipWith_at_sig : ∀ {caps : List (Cap Place)} {ls : List Nat}, ls.length = caps.length →
    (List.zipWith Cap.at caps ls).map Cap.sig = caps.map Cap.sig
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [List.zipWith_cons_cons, Cap.at, Cap.sig, zipWith_at_sig h]

/-- Under `Exclusive`, a variable lent `mut` is lent once, and not also `readonly`. -/
theorem Exclusive.roots_ok : ∀ {ys : List (Mode × Var)}, Exclusive ys →
    (roots .mut ys).Nodup ∧ ∀ y ∈ roots .ro ys, y ∉ roots .mut ys
  | [], _ => ⟨List.nodup_nil, by simp [roots]⟩
  | (m, y) :: ys, h => by
    simp only [Exclusive, List.pairwise_cons] at h
    obtain ⟨hy, hys⟩ := h
    obtain ⟨ih1, ih2⟩ := Exclusive.roots_ok hys
    have hmem : ∀ m', y ∈ roots m' ys → (m', y) ∈ ys := fun m' h => by
      simp only [roots, List.mem_map, List.mem_filter] at h
      obtain ⟨⟨m'', y'⟩, ⟨h1, h2⟩, rfl⟩ := h
      simp only [decide_eq_true_eq] at h2
      subst h2; exact h1
    cases m with
    | ro =>
      refine ⟨by rw [roots_cons_ro]; exact ih1, fun z hz hz' => ?_⟩
      rw [roots_cons_ro] at hz'
      rw [roots_cons_ro'] at hz
      rcases List.mem_cons.mp hz with rfl | hz
      · have := hy _ (hmem _ hz') rfl; cases this.2
      · exact ih2 z hz hz'
    | «mut» =>
      refine ⟨by
        rw [roots_cons_mut]
        exact List.nodup_cons.mpr ⟨(fun h => by have := hy _ (hmem _ h) rfl; cases this.1), ih1⟩, ?_⟩
      intro z hz hz'
      rw [roots_cons_mut'] at hz
      rw [roots_cons_mut] at hz'
      rcases List.mem_cons.mp hz' with rfl | hz'
      · have := hy _ (hmem _ hz) rfl; cases this.1
      · exact ih2 z hz hz'

theorem Entry.to_hidden (h : Entry F ι σ Γ env y s a L) (hy : y ∉ ys) : Entry F ι σ (hideAll Γ ys) env y s a L :=
  ⟨by rw [lookup_hideAll hy]; exact h.1, h.2.1, h.2.2⟩

theorem mem_roots {m : Mode} : y ∈ roots m ys ↔ (m, y) ∈ ys := by
  simp only [roots, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨m', y'⟩, ⟨h1, rfl⟩, rfl⟩; exact h1
  · intro h; exact ⟨(m, y), ⟨h, rfl⟩, rfl⟩

/-- The places a `handle` lent its arm, as the arm's variables: borrows, each as it was lent. -/
def capCtx (caps : List (Var × Mode × Ty)) : Ctx := caps.map fun c => (c.1, Slot.ref c.2.1 c.2.2)

/-- A context of borrows only. -/
def RefCtx (Γ : Ctx) : Prop := ∀ p ∈ Γ, ∃ m τ, p.2 = .ref m τ

theorem RefCtx.shape (h : RefCtx Γ) : shape Γ = Γ := by
  induction Γ with
  | nil => rfl
  | cons p Γ ih =>
    obtain ⟨m, τ, hp⟩ := h p (List.mem_cons_self ..)
    obtain ⟨x, s⟩ := p
    simp only at hp
    subst hp
    simp only [FlyCore.Ownership.shape, List.map_cons, Slot.shape] at ih ⊢
    rw [ih fun q hq => h q (List.mem_cons_of_mem _ hq)]

theorem capCtx_ref : RefCtx (capCtx caps) := by
  intro p hp
  simp only [capCtx, List.mem_map] at hp
  obtain ⟨q, -, rfl⟩ := hp
  exact ⟨_, _, rfl⟩

/-- What a frame's arm is lent, as the footprint of its variables: those lent `mut` its own, those
lent `readonly` read. -/
theorem CapsOk.foot : CapsOk F ι σ caps R H → Foot F ι σ (capCtx (caps.map Cap.sig)) (caps.map fun c => (c.name, c.loc)) H R
  | .nil => .nil
  | @CapsOk.ro _ _ _ a τ L rest R' H' x hL hr => by
    have := Foot.cons (s := .ref .ro τ) (x := x) (env := rest.map fun c => (c.name, c.loc)) hL hr.foot
    simpa [capCtx, Cap.sig, addE, addS, Slot.excl, exclPart, sharedPart] using this
  | @CapsOk.mut _ _ _ a τ L rest R' H' x hL hfn hr => by
    have := Foot.cons (s := .ref .mut τ) (x := x) (env := rest.map fun c => (c.name, c.loc)) hL hr.foot
    simpa [capCtx, Cap.sig, addE, addS, Slot.excl, exclPart_plain (s := .ref .mut τ) (by simp [Slot.shell_ref, hfn]),
      sharedPart_plain (s := .ref .mut τ) (by simp [Slot.shell_ref, hfn])] using this

/-- The places an arm was lent `mut` are no closures. -/
def CapsFns (caps : List (Cap Nat)) : Prop := ∀ c ∈ caps, c.mode = .mut → c.ty.shell = false

theorem CapsOk.fns : CapsOk F ι σ caps R H → CapsFns caps
  | .nil => fun _ h => by simp at h
  | .ro _ hr => fun c hc hm => by
    rcases List.mem_cons.mp hc with rfl | hc
    · cases hm
    · exact hr.fns c hc hm
  | .mut _ hfn hr => fun c hc hm => by
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hfn
    · exact hr.fns c hc hm

/-- And back: the footprint of an arm's captured variables is its frame's state. -/
theorem Foot.capsOk : ∀ {caps : List (Cap Nat)} {E S}, CapsFns caps →
    Foot F ι σ (capCtx (caps.map Cap.sig)) (caps.map fun c => (c.name, c.loc)) E S → CapsOk F ι σ caps S E
  | [], _, _, _, h => by cases h; exact .nil
  | ⟨x, m, τ, a⟩ :: caps, _, _, hfn, h => by
    simp only [capCtx, Cap.sig, List.map_cons] at h
    have hfn' : CapsFns caps := fun c hc => hfn c (List.mem_cons_of_mem _ hc)
    cases h with
    | cons hs hrest =>
      cases m with
      | ro => simpa [addE, addS, Slot.excl, exclPart, sharedPart] using CapsOk.ro (x := x) hs (Foot.capsOk hfn' hrest)
      | «mut» =>
        have hf : τ.shell = false := hfn _ (List.mem_cons_self ..) rfl
        simpa [addE, addS, Slot.excl, exclPart_plain (s := .ref .mut τ) (by simp [Slot.shell_ref, hf]),
          sharedPart_plain (s := .ref .mut τ) (by simp [Slot.shell_ref, hf])] using CapsOk.mut (x := x) hs hf (Foot.capsOk hfn' hrest)

theorem armCtx_eq : armCtx os rs op caps =
    fnCtx { owns := os.zip op.owns, refs := rs.zip op.refs, ret := op.ret, row := r, body := arm } ++ capCtx caps := by
  simp [armCtx, fnCtx, capCtx]

end FlyCore.Ownership
