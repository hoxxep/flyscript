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
inductive CapsOk (F : List Fn) (σ : Store) : List (Cap Nat) → List Nat → List Nat → Prop
  | nil : CapsOk F σ [] [] []
  | ro : LT F σ a τ L → CapsOk F σ rest R H → CapsOk F σ (⟨x, .ro, τ, a⟩ :: rest) (L ++ R) H
  | mut : LT F σ a τ L → CapsOk F σ rest R H → CapsOk F σ (⟨x, .mut, τ, a⟩ :: rest) R (L ++ H)

/-! ## Variables perhaps moved -/

theorem Slot.Le.excl : Slot.Le s' s → s'.excl = s.excl
  | .refl => rfl
  | .forget => rfl

theorem SlotOk.weaken : Slot.Le s' s → SlotOk F σ s a L → SlotOk F σ s' a L
  | .refl, h => h
  | .forget, h => .inr h

theorem Weaker.refl : ∀ Γ : Ctx, Weaker Γ Γ
  | [] => .nil
  | (_, _) :: Γ => .cons .refl (Weaker.refl Γ)

theorem Slot.Le.trans : Slot.Le s₁ s₂ → Slot.Le s₂ s₃ → Slot.Le s₁ s₃
  | .refl, h => h
  | h, .refl => h

theorem Weaker.trans : Weaker Γ₁ Γ₂ → Weaker Γ₂ Γ₃ → Weaker Γ₁ Γ₃
  | .nil, .nil => .nil
  | .cons h₁ w₁, .cons h₂ w₂ => .cons (h₁.trans h₂) (w₁.trans w₂)

theorem Foot.weaken : Foot F σ Γ env E S → Weaker Γ' Γ → Foot F σ Γ' env E S := by
  intro h
  induction h generalizing Γ' with
  | nil => intro w; cases w; exact .nil
  | @cons s a L Γ env E S x hs _ ih =>
    intro w
    cases w with
    | cons hle w =>
      have := Foot.cons (x := x) (hs.weaken hle) (ih w)
      simp only [addE, addS, hle.excl] at this ⊢
      exact this

theorem Inv.weaken (h : Inv F σ Γ env E S) (w : Weaker Γ' Γ) : Inv F σ Γ' env E S :=
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

theorem thaw_weaker_lend : Weaker Γb (lendCtx m Γ y) → Weaker (thaw Γ [y] Γb) Γ := by
  cases m
  · exact thaw_weaker
  · exact thaw_weaker_hide

/-- What the code the variables `ys` were hidden from leaves, them given back. -/
theorem unhideAll_weaker : ∀ {Γ Γb : Ctx} {ys : List Var}, Weaker Γb (hideAll Γ ys) → Weaker (unhideAll Γ ys Γb) Γ
  | _, _, [], h => h
  | Γ, _, y :: ys, h => thaw_weaker_hide (unhideAll_weaker (Γ := hide Γ y) (ys := ys) h)

theorem atom_weaker : AtomTy Γ a τ Γ' → (Γ.map Prod.fst).Nodup → Weaker Γ' Γ
  | .lit, _ => Weaker.refl _
  | .read _, _ => Weaker.refl _
  | .move hx, hk => setSlot_weaker hk hx .forget

theorem atoms_weaker : AtomsTy Γ as τs Γ' → (Γ.map Prod.fst).Nodup → Weaker Γ' Γ
  | .nil, _ => Weaker.refl _
  | .cons ha hrest, hk => (atoms_weaker hrest (by rw [atom_keys ha]; exact hk)).trans (atom_weaker ha hk)

/-- Typing only ever moves: what an expression leaves is what it found, some owned variables perhaps
moved. -/
theorem typed_weaker : Typed F O Γ e τ Γ' r → (Γ.map Prod.fst).Nodup → Weaker Γ' Γ
  | .atom ha, hk => atom_weaker ha hk
  | .add ha hb, hk => (atom_weaker hb (by rw [atom_keys ha]; exact hk)).trans (atom_weaker ha hk)
  | .new ha, hk => atom_weaker ha hk
  | .let_ hx ha hb, hk => by
    have := typed_weaker hb (List.nodup_cons.mpr ⟨by rw [typed_keys ha]; exact lookup_none_keys hx,
      by rw [typed_keys ha]; exact hk⟩)
    cases this with
    | cons _ w => exact w.trans (typed_weaker ha hk)
  | .write ha _, hk => atom_weaker ha hk
  | .assign ha _, hk => atom_weaker ha hk
  | .call _ _ _ hargs _ _, hk => atoms_weaker hargs hk
  | .lendCall _ _ _ hargs _ _ _ _ hx hb, hk => by
    have hk₁ := hk
    rw [← atoms_keys hargs] at hk₁
    have := typed_weaker hb (List.nodup_cons.mpr ⟨by rw [lendCtx_keys]; exact lookup_none_keys hx,
      by rw [lendCtx_keys]; exact hk₁⟩)
    cases this with
    | cons _ w => exact (thaw_weaker_lend w).trans (atoms_weaker hargs hk)
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
  | .lend hx _ _ hb, hk => by
    have := typed_weaker hb (List.nodup_cons.mpr ⟨by rw [lendCtx_keys]; exact lookup_none_keys hx,
      by rw [lendCtx_keys]; exact hk⟩)
    cases this with
    | cons _ w => exact thaw_weaker_lend w
  | .perform _ _ hargs _ _, hk => atoms_weaker hargs hk
  | .handle _ _ _ _ _ _ _ hb, hk =>
    unhideAll_weaker (thaw_weaker (typed_weaker hb (by rw [freeze_keys, hideAll_keys]; exact hk)))
  | .handleAbort _ _ _ hx hb hh, hk => by
    have := typed_weaker hh (List.nodup_cons.mpr ⟨by exact lookup_none_keys hx,
      by rw [typed_keys hb]; exact hk⟩)
    cases this with
    | cons _ w => exact w.trans (typed_weaker hb hk)

/-- A function's context: its owned parameters, live, then its borrowed ones. -/
def fnCtx (d : Fn) : Ctx :=
  d.owns.map (fun p => (p.1, Slot.own p.2 true)) ++ d.refs.map (fun p => (p.1, Slot.ref p.2.1 p.2.2))

/-- A function whose parameters are named apart and whose body has its result type, performing
only what its row names; or, for one that returns a borrow, whose body ends where the place it
returns is one of its result type, rooted at the borrowed parameter it says, and changeable if the
borrow is `mut`. -/
def FnOk (F : List Fn) (O : List Op) (d : Fn) : Prop :=
  ((d.owns.map Prod.fst) ++ (d.refs.map Prod.fst)).Nodup ∧
  match d.retp with
  | none => ∃ Γ', Typed F O (fnCtx d) d.body d.ret Γ' d.row
  | some (m, i, p) => ∃ Γ' x mi τi w, Typed F O (fnCtx d) d.body .int Γ' d.row ∧
      d.refs[i]? = some (x, mi, τi) ∧ PlaceTy Γ' p d.ret w x ∧ (m = .mut → w = true)

def FnsOk (F : List Fn) (O : List Op) : Prop := ∀ d ∈ F, FnOk F O d

/-! ## Steps that keep what they do not own -/

/-- Cells that were allocated and outside the footprint are as they were. -/
theorem Moves.keeps (h : Moves σ E σ' E' L) (hwf : WF σ) (hX : ∀ l ∈ X, σ.mem l ≠ none)
    (hd : Disj X E) : Agree σ σ' X :=
  fun l hl => h.frame l (hwf l (hX l hl)) (hd l hl)

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
    (hE : ∀ l ∈ E, σ.mem l ≠ none) (hE' : ∀ l, l ∈ E' ↔ l ∈ E ∨ (σ.next ≤ l ∧ l < σ'.next)) :
    Moves σ E σ' E' [] where
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
  within := fun l hl => (h.within l hl).imp_left (hE l).mp
  next := h.next
  wf := h.wf
  frame := fun l hl hn => h.frame l hl fun h' => hn ((hE l).mp h')
  alloc := fun l => by rw [h.alloc l, hE l]

theorem CapsOk.frame : CapsOk F σ caps R H → Agree σ σ' (R ++ H) → CapsOk F σ' caps R H
  | .nil, _ => .nil
  | .ro hL hr, hag => .ro (hL.frame fun l hl => hag l (by simp [hl]))
      (hr.frame fun l hl => hag l (by rcases List.mem_append.mp hl with h | h <;> simp [h]))
  | .mut hL hr, hag => .mut (hL.frame fun l hl => hag l (by simp [hl]))
      (hr.frame fun l hl => hag l (by rcases List.mem_append.mp hl with h | h <;> simp [h]))

theorem CapsOk.alloc : CapsOk F σ caps R H → ∀ l ∈ R ++ H, σ.mem l ≠ none
  | .nil, _, h => by simp at h
  | .ro hL hr, l, h => by
    simp only [List.mem_append, or_assoc] at h
    rcases h with h | h
    · exact hL.alloc l h
    · exact hr.alloc l (List.mem_append.mpr h)
  | .mut hL hr, l, h => by
    simp only [List.mem_append] at h
    rcases h with h | h | h
    · exact hr.alloc l (List.mem_append.mpr (.inl h))
    · exact hL.alloc l h
    · exact hr.alloc l (List.mem_append.mpr (.inr h))

/-- What a frame's arm only reads is as it was, wherever the store agrees on it. -/
theorem CapsOk.det_ro : CapsOk F σ caps R H → CapsOk F σ' caps R' H' → Agree σ σ' R → R' = R
  | .nil, .nil, _ => rfl
  | .ro hL hr, .ro hL' hr', hag => by
    obtain rfl := (hL.frame fun l hl => hag l (by simp [hl])).det hL'
    rw [hr.det_ro hr' fun l hl => hag l (by simp [hl])]
  | .mut _ hr, .mut _ hr', hag => hr.det_ro hr' hag

/-! ## Owned arguments -/

/-- Values of the given types, each owning its cells. -/
inductive Vals (F : List Fn) (σ : Store) : List Ty → List Val → List (List Nat) → Prop
  | nil : Vals F σ [] [] []
  | cons : VT F σ τ v L → Vals F σ τs vs Ls → Vals F σ (τ :: τs) (v :: vs) (L :: Ls)

theorem Vals.frame : Vals F σ τs vs Ls → Agree σ σ' Ls.flatten → Vals F σ' τs vs Ls := by
  intro h hag
  induction h with
  | nil => exact .nil
  | cons hv _ ih =>
    simp only [List.flatten_cons] at hag
    exact .cons (hv.frame fun l hl => hag l (List.mem_append.mpr (.inl hl)))
      (ih fun l hl => hag l (List.mem_append.mpr (.inr hl)))

theorem Vals.alloc : Vals F σ τs vs Ls → ∀ l ∈ Ls.flatten, σ.mem l ≠ none := by
  intro h
  induction h with
  | nil => simp
  | cons hv _ ih =>
    intro l hl
    rcases List.mem_append.mp (List.flatten_cons ▸ hl) with hl | hl
    · exact hv.alloc l hl
    · exact ih l hl

theorem Vals.length : Vals F σ τs vs Ls → vs.length = τs.length := by
  intro h
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-! ## Binding the owned parameters -/

def ownCtx (ps : List (Var × Ty)) : Ctx := ps.map fun p => (p.1, Slot.own p.2 true)

/-- Each owned argument in a fresh cell: the cells, and what the values owned, are the footprint of
the callee's owned parameters. -/
theorem allocAll_ok : ∀ {σ : Store} {names : List Var} {τs vs Ls}, Vals F σ τs vs Ls →
    names.length = τs.length → WF σ → Ls.flatten.Nodup →
    ∃ Eo, Foot F (allocAll σ (names.zip vs)).2 (ownCtx (names.zip τs)) (allocAll σ (names.zip vs)).1 Eo [] ∧
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
          (hvs.frame fun l hl => hag l (List.mem_append.mpr (.inr hl))) (by simpa using hl) hwf.alloc hnLs
      simp only [List.zip_cons_cons, allocAll]
      have hn1 : (σ.alloc v).2.next = σ.next + 1 := rfl
      have hc : (σ.alloc v).1 = σ.next := rfl
      rw [hc]
      generalize hr : allocAll (σ.alloc v).2 (names.zip vs) = r at hf hmem hle hwf2 hold hnew hlen
      obtain ⟨cells, σ2⟩ := r
      dsimp only at hf hmem hle hwf2 hold hnew hlen ⊢
      have hcL : σ.next ∉ L := fun h => Nat.lt_irrefl _ (hlow _ (List.mem_append.mpr (.inl h)))
      have hLt : LT F σ2 σ.next τ (σ.next :: L) := by
        refine (LT.of_contents (by simp [Store.alloc]) (hv.frame fun l hl => hag l
          (List.mem_append.mpr (.inl hl))) hcL).frame fun l hl => hold l ?_
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
        simpa [ownCtx, addE, addS, Slot.excl] using this
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
  | .lent τ => .lent τ

def shape (Γ : Ctx) : Ctx := Γ.map fun p => (p.1, p.2.shape)

theorem Slot.Le.shape : Slot.Le s' s → s'.shape = s.shape
  | .refl => rfl
  | .forget => rfl

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
  | a :: A, [], h, _ => by simp [shape] at h
  | a :: A, g :: Γ, h, hB => by
    simp only [shape, List.map_cons, List.cons_append, List.cons.injEq] at h
    obtain ⟨Γa, rfl, hΓa⟩ := shape_split A h.2 hB
    exact ⟨g :: Γa, rfl, by simp only [shape, List.map_cons] at hΓa ⊢; rw [hΓa, h.1]⟩

/-! ## Dropping the owned parameters -/

/-- Dropping the callee's owned parameters, live or moved, frees exactly their footprints. -/
theorem dropCells_ok : ∀ {Γo : Ctx} {σ : Store} {eo : Env} {Eo So} {owns : List (Var × Ty)},
    Foot F σ Γo eo Eo So → shape Γo = ownCtx owns → Eo.Nodup →
    So = [] ∧ ∃ σ', dropCells σ ((owns.map Prod.snd).zip (eo.map Prod.snd)) = some σ' ∧
      σ'.next = σ.next ∧ (∀ l ∈ Eo, σ'.mem l = none) ∧ ∀ l, l ∉ Eo → σ'.mem l = σ.mem l
  | [], σ, _, _, _, owns, h, hs, _ => by
    cases h
    cases owns with
    | nil => exact ⟨rfl, σ, by simp [dropCells], rfl, by simp, fun _ _ => rfl⟩
    | cons => simp [shape, ownCtx] at hs
  | (z, r) :: Γo, σ, _, _, _, owns, h, hs, hn => by
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
    | own τ live =>
    simp only [Slot.shape, Slot.own.injEq] at hrs
    obtain ⟨rfl, -⟩ := hrs
    simp only [addE, addS, Slot.excl, ↓reduceIte] at hn ⊢
    obtain ⟨hnM, hnE, hdME⟩ := nodup_append_disj.mp hn
    obtain ⟨σ1, hd1, hn1, hfree1, hkeep1⟩ := dropCell_own hr
    obtain ⟨rfl, -⟩ := dropCells_ok hrest hs hnE
    have hrest1 := hrest.frame (σ' := σ1) fun l hl => hkeep1 l fun h => hdME l h (by simpa using hl)
    obtain ⟨-, σ', hd', hn', hfree', hkeep'⟩ := dropCells_ok hrest1 hs hnE
    refine ⟨rfl, σ', ?_, by rw [hn', hn1], ?_, ?_⟩
    · simp only [List.map_cons, List.zip_cons_cons, dropCells, hd1, hd']
    · intro l hl
      rcases List.mem_append.mp hl with hl | hl
      · rw [hkeep' l fun h => hdME l hl h]; exact hfree1 l hl
      · exact hfree' l hl
    · intro l hl
      simp only [List.mem_append, not_or] at hl
      rw [hkeep' l hl.2, hkeep1 l hl.1]

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

def HoleOk (F : List Fn) (σ : Store) (Γ : Ctx) (env : Env) (h : Hole) : Prop :=
  ∃ s a τr, lookup h.root Γ = some s ∧ lookup h.root env = some a ∧ (h.mode = .mut → s.excl = true) ∧
    Path σ a τr h.path h.loc h.ty ∧ LT F σ a τr (h.path ++ h.old) ∧ SlotOk F σ s a (h.path ++ h.old) ∧
    LT F σ h.loc h.ty h.old ∧ ∀ σ' L', LT F σ' a τr L' → SlotOk F σ' s a L'

theorem HoleOk.entry (h : HoleOk F σ Γ env hl) :
    ∃ s a, Entry F σ Γ env hl.root s a (hl.path ++ hl.old) ∧ (hl.mode = .mut → s.excl = true) :=
  let ⟨s, a, _, hs, ha, hm, _, _, hso, _⟩ := h
  ⟨s, a, ⟨hs, ha, hso⟩, hm⟩

/-- The places a call lends denote locations, each a hole in its root's tree. -/
theorem lends_ok : Lends Γ lent ts ys → Foot F σ Γ env E S →
    ∃ hs : List Hole, hs.map (fun h => (h.mode, h.ty)) = ts ∧ hs.map (fun h => (h.mode, h.root)) = ys ∧
      lent.mapM (fun x => resolve σ env x.2) = some (hs.map Hole.loc) ∧ ∀ h ∈ hs, HoleOk F σ Γ env h := by
  intro hl hf
  induction hl with
  | nil => exact ⟨[], rfl, rfl, rfl, by simp⟩
  | @cons p τ w y m rest ts ys hp hw _ ih =>
    obtain ⟨hs, h1, h2, h3, h4⟩ := ih
    obtain ⟨a, τr, Lr, P, l, s, ha, hLr, hpath, hres, -, -, hs', hso, hex, hlt⟩ := place_ok hp hf
    obtain ⟨R, hR, rfl⟩ := path_split hpath hLr
    refine ⟨⟨m, τ, y, l, P, R⟩ :: hs, by simp [h1], by simp [h2], ?_, ?_⟩
    · simp [List.mapM_cons, hres, h3]
    · intro h hh
      rcases List.mem_cons.mp hh with rfl | hh
      · exact ⟨s, a, τr, hs', ha, fun hm => hex (hw hm), hpath, hLr, hso, hR, hlt⟩
      · exact h4 h hh

def refCtx (refs : List (Var × Mode × Ty)) : Ctx := refs.map fun p => (p.1, Slot.ref p.2.1 p.2.2)

/-- The cells of the trees lent `mut`, and of those lent `readonly`. -/
def mutCells (ps : List (Hole × List Nat)) : List Nat :=
  ps.flatMap fun p => if p.1.mode = .mut then p.2 else []

def roCells (ps : List (Hole × List Nat)) : List Nat :=
  ps.flatMap fun p => if p.1.mode = .mut then [] else p.2

theorem mem_mutCells : l ∈ mutCells ps ↔ ∃ p ∈ ps, p.1.mode = .mut ∧ l ∈ p.2 := by
  simp only [mutCells, List.mem_flatMap]
  constructor
  · rintro ⟨p, hp, hl⟩; split at hl
    · exact ⟨p, hp, ‹_›, hl⟩
    · simp at hl
  · rintro ⟨p, hp, hm, hl⟩; exact ⟨p, hp, by simp [hm, hl]⟩

theorem mem_roCells : l ∈ roCells ps ↔ ∃ p ∈ ps, p.1.mode = .ro ∧ l ∈ p.2 := by
  simp only [roCells, List.mem_flatMap]
  constructor
  · rintro ⟨p, hp, hl⟩; split at hl
    · simp at hl
    · exact ⟨p, hp, by cases h : p.1.mode <;> simp_all, hl⟩
  · rintro ⟨p, hp, hm, hl⟩; exact ⟨p, hp, by simp [hm, hl]⟩

/-- The callee's borrowed parameters, bound to the holes: each holds the tree at its hole. -/
theorem foot_refs : ∀ {refs : List (Var × Mode × Ty)} {hs : List Hole} {E S : List Nat},
    refs.map Prod.snd = hs.map (fun h => (h.mode, h.ty)) →
    (Foot F σ (refCtx refs) ((refs.map Prod.fst).zip (hs.map Hole.loc)) E S ↔
      ∃ ps : List (Hole × List Nat), ps.map Prod.fst = hs ∧ (∀ p ∈ ps, LT F σ p.1.loc p.1.ty p.2) ∧
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
        refine ⟨(h, L) :: ps, by simp [h1], ?_, ?_, ?_⟩
        · intro p hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact hs'
          · exact h2 p hp
        · cases hm : h.mode <;> simp [addE, Slot.excl, mutCells, hm]
        · cases hm : h.mode <;> simp [addS, Slot.excl, roCells, hm]
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
        cases hm : hh.mode <;> simpa [refCtx, addE, addS, Slot.excl, mutCells, roCells, hm] using this

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

/-- Two holes rooted at one variable are both `readonly`. -/
def Apart (h h' : Hole) : Prop := h.root = h'.root → h.mode = .ro ∧ h'.mode = .ro

theorem Apart.symm : Apart h h' → Apart h' h := fun h e => (h e.symm).symm

/-- The trees as they were at the holes. -/
def olds (hs : List Hole) : List (Hole × List Nat) := hs.map fun h => (h, h.old)

theorem mem_olds_mut : l ∈ mutCells (olds hs) ↔ ∃ h ∈ hs, h.mode = .mut ∧ l ∈ h.old := by
  rw [mem_mutCells]
  simp only [olds, List.mem_map]
  constructor
  · rintro ⟨_, ⟨h, hh, rfl⟩, hm, hl⟩; exact ⟨h, hh, hm, hl⟩
  · rintro ⟨h, hh, hm, hl⟩; exact ⟨_, ⟨h, hh, rfl⟩, hm, hl⟩

theorem mem_olds_ro : l ∈ roCells (olds hs) ↔ ∃ h ∈ hs, h.mode = .ro ∧ l ∈ h.old := by
  rw [mem_roCells]
  simp only [olds, List.mem_map]
  constructor
  · rintro ⟨_, ⟨h, hh, rfl⟩, hm, hl⟩; exact ⟨h, hh, hm, hl⟩
  · rintro ⟨h, hh, hm, hl⟩; exact ⟨_, ⟨h, hh, rfl⟩, hm, hl⟩

/-- A hole's tree is in the caller's footprints, the exclusive ones if it is lent `mut`. -/
theorem hole_in (hI : Inv F σ Γ env E S) (hok : HoleOk F σ Γ env h) :
    ∀ l ∈ h.path ++ h.old, (h.mode = .mut → l ∈ E) ∧ (l ∈ E ∨ l ∈ S) := by
  intro l hl
  obtain ⟨s, a, he, hm⟩ := hok.entry
  rcases hI.entry_sub he l hl with ⟨-, h1⟩ | ⟨hs, h1⟩
  · exact ⟨fun _ => h1, .inl h1⟩
  · exact ⟨fun h' => (by rw [hm h'] at hs; cases hs), .inr h1⟩

/-- Holes rooted at different variables, one of them lent `mut`, are apart. -/
theorem hole_apart (hI : Inv F σ Γ env E S) (hok : HoleOk F σ Γ env h) (hok' : HoleOk F σ Γ env h')
    (hr : h.root ≠ h'.root) (hm : h.mode = .mut) : Disj (h.path ++ h.old) (h'.path ++ h'.old) := by
  obtain ⟨s, a, he, hx⟩ := hok.entry
  obtain ⟨s', a', he', -⟩ := hok'.entry
  exact hI.apart he he' hr (.inl (hx hm))

/-- Two holes, one lent `mut`, are the same hole or rooted at different variables. -/
theorem hole_root {hs : List Hole} (hpw : hs.Pairwise Apart) (hh : h ∈ hs) (hh' : h' ∈ hs)
    (hm : h.mode = .mut) (hne : h ≠ h') : h.root ≠ h'.root :=
  fun e => by
    have := (pairwise_of_mem (fun _ _ => Apart.symm) hpw hh hh' hne) e
    rw [hm] at this; cases this.1

theorem olds_nodup (hI : Inv F σ Γ env E S) : ∀ {hs : List Hole}, (∀ h ∈ hs, HoleOk F σ Γ env h) →
    hs.Pairwise Apart → (mutCells (olds hs)).Nodup
  | [], _, _ => by simp [mutCells, olds]
  | h :: hs, hholes, hpw => by
    obtain ⟨hc, hl⟩ := List.pairwise_cons.mp hpw
    have ih := olds_nodup hI (fun h' hh => hholes h' (List.mem_cons_of_mem _ hh)) hl
    have hsplit : mutCells (olds (h :: hs)) = (if h.mode = .mut then h.old else []) ++ mutCells (olds hs) := by
      simp [mutCells, olds]
    rw [hsplit]
    split
    · rename_i hm
      obtain ⟨s, a, he, -⟩ := (hholes h (List.mem_cons_self ..)).entry
      refine nodup_append_disj.mpr ⟨(he.2.2.nodup.sublist (List.sublist_append_right _ _)), ih, ?_⟩
      intro l hl hl'
      obtain ⟨h', hh', -, hl'⟩ := mem_olds_mut.mp hl'
      have hr : h.root ≠ h'.root := fun e => by have := hc h' hh' e; rw [hm] at this; cases this.1
      exact hole_apart hI (hholes h (List.mem_cons_self ..)) (hholes h' (List.mem_cons_of_mem _ hh')) hr hm l
        (List.mem_append.mpr (.inr hl)) (List.mem_append.mpr (.inr hl'))
    · simpa using ih

/-! ## The callee's activation -/

/-- Each hole's cells were allocated before the call and are no argument's: not in the footprint of
the callee's owned parameters. -/
theorem hole_out {Eo Lall : List Nat} (hI : Inv F σ Γ env E S) (hok : HoleOk F σ Γ env h) (hwf : WF σ)
    (hEo_in : ∀ l ∈ Eo, l ∈ Lall ∨ σ.next ≤ l) (hdL : Disj Lall E) (hdLS : Disj Lall S) :
    ∀ l ∈ h.path ++ h.old, σ.mem l ≠ none ∧ l ∉ Eo := by
  intro l hl
  have hin := (hole_in hI hok l hl).2
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

/-- The callee starts with its owned parameters' footprints, the trees lent `mut` exclusive and those
lent `readonly` shared. -/
theorem callee_inv {Eo Lall : List Nat} {hs : List Hole} (hI : Inv F σ1 Γ₁ env E₁ S) (hholes : ∀ h ∈ hs, HoleOk F σ1 Γ₁ env h)
    (hpw : hs.Pairwise Apart) (hrefs : d.refs.map Prod.snd = hs.map fun h => (h.mode, h.ty))
    (hkeys : ((d.owns.map Prod.fst) ++ (d.refs.map Prod.fst)).Nodup)
    (hfo : Foot F σ2 (ownCtx d.owns) cells Eo []) (hEo : Eo.Nodup)
    (hEo_in : ∀ l ∈ Eo, l ∈ Lall ∨ σ1.next ≤ l) (hdL : Disj Lall E₁) (hdLS : Disj Lall S) (hwf : WF σ1)
    (hold : ∀ l, l < σ1.next → σ2.mem l = σ1.mem l) :
    Inv F σ2 (fnCtx d) (cells ++ (d.refs.map Prod.fst).zip (hs.map Hole.loc))
      (Eo ++ mutCells (olds hs)) (roCells (olds hs)) := by
  have hout := fun h hh => hole_out hI (hholes h hh) hwf hEo_in hdL hdLS
  have hfr := (foot_refs (F := F) (σ := σ2) hrefs).mpr ⟨olds hs, by simp [olds, Function.comp_def], ?_, rfl, rfl⟩
  · rw [fnCtx_eq]
    refine ⟨by simpa using hfo.append hfr, ?_, ?_, ?_⟩
    · refine nodup_append_disj.mpr ⟨hEo, olds_nodup hI hholes hpw, fun l hl hl' => ?_⟩
      obtain ⟨h, hh, -, hl'⟩ := mem_olds_mut.mp hl'
      exact (hout h hh l (List.mem_append.mpr (.inr hl'))).2 hl
    · intro l hl hl'
      obtain ⟨h, hh, hm, hl⟩ := mem_olds_ro.mp hl
      rcases List.mem_append.mp hl' with hl' | hl'
      · exact (hout h hh l (List.mem_append.mpr (.inr hl))).2 hl'
      · obtain ⟨h', hh', hm', hl'⟩ := mem_olds_mut.mp hl'
        have hne : h' ≠ h := fun e => by rw [e, hm] at hm'; cases hm'
        exact hole_apart hI (hholes h' hh') (hholes h hh) (hole_root hpw hh' hh hm' hne) hm' l
          (List.mem_append.mpr (.inr hl')) (List.mem_append.mpr (.inr hl))
    · simpa [ownCtx, refCtx, List.map_map, Function.comp_def] using hkeys
  · intro p hp
    simp only [olds, List.mem_map] at hp
    obtain ⟨h, hh, rfl⟩ := hp
    obtain ⟨-, -, -, -, -, -, -, -, -, hlt, -⟩ := hholes h hh
    exact hlt.frame fun l hl => hold l (hwf l (hout h hh l (List.mem_append.mpr (.inr hl))).1)

/-! ## The caller after the call -/

/-- A variable's footprint after the call: if a place rooted at it was lent `mut`, the path to the
hole and the tree the callee left there; otherwise as it was. -/
def fill (ps : List (Hole × List Nat)) (x : Var) (L : List Nat) : List Nat :=
  match ps.find? (fun p => p.1.root == x && p.1.mode == .mut) with
  | some p => p.1.path ++ p.2
  | none => L

section rebuild
variable {σ σ' : Store} {Γ : Ctx} {env : Env} {E S : List Nat} {hs : List Hole}
  {ps : List (Hole × List Nat)}

theorem ps_pairwise (hpw : hs.Pairwise Apart) (hps : ps.map Prod.fst = hs) :
    ps.Pairwise fun p q => Apart p.1 q.1 := by
  rw [← hps] at hpw; exact List.pairwise_map.mp hpw

theorem fill_of_mem (hpw : hs.Pairwise Apart) (hps : ps.map Prod.fst = hs) (hp : p ∈ ps)
    (hm : p.1.mode = .mut) : fill ps p.1.root L = p.1.path ++ p.2 := by
  unfold fill
  split
  · rename_i q hq
    have hq' := List.find?_some hq
    simp only [Bool.and_eq_true, beq_iff_eq] at hq'
    by_cases hne : q = p
    · rw [hne]
    · have := pairwise_of_mem (fun _ _ => Apart.symm) (ps_pairwise hpw hps) (List.mem_of_find?_eq_some hq) hp hne hq'.1
      rw [hq'.2] at this; cases this.1
  · rename_i hn
    have := List.find?_eq_none.mp hn p hp
    simp [hm] at this

theorem fill_cases (hholes : ∀ h ∈ hs, HoleOk F σ Γ env h) (hps : ps.map Prod.fst = hs)
    (he : Entry F σ Γ env x s a L) :
    (fill ps x L = L ∧ ∀ p ∈ ps, p.1.mode = .mut → p.1.root ≠ x) ∨
    (∃ p ∈ ps, fill ps x L = p.1.path ++ p.2 ∧ p.1.root = x ∧ p.1.mode = .mut ∧
      L = p.1.path ++ p.1.old ∧ s.excl = true) := by
  unfold fill
  split
  · rename_i q hq
    have hq' := List.find?_some hq
    simp only [Bool.and_eq_true, beq_iff_eq] at hq'
    have hqm := List.mem_of_find?_eq_some hq
    obtain ⟨s', a', he', hex⟩ := (hholes q.1 (hps ▸ List.mem_map_of_mem hqm)).entry
    rw [hq'.1] at he'
    obtain ⟨rfl, rfl, rfl⟩ := he.det he'
    exact .inr ⟨q, hqm, rfl, hq'.1, hq'.2, rfl, hex hq'.2⟩
  · rename_i hn
    refine .inl ⟨rfl, fun p hp hm hr => ?_⟩
    have := List.find?_eq_none.mp hn p hp
    simp [hm, hr] at this

theorem path_in_X (hI : Inv F σ Γ env E S) (hholes : ∀ h ∈ hs, HoleOk F σ Γ env h)
    (hpw : hs.Pairwise Apart) (hh : h ∈ hs) (hm : h.mode = .mut) :
    ∀ l ∈ h.path, l ∈ E ∧ l ∉ mutCells (olds hs) := by
  intro l hl
  refine ⟨(hole_in hI (hholes h hh) l (List.mem_append.mpr (.inl hl))).1 hm, fun hM => ?_⟩
  obtain ⟨h', hh', hm', hl'⟩ := mem_olds_mut.mp hM
  by_cases hne : h = h'
  · subst hne
    obtain ⟨_, _, _, _, _, _, _, hLT, _, _, _⟩ := hholes h hh
    exact (nodup_append_disj.mp hLT.nodup).2.2 l hl hl'
  · exact hole_apart hI (hholes h hh) (hholes h' hh') (hole_root hpw hh hh' hm hne) hm l
      (List.mem_append.mpr (.inl hl)) (List.mem_append.mpr (.inr hl'))

theorem mem_keep {M : List Nat} : l ∈ E.filter (fun l => l ∉ M) ↔ l ∈ E ∧ l ∉ M := by
  simp [List.mem_filter]

/-- After the call, what a place lent `mut` is rooted at holds the path to the place, as it was,
then what the callee left there. -/
theorem hole_after (hI : Inv F σ Γ env E S) (hholes : ∀ h ∈ hs, HoleOk F σ Γ env h)
    (hpw : hs.Pairwise Apart) (hps : ps.map Prod.fst = hs)
    (hnew : ∀ p ∈ ps, p.1.mode = .mut → LT F σ' p.1.loc p.1.ty p.2)
    (hag : Agree σ σ' (E.filter (fun l => l ∉ mutCells (olds hs)) ++ S))
    (hX : Disj (E.filter (fun l => l ∉ mutCells (olds hs))) (mutCells ps)) (hp : p ∈ ps)
    (hm : p.1.mode = .mut) :
    ∃ s a τr, lookup p.1.root Γ = some s ∧ lookup p.1.root env = some a ∧ s.excl = true ∧
      Path σ' a τr p.1.path p.1.loc p.1.ty ∧ LT F σ' a τr (p.1.path ++ p.2) ∧
      SlotOk F σ' s a (p.1.path ++ p.2) ∧ ∀ σ'' L', LT F σ'' a τr L' → SlotOk F σ'' s a L' := by
  have hph : p.1 ∈ hs := hps ▸ List.mem_map_of_mem hp
  obtain ⟨s, a, τr, hs', ha', hex, hpath, hLT, -, -, hlt⟩ := hholes p.1 hph
  have hagX : ∀ l, l ∈ E → l ∉ mutCells (olds hs) → σ'.mem l = σ.mem l :=
    fun l h1 h2 => hag l (List.mem_append.mpr (.inl (mem_keep.mpr ⟨h1, h2⟩)))
  have hX' := path_in_X hI hholes hpw hph hm
  obtain ⟨hLT', hpath'⟩ := path_join hpath hLT (fun l hl => hagX l (hX' l hl).1 (hX' l hl).2)
    (hnew p hp hm) (fun l hl hl' => hX l (mem_keep.mpr (hX' l hl)) (mem_mutCells.mpr ⟨p, hp, hm, hl'⟩))
  exact ⟨s, a, τr, hs', ha', hex hm, hpath', hLT', hlt σ' _ hLT', hlt⟩

/-- After the call, what a place lent `readonly` is rooted at is as it was. -/
theorem hole_after_ro (hI : Inv F σ Γ env E S) (hholes : ∀ h ∈ hs, HoleOk F σ Γ env h)
    (hpw : hs.Pairwise Apart) (hag : Agree σ σ' (E.filter (fun l => l ∉ mutCells (olds hs)) ++ S))
    (hh : h ∈ hs) (hm : h.mode = .ro) :
    ∃ s a τr, lookup h.root Γ = some s ∧ lookup h.root env = some a ∧
      Path σ' a τr h.path h.loc h.ty ∧ LT F σ' a τr (h.path ++ h.old) ∧ LT F σ' h.loc h.ty h.old ∧
      SlotOk F σ' s a (h.path ++ h.old) ∧ ∀ σ'' L', LT F σ'' a τr L' → SlotOk F σ'' s a L' := by
  obtain ⟨s, a, τr, hs', ha', -, hpath, hLT, hso, hold, hlt⟩ := hholes h hh
  -- The root's tree is no hole's lent `mut`: it is kept as it was.
  have hkeep : ∀ l ∈ h.path ++ h.old, σ'.mem l = σ.mem l := fun l hl => by
    have hin := hole_in hI (hholes h hh) l hl
    rcases hin.2 with hE | hS
    · refine hag l (List.mem_append.mpr (.inl (mem_keep.mpr ⟨hE, fun hM => ?_⟩)))
      obtain ⟨h', hh', hm', hl'⟩ := mem_olds_mut.mp hM
      have hne : h.root ≠ h'.root := fun e =>
        hole_root hpw hh' hh hm' (fun e' => by rw [← e', hm'] at hm; cases hm) e.symm
      exact hole_apart hI (hholes h' hh') (hholes h hh) (Ne.symm hne) hm' l
        (List.mem_append.mpr (.inr hl')) hl
    · exact hag l (List.mem_append.mpr (.inr hS))
  exact ⟨s, a, τr, hs', ha', hpath.frame fun l hl => hkeep l (List.mem_append.mpr (.inl hl)),
    hLT.frame hkeep, hold.frame fun l hl => hkeep l (List.mem_append.mpr (.inr hl)), hso.frame hkeep, hlt⟩

/-- After the call, the caller's variables hold what they held but for the holes lent `mut`, which
hold what the callee left there. -/
theorem caller_rebuild (hI : Inv F σ Γ env E S) (hholes : ∀ h ∈ hs, HoleOk F σ Γ env h)
    (hpw : hs.Pairwise Apart) (hps : ps.map Prod.fst = hs)
    (hnew : ∀ p ∈ ps, p.1.mode = .mut → LT F σ' p.1.loc p.1.ty p.2) (hMn : (mutCells ps).Nodup)
    (hag : Agree σ σ' (E.filter (fun l => l ∉ mutCells (olds hs)) ++ S))
    (hX : Disj (E.filter (fun l => l ∉ mutCells (olds hs))) (mutCells ps))
    (hSX : Disj S (mutCells ps)) :
    ∃ E', Inv F σ' Γ env E' S ∧
      ∀ l, l ∈ E' ↔ l ∈ E.filter (fun l => l ∉ mutCells (olds hs)) ∨ l ∈ mutCells ps := by
  have hpsok : ∀ p ∈ ps, HoleOk F σ Γ env p.1 := fun p hp => hholes p.1 (hps ▸ List.mem_map_of_mem hp)
  have hpsin : ∀ p ∈ ps, p.1 ∈ hs := fun p hp => hps ▸ List.mem_map_of_mem hp
  have hagX : ∀ l, l ∈ E → l ∉ mutCells (olds hs) → σ'.mem l = σ.mem l :=
    fun l h1 h2 => hag l (List.mem_append.mpr (.inl (mem_keep.mpr ⟨h1, h2⟩)))
  -- A variable none of whose places was lent `mut` keeps its footprint clear of the holes.
  have hclear : ∀ {x s a L}, Entry F σ Γ env x s a L → (∀ p ∈ ps, p.1.mode = .mut → p.1.root ≠ x) →
      ∀ l ∈ L, l ∈ E → l ∉ mutCells (olds hs) := by
    intro x s a L he hn l hl _ hM
    obtain ⟨h', hh', hm', hl'⟩ := mem_olds_mut.mp hM
    obtain ⟨p', hp', rfl⟩ := List.mem_map.mp (hps ▸ hh' : h' ∈ ps.map Prod.fst)
    obtain ⟨s', a', he', hex'⟩ := (hpsok p' hp').entry
    exact hI.apart he he' (fun e => hn p' hp' hm' e.symm) (.inr (hex' hm')) l hl
      (List.mem_append.mpr (.inr hl'))
  have hsub : ∀ {x s a L}, Entry F σ Γ env x s a L → s.excl = true → ∀ l ∈ fill ps x L,
      (l ∈ L ∧ l ∈ E.filter (fun l => l ∉ mutCells (olds hs))) ∨
      ∃ p ∈ ps, p.1.root = x ∧ p.1.mode = .mut ∧ l ∈ p.2 := by
    intro x s a L he hex l hl
    rcases fill_cases hholes hps he with ⟨hf, hn⟩ | ⟨p, hp, hf, hr, hm, hL, -⟩
    · rw [hf] at hl
      have hE := ((hI.entry_sub he l hl).resolve_right fun h => by rw [hex] at h; cases h.1).2
      exact .inl ⟨hl, mem_keep.mpr ⟨hE, hclear he hn l hl hE⟩⟩
    · rw [hf] at hl
      rcases List.mem_append.mp hl with hl | hl
      · exact .inl ⟨hL ▸ List.mem_append.mpr (.inl hl),
          mem_keep.mpr (path_in_X hI hholes hpw (hpsin p hp) hm l hl)⟩
      · exact .inr ⟨p, hp, hr, hm, hl⟩
  obtain ⟨E', hf', hn', hmem'⟩ := hI.foot.rebuild (σ' := σ') (fill ps) hI.keys
    (by
      intro x s a L he
      rcases fill_cases hholes hps he with ⟨hf, hn⟩ | ⟨p, hp, hf, hr, hm, hL, hex⟩
      · rw [hf]
        refine ⟨he.2.2.frame fun l hl => ?_, fun _ => rfl⟩
        rcases hI.entry_sub he l hl with ⟨-, hE⟩ | ⟨-, hS⟩
        · exact hagX l hE (hclear he hn l hl hE)
        · exact hag l (List.mem_append.mpr (.inr hS))
      · rw [hf]
        refine ⟨?_, fun h => by rw [hex] at h; cases h⟩
        obtain ⟨s', a', τr, hs', ha', -, hpath, hLT, -, -, hlt⟩ := hpsok p hp
        rw [hr] at hs' ha'
        cases lookup_det he.1 hs'
        cases lookup_det he.2.1 ha'
        have hX' := path_in_X hI hholes hpw (hpsin p hp) hm
        obtain ⟨hLT', -⟩ := path_join hpath hLT (fun l hl => hagX l (hX' l hl).1 (hX' l hl).2)
          (hnew p hp hm) (fun l hl hl' => hX l (mem_keep.mpr (hX' l hl))
            (mem_mutCells.mpr ⟨p, hp, hm, hl'⟩))
        exact hlt σ' _ hLT')
    (by
      intro x s a L y t b L' hx hy hne hex hey l hl hl'
      rcases hsub hx hex l hl with ⟨hlL, hlX⟩ | ⟨p, hp, hpr, hpm, hlp⟩ <;>
        rcases hsub hy hey l hl' with ⟨hlL', hlX'⟩ | ⟨q, hq, hqr, hqm, hlq⟩
      · exact hI.apart hx hy hne (.inl hex) l hlL hlL'
      · exact hX l hlX (mem_mutCells.mpr ⟨q, hq, hqm, hlq⟩)
      · exact hX l hlX' (mem_mutCells.mpr ⟨p, hp, hpm, hlp⟩)
      · have hpq : p ≠ q := fun e => hne (hpr ▸ hqr ▸ e ▸ rfl)
        have := flatMap_apart (f := fun p : Hole × List Nat => if p.1.mode = .mut then p.2 else []) hMn hp hq hpq
        simp only [hpm, hqm, ↓reduceIte] at this
        exact this l hlp hlq)
  refine ⟨E', ⟨hf', hn', fun l hS hl => ?_, hI.keys⟩, fun l => ?_⟩
  · obtain ⟨x, s, a, L, he, hex, hl⟩ := (hmem' l).mp hl
    rcases hsub he hex l hl with ⟨-, hlX⟩ | ⟨p, hp, -, hpm, hlp⟩
    · exact hI.disj l hS (mem_keep.mp hlX).1
    · exact hSX l hS (mem_mutCells.mpr ⟨p, hp, hpm, hlp⟩)
  · rw [hmem']
    constructor
    · rintro ⟨x, s, a, L, he, hex, hl⟩
      rcases hsub he hex l hl with ⟨-, hlX⟩ | ⟨p, hp, -, hpm, hlp⟩
      · exact .inl hlX
      · exact .inr (mem_mutCells.mpr ⟨p, hp, hpm, hlp⟩)
    · rintro (hlX | hlM)
      · obtain ⟨hE, hnM⟩ := mem_keep.mp hlX
        obtain ⟨x, s, a, L, he, hex, hl⟩ := (hI.foot.memE hI.keys l).mp hE
        refine ⟨x, s, a, L, he, hex, ?_⟩
        rcases fill_cases hholes hps he with ⟨hf, -⟩ | ⟨p, hp, hf, -, hm, hL, -⟩
        · rw [hf]; exact hl
        · rw [hf]
          rw [hL] at hl
          rcases List.mem_append.mp hl with hl | hl
          · exact List.mem_append.mpr (.inl hl)
          · exact absurd (mem_olds_mut.mpr ⟨p.1, hpsin p hp, hm, hl⟩) hnM
      · obtain ⟨p, hp, hpm, hlp⟩ := mem_mutCells.mp hlM
        obtain ⟨s, a, he, hex⟩ := (hpsok p hp).entry
        refine ⟨p.1.root, s, a, _, he, hex hpm, ?_⟩
        rw [fill_of_mem hpw hps hp hpm]
        exact List.mem_append.mpr (.inr hlp)

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

theorem SlotOk.ro {s : Slot} (h : SlotOk F σ s a L) (hs : ∀ τ, s ≠ .own τ false) : SlotOk F σ s.ro a L := by
  rcases s with ⟨τ, live⟩ | ⟨m, τ⟩ | τ
  · cases live
    · exact absurd rfl (hs τ)
    · exact h
  · exact h
  · exact h

theorem SlotOk.unro {s : Slot} (h : SlotOk F σ s.ro a L) (hs : ∀ τ, s ≠ .own τ false) : SlotOk F σ s a L := by
  rcases s with ⟨τ, live⟩ | ⟨m, τ⟩ | τ
  · cases live
    · exact absurd rfl (hs τ)
    · exact h
  · exact h
  · exact h

theorem Slot.ro_excl {s : Slot} : s.ro.excl = false := by
  rcases s with ⟨τ, live⟩ | ⟨m, τ⟩ | τ <;> rfl

/-- A slot not changeable is its own `ro`. -/
theorem Slot.ro_of_excl {s : Slot} (h : s.excl = false) : s.ro = s := by
  rcases s with ⟨τ, live⟩ | ⟨m, τ⟩ | τ
  · simp [Slot.excl] at h
  · cases m
    · rfl
    · simp [Slot.excl] at h
  · rfl

/-- Only read, a slot is weakened by nothing. -/
theorem Slot.Le.of_ro {s s' : Slot} (h : Slot.Le s' s.ro) : s' = s.ro := by
  rcases s with ⟨τ, live⟩ | ⟨m, τ⟩ | τ <;> (simp only [Slot.ro] at h ⊢; cases h; rfl)

/-- The variables `ys` only read, as a `handle`'s body has them: what they owned, `Fz`, is shared
while the body runs, and given back once it ends, as it was, if nothing changed it or what the
activation only reads. -/
theorem Foot.handle (h : Foot F σ Γ env E S) (hk : (Γ.map Prod.fst).Nodup)
    (hok : ∀ y ∈ ys, ∀ τ, lookup y Γ ≠ some (.own τ false)) :
    ∃ Eb Sb Fz, Foot F σ (freeze Γ ys) env Eb Sb ∧ E.Perm (Eb ++ Fz) ∧ Sb.Perm (Fz ++ S) ∧
      (∀ y s a L, Entry F σ Γ env y s a L → y ∈ ys → ∀ l ∈ L, l ∈ Fz ∨ l ∈ S) ∧
      ∀ σ' Γb Eb', Foot F σ' Γb env Eb' Sb → Weaker Γb (freeze Γ ys) → Agree σ σ' (Fz ++ S) →
        ∃ E', Foot F σ' (thaw Γ ys Γb) env E' S ∧ E'.Perm (Eb' ++ Fz) := by
  induction h with
  | nil =>
    refine ⟨[], [], [], .nil, .refl _, .refl _, fun y s a L he => absurd he.1 (by simp [lookup]), ?_⟩
    intro σ' Γb Eb' hb hw _
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
    have hentry : ∀ y t b L', Entry F σ ((x, s) :: Γ) ((x, a) :: env) y t b L' →
        (y = x ∧ t = s ∧ L' = L) ∨ (y ≠ x ∧ Entry F σ Γ env y t b L') := by
      intro y t b L' he
      rcases (entry_cons hx).mp he with ⟨rfl, rfl, rfl, hL⟩ | ⟨hne, he⟩
      · exact .inl ⟨rfl, rfl, hL.det hs⟩
      · exact .inr ⟨hne, he⟩
    by_cases hxy : x ∈ ys
    · have hsno : ∀ τ, s ≠ .own τ false := fun τ h => hok x hxy τ (by simp [lookup, h])
      have hsro := hs.ro hsno
      cases hex : s.excl
      · -- Only read already: shared before and after.
        have hro : s.ro = s := Slot.ro_of_excl hex
        refine ⟨Eb, L ++ Sb, Fz, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hfr]; simp only [hxy, ↓reduceIte]
          have := Foot.cons (x := x) hsro hfb
          simpa [addE, addS, Slot.ro_excl] using this
        · simpa [addE, hex] using hE
        · simp only [addS, hex, Bool.false_eq_true, ↓reduceIte]
          exact (hS.append_left L).trans perm_front
        · intro y t b L' he hy l hl
          rcases hentry y t b L' he with ⟨rfl, rfl, rfl⟩ | ⟨-, he⟩
          · exact .inr (by simp [addS, hex, hl])
          · rcases hent y t b L' he hy l hl with h | h
            · exact .inl h
            · exact .inr (by simp [addS, hex, h])
        · intro σ' Γb Eb' hb hw hag
          rw [hfr] at hw
          obtain ⟨s', Γb', rfl, hle, hw'⟩ := Weaker.cons_inv hw
          simp only [hxy, ↓reduceIte] at hle
          obtain rfl := hle.of_ro
          obtain ⟨L', Et, St, hs', hft, rfl, hSt⟩ := hb.uncons
          simp only [addS, Slot.ro_excl, Bool.false_eq_true, ↓reduceIte] at hSt
          have hLs : SlotOk F σ' s.ro a L := hsro.frame fun l hl => hag l (by simp [addS, hex, hl])
          obtain rfl := hLs.det hs'
          obtain rfl := List.append_cancel_left hSt
          obtain ⟨E', hf', hp⟩ := hthaw σ' Γb' Et hft hw' (fun l hl => hag l (by
            rcases List.mem_append.mp hl with h | h
            · exact List.mem_append.mpr (.inl h)
            · exact List.mem_append.mpr (.inr (by simp [addS, hex, h]))))
          refine ⟨E', ?_, by simpa [addE, Slot.ro_excl] using hp⟩
          rw [thaw_cons]; simp only [hxy, ↓reduceIte]
          simpa [addE, addS, hex, hLs.unro hsno] using Foot.cons (x := x) (hLs.unro hsno) hf'
      · -- Changeable: shared while the body runs, and owned again after.
        refine ⟨Eb, L ++ Sb, L ++ Fz, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hfr]; simp only [hxy, ↓reduceIte]
          have := Foot.cons (x := x) hsro hfb
          simpa [addE, addS, Slot.ro_excl] using this
        · simp only [addE, hex, ↓reduceIte]
          exact (hE.append_left L).trans perm_front
        · simp only [addS, hex, ↓reduceIte]
          rw [List.append_assoc]
          exact hS.append_left L
        · intro y t b L' he hy l hl
          rcases hentry y t b L' he with ⟨rfl, rfl, rfl⟩ | ⟨-, he⟩
          · exact .inl (List.mem_append.mpr (.inl hl))
          · rcases hent y t b L' he hy l hl with h | h
            · exact .inl (List.mem_append.mpr (.inr h))
            · exact .inr (by simp [addS, hex, h])
        · intro σ' Γb Eb' hb hw hag
          rw [hfr] at hw
          obtain ⟨s', Γb', rfl, hle, hw'⟩ := Weaker.cons_inv hw
          simp only [hxy, ↓reduceIte] at hle
          obtain rfl := hle.of_ro
          obtain ⟨L', Et, St, hs', hft, rfl, hSt⟩ := hb.uncons
          simp only [addS, Slot.ro_excl, Bool.false_eq_true, ↓reduceIte] at hSt
          have hLs : SlotOk F σ' s.ro a L := hsro.frame fun l hl => hag l (by simp [hl])
          obtain rfl := hLs.det hs'
          obtain rfl := List.append_cancel_left hSt
          obtain ⟨E', hf', hp⟩ := hthaw σ' Γb' Et hft hw' (fun l hl => hag l (by
            rcases List.mem_append.mp hl with h | h
            · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr h)))
            · exact List.mem_append.mpr (.inr (by simp [addS, hex, h]))))
          refine ⟨L ++ E', ?_, ?_⟩
          · rw [thaw_cons]; simp only [hxy, ↓reduceIte]
            simpa [addE, addS, hex] using Foot.cons (x := x) (hLs.unro hsno) hf'
          · simp only [addE, Slot.ro_excl, Bool.false_eq_true, ↓reduceIte]
            exact (hp.append_left L).trans perm_front
    · -- Not lent to the arm: as it is.
      refine ⟨addE s L Eb, addS s L Sb, Fz, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hfr]; simp only [hxy, ↓reduceIte]; exact .cons hs hfb
      · cases hex : s.excl <;> simp only [addE, hex, Bool.false_eq_true, ↓reduceIte]
        · exact hE
        · exact (hE.append_left L).trans perm_assoc
      · cases hex : s.excl <;> simp only [addS, hex, Bool.false_eq_true, ↓reduceIte]
        · exact (hS.append_left L).trans perm_front
        · exact hS
      · intro y t b L' he hy l hl
        rcases hentry y t b L' he with ⟨rfl, -, -⟩ | ⟨-, he⟩
        · exact absurd hy hxy
        · rcases hent y t b L' he hy l hl with h | h
          · exact .inl h
          · right; cases hex : s.excl <;> simp [addS, hex, h]
      · intro σ' Γb Eb' hb hw hag
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
          have hLs : SlotOk F σ' s a L := hs.frame fun l hl => hag l (by simp [addS, hex, hl])
          obtain rfl := hLs.det hs'
          simp only [addS, hex, Bool.false_eq_true, ↓reduceIte] at hSt
          obtain rfl := List.append_cancel_left hSt
          obtain ⟨E', hf', hp⟩ := hthaw σ' Γb' Et hft hw' (fun l hl => hag l (by
            rcases List.mem_append.mp hl with h | h
            · exact List.mem_append.mpr (.inl h)
            · exact List.mem_append.mpr (.inr (by simp [addS, hex, h]))))
          refine ⟨E', ?_, by simpa [addE, hex] using hp⟩
          rw [thaw_cons]; simp only [hxy, ↓reduceIte]
          simpa [addE, addS, hex] using Foot.cons (x := x) hLs hf'
        · simp only [addS, hex, hex', ↓reduceIte] at hSt
          subst hSt
          obtain ⟨E', hf', hp⟩ := hthaw σ' Γb' Et hft hw' (fun l hl => hag l (by
            rcases List.mem_append.mp hl with h | h
            · exact List.mem_append.mpr (.inl h)
            · exact List.mem_append.mpr (.inr (by simp [addS, hex, h]))))
          refine ⟨L' ++ E', ?_, ?_⟩
          · rw [thaw_cons]; simp only [hxy, ↓reduceIte]
            simpa [addE, addS, hex, hex'] using Foot.cons (x := x) hs' hf'
          · simp only [addE, hex', hex, ↓reduceIte]
            exact (hp.append_left L').trans perm_assoc

/-- The root of a place the code may reach has its value: it was not moved. -/
theorem PlaceTy.root_live : PlaceTy Γ p τ w y → ∀ τ', lookup y Γ ≠ some (.own τ' false)
  | .own h, τ', h' => by rw [h] at h'; cases h'
  | .ref h, τ', h' => by rw [h] at h'; cases h'
  | .deref hp, τ', h' => hp.root_live τ' h'

theorem Caps.roots_live : Caps Γ caps ys → ∀ p ∈ ys, ∀ τ, lookup p.2 Γ ≠ some (.own τ false)
  | .nil, _, h, _ => by simp at h
  | .ro hp hr, p, h, τ => by
    rcases List.mem_cons.mp h with rfl | h
    · exact hp.root_live τ
    · exact hr.roots_live p h τ
  | .mut hp hr, p, h, τ => by
    rcases List.mem_cons.mp h with rfl | h
    · exact hp.root_live τ
    · exact hr.roots_live p h τ

/-- The variables `ys`, in order, each changeable, with the trees they own in turn: `H`. -/
inductive Trees (F : List Fn) (σ : Store) (Γ : Ctx) (env : Env) : List Var → List Nat → Prop
  | nil : Trees F σ Γ env [] []
  | cons : Entry F σ Γ env y s a L → s.excl = true → Trees F σ Γ env ys H → Trees F σ Γ env (y :: ys) (L ++ H)

theorem roots_cons_ro : roots .mut ((.ro, y) :: ys) = roots .mut ys := by simp [roots]
theorem roots_cons_mut : roots .mut ((.mut, y) :: ys) = y :: roots .mut ys := by simp [roots]
theorem roots_cons_ro' : roots .ro ((.ro, y) :: ys) = y :: roots .ro ys := by simp [roots]
theorem roots_cons_mut' : roots .ro ((.mut, y) :: ys) = roots .ro ys := by simp [roots]

/-- The places a `handle` lends its arm, in the activation it is in: each holds a value of its
type; those lent `readonly` among the footprints of the variables they are rooted at, those lent
`mut` the trees of their variables, as they are now and as they will be. -/
theorem caps_ok (hc : Caps Γ caps ys) (hf : Foot F σ Γ env E S) :
    ∃ ls Rc Hc, caps.mapM (fun c => resolve σ env c.loc) = some ls ∧ ls.length = caps.length ∧
      CapsOk F σ (List.zipWith Cap.at caps ls) Rc Hc ∧
      (∀ l ∈ Rc, ∃ y, (.ro, y) ∈ ys ∧ ∃ s a L, Entry F σ Γ env y s a L ∧ l ∈ L) ∧
      Trees F σ Γ env (roots .mut ys) Hc ∧
      ∀ σ' Rc' Hc', CapsOk F σ' (List.zipWith Cap.at caps ls) Rc' Hc' → Trees F σ' Γ env (roots .mut ys) Hc' := by
  induction hc with
  | nil => exact ⟨[], [], [], rfl, rfl, .nil, by simp, .nil, fun _ _ _ h => by cases h; exact .nil⟩
  | @ro p τ w y rest ys' x hp _ ih =>
    obtain ⟨ls, Rc, Hc, hmap, hlen, hcok, hin, htr, hnew⟩ := ih
    obtain ⟨a, τr, Lr, P, l, s, ha, hLr, hpath, hres, -, -, hs, hso, -, -⟩ := place_ok hp hf
    obtain ⟨R, hR, rfl⟩ := path_split hpath hLr
    refine ⟨l :: ls, R ++ Rc, Hc, by simp [List.mapM_cons, hres, hmap], by simp [hlen], .ro hR hcok, ?_,
      by rw [roots_cons_ro]; exact htr, ?_⟩
    · intro l' hl'
      rcases List.mem_append.mp hl' with h | h
      · exact ⟨y, List.mem_cons_self .., s, a, P ++ R, ⟨hs, ha, hso⟩, List.mem_append.mpr (.inr h)⟩
      · obtain ⟨y', hy', s', a', L', he, hl⟩ := hin l' h
        exact ⟨y', List.mem_cons_of_mem _ hy', s', a', L', he, hl⟩
    · intro σ' Rc' Hc' h
      rw [roots_cons_ro]
      cases h with
      | ro _ hr => exact hnew σ' _ _ hr
  | @«mut» y τ rest ys' x hp _ ih =>
    obtain ⟨ls, Rc, Hc, hmap, hlen, hcok, hin, htr, hnew⟩ := ih
    obtain ⟨a, τr, Lr, P, l, s, ha, hLr, hpath, hres, -, -, hs, hso, hexw, hslot⟩ := place_ok hp hf
    obtain ⟨R, hR, rfl⟩ := path_split hpath hLr
    simp only [resolve] at hres
    rw [ha] at hres
    cases hres
    obtain ⟨rfl, hPR⟩ := hLr.det_ty hR
    obtain rfl : P = [] := by
      have := congrArg List.length hPR; simp only [List.length_append] at this
      exact List.eq_nil_of_length_eq_zero (by omega)
    simp only [List.nil_append] at hso hslot ⊢
    refine ⟨a :: ls, Rc, R ++ Hc, by simp [List.mapM_cons, resolve, ha, hmap], by simp [hlen], .mut hR hcok, ?_,
      by rw [roots_cons_mut]; exact .cons ⟨hs, ha, hso⟩ (hexw rfl) htr, ?_⟩
    · intro l' hl'
      obtain ⟨y', hy', s', a', L', he, hl⟩ := hin l' hl'
      exact ⟨y', List.mem_cons_of_mem _ hy', s', a', L', he, hl⟩
    · intro σ' Rc' Hc' h
      rw [roots_cons_mut]
      cases h with
      | «mut» hL hr => exact .cons ⟨hs, ha, hslot σ' _ hL⟩ (hexw rfl) (hnew σ' _ _ hr)

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
    rcases s with ⟨_, _⟩ | ⟨_, _⟩ | _
    · simp only [Slot.ro, Slot.ref.injEq] at hs; obtain ⟨rfl, -⟩ := hs; rfl
    · simp only [Slot.ro, Slot.ref.injEq] at hs; obtain ⟨rfl, -⟩ := hs; rfl
    · simp [Slot.ro] at hs
  | deref _ ih => exact ih hy

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
theorem Foot.hidden (h : Foot F σ Γ env E S) (hk : (Γ.map Prod.fst).Nodup) (he : Entry F σ Γ env y s a Ly)
    (hex : s.excl = true) :
    ∃ Eh, Foot F σ (hide Γ y) env Eh S ∧ E.Perm (Ly ++ Eh) ∧
      ∀ σ' Γb Eb' Ly', Foot F σ' Γb env Eb' S → Weaker Γb (hide Γ y) → Agree σ σ' S →
        SlotOk F σ' s a Ly' → ∃ E', Foot F σ' (thaw Γ [y] Γb) env E' S ∧ E'.Perm (Ly' ++ Eb') := by
  induction h with
  | nil => exact absurd he.1 (by simp [lookup])
  | @cons s0 a0 L0 Γ env E S x hs hrest ih =>
    simp only [List.map_cons, List.nodup_cons] at hk
    obtain ⟨hx, hk⟩ := hk
    rcases (entry_cons hx).mp he with ⟨rfl, rfl, rfl, hL⟩ | ⟨hne, he'⟩
    · -- The variable lent is this one.
      obtain rfl := hL.det hs
      have hhide : hide ((y, s) :: Γ) y = (y, .lent s.ty) :: Γ := by
        simp only [hide, List.map_cons, ↓reduceIte, List.cons.injEq, true_and]
        exact hide_absent hx
      have hS : addS s Ly S = S := by simp [addS, hex]
      have hE : addE s Ly E = Ly ++ E := by simp [addE, hex]
      rw [hS, hE]
      refine ⟨E, ?_, .refl _, ?_⟩
      · rw [hhide]
        simpa [addE, addS, Slot.excl] using Foot.cons (s := .lent s.ty) (x := y) (L := []) (a := a) rfl hrest
      · intro σ' Γb Eb' Ly' hb hw hag hs'
        rw [hhide] at hw
        obtain ⟨s', Γb', rfl, hle, hw'⟩ := Weaker.cons_inv hw
        cases hle
        obtain ⟨L', Et, St, hL', hft, rfl, hSt⟩ := hb.uncons
        simp only [SlotOk] at hL'
        subst hL'
        simp only [addS, Slot.excl, Bool.false_eq_true, ↓reduceIte, List.nil_append] at hSt
        subst hSt
        refine ⟨Ly' ++ Eb', ?_, .refl _⟩
        rw [thaw_cons]
        simp only [List.mem_singleton, ↓reduceIte]
        rw [thaw_absent hx (by rw [hw'.keys])]
        simpa [addE, addS, hex] using Foot.cons (x := y) hs' hft
    · -- Another: as it was.
      obtain ⟨Eh, hfh, hp, hthaw⟩ := ih hk he'
      have hhide : hide ((x, s0) :: Γ) y = (x, s0) :: hide Γ y := by
        simp only [hide, List.map_cons, List.cons.injEq]
        simp [Ne.symm hne]
      refine ⟨addE s0 L0 Eh, by rw [hhide]; exact .cons hs hfh, ?_, ?_⟩
      · cases hx0 : s0.excl <;> simp only [addE, hx0, Bool.false_eq_true, ↓reduceIte]
        · exact hp
        · exact (hp.append_left L0).trans perm_front
      · intro σ' Γb Eb' Ly' hb hw hag hs'
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
          have hLL := (hs.frame fun l hl => hag l (by simp [addS, hx0, hl])).det hL'
          subst hLL
          simp only [addS, hx0, Bool.false_eq_true, ↓reduceIte] at hSt
          have hSS := List.append_cancel_left hSt
          subst hSS
          obtain ⟨E', hf', hp'⟩ := hthaw σ' Γb' Et Ly' hft hw' (fun l hl => hag l (by simp [addS, hx0, hl])) hs'
          refine ⟨E', ?_, by simpa [addE, hx0] using hp'⟩
          rw [thaw_cons]
          simp only [List.mem_singleton, Ne.symm hne, ↓reduceIte]
          simpa [addE, addS, hx0] using Foot.cons (x := x) hL' hf'
        · simp only [addS, hx0, hex', ↓reduceIte] at hSt
          subst hSt
          obtain ⟨E', hf', hp'⟩ := hthaw σ' Γb' Et Ly' hft hw' (fun l hl => hag l (by simp [addS, hx0, hl])) hs'
          refine ⟨L' ++ E', ?_, ?_⟩
          · rw [thaw_cons]
            simp only [List.mem_singleton, Ne.symm hne, ↓reduceIte]
            simpa [addE, addS, hex', hx0] using Foot.cons (x := x) hL' hf'
          · simp only [addE, hex', hx0, ↓reduceIte]
            exact (hp'.append_left L').trans perm_front

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

theorem Trees.hide : Trees F σ Γ env ys H → y ∉ ys → Trees F σ (hide Γ y) env ys H
  | .nil, _ => .nil
  | .cons ⟨hl, ha, hs⟩ hex hr, h => by
    simp only [List.mem_cons, not_or] at h
    exact .cons ⟨by rw [lookup_hide_ne (Ne.symm h.1)]; exact hl, ha, hs⟩ hex (hr.hide h.2)

/-- The variables `ys`, each changeable, hidden from the code in turn: what the code may change is
the rest; once it ends, they are given back, each with the tree it has then. -/
theorem Foot.hiddenAll : ∀ {ys : List Var} {Γ : Ctx} {E H : List Nat}, Foot F σ Γ env E S → (Γ.map Prod.fst).Nodup →
    Trees F σ Γ env ys H → ys.Nodup →
    ∃ Eh, Foot F σ (hideAll Γ ys) env Eh S ∧ E.Perm (H ++ Eh) ∧
      ∀ σ' Γb Eb' H', Foot F σ' Γb env Eb' S → Weaker Γb (hideAll Γ ys) → Agree σ σ' S →
        Trees F σ' Γ env ys H' → ∃ E', Foot F σ' (unhideAll Γ ys Γb) env E' S ∧ E'.Perm (H' ++ Eb')
  | [], Γ, E, H, h, _, ht, _ => by
    cases ht
    refine ⟨E, h, .refl _, fun σ' Γb Eb' H' hb _ _ ht' => ?_⟩
    cases ht'
    exact ⟨Eb', hb, .refl _⟩
  | y :: ys, Γ, E, H, h, hk, ht, hn => by
    obtain ⟨hy, hn⟩ := List.nodup_cons.mp hn
    cases ht with
    | @cons _ s a L _ Hr he hex hr =>
    obtain ⟨Eh1, hf1, hp1, hre1⟩ := h.hidden hk he hex
    obtain ⟨Eh, hf, hp, hre⟩ := Foot.hiddenAll hf1 (by rw [hide_keys]; exact hk) (hr.hide hy) hn
    refine ⟨Eh, hf, hp1.trans ((hp.append_left L).trans (by simp)), ?_⟩
    intro σ' Γb Eb' H' hb hw hag ht'
    cases ht' with
    | @cons _ s' a' L' _ Hr' he' _ hr' =>
    obtain ⟨rfl, rfl⟩ : s' = s ∧ a' = a := by
      obtain ⟨h1, h2, -⟩ := he
      obtain ⟨h1', h2', -⟩ := he'
      rw [h1] at h1'; rw [h2] at h2'
      exact ⟨(Option.some.inj h1').symm, (Option.some.inj h2').symm⟩
    obtain ⟨E1', hf1', hp1'⟩ := hre σ' Γb Eb' Hr' hb hw hag (hr'.hide hy)
    obtain ⟨E', hf', hp'⟩ := hre1 σ' _ E1' L' hf1' (unhideAll_weaker hw) hag he'.2.2
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

theorem Entry.to_hidden (h : Entry F σ Γ env y s a L) (hy : y ∉ ys) : Entry F σ (hideAll Γ ys) env y s a L :=
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
theorem CapsOk.foot : CapsOk F σ caps R H → Foot F σ (capCtx (caps.map Cap.sig)) (caps.map fun c => (c.name, c.loc)) H R
  | .nil => .nil
  | @CapsOk.ro _ _ a τ L rest R' H' x hL hr => by
    have := Foot.cons (s := .ref .ro τ) (x := x) (env := rest.map fun c => (c.name, c.loc)) hL hr.foot
    simpa [capCtx, Cap.sig, addE, addS, Slot.excl] using this
  | @CapsOk.mut _ _ a τ L rest R' H' x hL hr => by
    have := Foot.cons (s := .ref .mut τ) (x := x) (env := rest.map fun c => (c.name, c.loc)) hL hr.foot
    simpa [capCtx, Cap.sig, addE, addS, Slot.excl] using this

/-- And back: the footprint of an arm's captured variables is its frame's state. -/
theorem Foot.capsOk : ∀ {caps : List (Cap Nat)} {E S},
    Foot F σ (capCtx (caps.map Cap.sig)) (caps.map fun c => (c.name, c.loc)) E S → CapsOk F σ caps S E
  | [], _, _, h => by cases h; exact .nil
  | ⟨x, m, τ, a⟩ :: caps, _, _, h => by
    simp only [capCtx, Cap.sig, List.map_cons] at h
    cases h with
    | cons hs hrest =>
      cases m with
      | ro => simpa [addE, addS, Slot.excl] using CapsOk.ro (x := x) hs (Foot.capsOk hrest)
      | «mut» => simpa [addE, addS, Slot.excl] using CapsOk.mut (x := x) hs (Foot.capsOk hrest)

theorem armCtx_eq : armCtx os rs op caps =
    fnCtx { owns := os.zip op.owns, refs := rs.zip op.refs, ret := op.ret, row := r, body := arm } ++ capCtx caps := by
  simp [armCtx, fnCtx, capCtx]

end FlyCore.Ownership
