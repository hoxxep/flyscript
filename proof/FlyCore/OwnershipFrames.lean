import FlyCore.OwnershipMoves

/-!
# Ownership: footprints, variable by variable

An activation's footprints are those of its variables. What a call does to its caller is described
variable by variable: the footprints of two variables are apart when either may be changed, a cell
is in the exclusive footprints just when some exclusive variable's footprint holds it, and every
variable's footprint may be rebuilt at once — as a call that lent several places `mut` leaves them.
-/

namespace FlyCore.Ownership

theorem Inv.alloc (h : Inv σ Γ env E S) : ∀ l ∈ E, σ.mem l ≠ none :=
  fun l hl => h.foot.alloc l (.inl hl)

theorem Inv.allocS (h : Inv σ Γ env E S) : ∀ l ∈ S, σ.mem l ≠ none :=
  fun l hl => h.foot.alloc l (.inr hl)

theorem Foot.uncons : Foot σ ((x, s) :: Γ) ((x, a) :: env) E S →
    ∃ L E' S', SlotOk σ s a L ∧ Foot σ Γ env E' S' ∧ E = addE s L E' ∧ S = addS s L S' := by
  intro h; cases h; exact ⟨_, _, _, ‹_›, ‹_›, rfl, rfl⟩

/-- Dropping an owned variable's cell, live or moved, frees exactly its footprint. -/
theorem dropCell_own : SlotOk σ (.own τ live) c L →
    ∃ σ', dropCell σ τ c = some σ' ∧ σ'.next = σ.next ∧ (∀ l ∈ L, σ'.mem l = none) ∧
      ∀ l, l ∉ L → σ'.mem l = σ.mem l := by
  intro h
  cases live with
  | true => exact dropCell_live h
  | false =>
    rcases h with ⟨hc, rfl⟩ | h
    · obtain ⟨σ', hd, hn, hfree, hkeep⟩ := dropCell_moved (τ := τ) hc
      exact ⟨σ', hd, hn, by simpa using hfree, fun l hl => hkeep l (by simpa using hl)⟩
    · exact dropCell_live h

theorem WF.of_free {D : List Nat} (hwf : WF σ) (hnext : σ'.next = σ.next) (hfree : ∀ l ∈ D, σ'.mem l = none)
    (hkeep : ∀ l, l ∉ D → σ'.mem l = σ.mem l) : WF σ' := by
  intro x hx
  by_cases hxD : x ∈ D
  · exact absurd (hfree x hxD) hx
  · rw [hkeep x hxD] at hx; rw [hnext]; exact hwf x hx

theorem lookup_some_keys {α : Type} {Γ : List (Var × α)} {a : α} :
    lookup x Γ = some a → x ∈ Γ.map Prod.fst := by
  induction Γ with
  | nil => simp [lookup]
  | cons p Γ ih =>
    obtain ⟨y, t⟩ := p
    intro h
    simp only [lookup] at h
    simp only [List.map_cons, List.mem_cons]
    split at h
    · exact .inl ‹_›
    · exact .inr (ih h)

theorem lookup_cons_ne {α : Type} {Γ : List (Var × α)} {t : α} (h : x ≠ y) :
    lookup x ((y, t) :: Γ) = lookup x Γ := by
  simp [lookup, h]

theorem Foot.append : Foot σ Γa ea Ea Sa → Foot σ Γb eb Eb Sb →
    Foot σ (Γa ++ Γb) (ea ++ eb) (Ea ++ Eb) (Sa ++ Sb) := by
  intro ha hb
  induction ha with
  | nil => simpa using hb
  | @cons s a L Γ env E S x hs _ ih =>
    have := Foot.cons (x := x) hs ih
    cases he : s.excl <;> simpa [addE, addS, he] using this

theorem Foot.split : ∀ {Γa : Ctx} {ea : Env} {E S}, Foot σ (Γa ++ Γb) (ea ++ eb) E S →
    Γa.length = ea.length →
    ∃ Ea Sa Eb Sb, Foot σ Γa ea Ea Sa ∧ Foot σ Γb eb Eb Sb ∧ E = Ea ++ Eb ∧ S = Sa ++ Sb
  | [], [], E, S, h, _ => ⟨[], [], E, S, .nil, by simpa using h, rfl, rfl⟩
  | (x, s) :: Γa, (y, a) :: ea, E, S, h, hl => by
    simp only [List.cons_append] at h
    cases h with
    | cons hs hrest =>
      obtain ⟨Ea, Sa, Eb, Sb, h1, h2, rfl, rfl⟩ := Foot.split hrest (by simpa using hl)
      refine ⟨addE s _ Ea, addS s _ Sa, Eb, Sb, .cons hs h1, h2, ?_, ?_⟩ <;>
        cases he : s.excl <;> simp [addE, addS, he]
  | [], _ :: _, _, _, _, hl => by simp at hl
  | _ :: _, [], _, _, _, hl => by simp at hl

/-- A variable of the activation, bound at `a` with footprint `L`. -/
def Entry (σ : Store) (Γ : Ctx) (env : Env) (x : Var) (s : Slot) (a : Nat) (L : List Nat) : Prop :=
  lookup x Γ = some s ∧ lookup x env = some a ∧ SlotOk σ s a L

theorem Entry.det (h : Entry σ Γ env x s a L) (h' : Entry σ Γ env x s' a' L') :
    s = s' ∧ a = a' ∧ L = L' := by
  obtain ⟨hs, ha, hL⟩ := h
  obtain ⟨hs', ha', hL'⟩ := h'
  cases lookup_det hs hs'
  cases lookup_det ha ha'
  exact ⟨rfl, rfl, hL.det hL'⟩

/-- The head of an activation's variables, and the rest, which do not see it. -/
theorem entry_cons (hx : x ∉ Γ.map Prod.fst) :
    Entry σ ((x, s) :: Γ) ((x, a) :: env) y t b L ↔
      (y = x ∧ t = s ∧ b = a ∧ SlotOk σ s a L) ∨ (y ≠ x ∧ Entry σ Γ env y t b L) := by
  unfold Entry
  by_cases hy : y = x
  · subst hy
    rw [show lookup y ((y, s) :: Γ) = some s by simp [lookup],
      show lookup y ((y, a) :: env) = some a by simp [lookup], Option.some.injEq, Option.some.injEq]
    constructor
    · rintro ⟨rfl, rfl, h⟩; exact .inl ⟨rfl, rfl, rfl, h⟩
    · rintro (⟨-, rfl, rfl, h⟩ | ⟨h, -⟩)
      · exact ⟨rfl, rfl, h⟩
      · exact absurd rfl h
  · simp only [lookup_cons_ne hy]
    constructor
    · intro h; exact .inr ⟨hy, h⟩
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact absurd h hy
      · exact h

/-- A cell is in the exclusive footprints just when it is in an exclusive variable's. -/
theorem Foot.memE : Foot σ Γ env E S → (Γ.map Prod.fst).Nodup → ∀ y,
    (y ∈ E ↔ ∃ x s a L, Entry σ Γ env x s a L ∧ s.excl = true ∧ y ∈ L) := by
  intro h
  induction h with
  | nil => intro _ y; simp [Entry, lookup]
  | @cons s a L Γ env E S x hs _ ih =>
    intro hk y
    simp only [List.map_cons] at hk
    obtain ⟨hx, hk⟩ := List.nodup_cons.mp hk
    rw [mem_addE, ih hk]
    constructor
    · rintro (⟨he, hy⟩ | ⟨x', s', a', L', he', hex, hy⟩)
      · exact ⟨x, s, a, L, (entry_cons hx).mpr (.inl ⟨rfl, rfl, rfl, hs⟩), he, hy⟩
      · exact ⟨x', s', a', L', (entry_cons hx).mpr (.inr ⟨fun h => hx (h ▸ lookup_some_keys he'.1), he'⟩),
          hex, hy⟩
    · rintro ⟨x', s', a', L', he', hex, hy⟩
      rcases (entry_cons hx).mp he' with ⟨rfl, rfl, rfl, hL⟩ | ⟨-, he'⟩
      · exact .inl ⟨hex, hL.det hs ▸ hy⟩
      · exact .inr ⟨x', s', a', L', he', hex, hy⟩

/-- A cell is in the shared footprints just when it is in a shared variable's. -/
theorem Foot.memS : Foot σ Γ env E S → (Γ.map Prod.fst).Nodup → ∀ y,
    (y ∈ S ↔ ∃ x s a L, Entry σ Γ env x s a L ∧ s.excl = false ∧ y ∈ L) := by
  intro h
  induction h with
  | nil => intro _ y; simp [Entry, lookup]
  | @cons s a L Γ env E S x hs _ ih =>
    intro hk y
    simp only [List.map_cons] at hk
    obtain ⟨hx, hk⟩ := List.nodup_cons.mp hk
    rw [mem_addS, ih hk]
    constructor
    · rintro (⟨he, hy⟩ | ⟨x', s', a', L', he', hex, hy⟩)
      · exact ⟨x, s, a, L, (entry_cons hx).mpr (.inl ⟨rfl, rfl, rfl, hs⟩), he, hy⟩
      · exact ⟨x', s', a', L', (entry_cons hx).mpr (.inr ⟨fun h => hx (h ▸ lookup_some_keys he'.1), he'⟩),
          hex, hy⟩
    · rintro ⟨x', s', a', L', he', hex, hy⟩
      rcases (entry_cons hx).mp he' with ⟨rfl, rfl, rfl, hL⟩ | ⟨-, he'⟩
      · exact .inl ⟨hex, hL.det hs ▸ hy⟩
      · exact .inr ⟨x', s', a', L', he', hex, hy⟩

theorem Inv.entry_sub (hI : Inv σ Γ env E S) (he : Entry σ Γ env x s a L) :
    ∀ y ∈ L, (s.excl = true ∧ y ∈ E) ∨ (s.excl = false ∧ y ∈ S) := by
  intro y hy
  cases hs : s.excl
  · exact .inr ⟨rfl, (hI.foot.memS hI.keys y).mpr ⟨x, s, a, L, he, hs, hy⟩⟩
  · exact .inl ⟨rfl, (hI.foot.memE hI.keys y).mpr ⟨x, s, a, L, he, hs, hy⟩⟩

/-- The head variable's footprint is apart from a later one's when either may be changed. -/
theorem foot_head_apart (hrest : Foot σ Γ env E S) (hk : (Γ.map Prod.fst).Nodup)
    (hn : (addE r M E).Nodup) (hd : Disj (addS r M S) (addE r M E)) (hy : Entry σ Γ env y t b L')
    (he : r.excl = true ∨ t.excl = true) : Disj M L' := by
  intro l hl hl'
  cases ht : t.excl
  · have hS : l ∈ S := (hrest.memS hk l).mpr ⟨y, t, b, L', hy, ht, hl'⟩
    have hr' : r.excl = true := by simpa [ht] using he
    exact hd l (mem_addS.mpr (.inr hS)) (mem_addE.mpr (.inl ⟨hr', hl⟩))
  · have hE : l ∈ E := (hrest.memE hk l).mpr ⟨y, t, b, L', hy, ht, hl'⟩
    cases hre : r.excl
    · exact hd l (mem_addS.mpr (.inl ⟨hre, hl⟩)) (mem_addE.mpr (.inr hE))
    · simp only [addE, hre, ↓reduceIte] at hn
      exact (nodup_append_disj.mp hn).2.2 l hl hE

/-- Two variables' footprints are apart when either may be changed. -/
theorem Inv.apart (hI : Inv σ Γ env E S) (hx : Entry σ Γ env x s a L) (hy : Entry σ Γ env y t b L')
    (hne : x ≠ y) (he : s.excl = true ∨ t.excl = true) : Disj L L' := by
  obtain ⟨hf, hn, hd, hk⟩ := hI
  revert hn hd hk
  induction hf generalizing x s a L y t b L' with
  | nil => simp [Entry, lookup] at hx
  | @cons r c M Γ env E S z hr hrest ih =>
    intro hn hd hk
    simp only [List.map_cons] at hk
    obtain ⟨hz, hkt⟩ := List.nodup_cons.mp hk
    rcases (entry_cons hz).mp hx with ⟨rfl, rfl, rfl, hL⟩ | ⟨hxz, hxt⟩
    · rcases (entry_cons hz).mp hy with ⟨rfl, -⟩ | ⟨-, hyt⟩
      · exact absurd rfl hne
      · cases hL.det hr; exact foot_head_apart hrest hkt hn hd hyt he
    · rcases (entry_cons hz).mp hy with ⟨rfl, rfl, rfl, hL'⟩ | ⟨-, hyt⟩
      · cases hL'.det hr; exact (foot_head_apart hrest hkt hn hd hxt he.symm).symm
      · refine ih hxt hyt hne he ?_ ?_ hkt
        · cases he : r.excl <;> simp only [addE, he, ↓reduceIte] at hn
          · exact hn
          · exact (nodup_append_disj.mp hn).2.1
        · exact hd.mono_left (fun l hl => mem_addS.mpr (.inr hl)) |>.mono_right
            (fun l hl => mem_addE.mpr (.inr hl))

/-- Every variable's footprint rebuilt at once, in a store where each holds what `nf` says: the
shared ones as they were, the exclusive ones apart from each other. -/
theorem Foot.rebuild (nf : Var → List Nat → List Nat) (h : Foot σ Γ env E S)
    (hk : (Γ.map Prod.fst).Nodup)
    (hok : ∀ x s a L, Entry σ Γ env x s a L → SlotOk σ' s a (nf x L) ∧ (s.excl = false → nf x L = L))
    (hdisj : ∀ x s a L y t b L', Entry σ Γ env x s a L → Entry σ Γ env y t b L' → x ≠ y →
      s.excl = true → t.excl = true → Disj (nf x L) (nf y L')) :
    ∃ E', Foot σ' Γ env E' S ∧ E'.Nodup ∧
      ∀ y, y ∈ E' ↔ ∃ x s a L, Entry σ Γ env x s a L ∧ s.excl = true ∧ y ∈ nf x L := by
  revert hk hok hdisj
  induction h with
  | nil => intro _ _ _; exact ⟨[], .nil, List.nodup_nil, by simp [Entry, lookup]⟩
  | @cons r c M Γ env E S z hr hrest ih =>
    intro hk hok hdisj
    simp only [List.map_cons] at hk
    obtain ⟨hz, hkt⟩ := List.nodup_cons.mp hk
    have hhead : Entry σ ((z, r) :: Γ) ((z, c) :: env) z r c M := (entry_cons hz).mpr (.inl ⟨rfl, rfl, rfl, hr⟩)
    have htail : ∀ {x s a L}, Entry σ Γ env x s a L → Entry σ ((z, r) :: Γ) ((z, c) :: env) x s a L ∧ x ≠ z :=
      fun he => have hne : _ ≠ z := fun h => hz (h ▸ lookup_some_keys he.1)
        ⟨(entry_cons hz).mpr (.inr ⟨hne, he⟩), hne⟩
    obtain ⟨E', hf', hn', hmem'⟩ := ih hkt (fun x s a L he => hok x s a L (htail he).1)
      (fun x s a L y t b L' hx hy hne => hdisj x s a L y t b L' (htail hx).1 (htail hy).1 hne)
    obtain ⟨hr', hsame⟩ := hok z r c M hhead
    have hS : addS r (nf z M) S = addS r M S := by
      cases he : r.excl
      · rw [hsame he]
      · simp [addS, he]
    refine ⟨addE r (nf z M) E', hS ▸ Foot.cons hr' hf', ?_, ?_⟩
    · cases he : r.excl <;> simp only [addE, he, ↓reduceIte]
      · exact hn'
      · refine nodup_append_disj.mpr ⟨hr'.nodup, hn', fun l hl hl' => ?_⟩
        obtain ⟨x, s, a, L, hx, hex, hl'⟩ := (hmem' l).mp hl'
        exact hdisj z r c M x s a L hhead (htail hx).1 (htail hx).2.symm he hex l hl hl'
    · intro l
      rw [mem_addE, hmem']
      constructor
      · rintro (⟨he, hl⟩ | ⟨x, s, a, L, hx, hex, hl⟩)
        · exact ⟨z, r, c, M, hhead, he, hl⟩
        · exact ⟨x, s, a, L, (htail hx).1, hex, hl⟩
      · rintro ⟨x, s, a, L, hx, hex, hl⟩
        rcases (entry_cons hz).mp hx with ⟨rfl, rfl, rfl, hL⟩ | ⟨-, hxt⟩
        · exact .inl ⟨hex, hL.det hr ▸ hl⟩
        · exact .inr ⟨x, s, a, L, hxt, hex, hl⟩

end FlyCore.Ownership
