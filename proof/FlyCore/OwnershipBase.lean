import FlyCore.Ownership

/-!
# Ownership: the shape of the store

What a well-typed program keeps true of the store: each location a variable stands for holds a
value of the variable's type, and the cells that value owns — the location itself and the cells of
its boxes — form a tree, its footprint. Footprints of what may be changed are disjoint; footprints
of what is only read may overlap each other, but nothing that may be changed. A `mut` borrow of a
closure may change what the closure captured but only reads the closure's own cell, so nothing puts
another closure in its place while the borrow lives.
-/

namespace FlyCore.Ownership

/-- The code `f` is a closure's, called as `k`, taking an `A` and giving a `B`, performing only
what `r` names, having captured a value of type `τc`, and lent `readonly` places of the types `R`
— none, but for a scope's task, lent the places its scope froze. -/
def CloOk (F : List Fn) (f : Nat) (τc : Ty) (k : Kind) (A B : Ty) (r : Row) (R : TyList) : Prop :=
  ∃ d xc pn, F[f]? = some d ∧ d.cap = some (xc, τc, k) ∧ d.owns = [(pn, A)] ∧
    d.refs.map Prod.snd = R.toList.map (fun τ => (Mode.ro, τ)) ∧
    d.retp = none ∧ d.ret = B ∧ d.row = r ∧ τc.complete = true ∧ τc.rfree = true

theorem map_ro_inj : ∀ {R R' : TyList}, R.toList.map (fun τ => (Mode.ro, τ)) = R'.toList.map (fun τ => (Mode.ro, τ)) →
    R = R'
  | .nil, .nil, _ => rfl
  | .nil, .cons _ _, h => by simp [TyList.toList] at h
  | .cons _ _, .nil, h => by simp [TyList.toList] at h
  | .cons _ _, .cons _ _, h => by
    simp only [TyList.toList, List.map_cons, List.cons.injEq, Prod.mk.injEq, true_and] at h
    rw [h.1, map_ro_inj h.2]

/-- What a closure captured has no place lent out of it. -/
theorem CloOk.complete : CloOk F f τc k A B r R → τc.complete = true :=
  fun ⟨_, _, _, _, _, _, _, _, _, _, h⟩ => h.1

/-- What a closure captured is said of no region. -/
theorem CloOk.rfree : CloOk F f τc k A B r R → τc.rfree = true :=
  fun ⟨_, _, _, _, _, _, _, _, _, _, h⟩ => h.2

/-- A closure's code says its type. -/
theorem CloOk.det : CloOk F f τc k A B r R → CloOk F f τc' k' A' B' r' R' →
    τc = τc' ∧ k = k' ∧ A = A' ∧ B = B' ∧ r = r' ∧ R = R' := by
  rintro ⟨d, xc, pn, hd, hcap, hown, hrefs, -, hret, hrow, -⟩ ⟨d', xc', pn', hd', hcap', hown', hrefs', -, hret', hrow', -⟩
  rw [hd] at hd'
  cases hd'
  rw [hcap] at hcap'
  rw [hown] at hown'
  simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hcap' hown'
  exact ⟨hcap'.2.1, hcap'.2.2, hown'.2, hret.symm.trans hret', hrow.symm.trans hrow', map_ro_inj (hrefs.symm.trans hrefs')⟩

/-- What the continuations a value may hold are taken to be: given the store their frames were
suspended at, their frames, their fiber, their type and their cells. -/
structure World where
  kok : Store → List Kont → Nat → Ty → List Nat → Prop

/-- Where code runs: the arenas of the regions it is in, the innermost first; the fiber it runs on;
and the world it is checked in. -/
structure Iota where
  arenas : List Nat
  fiber : Nat := 0
  w : World := ⟨fun _ _ _ _ _ => False⟩

instance : EmptyCollection Iota := ⟨{ arenas := [] }⟩

/-- The regions `k` out, in the same fiber and world. -/
def Iota.drop (k : Nat) (ι : Iota) : Iota := { ι with arenas := ι.arenas.drop k }

/-- One region in, its arena `a`. -/
def Iota.push (ι : Iota) (a : Nat) : Iota := { ι with arenas := a :: ι.arenas }

@[simp] theorem Iota.drop_arenas (ι : Iota) : (ι.drop k).arenas = ι.arenas.drop k := rfl
@[simp] theorem Iota.push_arenas (ι : Iota) : (ι.push a).arenas = a :: ι.arenas := rfl
@[simp] theorem Iota.drop_zero (ι : Iota) : ι.drop 0 = ι := rfl
@[simp] theorem Iota.drop_drop (ι : Iota) : (ι.drop k).drop j = ι.drop (j + k) := by
  simp only [Iota.drop, List.drop_drop]; congr 2; omega
@[simp] theorem Iota.push_drop_succ (ι : Iota) : (ι.push a).drop (k + 1) = ι.drop k := rfl

/-- A reference to a cell of the region `k` regions out, among the arenas `ι`, holding a `τ`. -/
def RefOk (ι : Iota) (σ : Store) (k : Nat) (τ : Ty) (l : Nat) : Prop :=
  ∃ a, ι.arenas[k]? = some a ∧ σ.rt l = some (a, τ)

/-- Data a region holds, of type `τ` said of that region, its arenas from it outwards `ι`: plain
data, or, for a list of the region, its elements' cells, each a cell of the region holding a `τ`. -/
def RD (ι : Iota) (σ : Store) : Ty → Val → Prop
  | .int, .int _ => True
  | .rref _ k τ, .rptr l => RefOk ι σ k τ l
  | .vec _ τ, .vec ls => ∀ l ∈ ls, RefOk ι σ 0 τ l
  | _, _ => False

/-- `a` holds a value of type `τ`, whose cells — `a` and every cell of its boxes — are `L`. -/
inductive LT (F : List Fn) (ι : Iota) (σ : Store) : Nat → Ty → List Nat → Prop
  | int : σ.mem a = some (.int n) → LT F ι σ a .int [a]
  | box : σ.mem a = some (.ptr b) → LT F ι σ b τ R → a ∉ R → LT F ι σ a (.box τ) (a :: R)
  | clo : σ.mem a = some (.clo f c τc) → CloOk F f τc k A B r Rf → LT F ι σ c τc R → a ∉ R →
      LT F ι σ a (.fn k A B r Rf) (a :: R)
  | pair : σ.mem a = some (.pair b c) → LT F ι σ b A R₁ → LT F ι σ c B R₂ → (∀ x ∈ R₁, x ∉ R₂) →
      a ∉ R₁ ++ R₂ → LT F ι σ a (.pair A B) (a :: (R₁ ++ R₂))
  | tag : σ.mem a = some (.tag A' B' t b) → LT F ι σ b (if t then A else B) R → a ∉ R → LT F ι σ a (.sum A B) (a :: R)
  /-- A place lent: what is there is the borrow's. -/
  | hole : LT F ι σ a (.hole τ) []
  /-- A reference into a region: the cell holding it is its holder's, the cell it refers to the
  region's. -/
  | rref : σ.mem a = some (.rptr l) → RefOk ι σ k τ l → LT F ι σ a (.rref c k τ) [a]
  /-- The arena of the region `k` regions out, which is `a`: its cells, every cell tagged as the
  region's, each holding data of the region. -/
  | arena : ι.arenas[k]? = some a → σ.mem a = some (.arena cs) → cs.Nodup → a ∉ cs →
      (∀ l ∈ cs, ∃ τ v, σ.rt l = some (a, τ) ∧ σ.mem l = some v ∧ RD (ι.drop k) σ τ v) →
      (∀ l x, σ.rt l = some (a, x) → l ∈ cs) → LT F ι σ a (.arena k) (a :: cs)
  /-- A vector: its cell holds its elements' cells, each holding a `τ`, their trees apart. -/
  | vec {cs : List Nat} {Rs : List (List Nat)} : σ.mem a = some (.vec cs) → Rs.length = cs.length →
      (∀ i (h : i < cs.length) (h' : i < Rs.length), LT F ι σ cs[i] τ Rs[i]) → Rs.flatten.Nodup →
      a ∉ Rs.flatten → LT F ι σ a (.vec g τ) (a :: Rs.flatten)

/-- A value of type `τ`, and the cells it owns. -/
inductive VT (F : List Fn) (ι : Iota) (σ : Store) : Ty → Val → List Nat → Prop
  | int : VT F ι σ .int (.int n) []
  | box : LT F ι σ b τ R → τ.complete → VT F ι σ (.box τ) (.ptr b) R
  | clo : CloOk F f τc k A B r Rf → LT F ι σ c τc R → τc.complete → VT F ι σ (.fn k A B r Rf) (.clo f c τc) R
  | pair : LT F ι σ b A R₁ → LT F ι σ c B R₂ → (∀ x ∈ R₁, x ∉ R₂) → A.complete → B.complete →
      VT F ι σ (.pair A B) (.pair b c) (R₁ ++ R₂)
  | tag : LT F ι σ b (if t then A else B) R → A.complete → B.complete → VT F ι σ (.sum A B) (.tag A' B' t b) R
  | rref : RefOk ι σ k τ l → VT F ι σ (.rref c k τ) (.rptr l) []
  | vec {cs : List Nat} {Rs : List (List Nat)} : Rs.length = cs.length → (∀ i (h : i < cs.length) (h' : i < Rs.length), LT F ι σ cs[i] τ Rs[i]) →
      Rs.flatten.Nodup → τ.complete → VT F ι σ (.vec g τ) (.vec cs) Rs.flatten

def Disj (A B : List Nat) : Prop := ∀ x ∈ A, x ∉ B

/-- Every allocated cell is below `next`. -/
def WF (σ : Store) : Prop := ∀ l, σ.mem l ≠ none → l < σ.next

/-- What region cells are tagged with stays so. -/
def RtExt (σ σ' : Store) : Prop := ∀ l x, σ.rt l = some x → σ'.rt l = some x

/-- Two stores agree at the cells `L`, and the later keeps the region tags of the earlier. -/
structure Agree (σ σ' : Store) (L : List Nat) : Prop where
  mem : ∀ l ∈ L, σ'.mem l = σ.mem l
  rt : RtExt σ σ'
  /-- No region whose arena cell is among `L` gained a cell. -/
  fresh : ∀ a ∈ L, ∀ l x, σ'.rt l = some (a, x) → σ.rt l = some (a, x)

instance : CoeFun (Agree σ σ' L) (fun _ => ∀ l ∈ L, σ'.mem l = σ.mem l) := ⟨Agree.mem⟩

theorem RtExt.refl : RtExt σ σ := fun _ _ h => h

theorem RtExt.trans (h₁ : RtExt σ σ') (h₂ : RtExt σ' σ'') : RtExt σ σ'' := fun l x h => h₂ l x (h₁ l x h)

theorem RtExt.of_eq (h : σ'.rt = σ.rt) : RtExt σ σ' := fun l x hx => by rw [h]; exact hx

/-- Agreement at fewer cells. -/
theorem Agree.mono (h : Agree σ σ' L) (hL : ∀ l ∈ L', l ∈ L) : Agree σ σ' L' :=
  ⟨fun l hl => h l (hL l hl), h.rt, fun a ha => h.fresh a (hL a ha)⟩

theorem Agree.trans (h₁ : Agree σ σ' L) (h₂ : Agree σ' σ'' L) : Agree σ σ'' L :=
  ⟨fun l hl => (h₂ l hl).trans (h₁ l hl), h₁.rt.trans h₂.rt,
    fun a ha l x hx => h₁.fresh a ha l x (h₂.fresh a ha l x hx)⟩

/-- Stores with the same region tags agree wherever their cells do. -/
theorem Agree.of (h : ∀ l ∈ L, σ'.mem l = σ.mem l) (hrt : σ'.rt = σ.rt) : Agree σ σ' L :=
  ⟨h, fun l x hx => by rw [hrt]; exact hx, fun _ _ l x hx => by rw [← hrt]; exact hx⟩

theorem Agree.self : Agree σ σ L := ⟨fun _ _ => rfl, RtExt.refl, fun _ _ _ _ h => h⟩

/-- Agreement through a store that kept the region tags of one that agreed. -/
theorem Agree.ofTrans {L0 : List Nat} (h : Agree σ σ1 L0) (hL : ∀ l ∈ L, l ∈ L0)
    (hmem : ∀ l ∈ L, σ'.mem l = σ.mem l) (hrt : σ'.rt = σ1.rt) : Agree σ σ' L :=
  ⟨hmem, h.rt.trans (RtExt.of_eq hrt), fun a ha l x hx => h.fresh a (hL a ha) l x (by rw [← hrt]; exact hx)⟩

/-- Agreement through a store with the region tags of the first, which then agreed with the last. -/
theorem Agree.ofPre {L0 : List Nat} (hrt : σ1.rt = σ.rt) (h : Agree σ1 σ' L0) (hL : ∀ l ∈ L, l ∈ L0)
    (hmem : ∀ l ∈ L, σ'.mem l = σ.mem l) : Agree σ σ' L :=
  ⟨hmem, (RtExt.of_eq hrt).trans h.rt, fun a ha l x hx => by rw [← hrt]; exact h.fresh a (hL a ha) l x hx⟩

@[simp] theorem Store.set_rt {σ : Store} : (σ.set l v).rt = σ.rt := rfl
@[simp] theorem Store.alloc_rt {σ : Store} : (σ.alloc v).2.rt = σ.rt := rfl
@[simp] theorem Store.fresh_rt {σ : Store} : σ.fresh.2.rt = σ.rt := rfl


theorem Disj.symm : Disj A B → Disj B A := fun h x hb ha => h x ha hb

theorem Disj.mono_left : Disj A B → (∀ x ∈ C, x ∈ A) → Disj C B := fun h hc x hx => h x (hc x hx)

theorem Disj.mono_right : Disj A B → (∀ x ∈ C, x ∈ B) → Disj A C :=
  fun h hc x hx hcx => h x hx (hc x hcx)

theorem disj_nil_left : Disj [] B := fun _ h => by simp at h

theorem disj_nil_right : Disj A [] := fun _ _ h => by simp at h

theorem disj_append_left : Disj (A ++ B) C ↔ Disj A C ∧ Disj B C := by
  constructor
  · intro h
    exact ⟨fun x hx => h x (List.mem_append.mpr (.inl hx)), fun x hx => h x (List.mem_append.mpr (.inr hx))⟩
  · intro ⟨h1, h2⟩ x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h1 x hx
    · exact h2 x hx

theorem disj_append_right : Disj A (B ++ C) ↔ Disj A B ∧ Disj A C := by
  constructor
  · intro h
    exact ⟨fun x hx hb => h x hx (List.mem_append.mpr (.inl hb)),
      fun x hx hc => h x hx (List.mem_append.mpr (.inr hc))⟩
  · intro ⟨h1, h2⟩ x hx hbc
    rcases List.mem_append.mp hbc with hb | hc
    · exact h1 x hx hb
    · exact h2 x hx hc

theorem disj_cons_left : Disj (a :: A) B ↔ a ∉ B ∧ Disj A B := by
  constructor
  · intro h
    exact ⟨h a (List.mem_cons_self ..), fun x hx => h x (List.mem_cons_of_mem _ hx)⟩
  · intro ⟨h1, h2⟩ x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h1
    · exact h2 x hx

theorem nodup_append_disj : (A ++ B).Nodup ↔ A.Nodup ∧ B.Nodup ∧ Disj A B := by
  rw [List.nodup_append]
  constructor
  · intro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun x hx hb => h3 x hx x hb rfl⟩
  · intro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun x hx y hy hxy => h3 x hx (hxy ▸ hy)⟩

/-! ## Trees -/

theorem mem_flatten_idx {Rs : List (List Nat)} : l ∈ Rs.flatten ↔ ∃ i, ∃ h : i < Rs.length, l ∈ Rs[i] := by
  simp only [List.mem_flatten]
  constructor
  · rintro ⟨R, hR, hl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hR
    exact ⟨i, hi, hl⟩
  · rintro ⟨i, hi, hl⟩
    exact ⟨_, List.getElem_mem hi, hl⟩

theorem mem_flatten_of {Rs : List (List Nat)} {i : Nat} (hi : i < Rs.length) (hl : l ∈ Rs[i]) : l ∈ Rs.flatten :=
  mem_flatten_idx.mpr ⟨i, hi, hl⟩

theorem LT.head : LT F ι σ a τ L → τ.isHole = false → a ∈ L := by
  intro h hτ
  cases h <;> simp_all [Ty.isHole]

theorem LT.cons : LT F ι σ a τ L → τ.isHole = false → ∃ R, L = a :: R := by
  intro h hτ
  cases h <;> simp_all [Ty.isHole]

theorem RefOk.frame (h : RefOk ι σ k τ l) (hr : RtExt σ σ') : RefOk ι σ' k τ l :=
  let ⟨a, ha, ht⟩ := h; ⟨a, ha, hr l _ ht⟩

theorem RD.frame {v : Val} (h : RD ι σ τ v) (hr : RtExt σ σ') : RD ι σ' τ v := by
  cases τ <;> cases v <;> simp only [RD] at h ⊢
  all_goals first | trivial | exact RefOk.frame h hr | exact fun l hl => (h l hl).frame hr

theorem LT.alloc : LT F ι σ a τ L → ∀ l ∈ L, σ.mem l ≠ none := by
  intro h
  induction h with
  | hole => intro l hl; simp at hl
  | int ha => intro l hl; simp at hl; subst hl; simp [ha]
  | box ha _ _ ih | clo ha _ _ _ ih | tag ha _ _ ih =>
    intro l hl
    rcases List.mem_cons.mp hl with rfl | hl
    · simp [ha]
    · exact ih l hl
  | pair ha _ _ _ _ ih1 ih2 =>
    intro l hl
    rcases List.mem_cons.mp hl with rfl | hl
    · simp [ha]
    · rcases List.mem_append.mp hl with hl | hl
      · exact ih1 l hl
      · exact ih2 l hl
  | rref ha _ => intro l hl; simp at hl; subst hl; simp [ha]
  | arena _ ha _ _ hcs _ =>
    intro l hl
    rcases List.mem_cons.mp hl with rfl | hl
    · simp [ha]
    · obtain ⟨_, _, _, hv, _⟩ := hcs l hl
      simp [hv]
  | vec ha hlen _ _ _ ih =>
    intro l hl
    rcases List.mem_cons.mp hl with rfl | hl
    · simp [ha]
    · obtain ⟨i, hi, hl⟩ := mem_flatten_idx.mp hl
      exact ih i (hlen ▸ hi) hi l hl

theorem LT.nodup : LT F ι σ a τ L → L.Nodup := by
  intro h
  induction h with
  | hole => simp
  | int => simp
  | box _ _ hn ih | clo _ _ _ hn ih | tag _ _ hn ih => exact List.nodup_cons.mpr ⟨hn, ih⟩
  | pair _ _ _ hd hn ih1 ih2 =>
    exact List.nodup_cons.mpr ⟨hn, List.nodup_append.mpr ⟨ih1, ih2, fun x hx y hy e => hd x hx (e ▸ hy)⟩⟩
  | rref => simp
  | arena _ _ hnd hn => exact List.nodup_cons.mpr ⟨hn, hnd⟩
  | vec _ _ _ hnd hn => exact List.nodup_cons.mpr ⟨hn, hnd⟩

theorem LT.frame : LT F ι σ a τ L → Agree σ σ' L → LT F ι σ' a τ L := by
  intro h
  induction h with
  | hole => intro _; exact .hole
  | int ha =>
    intro hag
    exact .int (by rw [hag _ (List.mem_singleton_self _)]; exact ha)
  | box ha _ hn ih =>
    intro hag
    refine .box (by rw [hag _ (List.mem_cons_self ..)]; exact ha) (ih (hag.mono fun l hl => List.mem_cons_of_mem _ hl)) hn
  | clo ha hc _ hn ih =>
    intro hag
    exact .clo (by rw [hag _ (List.mem_cons_self ..)]; exact ha) hc (ih (hag.mono fun l hl => List.mem_cons_of_mem _ hl)) hn
  | tag ha _ hn ih =>
    intro hag
    exact .tag (by rw [hag _ (List.mem_cons_self ..)]; exact ha) (ih (hag.mono fun l hl => List.mem_cons_of_mem _ hl)) hn
  | pair ha _ _ hd hn ih1 ih2 =>
    intro hag
    exact .pair (by rw [hag _ (List.mem_cons_self ..)]; exact ha)
      (ih1 (hag.mono fun l hl => List.mem_cons_of_mem _ (List.mem_append.mpr (.inl hl))))
      (ih2 (hag.mono fun l hl => List.mem_cons_of_mem _ (List.mem_append.mpr (.inr hl)))) hd hn
  | rref ha hr =>
    intro hag
    exact .rref (by rw [hag _ (List.mem_singleton_self _)]; exact ha) (hr.frame hag.rt)
  | arena hk ha hnd hn hcs hex =>
    intro hag
    refine .arena hk (by rw [hag _ (List.mem_cons_self ..)]; exact ha) hnd hn (fun l hl => ?_)
      (fun l x hx => hex l x (hag.fresh _ (List.mem_cons_self ..) l x hx))
    obtain ⟨τ, v, hrt, hv, hrd⟩ := hcs l hl
    exact ⟨τ, v, hag.rt l _ hrt, by rw [hag l (List.mem_cons_of_mem _ hl)]; exact hv, hrd.frame hag.rt⟩
  | vec ha hlen _ hnd hn ih =>
    intro hag
    exact .vec (by rw [hag _ (List.mem_cons_self ..)]; exact ha) hlen
      (fun i h h' => ih i h h' (hag.mono fun l hl => List.mem_cons_of_mem _ (mem_flatten_of h' hl))) hnd hn

theorem LT.det : LT F ι σ a τ L → LT F ι σ a τ L' → L = L' := by
  intro h
  induction h generalizing L' with
  | hole => intro h'; cases h'; rfl
  | int => intro h'; cases h'; rfl
  | box ha _ _ ih =>
    intro h'
    cases h' with
    | box ha' hb' _ =>
      rw [ha] at ha'
      cases ha'
      rw [ih hb']
  | clo ha _ _ _ ih =>
    intro h'
    cases h' with
    | clo ha' _ hb' _ =>
      rw [ha] at ha'
      cases ha'
      rw [ih hb']
  | pair ha _ _ _ _ ih1 ih2 =>
    intro h'
    cases h' with
    | pair ha' h1 h2 _ _ =>
      rw [ha] at ha'
      cases ha'
      rw [ih1 h1, ih2 h2]
  | tag ha _ _ ih =>
    intro h'
    cases h' with
    | tag ha' hb' _ =>
      rw [ha] at ha'
      cases ha'
      rw [ih hb']
  | rref => intro h'; cases h'; rfl
  | arena _ ha =>
    intro h'
    cases h' with
    | arena _ ha' =>
      rw [ha] at ha'
      cases ha'
      rfl
  | vec ha hlen _ _ _ ih =>
    intro h'
    cases h' with
    | vec ha' hlen' hel' _ _ =>
      rw [ha] at ha'
      cases ha'
      congr 2
      exact List.ext_getElem (hlen.trans hlen'.symm) fun i h1 h2 => ih i (hlen ▸ h1) h1 (hel' i (hlen ▸ h1) h2)

/-- What holds a closure is a closure, unless it is lent. -/
theorem LT.det_fn : LT F ι σ a (.fn k A B r Rf) L → LT F ι σ a τ L' → τ.isHole = false →
    τ = .fn k A B r Rf ∧ L = L' := by
  intro h h' hτ
  cases h with
  | clo ha hc hb _ =>
    cases h' with
    | int ha' => rw [ha] at ha'; cases ha'
    | box ha' => rw [ha] at ha'; cases ha'
    | pair ha' => rw [ha] at ha'; cases ha'
    | tag ha' => rw [ha] at ha'; cases ha'
    | hole => simp [Ty.isHole] at hτ
    | rref ha' => rw [ha] at ha'; cases ha'
    | arena _ ha' => rw [ha] at ha'; cases ha'
    | vec ha' => rw [ha] at ha'; cases ha'
    | clo ha' hc' hb' _ =>
      rw [ha] at ha'
      cases ha'
      obtain ⟨-, rfl, rfl, rfl, rfl, rfl⟩ := hc'.det hc
      rw [LT.det hb hb']
      exact ⟨rfl, rfl⟩

/-- A location holding a tree with a cell holds no place lent. -/
theorem LT.nonhole_of (h : LT F ι σ a τ L) (h' : LT F ι σ a τ' L) (hτ' : τ'.isHole = false) : τ.isHole = false := by
  cases hτ : τ.isHole
  · rfl
  · obtain ⟨R, rfl⟩ := h'.cons hτ'
    cases τ <;> simp [Ty.isHole] at hτ
    cases h

/-- A value has no place lent out of it. -/
theorem VT.complete : VT F ι σ τ v L → τ.complete = true := by
  intro h
  cases h <;> simp_all [Ty.complete]

theorem VT.alloc : VT F ι σ τ v L → ∀ l ∈ L, σ.mem l ≠ none := by
  intro h
  cases h with
  | int => simp
  | box h | clo _ h | tag h => exact h.alloc
  | pair h1 h2 _ =>
    intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact h1.alloc l hl
    · exact h2.alloc l hl
  | rref => simp
  | vec hlen hel _ _ =>
    intro l hl
    obtain ⟨i, hi, hl⟩ := mem_flatten_idx.mp hl
    exact (hel i (hlen ▸ hi) hi).alloc l hl

theorem VT.nodup : VT F ι σ τ v L → L.Nodup := by
  intro h
  cases h with
  | int => simp
  | box h | clo _ h | tag h => exact h.nodup
  | pair h1 h2 hd => exact List.nodup_append.mpr ⟨h1.nodup, h2.nodup, fun x hx y hy e => hd x hx (e ▸ hy)⟩
  | rref => simp
  | vec _ _ hnd _ => exact hnd

theorem VT.frame : VT F ι σ τ v L → Agree σ σ' L → VT F ι σ' τ v L := by
  intro h hag
  cases h with
  | int => exact .int
  | box h hc => exact .box (h.frame hag) hc
  | clo hc h hc' => exact .clo hc (h.frame hag) hc'
  | tag h hA hB => exact .tag (h.frame hag) hA hB
  | pair h1 h2 hd hA hB =>
    have e1 := h1.frame (σ' := σ') (hag.mono fun l hl => List.mem_append.mpr (.inl hl))
    have e2 := h2.frame (σ' := σ') (hag.mono fun l hl => List.mem_append.mpr (.inr hl))
    exact .pair e1 e2 hd hA hB
  | rref h => exact .rref (h.frame hag.rt)
  | vec hlen hel hnd hc =>
    exact .vec hlen (fun i h h' => (hel i h h').frame (hag.mono fun l hl => mem_flatten_of h' hl)) hnd hc

theorem agree_set : l ∉ L → Agree σ (σ.set l v) L := by
  intro h
  refine Agree.of (fun x hx => ?_) rfl
  simp only [Store.set]
  split
  · subst_vars; exact absurd hx h
  · rfl

theorem agree_alloc (hwf : WF σ) (hL : ∀ l ∈ L, σ.mem l ≠ none) : Agree σ (σ.alloc v).2 L := by
  refine Agree.of (fun x hx => ?_) rfl
  simp only [Store.alloc]
  split
  · subst_vars; exact absurd (hwf _ (hL _ hx)) (Nat.lt_irrefl _)
  · rfl

theorem WF.set (hwf : WF σ) (hl : l < σ.next) : WF (σ.set l v) := by
  intro x hx
  simp only [Store.set] at hx ⊢
  split at hx
  · subst_vars; exact hl
  · exact hwf x hx

theorem WF.set_none (hwf : WF σ) : WF (σ.set l none) := by
  intro x hx
  simp only [Store.set] at hx ⊢
  split at hx
  · simp at hx
  · exact hwf x hx

theorem WF.alloc (hwf : WF σ) : WF (σ.alloc v).2 := by
  intro x hx
  simp only [Store.alloc] at hx ⊢
  split at hx
  · subst_vars; exact Nat.lt_succ_self _
  · exact Nat.lt_succ_of_lt (hwf x hx)

/-- What a location holds: a value of its type, owning the rest of its footprint. -/
theorem LT.contents : LT F ι σ b τ R → τ.complete = true →
    ∃ w R', σ.mem b = some w ∧ VT F ι σ τ w R' ∧ R = b :: R' ∧ b ∉ R' := by
  intro h hc
  cases h with
  | int ha => exact ⟨_, [], ha, .int, rfl, by simp⟩
  | box ha hb hn => exact ⟨_, _, ha, .box hb (by simpa [Ty.complete] using hc), rfl, hn⟩
  | clo ha hc' hb hn => exact ⟨_, _, ha, .clo hc' hb (CloOk.complete hc'), rfl, hn⟩
  | pair ha h1 h2 hd hn =>
    simp only [Ty.complete, Bool.and_eq_true] at hc
    exact ⟨_, _, ha, .pair h1 h2 hd hc.1 hc.2, rfl, hn⟩
  | tag ha hb hn =>
    simp only [Ty.complete, Bool.and_eq_true] at hc
    exact ⟨_, _, ha, .tag hb hc.1 hc.2, rfl, hn⟩
  | hole => simp [Ty.complete] at hc
  | rref ha hr => exact ⟨_, [], ha, .rref hr, rfl, by simp⟩
  | arena => simp [Ty.complete] at hc
  | vec ha hlen hel hnd hn => exact ⟨_, _, ha, .vec hlen hel hnd (by simpa [Ty.complete] using hc), rfl, hn⟩

theorem LT.of_contents : σ.mem b = some w → VT F ι σ τ w R' → b ∉ R' → LT F ι σ b τ (b :: R') := by
  intro ha hv hn
  cases hv with
  | int => exact .int ha
  | box hb => exact .box ha hb hn
  | clo hc hb => exact .clo ha hc hb hn
  | pair h1 h2 hd => exact .pair ha h1 h2 hd hn
  | tag hb => exact .tag ha hb hn
  | rref hr => exact .rref ha hr
  | vec hlen hel hnd => exact .vec ha hlen hel hnd hn

/-! ## Dropping -/

/-- Dropping a vector's elements in order frees exactly their cells. -/
theorem dropElems_ok
    (ih : ∀ (τ : Ty) (σ : Store) v L, VT F ι σ τ v L → L.length ≤ k →
      ∃ σ', dropK k σ τ v = some σ' ∧ σ'.next = σ.next ∧ (∀ l ∈ L, σ'.mem l = none) ∧
        (∀ l, l ∉ L → σ'.mem l = σ.mem l) ∧ σ'.rt = σ.rt) (hc : τ.complete = true) :
    ∀ (cs : List Nat) (Rs : List (List Nat)) (σ : Store), Rs.length = cs.length →
      (∀ i (h : i < cs.length) (h' : i < Rs.length), LT F ι σ cs[i] τ Rs[i]) → Rs.flatten.Nodup →
      Rs.flatten.length ≤ k + 1 →
      ∃ σ', dropCellsWith (fun σ w => dropK k σ τ w) σ cs = some σ' ∧ σ'.next = σ.next ∧ (∀ l ∈ Rs.flatten, σ'.mem l = none) ∧
        (∀ l, l ∉ Rs.flatten → σ'.mem l = σ.mem l) ∧ σ'.rt = σ.rt
  | [], Rs, σ, hlen, _, _, _ => by
    obtain rfl : Rs = [] := List.eq_nil_of_length_eq_zero hlen
    exact ⟨σ, rfl, rfl, by simp, fun _ _ => rfl, rfl⟩
  | c :: cs, Rs, σ, hlen, hel, hnd, hk => by
    cases Rs with
    | nil => simp at hlen
    | cons R Rs =>
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    simp only [List.flatten_cons, List.length_append] at hk hnd
    have hdisj := (List.nodup_append.mp hnd)
    have h0 := hel 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero] at h0
    obtain ⟨w, R', hw, hv, rfl, hn⟩ := h0.contents hc
    simp only [List.length_cons] at hk
    obtain ⟨σ1, hd, hnext1, hfree1, hkeep1, hrt1⟩ := ih τ σ w R' hv (by omega)
    have hout : ∀ l ∈ Rs.flatten, l ∉ c :: R' := fun l hl h => hdisj.2.2 l h l hl rfl
    have hag : ∀ l ∈ Rs.flatten, (σ1.set c none).mem l = σ.mem l := fun l hl => by
      have h1 := hout l hl
      simp only [List.mem_cons, not_or] at h1
      simp only [Store.set, h1.1, ↓reduceIte]
      exact hkeep1 l h1.2
    have hel' : ∀ i (h : i < cs.length) (h' : i < Rs.length), LT F ι (σ1.set c none) cs[i] τ Rs[i] := fun i h h' =>
      (hel (i + 1) (by simp; omega) (by simp; omega)).frame (Agree.of (fun l hl => hag l (mem_flatten_of h' hl))
        (by simp [hrt1]))
    obtain ⟨σ2, hd2, hnext2, hfree2, hkeep2, hrt2⟩ := dropElems_ok ih hc cs Rs (σ1.set c none) hlen hel' hdisj.2.1 (by omega)
    refine ⟨σ2, by simp [dropCellsWith, hw, hd, hd2], by simp [hnext2, Store.set, hnext1], ?_, ?_, by simp [hrt2, hrt1]⟩
    · intro l hl
      rcases List.mem_append.mp hl with hl | hl
      · have : l ∉ Rs.flatten := fun h => hout l h hl
        rw [hkeep2 l this]
        rcases List.mem_cons.mp hl with rfl | hl
        · simp [Store.set]
        · have hlc : l ≠ c := fun e => hn (e ▸ hl)
          simp [Store.set, hlc, hfree1 l hl]
      · exact hfree2 l hl
    · intro l hl
      simp only [List.flatten_cons, List.mem_append, List.mem_cons, not_or] at hl
      obtain ⟨⟨hlc, hl1⟩, hl2⟩ := hl
      rw [hkeep2 l hl2]
      simp only [Store.set, hlc, ↓reduceIte]
      exact hkeep1 l hl1

/-- Distinct numbers below `n` are at most `n` of them. -/
theorem nodup_length_le : ∀ (n : Nat) (L : List Nat), L.Nodup → (∀ x ∈ L, x < n) → L.length ≤ n
  | 0, [], _, _ => Nat.le_refl _
  | 0, x :: _, _, h => absurd (h x (List.mem_cons_self ..)) (Nat.not_lt_zero _)
  | n + 1, L, hn, h => by
    have h' : ∀ x ∈ L.erase n, x < n := fun x hx => by
      have hne : x ≠ n := fun e => by subst e; exact (List.Nodup.mem_erase_iff hn).mp hx |>.1 rfl
      have := h x (List.mem_of_mem_erase hx)
      omega
    have ih := nodup_length_le n (L.erase n) (hn.erase n) h'
    have := List.length_erase (a := n) (l := L)
    split at this <;> omega

/-- A list of distinct cells, all allocated, is no longer than the store. -/
theorem length_le_next {L : List Nat} (hwf : WF σ) (hn : L.Nodup) (ha : ∀ l ∈ L, σ.mem l ≠ none) : L.length ≤ σ.next :=
  nodup_length_le σ.next L hn fun l hl => hwf l (ha l hl)

/-- Dropping a value with as many cells to spare as it owns frees exactly the cells it owns. -/
theorem dropK_ok : ∀ (k : Nat) (τ : Ty) (σ : Store) v L, VT F ι σ τ v L → L.length ≤ k →
    ∃ σ', dropK k σ τ v = some σ' ∧ σ'.next = σ.next ∧ (∀ l ∈ L, σ'.mem l = none) ∧
      (∀ l, l ∉ L → σ'.mem l = σ.mem l) ∧ σ'.rt = σ.rt := by
  intro k
  induction k with
  | zero =>
    intro τ σ v L h hk
    cases h with
    | int => exact ⟨σ, by simp [dropK], rfl, by simp, fun _ _ => rfl, rfl⟩
    | rref => exact ⟨σ, by simp [dropK], rfl, by simp, fun _ _ => rfl, rfl⟩
    | box hb hc => obtain ⟨R, rfl⟩ := hb.cons (Ty.complete_not_hole hc); simp at hk
    | clo _ hb hc => obtain ⟨R, rfl⟩ := hb.cons (Ty.complete_not_hole hc); simp at hk
    | pair h1 _ _ hc _ => obtain ⟨R, rfl⟩ := h1.cons (Ty.complete_not_hole hc); simp at hk
    | tag hb hA hB => obtain ⟨R, rfl⟩ := hb.cons (Ty.complete_not_hole (Ty.complete_ite hA hB)); simp at hk
    | vec hlen hel hnd hc =>
      rename_i τ' cs Rs
      cases cs with
      | nil =>
        obtain rfl : Rs = [] := List.eq_nil_of_length_eq_zero hlen
        exact ⟨σ, by simp [dropK], rfl, by simp, fun _ _ => rfl, rfl⟩
      | cons c cs =>
        have h0 := hel 0 (by simp) (by simp [hlen])
        obtain ⟨R, hR⟩ := h0.cons (Ty.complete_not_hole hc)
        have := List.length_pos_of_mem (mem_flatten_of (Rs := Rs) (i := 0) (by simp [hlen])
          (by rw [hR]; exact List.mem_cons_self ..))
        omega
  | succ k ih =>
    intro τ σ v L h hk
    cases h with
    | int => exact ⟨σ, by simp [dropK], rfl, by simp, fun _ _ => rfl, rfl⟩
    | rref => exact ⟨σ, by simp [dropK], rfl, by simp, fun _ _ => rfl, rfl⟩
    | vec hlen hel hnd hc =>
      rename_i τ' cs Rs
      obtain ⟨σ', h1, h2, h3, h4, h5⟩ := dropElems_ok ih hc cs Rs σ hlen hel hnd hk
      exact ⟨σ', by simpa [dropK] using h1, h2, h3, h4, h5⟩
    | @tag b t A B _ _ _ hb hA hB =>
      obtain ⟨w, R', hw, hv, rfl, hn⟩ := hb.contents (Ty.complete_ite hA hB)
      obtain ⟨σ1, hd, hnext, hfree, hkeep, hrt⟩ := ih _ σ w R' hv (by simpa using hk)
      refine ⟨σ1.set b none, by simp [dropK, hw, hd], by simp [Store.set, hnext], ?_, ?_, by simp [hrt]⟩
      · intro l hl
        simp only [Store.set]
        split
        · rfl
        · rcases List.mem_cons.mp hl with rfl | hl
          · contradiction
          · exact hfree l hl
      · intro l hl
        simp only [Store.set]
        split
        · subst_vars; simp at hl
        · exact hkeep l (fun h => hl (List.mem_cons_of_mem _ h))
    | @box b _ _ hb hc =>
      obtain ⟨w, R', hw, hv, rfl, hn⟩ := hb.contents hc
      obtain ⟨σ1, hd, hnext, hfree, hkeep, hrt⟩ := ih _ σ w R' hv (by simpa using hk)
      refine ⟨σ1.set b none, by simp [dropK, hw, hd], by simp [Store.set, hnext], ?_, ?_, by simp [hrt]⟩
      · intro l hl
        simp only [Store.set]
        split
        · rfl
        · rcases List.mem_cons.mp hl with rfl | hl
          · contradiction
          · exact hfree l hl
      · intro l hl
        simp only [Store.set]
        split
        · subst_vars; simp at hl
        · exact hkeep l (fun h => hl (List.mem_cons_of_mem _ h))
    | @clo f τc _ _ _ _ _ c _ hc hb hcc =>
      obtain ⟨w, R', hw, hv, rfl, hn⟩ := hb.contents hcc
      obtain ⟨σ1, hd, hnext, hfree, hkeep, hrt⟩ := ih _ σ w R' hv (by simpa using hk)
      refine ⟨σ1.set c none, by simp [dropK, hw, hd], by simp [Store.set, hnext], ?_, ?_, by simp [hrt]⟩
      · intro l hl
        simp only [Store.set]
        split
        · rfl
        · rcases List.mem_cons.mp hl with rfl | hl
          · contradiction
          · exact hfree l hl
      · intro l hl
        simp only [Store.set]
        split
        · subst_vars; simp at hl
        · exact hkeep l (fun h => hl (List.mem_cons_of_mem _ h))
    | @pair b A R₁ c B R₂ h1 h2 hd hA hB =>
      obtain ⟨w, R₁', hw, hv1, rfl, hn1⟩ := h1.contents hA
      obtain ⟨u, R₂', hu, hv2, rfl, hn2⟩ := h2.contents hB
      simp only [List.length_append, List.length_cons] at hk
      obtain ⟨σ1, hd1, hnext1, hfree1, hkeep1, hrt1⟩ := ih _ σ w R₁' hv1 (by omega)
      have hcR : c ∉ R₁' := fun h => hd _ (List.mem_cons_of_mem _ h) (List.mem_cons_self ..)
      have hbc : c ≠ b := fun e => hd b (List.mem_cons_self ..) (e ▸ List.mem_cons_self ..)
      have hu1 : σ1.mem c = some u := by rw [hkeep1 c hcR, hu]
      have hag : Agree σ (σ1.set b none) R₂' := Agree.of (fun l hl => by
        have hb' : l ≠ b := fun e => hd b (List.mem_cons_self ..) (e ▸ List.mem_cons_of_mem _ hl)
        have hR1 : l ∉ R₁' := fun h => hd l (List.mem_cons_of_mem _ h) (List.mem_cons_of_mem _ hl)
        simp only [Store.set, hb', ↓reduceIte]
        exact hkeep1 l hR1) (by simp [hrt1])
      obtain ⟨σ2, hd2, hnext2, hfree2, hkeep2, hrt2⟩ := ih _ (σ1.set b none) u R₂' (hv2.frame hag) (by omega)
      refine ⟨σ2.set c none, by simp [dropK, hw, hd1, hu1, hd2], by simp [Store.set, hnext2, hnext1], ?_, ?_,
        by simp [hrt2, hrt1]⟩
      · intro l hl
        simp only [Store.set]
        split
        · rfl
        · rename_i hlc
          rcases List.mem_append.mp hl with hl | hl
          · rcases List.mem_cons.mp hl with rfl | hl
            · have : l ∉ R₂' := fun h => hd l (List.mem_cons_self ..) (List.mem_cons_of_mem _ h)
              rw [hkeep2 l this]; simp [Store.set]
            · have : l ∉ R₂' := fun h => hd l (List.mem_cons_of_mem _ hl) (List.mem_cons_of_mem _ h)
              have hlb : l ≠ b := fun e => hn1 (e ▸ hl)
              rw [hkeep2 l this]; simp [Store.set, hlb, hfree1 l hl]
          · rcases List.mem_cons.mp hl with rfl | hl
            · exact absurd rfl hlc
            · exact hfree2 l hl
      · intro l hl
        simp only [List.mem_append, List.mem_cons, not_or] at hl
        obtain ⟨⟨hlb, hl1⟩, hlc, hl2⟩ := hl
        simp only [Store.set, hlc, ↓reduceIte]
        rw [hkeep2 l hl2]
        simp only [Store.set, hlb, ↓reduceIte]
        exact hkeep1 l hl1

/-- Dropping a value frees exactly the cells it owns. -/
theorem drop_ok (hwf : WF σ) : ∀ (τ : Ty) v L, VT F ι σ τ v L →
    ∃ σ', drop σ τ v = some σ' ∧ σ'.next = σ.next ∧ (∀ l ∈ L, σ'.mem l = none) ∧
      ∀ l, l ∉ L → σ'.mem l = σ.mem l :=
  fun τ v L h =>
    let ⟨σ', h1, h2, h3, h4, _⟩ := dropK_ok σ.next τ σ v L h (length_le_next hwf h.nodup h.alloc)
    ⟨σ', h1, h2, h3, h4⟩

theorem dropCellsWith_rt (h1 : ∀ σ w σ', drop1 σ w = some σ' → Store.rt σ' = σ.rt) :
    ∀ (σ : Store) (cs : List Nat) σ', dropCellsWith drop1 σ cs = some σ' → σ'.rt = σ.rt
  | σ, [], σ', h => by simp [dropCellsWith] at h; subst h; rfl
  | σ, c :: cs, σ', h => by
    simp only [dropCellsWith] at h
    split at h
    · split at h
      · rename_i σ1 hd
        exact (dropCellsWith_rt h1 _ cs σ' h).trans (by simp only [Store.set_rt]; exact h1 _ _ _ hd)
      · cases h
    · cases h

/-- Dropping a value changes no region tag. -/
theorem dropK_rt : ∀ (k : Nat) (σ : Store) (τ : Ty) (v : Val) (σ' : Store), dropK k σ τ v = some σ' → σ'.rt = σ.rt := by
  intro k
  induction k with
  | zero =>
    intro σ τ v σ' h
    cases τ <;> cases v <;> (try simp [dropK] at h)
    all_goals try (subst h; rfl)
    rename_i cs
    cases cs <;> simp [dropK] at h
    subst h; rfl
  | succ k ih =>
    intro σ τ v σ' h
    cases τ <;> cases v <;> simp only [dropK, reduceCtorEq] at h
    all_goals try (cases h; rfl)
    all_goals try (exact dropCellsWith_rt (fun σ w σ' h' => ih σ _ w σ' h') _ _ _ h)
    all_goals
      revert h
      repeat' split
      all_goals intro h
      all_goals (try simp at h)
    all_goals (subst h; simp only [Store.set_rt]
               first
               | exact ih _ _ _ _ (by assumption)
               | (refine (ih _ _ _ _ (by assumption)).trans ?_; simp only [Store.set_rt]; exact ih _ _ _ _ (by assumption)))

theorem drop_rt (h : drop σ τ v = some σ') : σ'.rt = σ.rt := dropK_rt _ _ _ _ _ h

theorem dropCell_rt (h : dropCell σ τ c = some σ') : σ'.rt = σ.rt := by
  unfold dropCell at h
  split at h
  · cases h; rfl
  · obtain ⟨σ'', h1, rfl⟩ := Option.map_eq_some_iff.mp h
    exact (Store.set_rt).trans (drop_rt h1)
  · cases h

theorem dropCells_rt : ∀ (σ : Store) (cs : List (Ty × Nat)) (σ' : Store), dropCells σ cs = some σ' → σ'.rt = σ.rt
  | _, [], _, h => by cases h; rfl
  | σ, (τ, c) :: rest, σ', h => by
    simp only [dropCells] at h
    split at h
    · rename_i σ1 h1
      exact (dropCells_rt σ1 rest σ' h).trans (dropCell_rt h1)
    · cases h

theorem allocAll_rt : ∀ (σ : Store) (xs : List (Var × Val)), (allocAll σ xs).2.rt = σ.rt
  | _, [] => rfl
  | σ, (_, v) :: rest => by simp only [allocAll]; rw [allocAll_rt]; rfl

@[simp] theorem Store.freeAll_rt : ∀ {σ : Store} {cs : List Nat}, (σ.freeAll cs).rt = σ.rt
  | _, [] => rfl
  | σ, _ :: cs => (Store.freeAll_rt (σ := σ.set _ none) (cs := cs))

@[simp] theorem Store.freeAll_next : ∀ {σ : Store} {cs : List Nat}, (σ.freeAll cs).next = σ.next
  | _, [] => rfl
  | σ, _ :: cs => (Store.freeAll_next (σ := σ.set _ none) (cs := cs))

theorem Store.freeAll_mem : ∀ {σ : Store} {cs : List Nat} {x : Nat},
    (σ.freeAll cs).mem x = if x ∈ cs then none else σ.mem x
  | _, [], _ => by simp [Store.freeAll]
  | σ, c :: cs, x => by
    simp only [Store.freeAll]
    rw [Store.freeAll_mem]
    by_cases h1 : x ∈ cs
    · simp [h1]
    · by_cases h2 : x = c
      · subst h2; simp [h1, Store.set]
      · simp [h1, h2, Store.set]

/-- Proves that a store kept another's region tags, where it came from it by setting, allocating
or dropping. -/
macro "rt_tac" : tactic => `(tactic| first
  | rfl
  | (simp only [Store.set_rt, Store.alloc_rt, Store.fresh_rt, allocAll_rt, Store.freeAll_rt]; done)
  | exact drop_rt (by assumption)
  | exact (Store.set_rt).trans (drop_rt (by assumption))
  | exact dropCell_rt (by assumption)
  | exact dropCells_rt _ _ _ (by assumption)
  | assumption
  | (subst_vars; simp only [Store.set_rt, Store.alloc_rt, Store.fresh_rt, allocAll_rt]; done)
  | (simp only [Store.set_rt, Store.alloc_rt, Store.fresh_rt]; first
      | exact drop_rt (by assumption)
      | exact dropCell_rt (by assumption)
      | exact dropCells_rt _ _ _ (by assumption)
      | assumption))

/-- Agreement of stores with the same region tags. -/
theorem Agree.of' (h : ∀ l ∈ L, σ'.mem l = σ.mem l) (hrt : σ'.rt = σ.rt := by rt_tac) : Agree σ σ' L :=
  Agree.of h hrt

/-- Dropping a variable's cell frees its footprint: the cell, and what a live value in it owns. -/
theorem dropCell_live (hwf : WF σ) : LT F ι σ c τ L → τ.complete = true →
    ∃ σ', dropCell σ τ c = some σ' ∧ σ'.next = σ.next ∧ (∀ l ∈ L, σ'.mem l = none) ∧
      ∀ l, l ∉ L → σ'.mem l = σ.mem l := by
  intro h hc
  obtain ⟨w, R', hw, hv, rfl, hn⟩ := h.contents hc
  obtain ⟨σ1, hd, hnext, hfree, hkeep⟩ := drop_ok hwf τ w R' hv
  refine ⟨σ1.set c none, ?_, by simp [Store.set, hnext], ?_, ?_⟩
  · cases hv <;> simp [dropCell, hw, hd]
  · intro l hl
    simp only [Store.set]
    split
    · rfl
    · rcases List.mem_cons.mp hl with rfl | hl
      · contradiction
      · exact hfree l hl
  · intro l hl
    simp only [Store.set]
    split
    · subst_vars; simp at hl
    · exact hkeep l (fun h => hl (List.mem_cons_of_mem _ h))

theorem dropCell_moved : σ.mem c = some .moved →
    ∃ σ', dropCell σ τ c = some σ' ∧ σ'.next = σ.next ∧ σ'.mem c = none ∧
      ∀ l, l ≠ c → σ'.mem l = σ.mem l := by
  intro h
  refine ⟨σ.set c none, by simp [dropCell, h], rfl, by simp [Store.set], ?_⟩
  intro l hl
  simp [Store.set, hl]

/-! ## Paths: how a place reaches into a variable's tree -/

/-- Following boxes, closures' captures and pairs' fields from `a`, which holds a `τa`, reaches `l`,
which holds a `τ`; `P` are the cells passed on the way, and the trees of the fields not followed,
which the place leaves as they are. -/
inductive Path (F : List Fn) (ι : Iota) (σ : Store) : Nat → Ty → List Nat → Nat → Ty → Prop
  | here : Path F ι σ a τ [] a τ
  | step : σ.mem a = some (.ptr b) → Path F ι σ b τ' P l τ → Path F ι σ a (.box τ') (a :: P) l τ
  | clo : σ.mem a = some (.clo f c τc) → CloOk F f τc k A B r Rf → Path F ι σ c τc P l τ →
      Path F ι σ a (.fn k A B r Rf) (a :: P) l τ
  | fst : σ.mem a = some (.pair b c) → LT F ι σ c B R → Path F ι σ b A P l τ →
      Path F ι σ a (.pair A B) (a :: (R ++ P)) l τ
  | snd : σ.mem a = some (.pair b c) → LT F ι σ b A R → Path F ι σ c B P l τ →
      Path F ι σ a (.pair A B) (a :: (R ++ P)) l τ
  | tag : σ.mem a = some (.tag A' B' t b) → Path F ι σ b (if t then A else B) P l τ →
      Path F ι σ a (.sum A B) (a :: P) l τ

theorem Path.snoc' : Path F ι σ a τa P l τl → τl = .box τ → σ.mem l = some (.ptr b) →
    Path F ι σ a τa (P ++ [l]) b τ := by
  intro h
  induction h with
  | here => intro he hl; subst he; exact .step hl .here
  | step ha _ ih => intro he hl; exact .step ha (ih he hl)
  | tag ha _ ih => intro he hl; exact .tag ha (ih he hl)
  | clo ha hc _ ih => intro he hl; exact .clo ha hc (ih he hl)
  | fst ha hR _ ih => intro he hl; simpa using Path.fst ha hR (ih he hl)
  | snd ha hR _ ih => intro he hl; simpa using Path.snd ha hR (ih he hl)

theorem Path.snoc : Path F ι σ a τa P l (.box τ) → σ.mem l = some (.ptr b) → Path F ι σ a τa (P ++ [l]) b τ :=
  fun h => h.snoc' rfl

/-- A path on into a field: the pair's cell, and the other field's tree, are passed. -/
theorem Path.snocFst' : Path F ι σ a τa P l τl → τl = .pair A B → σ.mem l = some (.pair b c) → LT F ι σ c B R →
    Path F ι σ a τa (P ++ (l :: R)) b A := by
  intro h
  induction h with
  | here => intro he hl hR; subst he; simpa using Path.fst hl hR .here
  | step ha _ ih => intro he hl hR; exact .step ha (ih he hl hR)
  | tag ha _ ih => intro he hl hR; exact .tag ha (ih he hl hR)
  | clo ha hc _ ih => intro he hl hR; exact .clo ha hc (ih he hl hR)
  | fst ha hR' _ ih => intro he hl hR; simpa using Path.fst ha hR' (ih he hl hR)
  | snd ha hR' _ ih => intro he hl hR; simpa using Path.snd ha hR' (ih he hl hR)

theorem Path.snocSnd' : Path F ι σ a τa P l τl → τl = .pair A B → σ.mem l = some (.pair b c) → LT F ι σ b A R →
    Path F ι σ a τa (P ++ (l :: R)) c B := by
  intro h
  induction h with
  | here => intro he hl hR; subst he; simpa using Path.snd hl hR .here
  | step ha _ ih => intro he hl hR; exact .step ha (ih he hl hR)
  | tag ha _ ih => intro he hl hR; exact .tag ha (ih he hl hR)
  | clo ha hc _ ih => intro he hl hR; exact .clo ha hc (ih he hl hR)
  | fst ha hR' _ ih => intro he hl hR; simpa using Path.fst ha hR' (ih he hl hR)
  | snd ha hR' _ ih => intro he hl hR; simpa using Path.snd ha hR' (ih he hl hR)

/-- A path on into what a tag carries. -/
theorem Path.snocTag' : Path F ι σ a τa P l τl → τl = .sum A B → σ.mem l = some (.tag A' B' t b) →
    Path F ι σ a τa (P ++ [l]) b (if t then A else B) := by
  intro h
  induction h with
  | here => intro he hl; subst he; exact .tag hl .here
  | step ha _ ih => intro he hl; exact .step ha (ih he hl)
  | tag ha _ ih => intro he hl; exact .tag ha (ih he hl)
  | clo ha hc _ ih => intro he hl; exact .clo ha hc (ih he hl)
  | fst ha hR _ ih => intro he hl; simpa using Path.fst ha hR (ih he hl)
  | snd ha hR _ ih => intro he hl; simpa using Path.snd ha hR (ih he hl)

/-- Two paths, the second from where the first ends, are one. -/
theorem Path.trans : Path F ι σ a τa P l τl → Path F ι σ l τl P' b τ → Path F ι σ a τa (P ++ P') b τ := by
  intro h h'
  induction h with
  | here => exact h'
  | step ha _ ih => exact .step ha (ih h')
  | tag ha _ ih => exact .tag ha (ih h')
  | clo ha hc _ ih => exact .clo ha hc (ih h')
  | fst ha hR _ ih => simpa using Path.fst ha hR (ih h')
  | snd ha hR _ ih => simpa using Path.snd ha hR (ih h')

/-- A path stays where its cells do. -/
theorem Path.frame : Path F ι σ a τa P l τ → Agree σ σ' P → Path F ι σ' a τa P l τ := by
  intro h hag
  induction h with
  | here => exact .here
  | step ha _ ih =>
    exact .step (by rw [hag _ (List.mem_cons_self ..)]; exact ha)
      (ih (hag.mono fun x hx => List.mem_cons_of_mem _ hx))
  | tag ha _ ih =>
    exact .tag (by rw [hag _ (List.mem_cons_self ..)]; exact ha)
      (ih (hag.mono fun x hx => List.mem_cons_of_mem _ hx))
  | clo ha hc _ ih =>
    exact .clo (by rw [hag _ (List.mem_cons_self ..)]; exact ha) hc
      (ih (hag.mono fun x hx => List.mem_cons_of_mem _ hx))
  | fst ha hR _ ih =>
    exact .fst (by rw [hag _ (List.mem_cons_self ..)]; exact ha)
      (hR.frame (hag.mono fun x hx => List.mem_cons_of_mem _ (List.mem_append.mpr (.inl hx))))
      (ih (hag.mono fun x hx => List.mem_cons_of_mem _ (List.mem_append.mpr (.inr hx))))
  | snd ha hR _ ih =>
    exact .snd (by rw [hag _ (List.mem_cons_self ..)]; exact ha)
      (hR.frame (hag.mono fun x hx => List.mem_cons_of_mem _ (List.mem_append.mpr (.inl hx))))
      (ih (hag.mono fun x hx => List.mem_cons_of_mem _ (List.mem_append.mpr (.inr hx))))

/-- A tree is the cells on a path into it, the trees of the fields it passes by, and the tree where
the path ends. -/
theorem path_split : Path F ι σ a τa P l τ → LT F ι σ a τa L → ∃ R, LT F ι σ l τ R ∧ L.Perm (P ++ R) := by
  intro hp
  induction hp generalizing L with
  | here => intro h; exact ⟨L, h, .refl _⟩
  | step ha _ ih =>
    intro h
    cases h with
    | box ha' hb hn =>
      rw [ha] at ha'
      cases ha'
      obtain ⟨R, hR, hp⟩ := ih hb
      exact ⟨R, hR, hp.cons _⟩
  | tag ha _ ih =>
    intro h
    cases h with
    | tag ha' hb hn =>
      rw [ha] at ha'
      cases ha'
      obtain ⟨R, hR, hp⟩ := ih hb
      exact ⟨R, hR, hp.cons _⟩
  | clo ha _ _ ih =>
    intro h
    cases h with
    | clo ha' _ hb hn =>
      rw [ha] at ha'
      cases ha'
      obtain ⟨R, hR, hp⟩ := ih hb
      exact ⟨R, hR, hp.cons _⟩
  | fst ha hR _ ih =>
    intro h
    cases h with
    | pair ha' h1 h2 _ _ =>
      rw [ha] at ha'
      cases ha'
      obtain rfl := h2.det hR
      obtain ⟨R', hR', hp⟩ := ih h1
      refine ⟨R', hR', List.Perm.cons _ ?_⟩
      exact ((hp.append_right _).trans (List.perm_append_comm)).trans (by simp)
  | snd ha hR _ ih =>
    intro h
    cases h with
    | pair ha' h1 h2 _ _ =>
      rw [ha] at ha'
      cases ha'
      obtain rfl := h1.det hR
      obtain ⟨R', hR', hp⟩ := ih h2
      exact ⟨R', hR', List.Perm.cons _ (by simpa using hp.append_left _)⟩

/-- Replacing the tree where a path ends keeps a tree: the cells on the way, and the fields passed
by, are unchanged, and the new tree shares none of them. -/
theorem path_join : Path F ι σ a τa P l τ → P.Nodup → Agree σ σ' P → LT F ι σ' l τ R' → Disj P R' →
    ∃ L', LT F ι σ' a τa L' ∧ L'.Perm (P ++ R') ∧ Path F ι σ' a τa P l τ := by
  intro hp
  induction hp with
  | here => intro _ _ h _; exact ⟨_, h, .refl _, .here⟩
  | step ha _ ih =>
    intro hn hag h' hd
    obtain ⟨hna, hn'⟩ := List.nodup_cons.mp hn
    obtain ⟨L1, hlt, hp, hpath⟩ := ih hn' ((hag.mono fun x hx => List.mem_cons_of_mem _ hx)) h'
      (fun x hx => hd x (List.mem_cons_of_mem _ hx))
    have ha' := (hag _ (List.mem_cons_self ..)).trans ha
    refine ⟨_, .box ha' hlt fun hx => ?_, hp.cons _, .step ha' hpath⟩
    rcases List.mem_append.mp (hp.mem_iff.mp hx) with hx | hx
    · exact hna hx
    · exact hd _ (List.mem_cons_self ..) hx
  | tag ha _ ih =>
    intro hn hag h' hd
    obtain ⟨hna, hn'⟩ := List.nodup_cons.mp hn
    obtain ⟨L1, hlt, hp, hpath⟩ := ih hn' ((hag.mono fun x hx => List.mem_cons_of_mem _ hx)) h'
      (fun x hx => hd x (List.mem_cons_of_mem _ hx))
    have ha' := (hag _ (List.mem_cons_self ..)).trans ha
    refine ⟨_, .tag ha' hlt fun hx => ?_, hp.cons _, .tag ha' hpath⟩
    rcases List.mem_append.mp (hp.mem_iff.mp hx) with hx | hx
    · exact hna hx
    · exact hd _ (List.mem_cons_self ..) hx
  | clo ha hc _ ih =>
    intro hn hag h' hd
    obtain ⟨hna, hn'⟩ := List.nodup_cons.mp hn
    obtain ⟨L1, hlt, hp, hpath⟩ := ih hn' ((hag.mono fun x hx => List.mem_cons_of_mem _ hx)) h'
      (fun x hx => hd x (List.mem_cons_of_mem _ hx))
    have ha' := (hag _ (List.mem_cons_self ..)).trans ha
    refine ⟨_, .clo ha' hc hlt fun hx => ?_, hp.cons _, .clo ha' hc hpath⟩
    rcases List.mem_append.mp (hp.mem_iff.mp hx) with hx | hx
    · exact hna hx
    · exact hd _ (List.mem_cons_self ..) hx
  | fst ha hR _ ih =>
    intro hn hag h' hd
    obtain ⟨hna, hn'⟩ := List.nodup_cons.mp hn
    obtain ⟨hnR, hnP, hdRP⟩ := nodup_append_disj.mp hn'
    obtain ⟨L1, hlt, hp, hpath⟩ := ih hnP ((hag.mono fun x hx => List.mem_cons_of_mem _ (List.mem_append.mpr (.inr hx)))) h'
      (fun x hx => hd x (List.mem_cons_of_mem _ (List.mem_append.mpr (.inr hx))))
    have ha' := (hag _ (List.mem_cons_self ..)).trans ha
    have hR' := hR.frame (σ' := σ') (hag.mono fun x hx => List.mem_cons_of_mem _ (List.mem_append.mpr (.inl hx)))
    refine ⟨_, .pair ha' hlt hR' (fun x hx hx' => ?_) (fun hx => ?_), ?_, .fst ha' hR' hpath⟩
    · rcases List.mem_append.mp (hp.mem_iff.mp hx) with hx | hx
      · exact hdRP x hx' hx
      · exact hd x (List.mem_cons_of_mem _ (List.mem_append.mpr (.inl hx'))) hx
    · rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_append.mp (hp.mem_iff.mp hx) with hx | hx
        · exact hna (List.mem_append.mpr (.inr hx))
        · exact hd _ (List.mem_cons_self ..) hx
      · exact hna (List.mem_append.mpr (.inl hx))
    · refine List.Perm.cons _ ?_
      exact ((hp.append_right _).trans List.perm_append_comm).trans (by simp)
  | snd ha hR _ ih =>
    intro hn hag h' hd
    obtain ⟨hna, hn'⟩ := List.nodup_cons.mp hn
    obtain ⟨hnR, hnP, hdRP⟩ := nodup_append_disj.mp hn'
    obtain ⟨L1, hlt, hp, hpath⟩ := ih hnP ((hag.mono fun x hx => List.mem_cons_of_mem _ (List.mem_append.mpr (.inr hx)))) h'
      (fun x hx => hd x (List.mem_cons_of_mem _ (List.mem_append.mpr (.inr hx))))
    have ha' := (hag _ (List.mem_cons_self ..)).trans ha
    have hR' := hR.frame (σ' := σ') (hag.mono fun x hx => List.mem_cons_of_mem _ (List.mem_append.mpr (.inl hx)))
    refine ⟨_, .pair ha' hR' hlt (fun x hx hx' => ?_) (fun hx => ?_), ?_, .snd ha' hR' hpath⟩
    · rcases List.mem_append.mp (hp.mem_iff.mp hx') with hx' | hx'
      · exact hdRP x hx hx'
      · exact hd x (List.mem_cons_of_mem _ (List.mem_append.mpr (.inl hx))) hx'
    · rcases List.mem_append.mp hx with hx | hx
      · exact hna (List.mem_append.mpr (.inl hx))
      · rcases List.mem_append.mp (hp.mem_iff.mp hx) with hx | hx
        · exact hna (List.mem_append.mpr (.inr hx))
        · exact hd _ (List.mem_cons_self ..) hx
    · exact List.Perm.cons _ (by simpa using hp.append_left _)

/-! ## The variables of an activation -/

/-- A slot whose footprint is exclusive: an owned variable or a `mut` borrow. -/
def Slot.excl : Slot → Bool
  | .own _ _ => true
  | .ref .mut _ => true
  | .ref .ro _ => false
  | .lent _ _ => false
  | .half _ _ _ => true

/-- The footprint a slot has: what an owned live variable or a borrow holds, owning the rest. A
variable perhaps moved holds the mark a move leaves, its footprint its cell alone, or still its
value: which, only running the program tells, and dropping it at the end of its scope looks. -/
def SlotOk (F : List Fn) (ι : Iota) (σ : Store) : Slot → Nat → List Nat → Prop
  | .own τ true, a, L => LT F ι σ a τ L
  | .own τ false, a, L => (σ.mem a = some .moved ∧ L = [a]) ∨ (LT F ι σ a τ L ∧ τ.isHole = false)
  | .ref _ τ, a, L => LT F ι σ a τ L
  | .lent _ false, _, L => L = []
  | .lent _ true, a, L => L = [a] ∧ σ.mem a ≠ none
  | .half t A B, a, L => LT F ι σ a (.lent1 t A B) L

/-- The part of a slot's footprint that may be changed, and the part that is only read: a `mut`
borrow of a closure only reads the closure's cell, the head of its footprint. -/
def exclPart (s : Slot) (L : List Nat) : List Nat := if s.excl then (if s.shell then L.tail else L) else []
def sharedPart (s : Slot) (L : List Nat) : List Nat := if s.excl then (if s.shell then L.take 1 else []) else L

/-- Adds a footprint to the exclusive ones and to the shared ones, as the slot says. -/
def addE (s : Slot) (L E : List Nat) : List Nat := exclPart s L ++ E
def addS (s : Slot) (L S : List Nat) : List Nat := sharedPart s L ++ S

/-- The footprints of an activation's variables, in order: of those that may be changed — owned
variables and `mut` borrows — and of those that may only be read, `readonly` borrows. -/
inductive Foot (F : List Fn) (ι : Iota) (σ : Store) : Ctx → Env → List Nat → List Nat → Prop
  | nil : Foot F ι σ [] [] [] []
  | cons : SlotOk F ι σ s a L → Foot F ι σ Γ env E S →
      Foot F ι σ ((x, s) :: Γ) ((x, a) :: env) (addE s L E) (addS s L S)

/-- The invariant of an activation: its variables' footprints, those that may be changed disjoint
from each other and from those that may be read. -/
structure Inv (F : List Fn) (ι : Iota) (σ : Store) (Γ : Ctx) (env : Env) (E S : List Nat) : Prop where
  foot : Foot F ι σ Γ env E S
  nodup : E.Nodup
  disj : Disj S E
  keys : (Γ.map Prod.fst).Nodup

theorem LT.not_moved : LT F ι σ a τ L → τ.isHole = false → σ.mem a ≠ some .moved := by
  intro h hτ
  cases h <;> simp_all [Ty.isHole]

theorem SlotOk.alloc : SlotOk F ι σ s a L → ∀ l ∈ L, σ.mem l ≠ none := by
  intro h
  rcases s with ⟨τ, live⟩ | ⟨m, τ⟩ | ⟨τ, hd⟩ | ⟨t, A, B⟩
  · cases live
    · rcases h with ⟨ha, rfl⟩ | ⟨h, -⟩
      · intro l hl; simp at hl; subst hl; simp [ha]
      · exact LT.alloc h
    · exact LT.alloc h
  · exact LT.alloc h
  · cases hd
    · simp only [SlotOk] at h; subst h; simp
    · obtain ⟨rfl, ha⟩ := h; simpa using ha
  · exact LT.alloc h

theorem SlotOk.frame : SlotOk F ι σ s a L → Agree σ σ' L → SlotOk F ι σ' s a L := by
  intro h hag
  rcases s with ⟨τ, live⟩ | ⟨m, τ⟩ | ⟨τ, hd⟩ | ⟨t, A, B⟩
  · cases live
    · rcases h with ⟨ha, rfl⟩ | h
      · exact .inl ⟨by rw [hag _ (by simp)]; exact ha, rfl⟩
      · exact .inr ⟨LT.frame h.1 hag, h.2⟩
    · exact LT.frame h hag
  · exact LT.frame h hag
  · cases hd
    · exact h
    · exact ⟨h.1, by rw [hag a (by simp [h.1])]; exact h.2⟩
  · exact LT.frame h hag

theorem SlotOk.nodup : SlotOk F ι σ s a L → L.Nodup := by
  intro h
  rcases s with ⟨τ, live⟩ | ⟨m, τ⟩ | ⟨τ, hd⟩ | ⟨t, A, B⟩
  · cases live
    · rcases h with ⟨_, rfl⟩ | ⟨h, -⟩
      · simp
      · exact LT.nodup h
    · exact LT.nodup h
  · exact LT.nodup h
  · cases hd
    · simp only [SlotOk] at h; subst h; simp
    · rw [h.1]; simp
  · exact LT.nodup h

theorem SlotOk.det : SlotOk F ι σ s a L → SlotOk F ι σ s a L' → L = L' := by
  intro h h'
  rcases s with ⟨τ, live⟩ | ⟨m, τ⟩ | ⟨τ, hd⟩ | ⟨t, A, B⟩
  · cases live
    · rcases h with ⟨ha, rfl⟩ | ⟨h, hh⟩ <;> rcases h' with ⟨ha', rfl⟩ | ⟨h', hh'⟩
      · rfl
      · exact absurd ha (h'.not_moved hh')
      · exact absurd ha' (h.not_moved hh)
      · exact LT.det h h'
    · exact LT.det h h'
  · exact LT.det h h'
  · cases hd
    · simp only [SlotOk] at h h'; rw [h, h']
    · rw [h.1, h'.1]
  · exact LT.det h h'

theorem mem_addE : l ∈ addE s L E ↔ l ∈ exclPart s L ∨ l ∈ E := by
  simp [addE]

theorem mem_addS : l ∈ addS s L S ↔ l ∈ sharedPart s L ∨ l ∈ S := by
  simp [addS]

theorem exclPart_sub : l ∈ exclPart s L → l ∈ L := by
  unfold exclPart; split
  · split
    · exact List.mem_of_mem_tail
    · exact id
  · simp

theorem sharedPart_sub : l ∈ sharedPart s L → l ∈ L := by
  unfold sharedPart; split
  · split
    · exact List.mem_of_mem_take
    · simp
  · exact id

/-- Every cell of a footprint is in one part or the other. -/
theorem mem_parts : l ∈ L → l ∈ exclPart s L ∨ l ∈ sharedPart s L := by
  intro h
  unfold exclPart sharedPart
  split
  · split
    · cases L with
      | nil => simp at h
      | cons a L => rcases List.mem_cons.mp h with rfl | h <;> simp_all
    · exact .inl h
  · exact .inr h

theorem parts_perm {L : List Nat} {s : Slot} : L.Perm (exclPart s L ++ sharedPart s L) := by
  unfold exclPart sharedPart
  split
  · split
    · cases L with
      | nil => simp
      | cons a L => simpa using (List.perm_append_singleton a L).symm
    · simp
  · simp

/-- A slot that is not a closure borrowed `mut`: all of its footprint changeable, or all only read. -/
theorem exclPart_plain (hs : s.shell = false) : exclPart s L = if s.excl then L else [] := by
  simp [exclPart, hs]

theorem sharedPart_plain (hs : s.shell = false) : sharedPart s L = if s.excl then [] else L := by
  simp [sharedPart, hs]

theorem Slot.shell_ref : (Slot.ref m τ).shell = (m == .mut && τ.shell) := by
  cases m <;> cases τ <;> rfl

theorem Ty.shell_nonhole {τ : Ty} (h : τ.shell = true) : τ.isHole = false := by
  cases τ <;> simp_all [Ty.shell, Ty.isHole]

theorem Slot.shell_own : (Slot.own τ l).shell = false := rfl

theorem Slot.shell_lent : (Slot.lent τ h).shell = false := rfl

theorem Slot.shell_excl {s : Slot} : s.shell = true → s.excl = true := by
  intro h; match s, h with
  | .ref .mut (.fn _ _ _ _ _), _ => rfl
  | .ref .mut (.vec false _), _ => rfl
  | .half _ _ _, _ => rfl

/-- A footprint without duplicates splits into disjoint parts. -/
theorem parts_disj : L.Nodup → Disj (exclPart s L) (sharedPart s L) := by
  intro hn x hx hy
  unfold exclPart at hx; unfold sharedPart at hy
  by_cases he : s.excl = true <;> by_cases hs : s.shell = true <;> simp only [he, hs, ↓reduceIte] at hx hy
  · cases L with
    | nil => simp at hx
    | cons a L =>
      simp only [List.tail_cons, List.take_succ_cons, List.take_zero, List.mem_singleton] at hx hy
      subst hy
      exact (List.nodup_cons.mp hn).1 hx
  all_goals simp_all

theorem parts_nodup : L.Nodup → (exclPart s L).Nodup ∧ (sharedPart s L).Nodup := by
  intro hn
  unfold exclPart sharedPart
  split
  · split
    · exact ⟨hn.sublist (List.tail_sublist _), hn.sublist (List.take_sublist _ _)⟩
    · exact ⟨hn, by simp⟩
  · exact ⟨by simp, hn⟩

theorem Foot.alloc : Foot F ι σ Γ env E S → ∀ l, l ∈ E ∨ l ∈ S → σ.mem l ≠ none := by
  intro h
  induction h with
  | nil => intro l h; simp at h
  | cons hs _ ih =>
    intro l hl
    rcases hl with hl | hl
    · rcases mem_addE.mp hl with hl | hl
      · exact hs.alloc l (exclPart_sub hl)
      · exact ih l (.inl hl)
    · rcases mem_addS.mp hl with hl | hl
      · exact hs.alloc l (sharedPart_sub hl)
      · exact ih l (.inr hl)

theorem Foot.frame : Foot F ι σ Γ env E S → Agree σ σ' (E ++ S) → Foot F ι σ' Γ env E S := by
  intro h
  induction h with
  | nil => intro _; exact .nil
  | @cons s a L Γ env E S x hs _ ih =>
    intro hag
    have hL : Agree σ σ' L := hag.mono fun l hl => by
      rcases mem_parts (s := s) hl with h | h
      · exact List.mem_append.mpr (.inl (mem_addE.mpr (.inl h)))
      · exact List.mem_append.mpr (.inr (mem_addS.mpr (.inl h)))
    exact .cons (hs.frame hL) (ih (hag.mono fun l hl => by
      rcases List.mem_append.mp hl with hl | hl
      · exact List.mem_append.mpr (.inl (mem_addE.mpr (.inr hl)))
      · exact List.mem_append.mpr (.inr (mem_addS.mpr (.inr hl)))))

end FlyCore.Ownership
