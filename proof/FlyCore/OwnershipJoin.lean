import FlyCore.OwnershipBase

/-!
# Ownership: a tree with several holes

A call may lend several places of one variable, each a field apart from the others. After it, the
variable's tree is what it kept and what the callee left at each place: replacing the trees at
holes that are apart, all at once, keeps a tree.
-/

namespace FlyCore.Ownership

/-- A hole in a tree: where it is, what it holds, the tree it had, and the tree it has after. -/
structure Cut where
  loc : Nat
  ty : Ty
  old : List Nat
  new : List Nat

theorem LT.ne_nil (h : LT F σ a τ L) : L ≠ [] := by
  obtain ⟨R, rfl⟩ := h.cons; simp

/-- A tree the path into it passes through holds the tree where the path ends. -/
theorem path_sub (hp : Path F σ a τa P l τ) (hL : LT F σ a τa L) (hR : LT F σ l τ R) : ∀ z ∈ R, z ∈ L := by
  obtain ⟨R', hR', hp'⟩ := path_split hp hL
  obtain rfl := hR.det hR'
  exact fun z hz => hp'.mem_iff.mpr (List.mem_append.mpr (.inr hz))

/-- The cells a tree keeps of its holes': those of no hole's old tree. -/
def Kept (L : List Nat) (cs : List Cut) (z : Nat) : Prop := z ∈ L ∧ ∀ c ∈ cs, z ∉ c.old

/-- A hole at the root is the only hole, and the tree after is its new tree. -/
theorem join_here (hL : LT F σ a τ L) (hc : c ∈ cs) (hloc : c.loc = a)
    (hcs : ∀ c ∈ cs, (∃ P, Path F σ a τ P c.loc c.ty) ∧ LT F σ c.loc c.ty c.old ∧ LT F σ' c.loc c.ty c.new)
    (hd : ∀ c ∈ cs, ∀ d ∈ cs, c ≠ d → Disj c.old d.old) :
    ∃ L', LT F σ' a τ L' ∧ (∀ z, z ∈ L' ↔ Kept L cs z ∨ ∃ c ∈ cs, z ∈ c.new) ∧
      ∀ c ∈ cs, ∃ P, Path F σ' a τ P c.loc c.ty := by
  obtain ⟨-, hold, hnew⟩ := hcs c hc
  rw [hloc] at hold hnew
  obtain ⟨rfl, rfl⟩ := hold.det_ty hL
  -- Any other hole lies in the root's tree, which is this hole's: apart from it, it is empty.
  have hsame : ∀ d ∈ cs, d = c := fun d hd' => by
    refine Classical.byContradiction fun hne => ?_
    obtain ⟨⟨P, hp⟩, hdo, -⟩ := hcs d hd'
    obtain ⟨R, hR⟩ := hdo.cons
    have := path_sub hp hL hdo d.loc (by rw [hR]; exact List.mem_cons_self ..)
    exact hd d hd' c hc hne d.loc (by rw [hR]; exact List.mem_cons_self ..) this
  refine ⟨c.new, hnew, fun z => ⟨fun h => .inr ⟨c, hc, h⟩, ?_⟩, fun d hd' => ?_⟩
  · rintro (⟨hz, hk⟩ | ⟨d, hd', hz⟩)
    · exact absurd hz (hk c hc)
    · rw [hsame d hd'] at hz; exact hz
  · rw [hsame d hd', hloc]; exact ⟨[], .here⟩

/-- The holes a node's child has, kept in the node. -/
theorem kept_up {L R : List Nat} (hRL : ∀ z ∈ R, z ∈ L) (hout : ∀ c ∈ cs, ∀ z ∈ c.old, z ∈ R ∨ z ∉ L)
    (h : Kept R cs₁ z) (hcs : ∀ c ∈ cs, c ∉ cs₁ → ∀ z ∈ c.old, z ∉ R) : Kept L cs z := by
  refine ⟨hRL z h.1, fun c hc hz => ?_⟩
  by_cases h1 : c ∈ cs₁
  · exact h.2 c h1 hz
  · exact hcs c hc h1 z hz h.1

/-- Replacing the trees at holes apart from each other, in a store that kept the rest, keeps a tree:
its cells those kept and the new trees', with a path to each hole. -/
theorem multi_join (hL : LT F σ a τ L) : ∀ (cs : List Cut),
    (∀ c ∈ cs, (∃ P, Path F σ a τ P c.loc c.ty) ∧ LT F σ c.loc c.ty c.old ∧ LT F σ' c.loc c.ty c.new) →
    (∀ c ∈ cs, ∀ d ∈ cs, c ≠ d → Disj c.old d.old) →
    (∀ z, Kept L cs z → σ'.mem z = σ.mem z) →
    (∀ c ∈ cs, ∀ z ∈ c.new, ¬ Kept L cs z) →
    (∀ c ∈ cs, ∀ d ∈ cs, c ≠ d → Disj c.new d.new) →
    ∃ L', LT F σ' a τ L' ∧ (∀ z, z ∈ L' ↔ Kept L cs z ∨ ∃ c ∈ cs, z ∈ c.new) ∧
      ∀ c ∈ cs, ∃ P, Path F σ' a τ P c.loc c.ty := by
  induction hL with
  | @int a n ha =>
    intro cs hcs hd hag hdn hnn
    by_cases hh : ∃ c ∈ cs, c.loc = a
    · obtain ⟨c, hc, hloc⟩ := hh
      exact join_here (.int ha) hc hloc hcs hd
    · -- An integer holds no hole but at itself.
      have hno : ∀ c ∈ cs, False := fun c hc => by
        obtain ⟨⟨P, hp⟩, -, -⟩ := hcs c hc
        generalize hl : c.loc = l at hp
        generalize c.ty = t at hp
        cases hp with
        | here => exact hh ⟨c, hc, hl⟩
      have hka : Kept [a] cs a := ⟨List.mem_singleton_self _, fun c hc => absurd hc (fun h => hno c h)⟩
      refine ⟨[a], .int ((hag a hka).trans ha), fun z => ?_, fun c hc => absurd hc (fun h => hno c h)⟩
      constructor
      · intro h; simp at h; subst h; exact .inl hka
      · rintro (h | ⟨c, hc, -⟩)
        · exact h.1
        · exact absurd hc (fun h => hno c h)
  | @box a b τ' R ha hb hn ih =>
    intro cs hcs hd hag hdn hnn
    by_cases hh : ∃ c ∈ cs, c.loc = a
    · obtain ⟨c, hc, hloc⟩ := hh
      exact join_here (.box ha hb hn) hc hloc hcs hd
    · -- Every hole is below the node, in its child.
      have hno : ∀ c ∈ cs, c.loc ≠ a := fun c hc e => hh ⟨c, hc, e⟩
      have hcs' : ∀ c ∈ cs, (∃ P, Path F σ b (τ') P c.loc c.ty) ∧ LT F σ c.loc c.ty c.old ∧ LT F σ' c.loc c.ty c.new := by
        intro c hc
        obtain ⟨⟨P, hp⟩, ho, hn'⟩ := hcs c hc
        refine ⟨?_, ho, hn'⟩
        have hl := hno c hc
        generalize c.loc = l at hp hl
        generalize c.ty = t at hp
        cases hp with
        | here => exact absurd rfl hl
        | step ha' hp' => rw [ha] at ha'; cases ha'; exact ⟨_, hp'⟩
      have hsub : ∀ c ∈ cs, ∀ z ∈ c.old, z ∈ R := fun c hc z hz => by
        obtain ⟨⟨P, hp⟩, ho, -⟩ := hcs' c hc
        exact path_sub hp hb ho z hz
      have hkept : ∀ {z}, Kept R cs z → Kept (a :: R) cs z := fun h => ⟨List.mem_cons_of_mem _ h.1, h.2⟩
      obtain ⟨L1, hL1, hmem1, hpaths1⟩ := ih cs hcs' hd (fun z h => hag z (hkept h))
        (fun c hc z hz h => hdn c hc z hz (hkept h)) hnn
      have hka : Kept (a :: R) cs a := ⟨List.mem_cons_self .., fun c hc h => hn (hsub c hc a h)⟩
      have ha' := (hag a hka).trans ha
      have hnL : a ∉ L1 := fun h => by
        rcases (hmem1 a).mp h with h | ⟨c, hc, h⟩
        · exact hn h.1
        · exact hdn c hc a h hka
      refine ⟨a :: L1, .box ha' hL1 hnL, fun z => ?_, fun c hc => ?_⟩
      · rw [List.mem_cons, hmem1]
        constructor
        · rintro (rfl | h | h)
          · exact .inl hka
          · exact .inl (hkept h)
          · exact .inr h
        · rintro (⟨hz, hk⟩ | h)
          · rcases List.mem_cons.mp hz with rfl | hz
            · exact .inl rfl
            · exact .inr (.inl ⟨hz, hk⟩)
          · exact .inr (.inr h)
      · obtain ⟨P, hp⟩ := hpaths1 c hc
        exact ⟨_, .step ha' hp⟩
  | @clo a f c0 τc k A B r R ha hc0 hb hn ih =>
    intro cs hcs hd hag hdn hnn
    by_cases hh : ∃ c ∈ cs, c.loc = a
    · obtain ⟨c, hc, hloc⟩ := hh
      exact join_here (.clo ha hc0 hb hn) hc hloc hcs hd
    · -- Every hole is below the node, in its child.
      have hno : ∀ c ∈ cs, c.loc ≠ a := fun c hc e => hh ⟨c, hc, e⟩
      have hcs' : ∀ c ∈ cs, (∃ P, Path F σ c0 (τc) P c.loc c.ty) ∧ LT F σ c.loc c.ty c.old ∧ LT F σ' c.loc c.ty c.new := by
        intro c hc
        obtain ⟨⟨P, hp⟩, ho, hn'⟩ := hcs c hc
        refine ⟨?_, ho, hn'⟩
        have hl := hno c hc
        generalize c.loc = l at hp hl
        generalize c.ty = t at hp
        cases hp with
        | here => exact absurd rfl hl
        | clo ha' _ hp' => rw [ha] at ha'; cases ha'; exact ⟨_, hp'⟩
      have hsub : ∀ c ∈ cs, ∀ z ∈ c.old, z ∈ R := fun c hc z hz => by
        obtain ⟨⟨P, hp⟩, ho, -⟩ := hcs' c hc
        exact path_sub hp hb ho z hz
      have hkept : ∀ {z}, Kept R cs z → Kept (a :: R) cs z := fun h => ⟨List.mem_cons_of_mem _ h.1, h.2⟩
      obtain ⟨L1, hL1, hmem1, hpaths1⟩ := ih cs hcs' hd (fun z h => hag z (hkept h))
        (fun c hc z hz h => hdn c hc z hz (hkept h)) hnn
      have hka : Kept (a :: R) cs a := ⟨List.mem_cons_self .., fun c hc h => hn (hsub c hc a h)⟩
      have ha' := (hag a hka).trans ha
      have hnL : a ∉ L1 := fun h => by
        rcases (hmem1 a).mp h with h | ⟨c, hc, h⟩
        · exact hn h.1
        · exact hdn c hc a h hka
      refine ⟨a :: L1, .clo ha' hc0 hL1 hnL, fun z => ?_, fun c hc => ?_⟩
      · rw [List.mem_cons, hmem1]
        constructor
        · rintro (rfl | h | h)
          · exact .inl hka
          · exact .inl (hkept h)
          · exact .inr h
        · rintro (⟨hz, hk⟩ | h)
          · rcases List.mem_cons.mp hz with rfl | hz
            · exact .inl rfl
            · exact .inr (.inl ⟨hz, hk⟩)
          · exact .inr (.inr h)
      · obtain ⟨P, hp⟩ := hpaths1 c hc
        exact ⟨_, .clo ha' hc0 hp⟩
  | @tag a A B t b R ha hb hn ih =>
    intro cs hcs hd hag hdn hnn
    by_cases hh : ∃ c ∈ cs, c.loc = a
    · obtain ⟨c, hc, hloc⟩ := hh
      exact join_here (.tag ha hb hn) hc hloc hcs hd
    · -- Every hole is below the node, in its child.
      have hno : ∀ c ∈ cs, c.loc ≠ a := fun c hc e => hh ⟨c, hc, e⟩
      have hcs' : ∀ c ∈ cs, (∃ P, Path F σ b (if t then A else B) P c.loc c.ty) ∧ LT F σ c.loc c.ty c.old ∧ LT F σ' c.loc c.ty c.new := by
        intro c hc
        obtain ⟨⟨P, hp⟩, ho, hn'⟩ := hcs c hc
        refine ⟨?_, ho, hn'⟩
        have hl := hno c hc
        generalize c.loc = l at hp hl
        generalize c.ty = t at hp
        cases hp with
        | here => exact absurd rfl hl
        | tag ha' hp' => rw [ha] at ha'; cases ha'; exact ⟨_, hp'⟩
      have hsub : ∀ c ∈ cs, ∀ z ∈ c.old, z ∈ R := fun c hc z hz => by
        obtain ⟨⟨P, hp⟩, ho, -⟩ := hcs' c hc
        exact path_sub hp hb ho z hz
      have hkept : ∀ {z}, Kept R cs z → Kept (a :: R) cs z := fun h => ⟨List.mem_cons_of_mem _ h.1, h.2⟩
      obtain ⟨L1, hL1, hmem1, hpaths1⟩ := ih cs hcs' hd (fun z h => hag z (hkept h))
        (fun c hc z hz h => hdn c hc z hz (hkept h)) hnn
      have hka : Kept (a :: R) cs a := ⟨List.mem_cons_self .., fun c hc h => hn (hsub c hc a h)⟩
      have ha' := (hag a hka).trans ha
      have hnL : a ∉ L1 := fun h => by
        rcases (hmem1 a).mp h with h | ⟨c, hc, h⟩
        · exact hn h.1
        · exact hdn c hc a h hka
      refine ⟨a :: L1, .tag ha' hL1 hnL, fun z => ?_, fun c hc => ?_⟩
      · rw [List.mem_cons, hmem1]
        constructor
        · rintro (rfl | h | h)
          · exact .inl hka
          · exact .inl (hkept h)
          · exact .inr h
        · rintro (⟨hz, hk⟩ | h)
          · rcases List.mem_cons.mp hz with rfl | hz
            · exact .inl rfl
            · exact .inr (.inl ⟨hz, hk⟩)
          · exact .inr (.inr h)
      · obtain ⟨P, hp⟩ := hpaths1 c hc
        exact ⟨_, .tag ha' hp⟩
  | @pair a b c A R₁ B R₂ ha h1 h2 hd0 hn ih1 ih2 =>
    intro cs hcs hd hag hdn hnn
    by_cases hh : ∃ d ∈ cs, d.loc = a
    · obtain ⟨d, hd', hloc⟩ := hh
      exact join_here (.pair ha h1 h2 hd0 hn) hd' hloc hcs hd
    · have hno : ∀ d ∈ cs, d.loc ≠ a := fun d hd' e => hh ⟨d, hd', e⟩
      -- Each hole lies in one field or the other.
      have hside : ∀ d ∈ cs, ((∃ P, Path F σ b A P d.loc d.ty) ∧ ∀ z ∈ d.old, z ∈ R₁) ∨
          ((∃ P, Path F σ c B P d.loc d.ty) ∧ ∀ z ∈ d.old, z ∈ R₂) := by
        intro d hd'
        obtain ⟨⟨P, hp⟩, ho, -⟩ := hcs d hd'
        have hl := hno d hd'
        have ho' := ho
        generalize d.loc = l at hp hl ho'
        generalize d.ty = t at hp ho'
        cases hp with
        | here => exact absurd rfl hl
        | fst ha' _ hp' =>
          rw [ha] at ha'; cases ha'
          exact .inl ⟨⟨_, hp'⟩, path_sub hp' h1 ho'⟩
        | snd ha' _ hp' =>
          rw [ha] at ha'; cases ha'
          exact .inr ⟨⟨_, hp'⟩, path_sub hp' h2 ho'⟩
      have hhead : ∀ d ∈ cs, d.loc ∈ d.old := fun d hd' => by
        obtain ⟨-, ho, -⟩ := hcs d hd'
        obtain ⟨R, hR⟩ := ho.cons
        rw [hR]; exact List.mem_cons_self ..
      let cs₁ := cs.filter (fun d => decide (d.loc ∈ R₁))
      let cs₂ := cs.filter (fun d => decide (d.loc ∈ R₂))
      have hm₁ : ∀ {d}, d ∈ cs₁ ↔ d ∈ cs ∧ d.loc ∈ R₁ := by simp [cs₁]
      have hm₂ : ∀ {d}, d ∈ cs₂ ↔ d ∈ cs ∧ d.loc ∈ R₂ := by simp [cs₂]
      -- A hole whose location is in a field lies in it.
      have hin₁ : ∀ d ∈ cs, d.loc ∈ R₁ → (∃ P, Path F σ b A P d.loc d.ty) ∧ ∀ z ∈ d.old, z ∈ R₁ := by
        intro d hd' hl
        rcases hside d hd' with h | ⟨-, h⟩
        · exact h
        · exact absurd (h d.loc (hhead d hd')) (hd0 _ hl)
      have hin₂ : ∀ d ∈ cs, d.loc ∈ R₂ → (∃ P, Path F σ c B P d.loc d.ty) ∧ ∀ z ∈ d.old, z ∈ R₂ := by
        intro d hd' hl
        rcases hside d hd' with ⟨-, h⟩ | h
        · exact absurd hl (hd0 _ (h d.loc (hhead d hd')))
        · exact h
      have hor : ∀ d ∈ cs, d ∈ cs₁ ∨ d ∈ cs₂ := fun d hd' => by
        rcases hside d hd' with ⟨-, h⟩ | ⟨-, h⟩
        · exact .inl (hm₁.mpr ⟨hd', h _ (hhead d hd')⟩)
        · exact .inr (hm₂.mpr ⟨hd', h _ (hhead d hd')⟩)
      have hup₁ : ∀ {z}, Kept R₁ cs₁ z → Kept (a :: (R₁ ++ R₂)) cs z := fun {z} h => by
        refine ⟨List.mem_cons_of_mem _ (List.mem_append.mpr (.inl h.1)), fun d hd' hz => ?_⟩
        rcases hor d hd' with h' | h'
        · exact h.2 d h' hz
        · exact hd0 z h.1 ((hin₂ d hd' (hm₂.mp h').2).2 z hz)
      have hup₂ : ∀ {z}, Kept R₂ cs₂ z → Kept (a :: (R₁ ++ R₂)) cs z := fun {z} h => by
        refine ⟨List.mem_cons_of_mem _ (List.mem_append.mpr (.inr h.1)), fun d hd' hz => ?_⟩
        rcases hor d hd' with h' | h'
        · exact hd0 z ((hin₁ d hd' (hm₁.mp h').2).2 z hz) h.1
        · exact h.2 d h' hz
      obtain ⟨L1, hL1, hmem1, hpaths1⟩ := ih1 cs₁
        (fun d hd' => ⟨(hin₁ d (hm₁.mp hd').1 (hm₁.mp hd').2).1, (hcs d (hm₁.mp hd').1).2⟩)
        (fun d hd' e he => hd d (hm₁.mp hd').1 e (hm₁.mp he).1)
        (fun z h => hag z (hup₁ h)) (fun d hd' z hz h => hdn d (hm₁.mp hd').1 z hz (hup₁ h))
        (fun d hd' e he => hnn d (hm₁.mp hd').1 e (hm₁.mp he).1)
      obtain ⟨L2, hL2, hmem2, hpaths2⟩ := ih2 cs₂
        (fun d hd' => ⟨(hin₂ d (hm₂.mp hd').1 (hm₂.mp hd').2).1, (hcs d (hm₂.mp hd').1).2⟩)
        (fun d hd' e he => hd d (hm₂.mp hd').1 e (hm₂.mp he).1)
        (fun z h => hag z (hup₂ h)) (fun d hd' z hz h => hdn d (hm₂.mp hd').1 z hz (hup₂ h))
        (fun d hd' e he => hnn d (hm₂.mp hd').1 e (hm₂.mp he).1)
      have hka : Kept (a :: (R₁ ++ R₂)) cs a := by
        refine ⟨List.mem_cons_self .., fun d hd' h => hn ?_⟩
        rcases hside d hd' with ⟨-, h'⟩ | ⟨-, h'⟩
        · exact List.mem_append.mpr (.inl (h' a h))
        · exact List.mem_append.mpr (.inr (h' a h))
      have ha' := (hag a hka).trans ha
      have hdisj : ∀ z ∈ L1, z ∉ L2 := fun z hz1 hz2 => by
        rcases (hmem1 z).mp hz1 with k1 | ⟨d1, hd1, n1⟩ <;> rcases (hmem2 z).mp hz2 with k2 | ⟨d2, hd2, n2⟩
        · exact hd0 z k1.1 k2.1
        · exact hdn d2 (hm₂.mp hd2).1 z n2 (hup₁ k1)
        · exact hdn d1 (hm₁.mp hd1).1 z n1 (hup₂ k2)
        · have hne : d1 ≠ d2 := fun e => by
            have := (hm₁.mp hd1).2
            rw [e] at this
            exact hd0 _ this (hm₂.mp hd2).2
          exact hnn d1 (hm₁.mp hd1).1 d2 (hm₂.mp hd2).1 hne z n1 n2
      have hnL : a ∉ L1 ++ L2 := fun h => by
        rcases List.mem_append.mp h with h | h
        · rcases (hmem1 a).mp h with k | ⟨d, hd', n⟩
          · exact hn (List.mem_append.mpr (.inl k.1))
          · exact hdn d (hm₁.mp hd').1 a n hka
        · rcases (hmem2 a).mp h with k | ⟨d, hd', n⟩
          · exact hn (List.mem_append.mpr (.inr k.1))
          · exact hdn d (hm₂.mp hd').1 a n hka
      refine ⟨a :: (L1 ++ L2), .pair ha' hL1 hL2 hdisj hnL, fun z => ?_, fun d hd' => ?_⟩
      · rw [List.mem_cons, List.mem_append, hmem1, hmem2]
        constructor
        · rintro (rfl | (h | ⟨d, hd', h⟩) | (h | ⟨d, hd', h⟩))
          · exact .inl hka
          · exact .inl (hup₁ h)
          · exact .inr ⟨d, (hm₁.mp hd').1, h⟩
          · exact .inl (hup₂ h)
          · exact .inr ⟨d, (hm₂.mp hd').1, h⟩
        · rintro (⟨hz, hk⟩ | ⟨d, hd', h⟩)
          · rcases List.mem_cons.mp hz with rfl | hz
            · exact .inl rfl
            · rcases List.mem_append.mp hz with hz | hz
              · exact .inr (.inl (.inl ⟨hz, fun e he => hk e (hm₁.mp he).1⟩))
              · exact .inr (.inr (.inl ⟨hz, fun e he => hk e (hm₂.mp he).1⟩))
          · rcases hor d hd' with h' | h'
            · exact .inr (.inl (.inr ⟨d, h', h⟩))
            · exact .inr (.inr (.inr ⟨d, h', h⟩))
      · rcases hor d hd' with h' | h'
        · obtain ⟨P, hp⟩ := hpaths1 d h'
          exact ⟨_, .fst ha' hL2 hp⟩
        · obtain ⟨P, hp⟩ := hpaths2 d h'
          exact ⟨_, .snd ha' hL1 hp⟩

end FlyCore.Ownership
