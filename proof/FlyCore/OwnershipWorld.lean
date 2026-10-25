import FlyCore.OwnershipKont

/-!
# Ownership: what a kept continuation is

A continuation an arm keeps is a value, and a value's footprint is said by `LT`, which says what the
continuation's frames are by `FramesOk`, which says what the values in them are by `LT` again. So the
continuations a value may hold are taken from a `World`, and the world the proof works in is the one
that takes exactly the continuations whose frames are as `FramesOk` says in that world: `Φ`'s least
fixed point, which exists because what `FramesOk` says only grows with the world (`FrameOk.mono`).
-/

namespace FlyCore.Ownership

variable {F : List Fn} {O : List Op}

/-- The continuations that are as their frames say in the world `W`: a fiber's frames, suspended
where it performed its `handle`'s operation, at the store `σs`, owning the cells `X`, each failure
they are unwinding with aimed at the fiber's own handler. -/
def Φ (F : List Fn) (O : List Op) (W : World) : World where
  kok σs K τc X := ∃ τ e g fa ff B s K' op ra rf A X', K = .capV τ e g fa ff B s :: K' ∧ τc = .cont op.ret τ ra ∧
    CapVOk F O e fa op τ ra ∧ FiberRow e ff ra rf ∧ (∀ a ∈ A, a = 0 ∨ (a = g ∧ ff = true)) ∧
    FramesOk F O ⟨[], W⟩ σs K' op ⟨[], [], τ, [], rf⟩ X' [] A ∧ X.Perm X'

theorem Φ.mono (h : W.le W') : (Φ F O W).le (Φ F O W') := by
  intro σs K τc X ⟨τ, e, g, fa, ff, B, s, K', op, ra, rf, A, X', hK, hτ, hc, hr, hA, hf, hX⟩
  exact ⟨τ, e, g, fa, ff, B, s, K', op, ra, rf, A, X', hK, hτ, hc, hr, hA, hf.mono (W := W') h, hX⟩

/-- A world that takes exactly what it says it does. -/
def WOk (F : List Fn) (O : List Op) (W : World) : Prop :=
  ∀ σs K τ X, W.kok σs K τ X ↔ (Φ F O W).kok σs K τ X

/-- The world of the proof: the continuations every world closed under `Φ` takes. -/
def Wstar (F : List Fn) (O : List Op) : World where
  kok σs K τ X := ∀ P : World, (Φ F O P).le P → P.kok σs K τ X

theorem Wstar_le (hP : (Φ F O P).le P) : (Wstar F O).le P := fun _ _ _ _ h => h P hP

theorem Wstar_post : (Φ F O (Wstar F O)).le (Wstar F O) :=
  fun σs K τ X h P hP => hP σs K τ X (Φ.mono (Wstar_le hP) σs K τ X h)

theorem Wstar_pre : (Wstar F O).le (Φ F O (Wstar F O)) :=
  Wstar_le (Φ.mono Wstar_post)

theorem Wstar_ok : WOk F O (Wstar F O) :=
  fun σs K τ X => ⟨Wstar_pre σs K τ X, Wstar_post σs K τ X⟩

/-- The world code is checked in takes exactly what it says it does: carried along as an instance,
since every step of the proof is in the same world. -/
class WorldOk (F : List Fn) (O : List Op) (W : World) : Prop where
  ok : WOk F O W

instance : WorldOk F O (Wstar F O) := ⟨Wstar_ok⟩

theorem WorldOk.of_eq (h : W = W') [hW : WorldOk F O W'] : WorldOk F O W := h ▸ hW

end FlyCore.Ownership
