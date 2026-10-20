module

public import ReasLib.CategoryTheory.InverseSystem.Sequential

/-!
# Eventually Isomorphic Sequential Inverse Systems

This leaf records the elementary consequence of eventually invertible successor
maps: every sufficiently late transition map is invertible.  It has no
additive, image, or limit hypotheses.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.SequentialInverseSystem

variable {A : Type u} [Category.{v} A]

/-- If all successor transition maps from stage `N` onward are isomorphisms, then every
transition map from a later stage to `N` is an isomorphism. -/
theorem transitionMap_isIso_of_eventually_isIso_stepMap
    (F : SequentialInverseSystem A) {N k : ℕ} (hNk : N ≤ k)
    (hF : ∀ n : ℕ, N ≤ n → IsIso (F.stepMap n)) :
    IsIso (F.transitionMap hNk) := sorry

end CategoryTheory.SequentialInverseSystem
