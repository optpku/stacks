module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist

/-!
# The Beilinson generator on projective space

This file defines the finite coproduct of the standard negative twisting sheaves on projective
space.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- The finite coproduct of the twists `𝒪(-i)` for `0 ≤ i ≤ n` on standard
projective `n`-space. -/
noncomputable def beilinsonGenerator (R : Type u) [CommRing R] (n : ℕ) :
    (scheme R n).Modules :=
  ∐ fun i : Fin (n + 1) ↦ twistingSheaf R n (-(i : ℤ))

/-- The Beilinson generator is the finite coproduct of its canonical twisting-sheaf
summands. -/
theorem beilinsonGenerator_def (R : Type u) [CommRing R] (n : ℕ) :
    beilinsonGenerator R n =
      ∐ fun i : Fin (n + 1) ↦ twistingSheaf R n (-(i : ℤ)) := sorry

end AlgebraicGeometry.ProjectiveSpace
