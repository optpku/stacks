/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Spec.GradedAction

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GradedSpec

/-- An action of the integral multiplicative group on an affine scheme is equivariantly
isomorphic to the spectrum action associated to an integer grading of its ring of global
sections. -/
theorem existsGradingIso
    (X : Mod (Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
      MultiplicativeGroup.group.X)
    [IsAffine X.X.left] :
    ∃ (𝒜 : ℤ → Submodule ℤ Γ(X.X.left, ⊤)) (h𝒜 : GradedAlgebra 𝒜),
      Nonempty (X ≅ @action _ _ 𝒜 h𝒜) := sorry

end AlgebraicGeometry.GradedSpec
