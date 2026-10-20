module

public import ReasLib.AlgebraicGeometry.Scheme.Spec.GradedAction

/-!
# Compatibility for the graded affine action

This module retains the lifted-integer algebra instance used by existing source-facing
consumers and re-exports the reusable graded affine action API.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GradedSpec

variable {A : Type u} [CommRing A] (𝒜 : ℤ → Submodule ℤ A) [GradedAlgebra 𝒜]

/-- The canonical algebra structure of a commutative ring over the universe lift of `ℤ`. -/
instance instAlgebraULiftInt : Algebra (ULift.{u} ℤ) A :=
  ULift.algebra' ℤ A

/- Compatibility check for the multiplicative-group action induced by an integer grading. -/
#check (AlgebraicGeometry.GradedSpec.action 𝒜 :
  Mod (Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) MultiplicativeGroup.group.X)

end AlgebraicGeometry.GradedSpec
