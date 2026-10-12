/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Spec.GradedAction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.GradedEquivariant
import StacksCheckRecall

universe u

/- Example 39.12.3 (1): An integer grading on `A` induces a `Gₘ`-action on `Spec A`. -/
@[stacks 0EKJ] #check (AlgebraicGeometry.GradedSpec.action :
  {A : Type u} → [CommRing A] → (𝒜 : ℤ → Submodule ℤ A) → [GradedAlgebra 𝒜] →
    CategoryTheory.Mod
      (CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℤ))))
      AlgebraicGeometry.MultiplicativeGroup.group.X)

/- Companion recall: on a homogeneous element of degree `n`, the induced coaction on the
coordinate ring of `Spec A` has source-order formula `f ⊗ₜ T n`. -/
#check AlgebraicGeometry.GradedSpec.coaction_sourceFormula

/- Example 39.12.3 (2): A graded `A`-module gives an equivariant affine tilde module. -/
@[stacks 0EKJ] #check (AlgebraicGeometry.GradedSpec.equivariantTilde :
  {A : Type u} → [CommRing A] → (𝒜 : ℤ → Submodule ℤ A) → [GradedAlgebra 𝒜] →
    GradedModule.Left.{0, u, u, 0} 𝒜 ℤ →
      AlgebraicGeometry.Scheme.QCoh.Equivariant
        AlgebraicGeometry.MultiplicativeGroup.group
        (AlgebraicGeometry.GradedSpec.action 𝒜))

/- Companion recall: on a homogeneous graded-module element, the induced linearization carries
the same source-order weight formula. -/
#check AlgebraicGeometry.GradedSpec.linearization_sourceFormula
