/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Spec.GradedAction.Classification
import StacksCheckRecall

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 39.12.4: an action of the integral multiplicative group on an affine scheme is
equivariantly isomorphic to the spectrum action associated to a `ℤ`-grading of its ring of
global sections. -/
@[stacks 0EKK]
#check (AlgebraicGeometry.GradedSpec.existsGradingIso :
  ∀ (X : Mod (Over (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℤ))))
      AlgebraicGeometry.MultiplicativeGroup.group.X)
      [AlgebraicGeometry.IsAffine X.X.left],
    ∃ (𝒜 : ℤ → Submodule ℤ Γ(X.X.left, ⊤)) (h𝒜 : GradedAlgebra 𝒜),
      Nonempty (X ≅ @AlgebraicGeometry.GradedSpec.action _ _ 𝒜 h𝒜))
