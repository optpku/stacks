module

import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.AmpleCriterion
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 30.17.7: let `X` be a scheme and let `L` be an ample invertible
`𝒪_X`-module. If there is an integer `n₀` such that
`H^p(X, L ^⊗ (-n)) = 0` for every integer `n ≥ n₀` and every `p > 0`, then `X` is
affine. -/
@[stacks 0EBD] #check
  (AlgebraicGeometry.Scheme.Modules.isAffine_of_isAmple_higherCohomology_neg_tensorPower_isZero :
    ∀ {X : Scheme.{u}} (L : X.Modules)
      [AlgebraicGeometry.Scheme.Modules.Invertible L]
      [AlgebraicGeometry.Scheme.Modules.IsAmple L]
      (n₀ : ℤ),
      (∀ n : ℤ, n₀ ≤ n → ∀ p : ℕ, 0 < p →
        IsZero (RingedSpace.moduleCohomology
          (AlgebraicGeometry.Scheme.Modules.tensorPowerInt L (-n)) p)) →
        IsAffine X)
