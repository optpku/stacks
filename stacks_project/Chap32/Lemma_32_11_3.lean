module

import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.AffineCover
import StacksCheckRecall

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 32.11.3: let `X` be a scheme which is set-theoretically the union of finitely
many affine closed subschemes. Then `X` is affine. -/
@[stacks 09NL] #check
  (AlgebraicGeometry.Scheme.isAffine_of_finite_affine_closedSubscheme_cover :
    ∀ {X : Scheme.{u}} {ι : Type u} [Finite ι] (Z : ι → X.IdealSheafData)
      [∀ j, IsAffine (Z j).subscheme],
      (∀ x : X, ∃ j : ι, x ∈ (Z j).support) → IsAffine X)
