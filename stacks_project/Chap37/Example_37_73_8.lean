module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ProjectiveSpace.AffineStratification

@[expose] public section

universe u

/- Example 37.73.8: the affine stratification number of standard projective `n`-space
over a field is `n`. -/
@[stacks 0F2Z] #check
  (AlgebraicGeometry.Scheme.FiniteAffineStratification.number_projectiveSpace_eq :
    ∀ (k : Type u) [Field k] (n : ℕ),
      AlgebraicGeometry.Scheme.FiniteAffineStratification.number
        (AlgebraicGeometry.ProjectiveSpace.scheme k n) = n)
