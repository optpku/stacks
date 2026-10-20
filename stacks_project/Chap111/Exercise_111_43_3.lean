module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.PuncturedAffineSpace.Cohomology

/-!
# Cohomology of punctured affine space
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Exercise 111.43.3 (1): Degree-zero cohomology for every dimension. -/
@[stacks 0DAL] #check (AlgebraicGeometry.PuncturedAffineSpace.cohomology_zero :
  ∀ (d : ℕ) (k : Type u) [Field k],
    IsIsomorphic (AlgebraicGeometry.PuncturedAffineSpace.structureSheafCohomology d k 0)
      (ModuleCat.of k (AlgebraicGeometry.PuncturedAffineSpace.sectionsModel d k)))

/- Exercise 111.43.3 (2): Cohomology in all other degrees vanishes. -/
@[stacks 0DAL] #check (AlgebraicGeometry.PuncturedAffineSpace.cohomology_isZero_of_ne :
  ∀ (d : ℕ) (k : Type u) [Field k] (n : ℕ), n ≠ 0 → n ≠ d.pred →
    IsZero (AlgebraicGeometry.PuncturedAffineSpace.structureSheafCohomology d k n))

/- Exercise 111.43.3 (3): Positive top cohomology in dimension at least two. -/
@[stacks 0DAL] #check (AlgebraicGeometry.PuncturedAffineSpace.cohomology_top :
  ∀ (d : ℕ) (k : Type u) [Field k], 2 ≤ d →
    IsIsomorphic (AlgebraicGeometry.PuncturedAffineSpace.structureSheafCohomology d k d.pred)
      (ModuleCat.of k (AlgebraicGeometry.PuncturedAffineSpace.negativeLaurent d k)))
