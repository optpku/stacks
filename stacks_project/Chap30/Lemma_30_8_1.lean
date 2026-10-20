/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.ProjectiveSpace.TwistCohomology
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.Limits

universe u

/- Lemma 30.8.1
For a commutative ring `R`, the cohomology of the degree-`d` twisting sheaf on standard
projective `n`-space is the degree-`d` polynomial piece in degree zero when `d ≥ 0`, the
inverse-monomial (top-dual) piece in degree `n` when `d < 0`, and zero in all other cases,
as `R`-modules.
-/
@[stacks 01XT] #check
  (AlgebraicGeometry.ProjectiveSpace.twistingSheaf.cohomology_zero_of_nonneg :
    ∀ (R : Type u) [CommRing R] (n : ℕ) (d : ℤ), 0 ≤ d →
      IsIsomorphic
        (AlgebraicGeometry.Scheme.Hom.cohomology
          (AlgebraicGeometry.ProjectiveSpace.toSpec R n)
          (AlgebraicGeometry.ProjectiveSpace.twistingSheaf R n d) 0)
        (ModuleCat.of R (AlgebraicGeometry.ProjectiveSpace.gradedPiece R n d)))

#check
  (AlgebraicGeometry.ProjectiveSpace.twistingSheaf.cohomology_top_of_neg :
    ∀ (R : Type u) [CommRing R] (n : ℕ) (d : ℤ), d < 0 →
      IsIsomorphic
        (AlgebraicGeometry.Scheme.Hom.cohomology
          (AlgebraicGeometry.ProjectiveSpace.toSpec R n)
          (AlgebraicGeometry.ProjectiveSpace.twistingSheaf R n d) n)
        (ModuleCat.of R (AlgebraicGeometry.ProjectiveSpace.topCohomologyDual R n d)))

#check
  (AlgebraicGeometry.ProjectiveSpace.twistingSheaf.cohomology_isZero_of_not_cases :
    ∀ (R : Type u) [CommRing R] (n q : ℕ) (d : ℤ),
      ¬ (q = 0 ∧ 0 ≤ d) → ¬ (q = n ∧ d < 0) →
        IsZero
          (AlgebraicGeometry.Scheme.Hom.cohomology
          (AlgebraicGeometry.ProjectiveSpace.toSpec R n)
          (AlgebraicGeometry.ProjectiveSpace.twistingSheaf R n d) q))
