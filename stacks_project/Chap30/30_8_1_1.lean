/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.ProjectiveSpace.TwistCohomology
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.Limits

universe u

/-
30.8.1.1 (1): degree-zero cohomology of `𝒪(d)` on standard projective `n`-space is the
degree-`d` homogeneous piece of the polynomial ring.
-/
@[stacks 01XU] #check
  (AlgebraicGeometry.ProjectiveSpace.twistingSheaf.cohomology_zero :
    ∀ (R : Type u) [CommRing R] (n : ℕ) (_ : 0 < n) (d : ℤ),
      IsIsomorphic
        (AlgebraicGeometry.Scheme.Hom.cohomology
          (AlgebraicGeometry.ProjectiveSpace.toSpec R n)
          (AlgebraicGeometry.ProjectiveSpace.twistingSheaf R n d) 0)
        (ModuleCat.of R (AlgebraicGeometry.ProjectiveSpace.gradedPiece R n d)))

/-
30.8.1.1 (2): cohomology of `𝒪(d)` on standard projective `n`-space vanishes outside degrees
zero and `n`.
-/
@[stacks 01XU] #check
  (AlgebraicGeometry.ProjectiveSpace.twistingSheaf.cohomology_isZero_of_ne :
    ∀ (R : Type u) [CommRing R] (n : ℕ) (_ : 0 < n) (d : ℤ) (q : ℕ),
      q ≠ 0 → q ≠ n →
        IsZero
          (AlgebraicGeometry.Scheme.Hom.cohomology
            (AlgebraicGeometry.ProjectiveSpace.toSpec R n)
            (AlgebraicGeometry.ProjectiveSpace.twistingSheaf R n d) q))

/-
30.8.1.1 (3): degree-`n` cohomology of `𝒪(d)` on standard projective `n`-space is the linear
dual of the homogeneous piece in degree `-n - 1 - d`.
-/
@[stacks 01XU] #check
  (AlgebraicGeometry.ProjectiveSpace.twistingSheaf.cohomology_top :
    ∀ (R : Type u) [CommRing R] (n : ℕ) (_ : 0 < n) (d : ℤ),
      IsIsomorphic
        (AlgebraicGeometry.Scheme.Hom.cohomology
          (AlgebraicGeometry.ProjectiveSpace.toSpec R n)
          (AlgebraicGeometry.ProjectiveSpace.twistingSheaf R n d) n)
        (ModuleCat.of R
          (AlgebraicGeometry.ProjectiveSpace.topCohomologyDual R n d)))
