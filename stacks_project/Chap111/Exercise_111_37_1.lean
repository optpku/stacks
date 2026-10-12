/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Examples
import StacksCheckRecall

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory

/- Exercise 111.37.1 (1): `Proj` of the standard graded ring `ℤ[T]` is affine and nonempty. -/
@[stacks 029X] #check (AlgebraicGeometry.projectiveSpace_zero_isAffine_nonempty :
  IsAffine (Proj (ProjectiveSpace.grading ℤ 0)) ∧
    Nonempty (Proj (ProjectiveSpace.grading ℤ 0)))

/- Exercise 111.37.1 (2): `Proj` of the Fermat cubic coordinate ring is integral and nonempty,
but not isomorphic to `ProjectiveSpace.scheme A n` for any ring `A` and any `n ≥ 0`. -/
@[stacks 029X] #check (AlgebraicGeometry.FermatCubic.spec :
  IsIntegral AlgebraicGeometry.FermatCubic.scheme ∧
    ∀ (A : Type) [CommRing A] (n : ℕ),
      IsEmpty (AlgebraicGeometry.FermatCubic.scheme ≅ ProjectiveSpace.scheme A n))
