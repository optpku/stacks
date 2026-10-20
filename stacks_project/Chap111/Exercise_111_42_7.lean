module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.TwistCohomology
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.Limits

universe u

/-
Exercise 111.42.7
Let `A` be a ring and let `ℙⁿ_A = Proj(A[T₀, …, Tₙ])` be projective space over `A`.
The cohomology of the Serre twists `𝒪(d)` of the structure sheaf on `ℙⁿ_A` is identified
as `A`-modules by the following three cases.
-/

/- Exercise 111.42.7 (1): degree-zero cohomology of `𝒪(d)` for `d ≥ 0` is the degree-`d`
homogeneous piece of the polynomial ring. -/
@[stacks 0D8W] #check
  (AlgebraicGeometry.ProjectiveSpace.twistingSheaf.cohomology_zero_of_nonneg :
    ∀ (R : Type u) [CommRing R] (n : ℕ) (d : ℤ), 0 ≤ d →
      IsIsomorphic
        (AlgebraicGeometry.Scheme.Hom.cohomology
          (AlgebraicGeometry.ProjectiveSpace.toSpec R n)
          (AlgebraicGeometry.ProjectiveSpace.twistingSheaf R n d) 0)
        (ModuleCat.of R (AlgebraicGeometry.ProjectiveSpace.gradedPiece R n d)))

/- Exercise 111.42.7 (2): top-degree cohomology of `𝒪(d)` for `d < 0` is the linear dual of
the homogeneous piece in degree `-n - 1 - d`. -/
@[stacks 0D8W] #check
  (AlgebraicGeometry.ProjectiveSpace.twistingSheaf.cohomology_top_of_neg :
    ∀ (R : Type u) [CommRing R] (n : ℕ) (d : ℤ), d < 0 →
      IsIsomorphic
        (AlgebraicGeometry.Scheme.Hom.cohomology
          (AlgebraicGeometry.ProjectiveSpace.toSpec R n)
          (AlgebraicGeometry.ProjectiveSpace.twistingSheaf R n d) n)
        (ModuleCat.of R (AlgebraicGeometry.ProjectiveSpace.topCohomologyDual R n d)))

/- Exercise 111.42.7 (3): cohomology of `𝒪(d)` vanishes outside the degree-zero
nonnegative-twist case and the top-degree negative-twist case. -/
@[stacks 0D8W] #check
  (AlgebraicGeometry.ProjectiveSpace.twistingSheaf.cohomology_isZero_of_not_cases :
    ∀ (R : Type u) [CommRing R] (n q : ℕ) (d : ℤ),
      ¬ (q = 0 ∧ 0 ≤ d) → ¬ (q = n ∧ d < 0) →
        IsZero
          (AlgebraicGeometry.Scheme.Hom.cohomology
            (AlgebraicGeometry.ProjectiveSpace.toSpec R n)
            (AlgebraicGeometry.ProjectiveSpace.twistingSheaf R n d) q))
