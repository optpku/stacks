module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Hypersurface.Cohomology

/-!
# Structure-sheaf cohomology of a projective hypersurface

For every homogeneous form `F`, cohomology of `O_{V₊(F)}` vanishes in degrees `q`
with `0 < q` and `n ≤ q`, and agrees with cohomology of its pushforward to projective
space. Intermediate-degree vanishing and the cokernel and top-degree identifications
below are conditional consequences for a nonzerodivisor `F`.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace (twistingSheaf)
open AlgebraicGeometry.ProjectiveSpace.Hypersurface
open scoped AlgebraicGeometry

universe u

section

variable {A : Type u} [CommRing A] (n d : ℕ)
variable (F : MvPolynomial (Fin (n + 1)) A) (hF : F ∈ ProjectiveSpace.grading A n d)
variable (q : ℕ)

/- Exercise 111.42.8: for an arbitrary homogeneous form `F`, structure-sheaf cohomology
of the closed subscheme `V₊(F)` vanishes in degrees `q` with `0 < q` and `n ≤ q`. -/
@[stacks 0D8X] #check
  (AlgebraicGeometry.ProjectiveSpace.Hypersurface.cohomology_isZero_of_ge n d F hF :
    ∀ (q : ℕ) (hq0 : 0 < q) (hqn : n ≤ q),
    IsZero
      (Scheme.Hom.cohomology (hom n d F hF)
        (SheafOfModules.unit (scheme n d F hF).ringCatSheaf) q))

/- Exercise 111.42.8 (1): for an arbitrary homogeneous form `F`, cohomology of the
structure sheaf agrees with cohomology of its pushforward to `P^n_A`. -/
@[stacks 0D8X] #check
  (AlgebraicGeometry.ProjectiveSpace.Hypersurface.cohomology_iso_pushforward n d F hF q :
    IsIsomorphic
      (Scheme.Hom.cohomology (hom n d F hF)
        (SheafOfModules.unit (scheme n d F hF).ringCatSheaf) q)
      (Scheme.Hom.cohomology (ProjectiveSpace.toSpec A n)
        (pushforwardStructure n d F hF) q))

/- Exercise 111.42.8 (2): conditional intermediate-degree vanishing when `F` is a
nonzerodivisor, `0 < n`, `0 < q`, and `q + 1 < n`. -/
@[stacks 0D8X] #check
  (AlgebraicGeometry.ProjectiveSpace.Hypersurface.cohomology_isZero_of_lt n d F hF :
    ∀ (hn : 0 < n)
      (hF_nzd : F ∈ nonZeroDivisors (MvPolynomial (Fin (n + 1)) A))
      (q : ℕ) (hq0 : 0 < q) (hqn : q + 1 < n),
    IsZero
      (Scheme.Hom.cohomology (hom n d F hF)
        (SheafOfModules.unit (scheme n d F hF).ringCatSheaf) q))

/- Exercise 111.42.8 (3): conditional degree-zero cokernel description when `F` is a
nonzerodivisor and `2 ≤ n`. -/
@[stacks 0D8X] #check
  (AlgebraicGeometry.ProjectiveSpace.Hypersurface.cohomology_zero_isCokernel n d F hF :
    ∀ (hn : 2 ≤ n)
      (hF_nzd : F ∈ nonZeroDivisors (MvPolynomial (Fin (n + 1)) A)),
    IsIsomorphic
      (Scheme.Hom.cohomology (hom n d F hF)
        (SheafOfModules.unit (scheme n d F hF).ringCatSheaf) 0)
      (cokernel
        ((Scheme.Hom.cohomologyFunctor (ProjectiveSpace.toSpec A n) 0).map
          (multiplication n d F hF))))

/- Exercise 111.42.8 (4): conditional top-degree identification when `F` is a
nonzerodivisor and `2 ≤ n`. -/
@[stacks 0D8X] #check
  (AlgebraicGeometry.ProjectiveSpace.Hypersurface.cohomology_pred_isTop n d F hF :
    ∀ (hn : 2 ≤ n)
      (hF_nzd : F ∈ nonZeroDivisors (MvPolynomial (Fin (n + 1)) A)),
    IsIsomorphic
      (Scheme.Hom.cohomology (hom n d F hF)
        (SheafOfModules.unit (scheme n d F hF).ringCatSheaf) (n - 1))
      (Scheme.Hom.cohomology (ProjectiveSpace.toSpec A n)
        (twistingSheaf A n (-d)) n))

end
