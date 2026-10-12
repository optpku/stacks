/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension.Dualizing

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.DerivedCategory
open CategoryTheory.DerivedCategory.LocalCohomology

universe u

namespace Ideal.LocalCohomology

/-- For a Noetherian local ring of Krull dimension `d`, degree-`d` local cohomology
of the regular module supported at the maximal ideal is nonzero for every
right-adjoint presentation. -/
theorem topCohomology_not_isZero {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (d : ℕ) (hdim : ringKrullDim A = d)
    (RΓ : DerivedCategory (ModuleCat A) ⥤
      DerivedCategory.IdealPowerTorsion (IsLocalRing.maximalIdeal A))
    (hRΓ : DerivedCategory.IdealPowerTorsion.inclusion
      (IsLocalRing.maximalIdeal A) ⊣ RΓ) :
    ¬ IsZero (supportedCohomology (IsLocalRing.maximalIdeal A) RΓ
      (ModuleCat.of A A) (d : ℤ)) := sorry

/-- The local-cohomological dimension of the maximal ideal of a Noetherian local
ring equals its Krull dimension. -/
theorem dimension_maximalIdeal_eq {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (d : ℕ) (hdim : ringKrullDim A = d) :
    dimension (IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing = (d : ℤ) := sorry

end Ideal.LocalCohomology
