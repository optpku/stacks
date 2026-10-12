/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.IdealComplement

@[expose] public section

open CategoryTheory CategoryTheory.DerivedCategory AlgebraicGeometry.Scheme.Modules

noncomputable section

universe u

namespace Ideal.LocalCohomology

variable {A : Type u} [CommRing A]

/-- The regular-module local-cohomological dimension bound is equivalent to the same bound
for every module and every right-adjoint presentation of local cohomology. -/
theorem hasDimensionLE_iff_allModules (I : Ideal A) (hI : I.FG) (d : ℤ) (hd : -1 ≤ d) :
    HasDimensionLE I d ↔
      ∀ (RΓ : DerivedCategory (ModuleCat A) ⥤
          DerivedCategory.IdealPowerTorsion I)
        (hRΓ : DerivedCategory.IdealPowerTorsion.inclusion I ⊣ RΓ) (M : ModuleCat A),
        (RΓ.obj (ModuleCat.single0 M)).obj.IsLE d := sorry

/-- Local-cohomological dimension at most `-1` is equivalent to an empty zero locus. -/
theorem hasDimensionLE_negOne_iff_empty (I : Ideal A) (hI : I.FG) :
    HasDimensionLE I (-1) ↔ PrimeSpectrum.zeroLocus (I : Set A) = ∅ := sorry

/-- Local-cohomological dimension at most zero is equivalent to a clopen zero locus. -/
theorem hasDimensionLE_zero_iff_isClopen (I : Ideal A) (hI : I.FG) :
    HasDimensionLE I 0 ↔ IsClopen (PrimeSpectrum.zeroLocus (I : Set A)) := sorry

/-- For a positive bound, local-cohomological dimension is equivalent to complement
cohomology vanishing in all degrees at least that bound. -/
theorem hasDimensionLE_iff_complementCohomology (I : Ideal A) (hI : I.FG)
    (d : ℤ) (hd : 0 < d) :
    HasDimensionLE I d ↔
      ∀ (F : (idealComplementOpens I).toScheme.Modules)
        [F.IsQuasicoherent] (i : ℕ), d ≤ (i : ℤ) →
        CategoryTheory.Limits.IsZero
          (IdealComplement.cohomology I F i) := sorry

end Ideal.LocalCohomology
