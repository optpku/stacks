/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension.Characterization
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.DerivedCategory AlgebraicGeometry.Scheme.Modules

universe u

namespace Ideal.LocalCohomology

/- Lemma 51.4.1 (1): the local-cohomological dimension bound is characterized by
   modulewise vanishing and by the geometry of the zero locus or its complement. -/
@[stacks 0DX7] #check
  (Ideal.LocalCohomology.hasDimensionLE_iff_allModules :
    ∀ {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG) (d : ℤ) (hd : -1 ≤ d),
      Ideal.LocalCohomology.HasDimensionLE I d ↔
        ∀ (RΓ : DerivedCategory (ModuleCat A) ⥤
            DerivedCategory.IdealPowerTorsion I)
          (hRΓ : DerivedCategory.IdealPowerTorsion.inclusion I ⊣ RΓ) (M : ModuleCat A),
          (RΓ.obj (ModuleCat.single0 M)).obj.IsLE d)

/- Lemma 51.4.1 (2): the negative-one bound is equivalent to an empty zero locus. -/
@[stacks 0DX7] #check
  (Ideal.LocalCohomology.hasDimensionLE_negOne_iff_empty :
    ∀ {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG),
      Ideal.LocalCohomology.HasDimensionLE I (-1) ↔
        PrimeSpectrum.zeroLocus (I : Set A) = ∅)

/- Lemma 51.4.1 (3): the zero bound is equivalent to a clopen zero locus. -/
@[stacks 0DX7] #check
  (Ideal.LocalCohomology.hasDimensionLE_zero_iff_isClopen :
    ∀ {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG),
      Ideal.LocalCohomology.HasDimensionLE I 0 ↔
        IsClopen (PrimeSpectrum.zeroLocus (I : Set A)))

/- Lemma 51.4.1 (4): a positive bound is equivalent to complement cohomology vanishing. -/
@[stacks 0DX7] #check
  (Ideal.LocalCohomology.hasDimensionLE_iff_complementCohomology :
    ∀ {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG) (d : ℤ) (hd : 0 < d),
      Ideal.LocalCohomology.HasDimensionLE I d ↔
        ∀ (F : (idealComplementOpens I).toScheme.Modules)
          [F.IsQuasicoherent] (i : ℕ), d ≤ (i : ℤ) →
          CategoryTheory.Limits.IsZero
            (IdealComplement.cohomology I F i))

end Ideal.LocalCohomology
