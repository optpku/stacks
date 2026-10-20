/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension.MaximalIdeal
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.DerivedCategory
open CategoryTheory.DerivedCategory.LocalCohomology

universe u

namespace Ideal.LocalCohomology

/- Lemma 51.4.9 (1): for a Noetherian local ring of Krull dimension `d`, every
right-adjoint presentation of its degree-`d` local cohomology supported at the maximal ideal
is not a zero object. -/
@[stacks 0DXE] #check
  (Ideal.LocalCohomology.topCohomology_not_isZero :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      (d : ℕ) (hdim : ringKrullDim A = d)
      (RΓ : DerivedCategory (ModuleCat A) ⥤
        DerivedCategory.IdealPowerTorsion (IsLocalRing.maximalIdeal A))
      (hRΓ : DerivedCategory.IdealPowerTorsion.inclusion
        (IsLocalRing.maximalIdeal A) ⊣ RΓ),
      ¬ IsZero (supportedCohomology (IsLocalRing.maximalIdeal A) RΓ
        (ModuleCat.of A A) (d : ℤ)))

/- Lemma 51.4.9 (2): the maximal ideal of a Noetherian local ring has
local-cohomological dimension equal to the ring's Krull dimension. -/
@[stacks 0DXE] #check
  (Ideal.LocalCohomology.dimension_maximalIdeal_eq :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      (d : ℕ) (hdim : ringKrullDim A = d),
      dimension (IsLocalRing.maximalIdeal A)
        (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing = (d : ℤ))

end Ideal.LocalCohomology
