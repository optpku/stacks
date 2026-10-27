/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.ClosedSupportModel
public import ReasLib.RingTheory.Ideal.FiniteGeneration.Family

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.LocalCohomology

variable {A : Type u} [CommRing A]

/-- Closed-support local cohomology for a finitely generated ideal, constructed by localizing
actual tensor totalization with the extended ordered Cech complex of generators selected from
`hI`. Its preservation, support, and adjunction proofs are recorded in `ClosedSupportModel`. -/
abbrev functor (I : Ideal A) (hI : I.FG) :
    DerivedCategory (ModuleCat A) ⥤
      DerivedCategory.CohomologyIn (ModuleCat.isIdealPowerTorsion I) :=
  ClosedSupportModel.functor I (Ideal.FiniteGeneratingFamily.ofFG I hI).generator
    (Ideal.FiniteGeneratingFamily.ofFG I hI).span_eq

end CategoryTheory.DerivedCategory.LocalCohomology

end
