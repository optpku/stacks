/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Model.GoodReduction
public import ReasLib.AlgebraicGeometry.Scheme.Model.Regular.Smooth

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Definition 55.14.8. A smooth projective curve over the fraction field of a discrete
valuation ring, whose global functions are precisely the constants, has good reduction
when the equivalent smooth-model conditions hold. -/
@[stacks 0CDJ]
#check (AlgebraicGeometry.Scheme.Hom.hasGoodReduction :
    ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom], Prop)

#check (AlgebraicGeometry.Scheme.Hom.exists_smoothModel_iff_exists_smoothMinimalModel :
    ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom)),
    (∃ M : RegularModel R K C, Smooth M.base) ↔
      ∃ M : RegularModel R K C, IsMinimalModel M.base ∧ Smooth M.base)

#check (AlgebraicGeometry.Scheme.Hom.exists_smoothMinimalModel_iff_forall_minimalModel_smooth :
    ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom)),
    (∃ M : RegularModel R K C, IsMinimalModel M.base ∧ Smooth M.base) ↔
      ∀ M : RegularModel R K C, IsMinimalModel M.base → Smooth M.base)

end AlgebraicGeometry.Scheme.Hom
