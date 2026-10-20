/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.Restriction
import StacksCheckRecall

/-!
# Lemma 15.92.24: derived completeness under restriction of scalars

The generic restriction/base-change API is owned by
`ReasLib.Algebra.Homology.DerivedCategory.Completeness.Restriction`.  This chapter file keeps the
source tag and the historical `CategoryTheory` lookup path only; the old Milnor-limit proof route
was chapter-local implementation detail and is not part of the reusable statement surface.

@stack 0924
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.DerivedCategory

export _root_.DerivedCategory
  (isZero_restrictScalars_iff
    localizationAwayDerivedHomVanishingCondition_restrictScalars_iff
    localizationAwayDerivedHomVanishingIdeal_restrictScalars
    isDerivedCompleteWithRespectTo_iff_restrictScalars)

/- Lemma 15.92.24 (Stacks `0924`): for `σ : A →+* B`, restriction of scalars identifies the
derived-complete objects for `I` with those for `I.map σ`. -/
@[stacks 0924 "derived completeness under restriction of scalars"]
#check @_root_.DerivedCategory.isDerivedCompleteWithRespectTo_iff_restrictScalars
@[stacks 0924 "restriction of scalars reflects zero objects"]
#check @_root_.DerivedCategory.isZero_restrictScalars_iff
@[stacks 0924 "restriction of scalars and localization-away vanishing"]
#check @_root_.DerivedCategory.localizationAwayDerivedHomVanishingCondition_restrictScalars_iff
@[stacks 0924 "restriction of scalars and vanishing ideals"]
#check @_root_.DerivedCategory.localizationAwayDerivedHomVanishingIdeal_restrictScalars

#check @CategoryTheory.DerivedCategory.isDerivedCompleteWithRespectTo_iff_restrictScalars
#check @CategoryTheory.DerivedCategory.isZero_restrictScalars_iff

end CategoryTheory.DerivedCategory

namespace CategoryTheory

/- Existing chapter consumers historically used the parent `CategoryTheory` qualification. -/
export _root_.DerivedCategory
  (isZero_restrictScalars_iff
    localizationAwayDerivedHomVanishingCondition_restrictScalars_iff
    localizationAwayDerivedHomVanishingIdeal_restrictScalars
    isDerivedCompleteWithRespectTo_iff_restrictScalars)

#check @CategoryTheory.isDerivedCompleteWithRespectTo_iff_restrictScalars

end CategoryTheory

end
