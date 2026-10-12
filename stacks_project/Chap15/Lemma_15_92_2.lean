/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.Ideal
import StacksCheckRecall

/-!
# Lemma 15.92.2: the localization-away vanishing ideal

The ideal and its radicality are reusable derived-category infrastructure owned by
`ReasLib.Algebra.Homology.DerivedCategory.Completeness.Ideal`.  This chapter file is a tagged
source-facing recall and preserves the historical `CategoryTheory.DerivedCategory` lookup path.

@stack 091Q
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.DerivedCategory

export _root_.DerivedCategory
  (localizationAwayDerivedHomVanishingCondition_zero
    localizationAwayDerivedHomVanishingCondition_add
    localizationAwayDerivedHomVanishingCondition_smul
    localizationAwayDerivedHomVanishingCondition_of_pow
    localizationAwayDerivedHomVanishingIdeal
    mem_localizationAwayDerivedHomVanishingIdeal_iff
    localizationAwayDerivedHomVanishingIdeal_isRadical)

/- Lemma 15.92.2 (Stacks `091Q`): the localization-away derived-Hom vanishing locus is a radical
ideal; its carrier is the predicate from Lemma 15.92.1. -/
@[stacks 091Q "localization-away vanishing ideal and radicality"]
#check @_root_.DerivedCategory.localizationAwayDerivedHomVanishingIdeal
@[stacks 091Q "membership in the localization-away vanishing ideal"]
#check @_root_.DerivedCategory.mem_localizationAwayDerivedHomVanishingIdeal_iff
@[stacks 091Q "radicality of the localization-away vanishing ideal"]
#check @_root_.DerivedCategory.localizationAwayDerivedHomVanishingIdeal_isRadical

#check @CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingIdeal
#check @CategoryTheory.DerivedCategory.mem_localizationAwayDerivedHomVanishingIdeal_iff
#check @CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingIdeal_isRadical

end CategoryTheory.DerivedCategory

end
