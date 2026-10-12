/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.MorphismProperty.SaturatedMultiplicativeSystem
public import ReasLib.CategoryTheory.ObjectProperty.Localization.FullSubcategory

@[expose] public section

/-!
# Saturation of Localization Systems on Full Subcategories

This leaf identifies the restriction of a saturated morphism property to a full subcategory
with the morphisms inverted by the localized inclusion.  It is independent of denominator-cover
and resolution hypotheses.
-/

universe v u

namespace CategoryTheory

open Localization MorphismProperty ObjectProperty

variable {D : Type u} [Category.{v} D]
  (P : ObjectProperty D) (S : MorphismProperty D)

namespace fullSubcategoryLocalizationSystem

/-- Stacks 0GSL: the restriction of a saturated system to a full subcategory consists exactly
of the arrows whose image under the localized inclusion is an isomorphism. -/
@[stacks 0GSL "saturation of a restricted localization system"]
theorem eq_inverseImage_isomorphisms [IsSaturatedMultiplicativeSystem S] :
    fullSubcategoryLocalizationSystem P S =
      (isomorphisms S.Localization).inverseImage (P.ι ⋙ S.Q) := sorry

end fullSubcategoryLocalizationSystem

end CategoryTheory
