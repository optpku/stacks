/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.MorphismProperty.Localization.Preadditive
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe w v u

namespace CategoryTheory

open MorphismProperty

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {D : Type u} [Category.{w} D]
variable {W : MorphismProperty C} (L : C ⥤ D) [L.IsLocalization W]

/- Lemma 12.8.1: a left- or right-fraction localization has a unique preadditive structure making
the localization functor additive. -/
@[stacks 05QD]
#check Localization.existsUniquePreadditive L W

/- The right-fraction branch is available as an explicit reusable structure and additive bridge. -/
section Right

variable [W.HasRightCalculusOfFractions]

#check Localization.preadditiveOfHasRightCalculusOfFractions L W
#check Localization.functorAdditiveOfHasRightCalculusOfFractions L W

end Right

end CategoryTheory
