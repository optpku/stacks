module

public import ReasLib.CategoryTheory.MorphismProperty.Localization.RightFraction.Quotient
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

open MorphismProperty

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
  [W.HasRightCalculusOfFractions]

/-
The source-facing models from Lemmas 4.27.8 and 4.27.16 are now the two explicit quotient
models `LeftFraction.Localization W` and `RightFraction.Localization W`. Both are localization
models for `W`; `Localization.uniq` therefore gives the required equivalence in the source's
left-to-right direction without identifying the textbook right-fraction category with a separate
generic localization presentation.
-/

/- Lemma 4.27.19: the category of left fractions and the category of right fractions for a
multiplicative system `W` are canonically equivalent. -/
@[stacks 04VL "canonical equivalence of left- and right-fraction localizations"]
#check (Localization.uniq (LeftFraction.Localization.Q W) (RightFraction.Localization.Q W) W :
  LeftFraction.Localization W ≌ RightFraction.Localization W)

end CategoryTheory
