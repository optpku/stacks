module

public import ReasLib.CategoryTheory.MorphismProperty.Localization.RightFraction.Quotient
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

open MorphismProperty

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
variable {X Y Z : C}
variable (f : RightFraction.Localization.Hom W X Y)
variable (g : RightFraction.Localization.Hom W Y Z)

/- Mathlib's left-fraction quotient is used internally by ReasLib's right-oriented quotient
owner. The public source facade below therefore talks directly about right-fraction classes,
their composition, and the resulting category, without exposing the opposite-category transport. -/

/- Lemma 4.27.11 (1): the canonical relation on right fractions is an equivalence relation. -/
@[stacks 04VH "equivalence relation on right fractions"]
#check (MorphismProperty.equivalenceRightFractionRel (W := W) X Y :
  @_root_.Equivalence (W.RightFraction X Y) MorphismProperty.RightFractionRel)

/- Lemma 4.27.11 (2): composition descends to equivalence classes of right fractions. -/
@[stacks 04VH "composition on equivalence classes of right fractions"]
#check (RightFraction.Localization.Hom.comp f g : RightFraction.Localization.Hom W X Z)

/- Lemma 4.27.11 (3): right-fraction classes form a category. -/
@[stacks 04VH "category structure on the right-fraction localization"]
#check (RightFraction.Localization.instCategory W : Category (RightFraction.Localization W))

end CategoryTheory
