module

public import ReasLib.CategoryTheory.MorphismProperty.Localization.FiniteFractions
import StacksCheckRecall

@[expose] public section

open CategoryTheory.MorphismProperty

universe u v uI uD vD

namespace CategoryTheory.Localization

variable {C : Type u} {D : Type uD} [Category.{v} C] [Category.{vD} D]
variable (L : C ⥤ D) (W : MorphismProperty C)
variable [L.IsLocalization W] [W.HasRightCalculusOfFractions]
variable {I : Type uI} [Finite I] {X : C} {Y : I → C}
variable (g : ∀ i, L.obj X ⟶ L.obj (Y i))

/- Lemma 4.27.13: a finite family of morphisms in a localization with common source admits
right-fraction representatives with one common denominator. -/
@[stacks 04VI]
#check (exists_rightFraction_finite L W g :
  ∃ (X' : C) (s : X' ⟶ X) (hs : W s) (f : ∀ i, X' ⟶ Y i),
    ∀ i, g i = (RightFraction.mk s hs (f i)).map L (inverts L W))

end CategoryTheory.Localization
