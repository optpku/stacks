module

public import ReasLib.CategoryTheory.MorphismProperty.Localization.FiniteFractions
import StacksCheckRecall

@[expose] public section

open CategoryTheory.MorphismProperty

universe u v uI uD vD

namespace CategoryTheory.Localization

variable {C : Type u} {D : Type uD} [Category.{v} C] [Category.{vD} D]
variable (L : C ⥤ D) (W : MorphismProperty C)
variable [L.IsLocalization W] [W.HasLeftCalculusOfFractions]
variable {I : Type uI} [Finite I] {X : I → C} {Y : C}
variable (g : ∀ i, L.obj (X i) ⟶ L.obj Y)

/- Lemma 4.27.5: a finite family of morphisms in a localization with common target admits
left-fraction representatives with one common denominator. -/
@[stacks 04VE]
#check (exists_leftFraction_finite L W g :
  ∃ (Y' : C) (s : Y ⟶ Y') (hs : W s) (f : ∀ i, X i ⟶ Y'),
    ∀ i, g i = (LeftFraction.mk (f i) s hs).map L (inverts L W))

end CategoryTheory.Localization
