module

public import ReasLib.CategoryTheory.MorphismProperty.Localization.FiniteShapes
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe vC uC vD uD

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable (L : C ⥤ D) (W : MorphismProperty C)
variable [L.IsLocalization W] [W.HasLeftCalculusOfFractions]

/- Lemma 4.27.9: a localization functor for a left multiplicative system preserves finite
colimits. -/
@[stacks 05Q2]
#check (Functor.IsLocalization.preservesFiniteColimits L W : PreservesFiniteColimits L)
