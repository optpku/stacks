module

public import ReasLib.CategoryTheory.MorphismProperty.Localization.RightFractionColimit.Functoriality
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory
namespace MorphismProperty

open Limits

universe v u vD uD

variable {C : Type u} [Category.{v} C]
variable {D : Type uD} [Category.{vD} D]
variable (L : C ⥤ D) (W : MorphismProperty C)
variable [L.IsLocalization W] [W.HasRightCalculusOfFractions]
variable (X Y : C)

/- Remark 4.27.15 (1): source denominators of a right multiplicative system form a cofiltered
category. -/
@[stacks 05Q4 "cofiltered category of source denominators"]
#check (RightFraction.sourceArrows_isCofiltered W X :
  IsCofiltered (MorphismProperty.Over W ⊤ X))

/- Remark 4.27.15 (2), formula 4.27.15.1: localized Hom-sets are filtered colimits over source
denominators. -/
@[stacks 05Q4 "localized Hom-set as a filtered colimit"]
#check (RightFraction.Localization.homColimit.equivTo L W X Y :
  (colimit (RightFraction.Localization.homDiagram W X Y) : Type (max u v)) ≃
    (L.obj X ⟶ L.obj Y))

end MorphismProperty
end CategoryTheory
