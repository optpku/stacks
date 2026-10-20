/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.MorphismProperty.Localization.LeftFractionColimit.Functoriality
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory
namespace MorphismProperty

open Limits

universe v u

variable {C : Type u} [Category.{v} C]
variable (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
variable (X Y : C)

/- Remark 4.27.7 (1): target denominators of a left multiplicative system form a filtered
category. -/
@[stacks 05Q0 "filtered category of target denominators"]
#check (LeftFraction.targetArrows_isFiltered W Y :
  IsFiltered (MorphismProperty.Under W ⊤ Y))

/- Remark 4.27.7 (2), formula 4.27.7.1: localized Hom-sets are filtered colimits over target
denominators. -/
@[stacks 05Q0 "localized Hom-set as a filtered colimit"]
#check (LeftFraction.Localization.homColimit.iso W X Y :
  colimit (LeftFraction.Localization.homDiagram W X Y) ≅
    ((LeftFraction.Localization.Q W).obj X ⟶ (LeftFraction.Localization.Q W).obj Y))

end MorphismProperty
end CategoryTheory
