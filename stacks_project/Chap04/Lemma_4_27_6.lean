/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.MorphismProperty.Localization.FractionEquality
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory
namespace MorphismProperty
namespace LeftFraction

universe v u vD uD

variable {C : Type u} {D : Type uD} [Category.{v} C] [Category.{vD} D]
variable (L : C ⥤ D) (W : MorphismProperty C)
  [L.IsLocalization W] [W.HasLeftCalculusOfFractions]
variable {X Y Y' : C} (f g : X ⟶ Y') (s : Y ⟶ Y') (hs : W s)

/- Lemma 4.27.6: equality of two left fractions with a common denominator is equivalent to the
two standard common-refinement criteria. -/
@[stacks 04VF]
#check (map_mk_tfae L W f g s hs :
  [ (LeftFraction.mk f s hs).map L (Localization.inverts L W) =
      (LeftFraction.mk g s hs).map L (Localization.inverts L W),
    ∃ (Y'' : C) (t : Y' ⟶ Y''), W t ∧ f ≫ t = g ≫ t,
    ∃ (Y'' : C) (a : Y' ⟶ Y''), f ≫ a = g ≫ a ∧ W (s ≫ a) ].TFAE)

end LeftFraction
end MorphismProperty
end CategoryTheory
