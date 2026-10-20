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
namespace RightFraction

universe v u vD uD

variable {C : Type u} {D : Type uD} [Category.{v} C] [Category.{vD} D]
variable (L : C ⥤ D) (S : MorphismProperty C)
  [L.IsLocalization S] [S.HasRightCalculusOfFractions]
variable {X X' Y : C} (f g : X' ⟶ Y) (s : X' ⟶ X) (hs : S s)

/- Lemma 4.27.14: equality of two right fractions with a common denominator is equivalent to the
two standard common-refinement criteria. -/
@[stacks 04VJ]
#check (map_mk_tfae L S f g s hs :
  [ (RightFraction.mk s hs f).map L (Localization.inverts L S) =
      (RightFraction.mk s hs g).map L (Localization.inverts L S),
    ∃ (X'' : C) (t : X'' ⟶ X'), S t ∧ t ≫ f = t ≫ g,
    ∃ (X'' : C) (a : X'' ⟶ X'), a ≫ f = a ≫ g ∧ S (a ≫ s) ].TFAE)

end RightFraction
end MorphismProperty
end CategoryTheory
