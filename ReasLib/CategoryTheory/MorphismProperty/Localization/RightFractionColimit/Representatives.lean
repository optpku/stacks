module

public import ReasLib.CategoryTheory.MorphismProperty.Localization.RightFractionColimit.Comparison

/-!
# Representatives in the abstract right-fraction Hom-colimit

This file lifts the canonical `ColimitType` representative of a right fraction to mathlib's
chosen source-denominator colimit and records both directions of the localization comparison.
-/

@[expose] public section

universe v u vD uD

namespace CategoryTheory.MorphismProperty.RightFraction.Localization

open Limits Opposite

variable {C : Type u} [Category.{v} C]

/-- The canonical representative of a right fraction in mathlib's chosen source-denominator
Hom-colimit. -/
noncomputable def fractionToColimit (W : MorphismProperty C)
    [W.HasRightCalculusOfFractions] (X Y : C) (z : W.RightFraction X Y) :
    (colimit (homDiagram W X Y) : Type (max u v)) :=
  colimit.ι (homDiagram W X Y)
    (Opposite.op (Over.mk (⊤ : MorphismProperty C) z.s z.hs)) (ULift.up z.f)

/-- The quotient-valued Hom-colimit equivalence sends the canonical abstract representative to
the class of its right fraction. -/
@[simp]
theorem homColimit.equiv.apply_fractionToColimit
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions]
    (X Y : C) (z : W.RightFraction X Y) :
    homColimit.equiv W X Y (fractionToColimit W X Y z) =
      Hom.mk z := sorry

variable {D : Type uD} [Category.{vD} D]

/-- The model-independent Hom-colimit equivalence sends the canonical abstract representative
to the localized morphism represented by its right fraction. -/
@[simp]
theorem homColimit.equivTo.apply_fractionToColimit
    (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] [W.HasRightCalculusOfFractions] (X Y : C)
    (z : W.RightFraction X Y) :
    homColimit.equivTo L W X Y (fractionToColimit W X Y z) =
      z.map L (CategoryTheory.Localization.inverts L W) := sorry

/-- Pulling the localized image of a right fraction back through the abstract Hom-colimit
comparison gives its canonical coprojection representative. -/
@[simp]
theorem homColimit.equivTo.symm_apply_fraction_map
    (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] [W.HasRightCalculusOfFractions] (X Y : C)
    (z : W.RightFraction X Y) :
    (homColimit.equivTo L W X Y).symm
        (z.map L (CategoryTheory.Localization.inverts L W)) =
      fractionToColimit W X Y z := sorry

end CategoryTheory.MorphismProperty.RightFraction.Localization
