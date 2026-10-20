/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.MorphismProperty.Localization.LeftFractionColimit.Comparison

/-!
# Representatives in the abstract left-fraction Hom-colimit

The concrete `ColimitType` model already has canonical representatives of left fractions. This
file exposes the corresponding coprojections in mathlib's chosen colimit and computes both
directions of the localization comparison on them.
-/

@[expose] public section

universe v u vD uD

namespace CategoryTheory.MorphismProperty.LeftFraction.Localization

open Limits Opposite

variable {C : Type u} [Category.{v} C]

/-- The canonical representative of a left fraction in mathlib's chosen target-denominator
Hom-colimit. -/
noncomputable def fractionToColimit (W : MorphismProperty C) (X Y : C)
    (z : W.LeftFraction X Y) :
    (colimit (homDiagram W X Y) : Type (max u v)) :=
  colimit.ι (homDiagram W X Y) (Under.mk ⊤ z.s z.hs)
    (ULift.up (eqToHom (Opposite.unop_op X).symm ≫ z.f))

/-- The quotient-valued Hom-colimit equivalence sends the canonical abstract representative to
the class of its left fraction. -/
@[simp]
theorem homColimit.equiv.apply_fractionToColimit
    (W : MorphismProperty C) (X Y : C) (z : W.LeftFraction X Y) :
    homColimit.equiv W X Y (fractionToColimit W X Y z) =
      Hom.mk z := sorry

variable {D : Type uD} [Category.{vD} D]

/-- The model-independent Hom-colimit equivalence sends the canonical abstract representative
to the localized morphism represented by its left fraction. -/
@[simp]
theorem homColimit.equivTo.apply_fractionToColimit
    (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] [W.HasLeftCalculusOfFractions] (X Y : C)
    (z : W.LeftFraction X Y) :
    homColimit.equivTo L W X Y (fractionToColimit W X Y z) =
      z.map L (CategoryTheory.Localization.inverts L W) := sorry

/-- Pulling the localized image of a left fraction back through the abstract Hom-colimit
comparison gives its canonical coprojection representative. -/
@[simp]
theorem homColimit.equivTo.symm_apply_fraction_map
    (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] [W.HasLeftCalculusOfFractions] (X Y : C)
    (z : W.LeftFraction X Y) :
    (homColimit.equivTo L W X Y).symm
        (z.map L (CategoryTheory.Localization.inverts L W)) =
      fractionToColimit W X Y z := sorry

end CategoryTheory.MorphismProperty.LeftFraction.Localization
