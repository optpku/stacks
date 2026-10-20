/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Localization.HomEquiv
public import ReasLib.CategoryTheory.MorphismProperty.Localization.LeftFractionColimit.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparing the left-fraction Hom-colimit with localization models

The explicit quotient presentation is transported to an arbitrary localization model.  This
leaf also records the canonical-localization isomorphism and all coprojection computations.
-/

@[expose] public section

universe v u vD uD

namespace CategoryTheory.MorphismProperty.LeftFraction.Localization

open Limits

variable {C : Type u} [Category.{v} C]
variable {D : Type uD} [Category.{vD} D]

/-- The data-clean equivalence from the concrete target-denominator colimit
model to the Hom-set in any localization model of `W`.  It is obtained by
first passing to the canonical quotient of left fractions and then transporting
along the universal localization comparison. -/
noncomputable def homColimit.typeEquivTo
    (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] [W.HasLeftCalculusOfFractions] (X Y : C) :
    (homDiagram W X Y).ColimitType ≃ (L.obj X ⟶ L.obj Y) :=
  (homColimit.typeEquiv W X Y).trans
    (CategoryTheory.Localization.homEquiv (X := X) (Y := Y) W (Q W) L)

/-- The concrete Hom-colimit comparison evaluates a diagram coprojection as
the corresponding left fraction in any localization model. -/
@[simp]
theorem homColimit.typeEquivTo.apply_ιColimitType
    (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] [W.HasLeftCalculusOfFractions] (X Y : C)
    (s : MorphismProperty.Under W ⊤ Y) (f : (homDiagram W X Y).obj s) :
    homColimit.typeEquivTo L W X Y ((homDiagram W X Y).ιColimitType s f) =
      (fraction W X Y s f).map L (CategoryTheory.Localization.inverts L W) := sorry

/-- The concrete Hom-colimit comparison evaluates the canonical representative
of a left fraction as that fraction in any localization model. -/
@[simp]
theorem homColimit.typeEquivTo.apply_fractionToColimitType
    (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] [W.HasLeftCalculusOfFractions] (X Y : C)
    (z : W.LeftFraction X Y) :
    homColimit.typeEquivTo L W X Y (fractionToColimitType W X Y z) =
      z.map L (CategoryTheory.Localization.inverts L W) := sorry

/-- Pulling the localized image of a left fraction back through the concrete
Hom-colimit comparison gives its canonical colimit representative. -/
@[simp]
theorem homColimit.typeEquivTo.symm_apply_fraction_map
    (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] [W.HasLeftCalculusOfFractions] (X Y : C)
    (z : W.LeftFraction X Y) :
    (homColimit.typeEquivTo L W X Y).symm
        (z.map L (CategoryTheory.Localization.inverts L W)) =
      fractionToColimitType W X Y z := sorry

/-- The left-fraction Hom-colimit computes the Hom-set in any localization model of `W`. -/
noncomputable def homColimit.equivTo
    (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] [W.HasLeftCalculusOfFractions] (X Y : C) :
    (colimit (homDiagram W X Y) : Type (max u v)) ≃ (L.obj X ⟶ L.obj Y) :=
  (Limits.Types.colimitEquivColimitType (homDiagram W X Y)).trans
    (homColimit.typeEquivTo L W X Y)

/-- The model-independent left-fraction Hom-colimit equivalence sends a coprojection to the
localized morphism represented by its fraction. -/
@[simp]
theorem homColimit.equivTo.apply_ι
    (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] [W.HasLeftCalculusOfFractions] (X Y : C)
    (s : MorphismProperty.Under W ⊤ Y) (f : (homDiagram W X Y).obj s) :
    homColimit.equivTo L W X Y (colimit.ι (homDiagram W X Y) s f) =
      (fraction W X Y s f).map L (CategoryTheory.Localization.inverts L W) := sorry

/-- For a morphism property `W` with a left calculus of fractions, the localized Hom-set
`((Q W).obj X ⟶ (Q W).obj Y)` is canonically isomorphic to the filtered colimit of
`ULift (X ⟶ Y')` over denominators `s : Y ⟶ Y'` in
`MorphismProperty.Under W ⊤ Y`. -/
@[stacks 05Q1 "localized Hom-set as a filtered colimit over target denominators"]
noncomputable def homColimit.iso
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] (X Y : C) :
    colimit (homDiagram W X Y) ≅ ((Q W).obj X ⟶ (Q W).obj Y) :=
  (homColimit.equiv W X Y).toIso

/-- The localized Hom comparison sends the coprojection represented by a
numerator `f` and denominator `s` to their left-fraction class. -/
@[simp]
theorem homColimit.iso.hom_ι
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] (X Y : C)
    (s : MorphismProperty.Under W ⊤ Y) (f : (homDiagram W X Y).obj s) :
    (homColimit.iso W X Y).hom (colimit.ι (homDiagram W X Y) s f) =
      homMk (fraction W X Y s f) := sorry
/- Proof strategy: rewrite the abstract coprojection with
`Limits.Types.colimitEquivColimitType_apply`, unfold `homColimit.typeEquiv` and
`colimitTypeToHom`, and use the defining computation of
`Functor.descColimitType` on `Functor.ιColimitType`. -/

/-- The inverse localized Hom comparison sends the left-fraction class represented at a
target denominator back to its diagram coprojection. -/
@[simp]
theorem homColimit.iso.inv_hom_ι
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] (X Y : C)
    (s : MorphismProperty.Under W ⊤ Y) (f : (homDiagram W X Y).obj s) :
    (homColimit.iso W X Y).inv (homMk (fraction W X Y s f)) =
      colimit.ι (homDiagram W X Y) s f := sorry



end CategoryTheory.MorphismProperty.LeftFraction.Localization
