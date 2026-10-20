/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Localization.HomEquiv
public import ReasLib.CategoryTheory.MorphismProperty.Localization.RightFractionColimit.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparing the right-fraction Hom-colimit with localization models

The explicit quotient presentation is transported to arbitrary localization models. This leaf
also records the quotient-localization and canonical-localization isomorphisms together with
their coprojection computations.
-/

@[expose] public section

universe v u vD uD

namespace CategoryTheory.MorphismProperty.RightFraction.Localization

open Limits

variable {C : Type u} [Category.{v} C]
variable {D : Type uD} [Category.{vD} D]

/-- The concrete source-denominator colimit is equivalent to the Hom-set in any localization
model of `W`, obtained from the explicit right-fraction quotient. -/
noncomputable def homColimit.typeEquivTo
    (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] [W.HasRightCalculusOfFractions] (X Y : C) :
    (homDiagram W X Y).ColimitType ≃ (L.obj X ⟶ L.obj Y) :=
  (homColimit.typeEquiv W X Y).trans
    (CategoryTheory.Localization.homEquiv (X := X) (Y := Y) W
      (RightFraction.Localization.Q W) L)

/-- The model-independent concrete Hom-colimit comparison evaluates a diagram coprojection as
the corresponding right fraction in `L`. -/
@[simp]
theorem homColimit.typeEquivTo.apply_ιColimitType
    (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] [W.HasRightCalculusOfFractions] (X Y : C)
    (s : (MorphismProperty.Over W ⊤ X)ᵒᵖ) (f : (homDiagram W X Y).obj s) :
    homColimit.typeEquivTo L W X Y ((homDiagram W X Y).ιColimitType s f) =
      (fraction W X Y s f).map L (CategoryTheory.Localization.inverts L W) := sorry

/-- The model-independent concrete Hom-colimit comparison evaluates the canonical
representative of a right fraction in `L`. -/
@[simp]
theorem homColimit.typeEquivTo.apply_fractionToColimitType
    (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] [W.HasRightCalculusOfFractions] (X Y : C)
    (z : W.RightFraction X Y) :
    homColimit.typeEquivTo L W X Y (fractionToColimitType W X Y z) =
      z.map L (CategoryTheory.Localization.inverts L W) := sorry

/-- Pulling the localized image of a right fraction back through the concrete Hom-colimit
comparison gives its canonical colimit representative. -/
@[simp]
theorem homColimit.typeEquivTo.symm_apply_fraction_map
    (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] [W.HasRightCalculusOfFractions] (X Y : C)
    (z : W.RightFraction X Y) :
    (homColimit.typeEquivTo L W X Y).symm
        (z.map L (CategoryTheory.Localization.inverts L W)) =
      fractionToColimitType W X Y z := sorry

/-- For any localization model `L` of a morphism property `W` with a right calculus of
fractions, the localized Hom-set is canonically equivalent to the filtered colimit of
`ULift (X₀ ⟶ Y)` over source denominators `s : X₀ ⟶ X` in
`(MorphismProperty.Over W ⊤ X)ᵒᵖ`. -/
@[stacks 05Q4 "localized Hom-set as a filtered colimit",
  stacks 05Q5 "localized Hom-set as a colimit over source denominators"]
noncomputable def homColimit.equivTo
    (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] [W.HasRightCalculusOfFractions] (X Y : C) :
    (colimit (homDiagram W X Y) : Type (max u v)) ≃ (L.obj X ⟶ L.obj Y) :=
  (Limits.Types.colimitEquivColimitType (homDiagram W X Y)).trans
    (homColimit.typeEquivTo L W X Y)

/-- The model-independent Hom-colimit equivalence sends a coprojection to the localized
morphism represented by its right fraction. -/
@[simp]
theorem homColimit.equivTo.apply_ι
    (L : C ⥤ D) (W : MorphismProperty C)
    [L.IsLocalization W] [W.HasRightCalculusOfFractions] (X Y : C)
    (s : (MorphismProperty.Over W ⊤ X)ᵒᵖ) (f : (homDiagram W X Y).obj s) :
    homColimit.equivTo L W X Y (colimit.ι (homDiagram W X Y) s f) =
      (fraction W X Y s f).map L (CategoryTheory.Localization.inverts L W) := sorry

/-- The Hom-colimit formula with target the explicit right-fraction quotient localization. -/
noncomputable def homColimit.quotientIso
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions] (X Y : C) :
    colimit (homDiagram W X Y) ≅ ((Q W).obj X ⟶ (Q W).obj Y) :=
  (homColimit.equiv W X Y).toIso

/-- The explicit quotient Hom-colimit comparison sends a coprojection to the corresponding
right-fraction localization morphism. -/
@[simp]
theorem homColimit.quotientIso.hom_ι
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions] (X Y : C)
    (s : (MorphismProperty.Over W ⊤ X)ᵒᵖ) (f : (homDiagram W X Y).obj s) :
    (homColimit.quotientIso W X Y).hom (colimit.ι (homDiagram W X Y) s f) =
      homMk (fraction W X Y s f) := sorry

/-- The inverse quotient comparison sends the right-fraction class represented at a source
denominator back to its diagram coprojection. -/
@[simp]
theorem homColimit.quotientIso.inv_hom_ι
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions] (X Y : C)
    (s : (MorphismProperty.Over W ⊤ X)ᵒᵖ) (f : (homDiagram W X Y).obj s) :
    (homColimit.quotientIso W X Y).inv (homMk (fraction W X Y s f)) =
      colimit.ι (homDiagram W X Y) s f := sorry

/-- The Hom-colimit formula with target mathlib's canonical localization model `W.Q`. -/
noncomputable def homColimit.iso
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions] (X Y : C) :
    colimit (homDiagram W X Y) ≅ (W.Q.obj X ⟶ W.Q.obj Y) :=
  (homColimit.equivTo W.Q W X Y).toIso

/-- The canonical-localization Hom-colimit comparison sends a coprojection to the corresponding
right fraction. -/
@[simp]
theorem homColimit.iso.hom_ι
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions] (X Y : C)
    (s : (MorphismProperty.Over W ⊤ X)ᵒᵖ) (f : (homDiagram W X Y).obj s) :
    (homColimit.iso W X Y).hom (colimit.ι (homDiagram W X Y) s f) =
      (fraction W X Y s f).mapQ := sorry

/-- The inverse canonical-localization comparison sends the localized right fraction
represented at a source denominator back to its diagram coprojection. -/
@[simp]
theorem homColimit.iso.inv_ι
    (W : MorphismProperty C) [W.HasRightCalculusOfFractions] (X Y : C)
    (s : (MorphismProperty.Over W ⊤ X)ᵒᵖ) (f : (homDiagram W X Y).obj s) :
    (homColimit.iso W X Y).inv ((fraction W X Y s f).mapQ) =
      colimit.ι (homDiagram W X Y) s f := sorry



end CategoryTheory.MorphismProperty.RightFraction.Localization
