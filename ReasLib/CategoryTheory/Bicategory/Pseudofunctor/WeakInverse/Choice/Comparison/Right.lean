/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.WeakInverse.Choice.Construction
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseEquivalence.Equivalence

/-!
# Target-side comparison for a chosen pseudoinverse

The chosen object equivalences assemble into an equivalence from the chosen
pseudoinverse followed by the original biequivalence to the identity.
-/

@[expose] public section

universe wB vB uB wC vC uC

namespace CategoryTheory.Pseudofunctor

open Bicategory
open scoped Bicategory Pseudofunctor.StrongTrans

variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]

namespace ChosenInverse

/-- Naturality of the target-side comparison from the chosen pseudoinverse
followed by `F` to the identity pseudofunctor. -/
noncomputable def rightNaturalityIso (F : B ⥤ᵖ C) [F.IsBiequivalence]
    {X Y : C} (f : X ⟶ Y) :
    ((F.chosenInverse.comp F).map f) ≫
        (objPreimage.equivalence F Y).hom ≅
      (objPreimage.equivalence F X).hom ≫ f :=
  Bicategory.whiskerRightIso (mapImage.iso F f)
      (objPreimage.equivalence F Y).hom ≪≫
    α_ ((objPreimage.equivalence F X).hom ≫ f)
      (objPreimage.equivalence F Y).inv
      (objPreimage.equivalence F Y).hom ≪≫
    Bicategory.whiskerLeftIso
      ((objPreimage.equivalence F X).hom ≫ f)
      (objPreimage.equivalence F Y).counit ≪≫
    ρ_ ((objPreimage.equivalence F X).hom ≫ f)

/-- The target-side comparison from the chosen pseudoinverse followed by `F`
to the identity pseudofunctor. -/
noncomputable def rightStrongTrans (F : B ⥤ᵖ C) [F.IsBiequivalence] :
    F.chosenInverse.comp F ⟶ Pseudofunctor.id C where
  app X := (objPreimage.equivalence F X).hom
  naturality := rightNaturalityIso F
  naturality_naturality := sorry
  naturality_id := sorry
  naturality_comp := sorry

/-- Pointwise equivalence data on the target-side comparison. -/
noncomputable def rightPointwise (F : B ⥤ᵖ C) [F.IsBiequivalence] :
    StrongTrans.PointwiseEquivalence (rightStrongTrans F) :=
  StrongTrans.PointwiseEquivalence.ofComponents
    (fun X ↦ objPreimage.equivalence F X) (fun _ ↦ Iso.refl _)

/-- The target-side equivalence from the chosen pseudoinverse followed by `F`
to the identity pseudofunctor. -/
noncomputable def rightEquivalence (F : B ⥤ᵖ C) [F.IsBiequivalence] :
    F.chosenInverse.comp F ≌ Pseudofunctor.id C :=
  (rightPointwise F).toEquivalence

end ChosenInverse

end CategoryTheory.Pseudofunctor
