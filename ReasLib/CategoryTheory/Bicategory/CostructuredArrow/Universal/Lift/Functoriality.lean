/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Universal.Lift

/-!
# Functoriality of universal costructured-arrow lifts

Universal lifts are selected through inverse equivalences, so identities and composites agree
with the selected lifts only up to canonical invertible `2`-morphisms. This file owns those
shape-independent comparisons for an arbitrary pseudofunctor `K`.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe wA vA uA wC vC uC

namespace CategoryTheory

open Bicategory

namespace Bicategory.ColaxCostructuredArrow.IsUniversal

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {C : Type uC} [Bicategory.{wC, vC} C]
variable {K : A ⥤ᵖ C} {X : C}

/-- Comparison sends the identity source map of a costructured arrow to its structural map up to
the pseudofunctor unit constraint and the left unitor. -/
noncomputable def lift.id.comparisonIso (S : ColaxCostructuredArrow K X) :
    (S.comparison S.left).obj (𝟙 S.left) ≅ S.hom :=
  whiskerRightIso (K.mapId S.left) S.hom ≪≫ λ_ S.hom

/-- Comparison sends two successive universal lifts to the source structural map up to the
pseudofunctor composition constraint and the two chosen lift comparisons. -/
noncomputable def lift.comp.comparisonIso (R S T : ColaxCostructuredArrow K X)
    [S.IsUniversal] [T.IsUniversal] :
    (T.comparison R.left).obj (lift R S ≫ lift S T) ≅ R.hom :=
  whiskerRightIso (K.mapComp (lift R S) (lift S T)) T.hom ≪≫
    α_ (K.map (lift R S)) (K.map (lift S T)) T.hom ≪≫
    whiskerLeftIso (K.map (lift R S)) (lift.comparisonIso S T) ≪≫
    lift.comparisonIso R S

/-- The selected universal self-lift is canonically isomorphic to the identity source map. -/
noncomputable def lift.id.iso (S : ColaxCostructuredArrow K X) [S.IsUniversal] :
    𝟙 S.left ≅ lift S S :=
  lift.uniqueIso S S (𝟙 S.left) (lift.id.comparisonIso S)

/-- A composite of selected universal lifts is canonically isomorphic to the selected lift
between its endpoints. -/
noncomputable def lift.comp.iso (R S T : ColaxCostructuredArrow K X)
    [S.IsUniversal] [T.IsUniversal] :
    lift R S ≫ lift S T ≅ lift R T :=
  lift.uniqueIso R T (lift R S ≫ lift S T) (lift.comp.comparisonIso R S T)

namespace lift.id.iso

/-- Comparison sends the forward cell of the universal identity isomorphism to its canonical
identity presentation followed by the inverse selected-lift comparison. -/
@[simp]
theorem map_hom (S : ColaxCostructuredArrow K X) [S.IsUniversal] :
    (S.comparison S.left).map (lift.id.iso S).hom =
      (lift.id.comparisonIso S ≪≫ (lift.comparisonIso S S).symm).hom := sorry

/-- Comparison sends the inverse cell of the universal identity isomorphism to the inverse of
its canonical presentation composite. -/
@[simp]
theorem map_inv (S : ColaxCostructuredArrow K X) [S.IsUniversal] :
    (S.comparison S.left).map (lift.id.iso S).inv =
      (lift.id.comparisonIso S ≪≫ (lift.comparisonIso S S).symm).inv := sorry

end lift.id.iso

namespace lift.comp.iso

/-- Comparison sends the forward cell of the universal composition isomorphism to its canonical
composite presentation followed by the inverse endpoint lift comparison. -/
@[simp]
theorem map_hom (R S T : ColaxCostructuredArrow K X)
    [S.IsUniversal] [T.IsUniversal] :
    (T.comparison R.left).map (lift.comp.iso R S T).hom =
      (lift.comp.comparisonIso R S T ≪≫ (lift.comparisonIso R T).symm).hom := sorry

/-- Comparison sends the inverse cell of the universal composition isomorphism to the inverse
of its canonical presentation composite. -/
@[simp]
theorem map_inv (R S T : ColaxCostructuredArrow K X)
    [S.IsUniversal] [T.IsUniversal] :
    (T.comparison R.left).map (lift.comp.iso R S T).inv =
      (lift.comp.comparisonIso R S T ≪≫ (lift.comparisonIso R T).symm).inv := sorry

end lift.comp.iso

end Bicategory.ColaxCostructuredArrow.IsUniversal

end CategoryTheory
