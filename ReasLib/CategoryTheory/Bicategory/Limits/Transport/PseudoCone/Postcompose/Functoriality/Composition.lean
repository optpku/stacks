/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Postcompose.Lift

/-!
# Composition comparison for universal maps induced by diagram transformations

Universal maps induced by successive strong transformations compose canonically to the
universal map induced by their vertical composite. The presentation in this file is valid
for three arbitrary diagrams and does not assume that the source pseudocone is a bilimit.

The comparison is recorded both as an isomorphism of apex maps and after applying the
represented comparison functor. Projection formulas expose the underlying pasting without
requiring downstream code to unfold a long chain of `Iso.trans`.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe uB vB wB uJ vJ wJ

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory.PseudoCone

variable {J : Type uJ} [Bicategory.{wJ, vJ} J]
variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {E F G : Pseudofunctor J B}

/-- The composite of two universal diagram maps presents postcomposition by the composite
diagram transformation.

The pasting consists of the constant-diagram composition comparison, the universal
comparison for the second map, the universal comparison for the first map, and the
associators for vertical composition of strong transformations. -/
noncomputable def mapDiagram.comp.comparisonIso
    (S : PseudoCone E) (T : PseudoCone F) (U : PseudoCone G)
    [T.IsBilimit] [U.IsBilimit]
    (α : E ⟶ F) (β : F ⟶ G) :
    (U.comparison S.pt).obj
        (mapDiagram S T α ≫ mapDiagram T U β) ≅
      (postcomposeObj (α ≫ β) S).π :=
  Bicategory.whiskerRightIso
      ((Pseudofunctor.constDiagram J B).mapComp
        (mapDiagram S T α) (mapDiagram T U β)) U.π ≪≫
    α_ _ _ _ ≪≫
    Bicategory.whiskerLeftIso
      ((Pseudofunctor.constDiagram J B).map
        (mapDiagram S T α))
      (mapDiagram.comparisonIso T U β) ≪≫
    (α_ _ _ _).symm ≪≫
    Bicategory.whiskerRightIso
      (mapDiagram.comparisonIso S T α) β ≪≫
    α_ _ _ _

/-- The forward cell of the composite-map presentation is the explicit six-stage
pasting of composition comparison, associators, and universal comparisons. -/
@[simp]
theorem mapDiagram.comp.comparisonIso.hom
    (S : PseudoCone E) (T : PseudoCone F) (U : PseudoCone G)
    [T.IsBilimit] [U.IsBilimit]
    (α : E ⟶ F) (β : F ⟶ G) :
    (mapDiagram.comp.comparisonIso S T U α β).hom =
      (Bicategory.whiskerRightIso
        ((Pseudofunctor.constDiagram J B).mapComp
          (mapDiagram S T α) (mapDiagram T U β)) U.π).hom ≫
      (α_ _ _ _).hom ≫
      (Bicategory.whiskerLeftIso
        ((Pseudofunctor.constDiagram J B).map
          (mapDiagram S T α))
        (mapDiagram.comparisonIso T U β)).hom ≫
      (α_ _ _ _).inv ≫
      (Bicategory.whiskerRightIso
        (mapDiagram.comparisonIso S T α) β).hom ≫
      (α_ _ _ _).hom := sorry

/-- The inverse cell of the composite-map presentation is the reverse six-stage
pasting. -/
@[simp]
theorem mapDiagram.comp.comparisonIso.inv
    (S : PseudoCone E) (T : PseudoCone F) (U : PseudoCone G)
    [T.IsBilimit] [U.IsBilimit]
    (α : E ⟶ F) (β : F ⟶ G) :
    (mapDiagram.comp.comparisonIso S T U α β).inv =
      (α_ _ _ _).inv ≫
      (Bicategory.whiskerRightIso
        (mapDiagram.comparisonIso S T α) β).inv ≫
      (α_ _ _ _).hom ≫
      (Bicategory.whiskerLeftIso
        ((Pseudofunctor.constDiagram J B).map
          (mapDiagram S T α))
        (mapDiagram.comparisonIso T U β)).inv ≫
      (α_ _ _ _).inv ≫
      (Bicategory.whiskerRightIso
        ((Pseudofunctor.constDiagram J B).mapComp
          (mapDiagram S T α) (mapDiagram T U β)) U.π).inv := sorry

/-- Universal maps along successive diagram transformations compose canonically to the
universal map along their composite. -/
noncomputable abbrev mapDiagram.comp.iso
    (S : PseudoCone E) (T : PseudoCone F) (U : PseudoCone G)
    [T.IsBilimit] [U.IsBilimit]
    (α : E ⟶ F) (β : F ⟶ G) :
    mapDiagram S T α ≫ mapDiagram T U β ≅
      mapDiagram S U (α ≫ β) :=
  PseudoCone.lift.uniqueIso (postcomposeObj (α ≫ β) S) U
    (mapDiagram S T α ≫ mapDiagram T U β)
    (mapDiagram.comp.comparisonIso S T U α β)

/-- Under the represented comparison, the forward composition coherence is the explicit
composite presentation followed by the inverse universal comparison. -/
@[simp]
theorem mapDiagram.comp.iso.map_hom
    (S : PseudoCone E) (T : PseudoCone F) (U : PseudoCone G)
    [T.IsBilimit] [U.IsBilimit]
    (α : E ⟶ F) (β : F ⟶ G) :
    (U.comparison S.pt).map (mapDiagram.comp.iso S T U α β).hom =
      (mapDiagram.comp.comparisonIso S T U α β ≪≫
        (mapDiagram.comparisonIso S U (α ≫ β)).symm).hom := sorry

/-- Under the represented comparison, the inverse composition coherence is the inverse of
the explicit composite-presentation comparison. -/
@[simp]
theorem mapDiagram.comp.iso.map_inv
    (S : PseudoCone E) (T : PseudoCone F) (U : PseudoCone G)
    [T.IsBilimit] [U.IsBilimit]
    (α : E ⟶ F) (β : F ⟶ G) :
    (U.comparison S.pt).map (mapDiagram.comp.iso S T U α β).inv =
        (mapDiagram.comp.comparisonIso S T U α β ≪≫
        (mapDiagram.comparisonIso S U (α ≫ β)).symm).inv := sorry

/-- The universal-map action on a left-whiskered diagram modification is controlled by the
composition comparison isomorphisms. -/
@[simp]
theorem mapDiagram.map₂.whiskerLeft
    (S : PseudoCone E) (T : PseudoCone F) (U : PseudoCone G)
    [T.IsBilimit] [U.IsBilimit]
    (α : E ⟶ F) {β γ : F ⟶ G} (Γ : β ⟶ γ) :
    mapDiagram.map₂ S U (α ◁ Γ) =
      (mapDiagram.comp.iso S T U α β).inv ≫
        mapDiagram S T α ◁ mapDiagram.map₂ T U Γ ≫
      (mapDiagram.comp.iso S T U α γ).hom := sorry

/-- The universal-map action on a right-whiskered diagram modification is controlled by the
composition comparison isomorphisms. -/
@[simp]
theorem mapDiagram.map₂.whiskerRight
    (S : PseudoCone E) (T : PseudoCone F) (U : PseudoCone G)
    [T.IsBilimit] [U.IsBilimit]
    {α β : E ⟶ F} (Γ : α ⟶ β) (γ : F ⟶ G) :
    mapDiagram.map₂ S U (Γ ▷ γ) =
      (mapDiagram.comp.iso S T U α γ).inv ≫
        mapDiagram.map₂ S T Γ ▷ mapDiagram T U γ ≫
      (mapDiagram.comp.iso S T U β γ).hom := sorry

/- Data and axiom audit (mathlib 4.32):

`mapDiagram.comp.comparisonIso` is an explicit pasting of canonical pseudofunctor
composition comparisons, associators, and the two already specified lift comparisons.
`mapDiagram.comp.iso` then uses the generic uniqueness isomorphism for the final bilimit
lift. No additional apex map or comparison cell is selected by an opaque witness. -/

end Bicategory.PseudoCone

end CategoryTheory
