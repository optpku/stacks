/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Family.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Postcompose.Lift
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

/-!
# Maps between explicitly selected bilimit apexes

A strong transformation between diagrams induces a universal map between the apexes
selected by a `BilimitConeFamily`; a modification induces a `2`-morphism between such
maps.

This file is the family-level facade of the shape-independent
`PseudoCone.mapDiagram` API. Identity and composition comparison isomorphisms, and the
resulting pseudofunctor, are layered downstream.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe uB vB wB uJ vJ wJ

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory

variable {J : Type uJ} [Bicategory.{wJ, vJ} J]
variable {B : Type uB} [Bicategory.{wB, vB} B]

namespace BilimitConeFamily

/-- The universal map between selected bilimit apexes induced by a diagram
transformation. -/
noncomputable def map (L : BilimitConeFamily (J := J) (B := B))
    {E F : Pseudofunctor J B} (α : E ⟶ F) :
    L.apex E ⟶ L.apex F :=
  PseudoCone.mapDiagram (L.cone E) (L.cone F) α

/-- The complete cone-transformation comparison specifying a selected bilimit-apex
map. -/
noncomputable def mapComparisonIso
    (L : BilimitConeFamily (J := J) (B := B))
    {E F : Pseudofunctor J B} (α : E ⟶ F) :
    ((L.cone F).comparison (L.apex E)).obj (L.map α) ≅
      (PseudoCone.postcomposeObj α (L.cone E)).π :=
  PseudoCone.mapDiagram.comparisonIso (L.cone E) (L.cone F) α

/-- The forward cell of a selected bilimit-apex comparison is the forward cell of the
shape-independent universal comparison. -/
@[simp]
theorem mapComparisonIso_hom
    (L : BilimitConeFamily (J := J) (B := B))
    {E F : Pseudofunctor J B} (α : E ⟶ F) :
    (L.mapComparisonIso α).hom =
      (PseudoCone.mapDiagram.comparisonIso (L.cone E) (L.cone F) α).hom := sorry

/-- The inverse cell of a selected bilimit-apex comparison is the inverse cell of the
shape-independent universal comparison. -/
@[simp]
theorem mapComparisonIso_inv
    (L : BilimitConeFamily (J := J) (B := B))
    {E F : Pseudofunctor J B} (α : E ⟶ F) :
    (L.mapComparisonIso α).inv =
      (PseudoCone.mapDiagram.comparisonIso (L.cone E) (L.cone F) α).inv := sorry

/-- A modification between diagram transformations induces a `2`-morphism between the
selected bilimit-apex maps. -/
noncomputable def map₂ (L : BilimitConeFamily (J := J) (B := B))
    {E F : Pseudofunctor J B} {α β : E ⟶ F} (Γ : α ⟶ β) :
    L.map α ⟶ L.map β :=
  PseudoCone.mapDiagram.map₂ (L.cone E) (L.cone F) Γ

/-- Mapping the identity modification gives the identity cell of the selected apex
map. -/
@[simp]
theorem map₂_id (L : BilimitConeFamily (J := J) (B := B))
    {E F : Pseudofunctor J B} (α : E ⟶ F) :
    L.map₂ (𝟙 α) = 𝟙 (L.map α) := sorry

/-- Mapping modifications between diagrams preserves their vertical composition. -/
@[simp]
theorem map₂_comp (L : BilimitConeFamily (J := J) (B := B))
    {E F : Pseudofunctor J B} {α β γ : E ⟶ F}
    (Γ : α ⟶ β) (Δ : β ⟶ γ) :
    L.map₂ (Γ ≫ Δ) = L.map₂ Γ ≫ L.map₂ Δ := sorry

/-- The represented comparison sends the selected bilimit-apex `2`-cell to the
postcomposed diagram modification, conjugated by the two universal comparisons. -/
@[simp]
theorem comparison_map_map₂
    (L : BilimitConeFamily (J := J) (B := B))
    {E F : Pseudofunctor J B} {α β : E ⟶ F} (Γ : α ⟶ β) :
    ((L.cone F).comparison (L.apex E)).map (L.map₂ Γ) =
      (L.mapComparisonIso α).hom ≫
        PseudoCone.postcomposeModification Γ (L.cone E) ≫
        (L.mapComparisonIso β).inv := sorry

/-- At a diagram vertex, the represented selected-apex `2`-cell is the postcomposed
modification conjugated by the two selected comparison components. -/
@[simp]
theorem comparison_map_map₂_app
    (L : BilimitConeFamily (J := J) (B := B))
    {E F : Pseudofunctor J B} {α β : E ⟶ F}
    (Γ : α ⟶ β) (j : J) :
    (((L.cone F).comparison (L.apex E)).map (L.map₂ Γ)).as.app j =
      (Pseudofunctor.StrongTrans.isoApp
        (L.mapComparisonIso α) j).hom ≫
        (PseudoCone.postcomposeModification Γ (L.cone E)).as.app j ≫
        (Pseudofunctor.StrongTrans.isoApp
          (L.mapComparisonIso β) j).inv := sorry

/- Data and axiom audit (mathlib 4.32):

`map`, `mapComparisonIso`, and `map₂` are direct specializations of the single
shape-independent `PseudoCone.mapDiagram.functor` associated to the two explicitly stored
cones. No family-level choice is introduced; noncomputability comes only from the
encapsulated quasi-inverse of the selected target cone's represented comparison. -/

end BilimitConeFamily

end Bicategory

end CategoryTheory
