/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Family.Map
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Postcompose.Functoriality.Composition
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

/-!
# Composition comparison for a family of selected bilimit apexes

For an explicit `BilimitConeFamily`, universal maps induced by successive diagram
transformations compose canonically to the map induced by their composite.

The family-facing comparison is oriented as
`map (α ≫ β) ≅ map α ≫ map β`, matching the `mapComp` field of a pseudofunctor.
The complete represented-cone presentation and its two projection formulas are retained
for downstream coherence arguments.
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

/-- The composite of two selected universal apex maps, viewed through the target
represented comparison, presents postcomposition by the composite diagram
transformation. -/
noncomputable abbrev mapCompComparisonIso
    (L : BilimitConeFamily (J := J) (B := B))
    {E F G : Pseudofunctor J B} (α : E ⟶ F) (β : F ⟶ G) :
    ((L.cone G).comparison (L.apex E)).obj
        (L.map α ≫ L.map β) ≅
      (PseudoCone.postcomposeObj (α ≫ β) (L.cone E)).π :=
  PseudoCone.mapDiagram.comp.comparisonIso
    (L.cone E) (L.cone F) (L.cone G) α β

/-- The forward cell of the family-level composite presentation is the explicit pasting of
constant-diagram composition, associators, and the two selected universal
comparisons. -/
@[simp]
theorem mapCompComparisonIso_hom
    (L : BilimitConeFamily (J := J) (B := B))
    {E F G : Pseudofunctor J B} (α : E ⟶ F) (β : F ⟶ G) :
    (L.mapCompComparisonIso α β).hom =
      (Bicategory.whiskerRightIso
        ((Pseudofunctor.constDiagram J B).mapComp
          (L.map α) (L.map β)) (L.cone G).π).hom ≫
      (α_ _ _ _).hom ≫
      (Bicategory.whiskerLeftIso
        ((Pseudofunctor.constDiagram J B).map (L.map α))
        (L.mapComparisonIso β)).hom ≫
      (α_ _ _ _).inv ≫
      (Bicategory.whiskerRightIso
        (L.mapComparisonIso α) β).hom ≫
      (α_ _ _ _).hom := sorry

/-- The inverse cell of the family-level composite presentation is the reverse explicit
pasting. -/
@[simp]
theorem mapCompComparisonIso_inv
    (L : BilimitConeFamily (J := J) (B := B))
    {E F G : Pseudofunctor J B} (α : E ⟶ F) (β : F ⟶ G) :
    (L.mapCompComparisonIso α β).inv =
      (α_ _ _ _).inv ≫
      (Bicategory.whiskerRightIso
        (L.mapComparisonIso α) β).inv ≫
      (α_ _ _ _).hom ≫
      (Bicategory.whiskerLeftIso
        ((Pseudofunctor.constDiagram J B).map (L.map α))
        (L.mapComparisonIso β)).inv ≫
      (α_ _ _ _).inv ≫
      (Bicategory.whiskerRightIso
        ((Pseudofunctor.constDiagram J B).mapComp
          (L.map α) (L.map β)) (L.cone G).π).inv := sorry

/-- The composition comparison for the selected bilimit-apex assignment, oriented as
required by a pseudofunctor. -/
noncomputable abbrev mapCompIso
    (L : BilimitConeFamily (J := J) (B := B))
    {E F G : Pseudofunctor J B} (α : E ⟶ F) (β : F ⟶ G) :
    L.map (α ≫ β) ≅ L.map α ≫ L.map β :=
  (PseudoCone.mapDiagram.comp.iso
    (L.cone E) (L.cone F) (L.cone G) α β).symm

/-- The forward family-level composition cell is the inverse universal-lift composition
cell. -/
@[simp]
theorem mapCompIso_hom
    (L : BilimitConeFamily (J := J) (B := B))
    {E F G : Pseudofunctor J B} (α : E ⟶ F) (β : F ⟶ G) :
    (L.mapCompIso α β).hom =
      (PseudoCone.mapDiagram.comp.iso
        (L.cone E) (L.cone F) (L.cone G) α β).inv := sorry

/-- The inverse family-level composition cell is the forward universal-lift composition
cell. -/
@[simp]
theorem mapCompIso_inv
    (L : BilimitConeFamily (J := J) (B := B))
    {E F G : Pseudofunctor J B} (α : E ⟶ F) (β : F ⟶ G) :
    (L.mapCompIso α β).inv =
      (PseudoCone.mapDiagram.comp.iso
        (L.cone E) (L.cone F) (L.cone G) α β).hom := sorry

/-- The represented comparison sends the forward family-level composition coherence to
the inverse explicit composite presentation followed by the universal comparison. -/
@[simp]
theorem comparison_map_mapCompIso_hom
    (L : BilimitConeFamily (J := J) (B := B))
    {E F G : Pseudofunctor J B} (α : E ⟶ F) (β : F ⟶ G) :
    ((L.cone G).comparison (L.apex E)).map
        (L.mapCompIso α β).hom =
      (L.mapCompComparisonIso α β ≪≫
        (L.mapComparisonIso (α ≫ β)).symm).inv := sorry

/-- The represented comparison sends the inverse family-level composition coherence to
the forward explicit composite presentation followed by the inverse universal
comparison. -/
@[simp]
theorem comparison_map_mapCompIso_inv
    (L : BilimitConeFamily (J := J) (B := B))
    {E F G : Pseudofunctor J B} (α : E ⟶ F) (β : F ⟶ G) :
    ((L.cone G).comparison (L.apex E)).map
        (L.mapCompIso α β).inv =
      (L.mapCompComparisonIso α β ≪≫
        (L.mapComparisonIso (α ≫ β)).symm).hom := sorry

/- Data and axiom audit (mathlib 4.32):

`mapCompComparisonIso` directly specializes the shape-independent composite presentation,
and `mapCompIso` only reverses its universal-lift orientation for the pseudofunctor API.
No family-level composition map, comparison cell, or witness is independently chosen. -/

end BilimitConeFamily

end Bicategory

end CategoryTheory
