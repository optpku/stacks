/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Postcompose.Pseudofunctor.Basic

/-!
# Computations for pseudocone postcomposition

This file exposes the principal fields and nested projections of
`PseudoCone.postcompose`. These formulas let downstream constructions compute through
the public pseudofunctor without unfolding its private prelax and coherence assembly.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe uB vB wB uJ vJ wJ

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory.PseudoCone

variable {J : Type uJ} [Bicategory.{wJ, vJ} J]
variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {E F : Pseudofunctor J B}


/-- The object action of pseudocone postcomposition is `postcomposeObj`. -/
@[simp]
theorem postcompose_obj
    (α : Pseudofunctor.StrongTrans E F) (S : PseudoCone E) :
    (postcompose α).obj S = postcomposeObj α S := sorry

/-- The `1`-morphism action of pseudocone postcomposition is `postcomposeMap`. -/
@[simp]
theorem postcompose_map
    (α : Pseudofunctor.StrongTrans E F)
    {S T : PseudoCone E} (u : S ⟶ T) :
    (postcompose α).map u = postcomposeMap α u := sorry

/-- The `2`-morphism action of pseudocone postcomposition is `postcomposeMap₂`. -/
@[simp]
theorem postcompose_map₂
    (α : Pseudofunctor.StrongTrans E F)
    {S T : PseudoCone E} {u v : S ⟶ T} (η : u ⟶ v) :
    (postcompose α).map₂ η = postcomposeMap₂ α η := sorry

/-- The identity comparison is the canonical `ColaxCostructuredArrow` comparison
field of `postcompose`. -/
@[simp]
theorem postcompose_mapId
    (α : Pseudofunctor.StrongTrans E F) (S : PseudoCone E) :
    (postcompose α).mapId S =
      ColaxCostructuredArrow.postcompose.mapId
        (K := Pseudofunctor.constDiagram J B) (X := E) (Y := F) α S := sorry

/-- The composition comparison is the canonical `ColaxCostructuredArrow`
comparison field of `postcompose`. -/
@[simp]
theorem postcompose_mapComp
    (α : Pseudofunctor.StrongTrans E F)
    {R S T : PseudoCone E} (u : R ⟶ S) (v : S ⟶ T) :
    (postcompose α).mapComp u v =
      ColaxCostructuredArrow.postcompose.mapComp
        (K := Pseudofunctor.constDiagram J B) (X := E) (Y := F) α u v := sorry

/-- Postcomposition leaves the apex of a pseudocone unchanged. -/
@[simp]
theorem postcompose_obj_pt
    (α : Pseudofunctor.StrongTrans E F) (S : PseudoCone E) :
    ((postcompose α).obj S).pt = S.pt := sorry

/-- The transformation of a postcomposed pseudocone is vertical composition with the
given diagram transformation. -/
@[simp]
theorem postcompose_obj_π
    (α : Pseudofunctor.StrongTrans E F) (S : PseudoCone E) :
    ((postcompose α).obj S).π = S.π ≫ α := sorry

/-- Postcomposition leaves the apex map of a pseudocone morphism unchanged. -/
@[simp]
theorem postcompose_map_map
    (α : Pseudofunctor.StrongTrans E F)
    {S T : PseudoCone E} (u : S ⟶ T) :
    PseudoCone.map ((postcompose α).map u) =
      PseudoCone.map u := sorry

/-- The comparison of a postcomposed pseudocone morphism is the explicit
associator-and-whiskering composite `postcomposeFac`. -/
@[simp]
theorem postcompose_map_fac
    (α : Pseudofunctor.StrongTrans E F)
    {S T : PseudoCone E} (u : S ⟶ T) :
    PseudoCone.fac ((postcompose α).map u) =
      postcomposeFac α u := sorry

/-- Postcomposition leaves the apex cell of a pseudocone `2`-morphism unchanged. -/
@[simp]
theorem postcompose_map₂_map₂
    (α : Pseudofunctor.StrongTrans E F)
    {S T : PseudoCone E} {u v : S ⟶ T} (η : u ⟶ v) :
    PseudoCone.map₂ ((postcompose α).map₂ η) =
      PseudoCone.map₂ η := sorry

/-- The forward identity comparison for pseudocone postcomposition has identity apex
cell. -/
@[simp]
theorem postcompose_mapId_hom_map₂
    (α : Pseudofunctor.StrongTrans E F) (S : PseudoCone E) :
    PseudoCone.map₂ ((postcompose α).mapId S).hom =
      𝟙 (𝟙 S.pt) := sorry

/-- The inverse identity comparison for pseudocone postcomposition has identity apex
cell. -/
@[simp]
theorem postcompose_mapId_inv_map₂
    (α : Pseudofunctor.StrongTrans E F) (S : PseudoCone E) :
    PseudoCone.map₂ ((postcompose α).mapId S).inv =
      𝟙 (𝟙 S.pt) := sorry

/-- The forward composition comparison for pseudocone postcomposition has identity apex
cell. -/
@[simp]
theorem postcompose_mapComp_hom_map₂
    (α : Pseudofunctor.StrongTrans E F)
    {R S T : PseudoCone E} (u : R ⟶ S) (v : S ⟶ T) :
    PseudoCone.map₂ ((postcompose α).mapComp u v).hom =
      𝟙 (PseudoCone.map u ≫ PseudoCone.map v) := sorry

/-- The inverse composition comparison for pseudocone postcomposition has identity apex
cell. -/
@[simp]
theorem postcompose_mapComp_inv_map₂
    (α : Pseudofunctor.StrongTrans E F)
    {R S T : PseudoCone E} (u : R ⟶ S) (v : S ⟶ T) :
    PseudoCone.map₂ ((postcompose α).mapComp u v).inv =
      𝟙 (PseudoCone.map u ≫ PseudoCone.map v) := sorry

/- Data and axiom audit (mathlib 4.32):

This module introduces no new data. Every theorem identifies a projection of
`postcompose` with the explicit object, morphism, cell, or comparison owner imported
from the preceding layers. -/

end Bicategory.PseudoCone

end CategoryTheory
