/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Hom
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoCone.Hom
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Postcompose.Basic

/-!
# Postcomposition of morphisms of conical pseudocones

A fixed strong transformation of diagrams postcomposes not only pseudocones, but also
their `1`- and `2`-morphisms. Apex maps and apex `2`-cells remain unchanged; only the
comparison modification of a pseudocone morphism is postcomposed.

This file contains the data-level action and its projection formulas. Identity,
composition, and pseudofunctor coherence are layered in downstream modules.
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

/-- The comparison modification of a pseudocone morphism after postcomposing the diagram.

The inverse associator exposes the original comparison as the left factor, after which
right whiskering postcomposes that comparison by `α`. -/
abbrev postcomposeFac
    (α : Pseudofunctor.StrongTrans E F)
    {S T : PseudoCone E} (u : S ⟶ T) :
    ((postcomposeObj α T).comparison S.pt).obj (PseudoCone.map u) ⟶
      (postcomposeObj α S).π :=
  ColaxCostructuredArrow.postcompose.fac
    (K := Pseudofunctor.constDiagram J B) (X := E) (Y := F) α u

/-- At a diagram vertex, the postcomposed comparison is the associator component followed
by right whiskering of the original comparison. -/
@[simp]
theorem postcomposeFac_app
    (α : Pseudofunctor.StrongTrans E F)
    {S T : PseudoCone E} (u : S ⟶ T) (j : J) :
    (postcomposeFac α u).as.app j =
      ((α_
        ((Pseudofunctor.constDiagram J B).map (PseudoCone.map u))
        T.π α).inv).as.app j ≫
        (PseudoCone.fac u).as.app j ▷ α.app j := sorry

/-- Postcompose a morphism of conical pseudocones by a strong transformation of diagrams.
Its apex map is unchanged and its comparison modification is `postcomposeFac`. -/
abbrev postcomposeMap
    (α : Pseudofunctor.StrongTrans E F)
    {S T : PseudoCone E} (u : S ⟶ T) :
    postcomposeObj α S ⟶ postcomposeObj α T :=
  ColaxCostructuredArrow.postcompose.map
    (K := Pseudofunctor.constDiagram J B) (X := E) (Y := F) α u

/-- Postcomposition of a pseudocone morphism leaves its apex map unchanged. -/
@[simp]
theorem postcomposeMap_map
    (α : Pseudofunctor.StrongTrans E F)
    {S T : PseudoCone E} (u : S ⟶ T) :
    PseudoCone.map (postcomposeMap α u) = PseudoCone.map u := sorry

/-- The comparison modification of a postcomposed pseudocone morphism is
`postcomposeFac`. -/
@[simp]
theorem postcomposeMap_fac
    (α : Pseudofunctor.StrongTrans E F)
    {S T : PseudoCone E} (u : S ⟶ T) :
    PseudoCone.fac (postcomposeMap α u) = postcomposeFac α u := sorry

/-- The vertex component of the comparison carried by a postcomposed pseudocone morphism
is the explicit associator-and-whiskering composite. -/
@[simp]
theorem postcomposeMap_fac_app
    (α : Pseudofunctor.StrongTrans E F)
    {S T : PseudoCone E} (u : S ⟶ T) (j : J) :
    (PseudoCone.fac (postcomposeMap α u)).as.app j =
      ((α_
        ((Pseudofunctor.constDiagram J B).map (PseudoCone.map u))
        T.π α).inv).as.app j ≫
        (PseudoCone.fac u).as.app j ▷ α.app j := sorry

/-- Postcompose a `2`-morphism of conical pseudocones by a strong transformation of
diagrams. Its apex cell is unchanged. -/
abbrev postcomposeMap₂
    (α : Pseudofunctor.StrongTrans E F)
    {S T : PseudoCone E} {u v : S ⟶ T} (η : u ⟶ v) :
    postcomposeMap α u ⟶ postcomposeMap α v :=
  ColaxCostructuredArrow.postcompose.map₂
    (K := Pseudofunctor.constDiagram J B) (X := E) (Y := F) α η

/-- Postcomposition of a pseudocone `2`-morphism leaves its apex cell unchanged. -/
@[simp]
theorem postcomposeMap₂_map₂
    (α : Pseudofunctor.StrongTrans E F)
    {S T : PseudoCone E} {u v : S ⟶ T} (η : u ⟶ v) :
    PseudoCone.map₂ (postcomposeMap₂ α η) = PseudoCone.map₂ η := sorry

/- Data and axiom audit (mathlib 4.32):

The comparison, `1`-morphism, and `2`-morphism actions are transparent specializations of
the canonical `ColaxCostructuredArrow` postcomposition API. Hence this readable layer adds
no second data owner or compatibility proof; its deferred statements only expose
`PseudoCone`-specific apex and diagram-component formulas. -/

end Bicategory.PseudoCone

end CategoryTheory
