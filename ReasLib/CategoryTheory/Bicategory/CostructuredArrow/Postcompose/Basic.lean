/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Basic

/-!
# Postcomposition of colax costructured arrows

This file contains the object-level action of a target `1`-morphism on colax
costructured arrows. For `K : A ⥤ᵖ C` and `f : X ⟶ Y`, it sends the structural
map `S.hom : K.obj S.left ⟶ X` to `S.hom ≫ f`.

The action of target `2`-morphisms is obtained from mathlib's
`Bicategory.postcomposing` functor and ordinary evaluation. Transport of
costructured-arrow `1`- and `2`-morphisms belongs in downstream modules.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe uA vA wA uC vC wC

namespace CategoryTheory

open Bicategory

namespace Bicategory.ColaxCostructuredArrow

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {C : Type uC} [Bicategory.{wC, vC} C]
variable {K : Pseudofunctor A C}
variable {X Y : C}

namespace postcompose

/-- Postcompose the structural map of a colax costructured arrow by a target
`1`-morphism.

The source object is retained literally, while the structural map is changed
from `S.hom` to `S.hom ≫ f`. -/
def obj (f : X ⟶ Y) (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow K Y :=
  ColaxCostructuredArrow.mk S.left (S.hom ≫ f)

/-- Postcomposition does not change the source object of a colax costructured
arrow. -/
@[simp]
theorem obj.left
    (f : X ⟶ Y) (S : ColaxCostructuredArrow K X) :
    (obj f S).left = S.left := sorry

/-- The structural map of a postcomposed colax costructured arrow is the
corresponding composite. -/
@[simp]
theorem obj.hom
    (f : X ⟶ Y) (S : ColaxCostructuredArrow K X) :
    (obj f S).hom = S.hom ≫ f := sorry

variable (Y) in
/-- For a fixed colax costructured arrow, postcomposition of its structural map
is functorial in the target `1`-morphism.

This is the evaluation at `S.hom` of mathlib's functor
`Bicategory.postcomposing (K.obj S.left) X Y`. The target object `Y` is
explicit because it is not determined by `S`. -/
def structuralFunctor (S : ColaxCostructuredArrow K X) :
    (X ⟶ Y) ⥤ (K.obj S.left ⟶ Y) :=
  Bicategory.postcomposing (K.obj S.left) X Y ⋙
    (evaluation (K.obj S.left ⟶ X) (K.obj S.left ⟶ Y)).obj S.hom

/-- The object action of `postcompose.structuralFunctor` is the structural map
of the corresponding postcomposed costructured arrow. -/
@[simp]
theorem structuralFunctor.obj
    (S : ColaxCostructuredArrow K X) (f : X ⟶ Y) :
    (structuralFunctor Y S).obj f =
      (obj f S).hom := sorry

/-- A target `2`-morphism acts on the structural map of a fixed colax
costructured arrow by left whiskering. -/
abbrev cell
    {f g : X ⟶ Y} (η : f ⟶ g)
    (S : ColaxCostructuredArrow K X) :
    (obj f S).hom ⟶ (obj g S).hom :=
  (structuralFunctor Y S).map η

/-- The cell induced by a target `2`-morphism is ordinary left whiskering by
the structural map. -/
@[simp]
theorem cell.apply
    {f g : X ⟶ Y} (η : f ⟶ g)
    (S : ColaxCostructuredArrow K X) :
    cell η S = S.hom ◁ η := sorry

/-- Postcomposition sends an identity target cell to an identity cell. -/
@[simp]
theorem cell.id
    (f : X ⟶ Y) (S : ColaxCostructuredArrow K X) :
    cell (𝟙 f) S =
      𝟙 (obj f S).hom := sorry

/-- Postcomposition preserves vertical composition of target cells. -/
@[simp]
theorem cell.comp
    {f g h : X ⟶ Y} (η : f ⟶ g) (θ : g ⟶ h)
    (S : ColaxCostructuredArrow K X) :
    cell (η ≫ θ) S =
      cell η S ≫ cell θ S := sorry

/- Data and axiom audit (mathlib 4.32):

`postcompose.obj` explicitly retains `S.left` and composes `S.hom` with `f`.
`postcompose.structuralFunctor` is the composite of mathlib's existing
`Bicategory.postcomposing` and evaluation functors. Consequently
`postcompose.cell` contains no selected witness or new coherence datum. -/

end postcompose

end Bicategory.ColaxCostructuredArrow

end CategoryTheory
